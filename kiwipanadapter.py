#!/usr/bin/env python3
## -*- python -*-
#
# Lightweight local panadapter: a live waterfall + S-meter + audio player
# for the band around whatever frequency FreeDV (via a real rigctld) is
# currently tuned to. Deliberately avoids a browser and heavy GUI
# toolkits/plotting libraries to keep CPU/GPU load down; uses stock
# Tkinter only.
#
# The frequency/mode is learned by polling a rigctld TCP port (the same
# interface FreeDV itself talks to, normally a real hamlib rigctld driving
# an actual radio) -- this script is just another rigctl client. Waterfall
# (LiveWFStream) and audio (LiveAudioStream) are two independent Kiwi
# connections, both retuned in-process from that same rigctl polling --
# audio no longer needs a separately-spawned kiwiclientd.py process.

import argparse
import logging
import math
import os
import queue
import socket
import threading
import time
from queue import Queue, Empty
from types import SimpleNamespace

import numpy as np
import soundcard as sc
import tkinter as tk
from tkinter import ttk

from kiwi.client import KiwiSDRStream
from kiwi.worker import KiwiWorker

HAS_RESAMPLER = True
try:
    from samplerate import Resampler
except ImportError:
    HAS_RESAMPLER = False

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SDR_LIST = os.path.join(SCRIPT_DIR, 'sdr_list.txt')
DEFAULT_CONFIG = os.path.join(SCRIPT_DIR, 'panadapter.conf')
WF_NATIVE_BINS = 1024   # matches Kiwi's fixed waterfall bin count -- native buffer width
MAX_FREQ_KHZ = 30000.0  # Kiwi's full tunable range; zoom 0 spans this whole width
MAX_HISTORY_ROWS = 600  # native buffer height (scrollback); displayed height can be less or more
DEFAULT_WINDOW_HEIGHT = 300
WF_CAL = -13           # typical Kiwi waterfall calibration offset, dB
MAX_RECONNECT_RETRIES = 5     # per-side auto-retry cap when a connection dies unexpectedly (see _poll_reconnect)
RECONNECT_RETRY_DELAY_SEC = 2.0
RECONNECT_HEALTHY_RESET_SEC = 3.0  # a stream up this long counts as recovered -- resets the retry counter
                                    # (some Kiwis/proxies cleanly kick a mimic_browser connection every ~10s
                                    # regardless; without this, that alone exhausts MAX_RECONNECT_RETRIES and
                                    # the app gives up for good even though every individual reconnect works)

# Real headers/URL path captured from an actual Firefox 140 connecting to a
# KiwiSDR (packet capture, 2026-07-30) -- some Kiwis (confirmed: a genuine
# KiwiSDR 2, firmware 1.902) allow a browser's own two connections (SND +
# W/F) from one IP but block a second bare/API-style connection from the
# same IP. Live-tested: mimicking these gets both connections through
# reliably (5/6 clean, the one miss was an explicit fast rejection likely
# from leftover server-side state during rapid back-to-back test runs, not
# a repeatable "no"). Used only for SDR entries flagged 'mimic_browser' in
# sdr_list.txt -- see make_stream_options().
BROWSER_MIMIC_URL_PREFIX = '/ws/kiwi'
# Real client self-identification string captured from the same Firefox
# session -- sent once per connection right after 'SET auth', as
# 'SERVER DE CLIENT <name> <SND|W/F>'. This is the exact string Weston's own
# page already causes a real browser visit to send; some Kiwis may cap
# session length for connections that never identify themselves this way.
BROWSER_MIMIC_CLIENT_IDENT = 'openwebrx.js'
BROWSER_MIMIC_HEADERS = [
    'User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:140.0) Gecko/20100101 Firefox/140.0',
    'Accept: */*',
    'Accept-Language: en-US,en;q=0.5',
    'Accept-Encoding: gzip, deflate',
    'DNT: 1',
    'Pragma: no-cache',
    'Cache-Control: no-cache',
]
# Exact header emission order captured from the same Firefox session -- the
# values above already matched, but kiwi/wsclient.py's default handshake
# groups its own WS-protocol headers first and appends extras afterward,
# which doesn't match how a real browser interleaves them. Some
# servers/proxies fingerprint clients by header order, not just content.
BROWSER_MIMIC_HEADER_ORDER = [
    'Host', 'User-Agent', 'Accept', 'Accept-Language', 'Accept-Encoding',
    'Sec-WebSocket-Version', 'Origin', 'Sec-WebSocket-Extensions',
    'Sec-WebSocket-Key', 'DNT', 'Connection', 'Pragma', 'Cache-Control',
    'Upgrade',
]

def parse_bool(val):
    return val.strip().lower() in ('1', 'true', 'yes', 'on')


# Adjustable settings that live in the flat text config file, with their types
CONFIG_SCHEMA = {
    'span_khz': float,
    'mindb': float,
    'maxdb': float,
    'rigctl_host': str,
    'rigctl_port': int,
    'default_freq': float,
    'smeter_decay_db_sec': float,
    'smeter_cal_db': float,
    'smeter_peak_hold_sec': float,
    'smeter_peak_decay_db_sec': float,
    'smeter_passband_center_hz': float,
    'smeter_passband_bw_hz': float,
    'wf_auto_range_db': float,
    'wf_auto_beta': float,
    'wf_auto_percentile': float,
    'freq_major_khz': float,
    'freq_minor_khz': float,
    'window_height': int,
    'window_x': int,
    'window_y': int,
    'last_sdr': str,
    'modulation': str,
    'sounddevice': str,
    'ncomp': parse_bool,
    'lp_cut': float,
    'hp_cut': float,
    'agc_gain': float,
    'blocksize': int,
    'nb': parse_bool,
    'nb_gate': int,
    'nb_thresh': int,
    'de_emp': parse_bool,
    'resample': int,
    'ifreq': float,
}


def zoom_for_span(span_khz, max_freq_khz=MAX_FREQ_KHZ, max_zoom=14):
    """Largest (most zoomed-in) Kiwi zoom level whose span still covers span_khz."""
    for z in range(max_zoom, -1, -1):
        if max_freq_khz / (2 ** z) >= span_khz:
            return z
    return 0


def span_for_zoom(zoom, max_freq_khz=MAX_FREQ_KHZ):
    """Actual bandwidth (kHz) the Kiwi delivers at a given zoom level -- a coarser,
    power-of-two-quantized value that's usually wider than any requested span_khz."""
    return max_freq_khz / (2 ** zoom)


def nearest_resize(img, new_h, new_w):
    """Cheap nearest-neighbor resize (up or down) of an (H,W,3) uint8 array, numpy only."""
    src_h, src_w = img.shape[:2]
    row_idx = (np.arange(new_h) * src_h // new_h).astype(np.intp)
    col_idx = (np.arange(new_w) * src_w // new_w).astype(np.intp)
    return img[row_idx][:, col_idx]


def tick_positions(start_khz, stop_khz, step):
    """kHz values of ticks at multiples of step within [start_khz, stop_khz], drift-free."""
    if step <= 0:
        return []
    first = math.ceil(start_khz / step) * step
    n = int(math.floor((stop_khz - first) / step + 1e-9)) + 1
    return [first + i * step for i in range(max(n, 0))]


def build_colormap():
    """Reproduce the Kiwi web UI's waterfall color palette as a 256x3 uint8 LUT."""
    lut = np.zeros((256, 3), dtype=np.uint8)
    for i in range(256):
        if i < 32:
            r, g, b = 0, 0, i * 255 // 31
        elif i < 72:
            r, g, b = 0, (i - 32) * 255 // 39, 255
        elif i < 96:
            r, g, b = 0, 255, 255 - (i - 72) * 255 // 23
        elif i < 116:
            r, g, b = (i - 96) * 255 // 19, 255, 0
        elif i < 184:
            r, g, b = 255, 255 - (i - 116) * 255 // 67, 0
        else:
            r, g, b = 255, 0, (i - 184) * 128 // 70
        lut[i] = (r, g, b)
    return lut


COLORMAP = build_colormap()


def make_stream_options(host, port, options, ws_offset=0, mimic_browser=False, ws_timestamp=None):
    """Attribute set KiwiSDRStream/KiwiWorker need, covering both
    LiveWFStream (a plain W/F-only connection, like kiwirecorder's own
    KiwiWaterfallRecorder) and LiveAudioStream (audio playback, ported from
    kiwiclientd's KiwiSoundRecorder) -- these are two independent
    connections/channels, so by default each gets its own ws_timestamp
    (ws_offset differentiates them -- the SND/W/F suffix in the URL already
    keeps the two apart, so this is just extra insurance). Pass an explicit
    ws_timestamp to force both connections to share one value instead --
    needed for mimic_browser, since a real browser tab opens its SND and W/F
    sockets off the *same* page-load timestamp, and a single-IP-restricted
    Kiwi's admission check for the second connection appears to key off that
    match (see _start_stream). mimic_browser (from that SDR's sdr_list.txt
    entry) makes kiwi/client.py's _prepare_stream send a real browser's
    headers/URL path instead of this client's normal bare handshake -- see
    BROWSER_MIMIC_HEADERS above."""
    return SimpleNamespace(
        server_host=host,
        server_port=port,
        password='',
        admin=False,
        tlimit_password='',
        user=options.user,
        nolocal=False,
        ADC_OV=False,
        idx=0,
        multiple_connections=False,
        station=None,
        filename='',
        dir=None,
        netcat=False,
        tlimit=None,
        stats=False,
        rev_bin=False,
        wf_cal=WF_CAL,
        freq_pbc=False,
        modulation=options.modulation,
        lp_cut=options.lp_cut,
        hp_cut=options.hp_cut,
        wideband=False,
        ws_timestamp=(ws_timestamp if ws_timestamp is not None
                      else int(time.time() + os.getpid() + ws_offset) & 0xffffffff),
        bad_cmd=False,
        sound=True,
        resample=options.resample,
        nb=options.nb,
        nb_gate=options.nb_gate,
        nb_thresh=options.nb_thresh,
        nb_test=False,
        de_emp=options.de_emp,
        agc_gain=options.agc_gain,
        compression=not options.ncomp,
        sounddevice=options.sounddevice,
        blocksize=options.blocksize,
        ifreq=options.ifreq,
        thresh=None,
        quiet=True,
        S_meter=-1,
        sdt=0,
        tstamp=False,
        test_mode=False,
        socket_timeout=10,
        connect_timeout=5,
        connect_retries=1,
        busy_timeout=10,
        busy_retries=1,
        is_kiwi_tdoa=False,
        rigctl_enabled=False,
        no_api=False,
        origin=('http://%s:%s' % (host, port)) if mimic_browser else None,
        use_permessage_deflate=mimic_browser,
        extra_headers=BROWSER_MIMIC_HEADERS if mimic_browser else None,
        header_order=BROWSER_MIMIC_HEADER_ORDER if mimic_browser else None,
        url_prefix=BROWSER_MIMIC_URL_PREFIX if mimic_browser else '',
        client_ident=BROWSER_MIMIC_CLIENT_IDENT if mimic_browser else None,
    )


def load_config(path):
    """Flat text file: 'key value' per line, '#' comments, blank lines ignored."""
    if not os.path.exists(path):
        with open(path, 'w') as f:
            f.write("# kiwipanadapter adjustable settings ('key value' per line, '#' comments)\n")
            f.write("span_khz        50\n")
            f.write("mindb           -120\n")
            f.write("maxdb           -40\n")
            f.write("rigctl_host     127.0.0.1\n")
            f.write("rigctl_port     6400\n")
            f.write("default_freq    14200\n")
            f.write("smeter_decay_db_sec  20\n")
            f.write("smeter_cal_db  12\n")
            f.write("smeter_peak_hold_sec  3\n")
            f.write("smeter_peak_decay_db_sec  2\n")
            f.write("smeter_passband_center_hz  1500\n")
            f.write("smeter_passband_bw_hz      2400\n")
            f.write("wf_auto_range_db  50\n")
            f.write("wf_auto_beta      0.9\n")
            f.write("wf_auto_percentile  10\n")
            f.write("freq_major_khz  5\n")
            f.write("freq_minor_khz  1\n")
            f.write("window_height   %d\n" % DEFAULT_WINDOW_HEIGHT)
            f.write("modulation      usb\n")
            f.write("ncomp           false\n")
            f.write("# sounddevice  name  -- run --ls-snd to list available sound devices\n")
    cfg = {}
    with open(path) as f:
        for line in f:
            line = line.split('#', 1)[0].strip()
            if not line:
                continue
            parts = line.split(None, 1)
            if len(parts) != 2:
                continue
            key, val = parts
            if key in CONFIG_SCHEMA:
                cfg[key] = CONFIG_SCHEMA[key](val.strip())
    return cfg


def save_config_value(path, key, value):
    """Update (or append) a single 'key value' line in place, leaving everything else untouched."""
    lines = []
    if os.path.exists(path):
        with open(path) as f:
            lines = f.readlines()
    new_line = '%s    %s\n' % (key, value)
    for i, line in enumerate(lines):
        stripped = line.split('#', 1)[0].strip()
        parts = stripped.split(None, 1)
        if parts and parts[0] == key:
            lines[i] = new_line
            break
    else:
        lines.append(new_line)
    with open(path, 'w') as f:
        f.writelines(lines)


def _parse_sdr_tokens(parts):
    """parts: whitespace-split tokens of 'name... host port [mimic_browser] [no_sound]'
    (trailing flags in any order). Returns (name, host, port, mimic_browser,
    no_sound) or None if it doesn't parse."""
    if len(parts) < 2:
        return None
    mimic_browser = False
    no_sound = False
    while parts and not parts[-1].lstrip('-').isdigit():
        if parts[-1] == 'mimic_browser':
            mimic_browser = True
        elif parts[-1] == 'no_sound':
            no_sound = True
        parts = parts[:-1]
    if len(parts) < 2 or not parts[-1].lstrip('-').isdigit():
        return None
    host = parts[-2]
    port = int(parts[-1])
    name = ' '.join(parts[:-2]) if len(parts) > 2 else host
    return name, host, port, mimic_browser, no_sound


def load_sdr_list(path):
    """Flat text file: 'name host port [mimic_browser] [no_sound]' per line,
    '#' comments, blank lines ignored. The optional trailing 'mimic_browser'
    flag is for Kiwis that block a second plain connection from the same IP
    (e.g. some single-IP-restricted KiwiSDRs) but do allow a browser's own
    two connections -- when set, both the waterfall and audio connections to
    that SDR present themselves with a real browser's headers/URL path
    instead of this client's normal bare handshake. The optional trailing
    'no_sound' flag skips the audio connection entirely, opening only the
    waterfall -- for an SDR whose audio channel isn't usable/wanted (e.g.
    Weston's still-unexplained ~10s audio-channel disconnect).

    A whole line starting with '#' that still parses as a valid entry (once
    the '#' is stripped) is a *disabled* entry -- kept out of the main SDR
    selector but still shown (and re-enable/disable-toggleable) in the
    Manage... dialog, so an SDR can be temporarily hidden without deleting
    it and losing its host/port. An ordinary comment (the header line, or
    anything that doesn't parse as an entry) is just a comment, as before."""
    if not os.path.exists(path):
        with open(path, 'w') as f:
            f.write("# name              host                     port    [mimic_browser] [no_sound]\n")
            f.write("example             kiwisdr.example.com      8073\n")
    sdrs = []
    with open(path) as f:
        for line in f:
            stripped = line.strip()
            disabled = False
            content = stripped
            if content.startswith('#'):
                candidate = content[1:].strip()
                parsed = _parse_sdr_tokens(candidate.split())
                if parsed is None:
                    continue   # an ordinary comment/header line
                disabled = True
                name, host, port, mimic_browser, no_sound = parsed
            else:
                content = content.split('#', 1)[0].strip()
                if not content:
                    continue
                parsed = _parse_sdr_tokens(content.split())
                if parsed is None:
                    continue
                name, host, port, mimic_browser, no_sound = parsed
            sdrs.append({'name': name, 'host': host, 'port': port,
                         'mimic_browser': mimic_browser, 'no_sound': no_sound,
                         'disabled': disabled})
    return sdrs


def save_sdr_list(path, sdrs):
    """Rewrite the flat 'name host port [mimic_browser] [no_sound]' file from
    an in-memory list. A disabled entry is written back as a '#'-commented
    line (still a valid entry, just hidden from the selector -- see
    load_sdr_list)."""
    name_w = max((len(s['name']) for s in sdrs), default=4) + 2
    host_w = max((len(s['host']) for s in sdrs), default=4) + 2
    with open(path, 'w') as f:
        f.write("# name              host                     port    [mimic_browser] [no_sound]\n")
        for s in sdrs:
            suffix = ''
            if s.get('mimic_browser'):
                suffix += '  mimic_browser'
            if s.get('no_sound'):
                suffix += '  no_sound'
            prefix = '# ' if s.get('disabled') else ''
            f.write("%s%-*s %-*s %s%s\n" % (prefix, name_w, s['name'], host_w, s['host'], s['port'], suffix))


class RigctlPoller(threading.Thread):
    """Polls a rigctld TCP port (a real hamlib rigctld talking to an actual
    radio, or any other rigctld) for the current frequency and mode, same as
    FreeDV does, and reports both back via plain local callbacks every tick.

    Now that both the waterfall (LiveWFStream) and audio (LiveAudioStream)
    connections live in-process, there's no separate process to relay
    frequency/mode into -- the caller just calls their retune()/set_mode()
    methods directly from these callbacks. Those methods already dedupe
    against each stream's own current live freq/mode before sending
    anything to the Kiwi, so this poller doesn't need to track "did it
    change" itself.
    """

    def __init__(self, host, port, on_freq_khz, on_mode=None, poll_interval=0.5):
        super().__init__(daemon=True)
        self._host = host
        self._port = port
        self._on_freq_khz = on_freq_khz
        self._on_mode = on_mode
        self._poll_interval = poll_interval
        self._stop_event = threading.Event()
        self._recv_buf = ''

    def stop(self):
        self._stop_event.set()

    def _read_line(self, sock):
        # Proper line buffering: a single recv() can deliver more than one
        # reply line at once (e.g. mode+passband arriving together), so
        # leftover bytes after the first newline must be kept for the next
        # call rather than discarded/conflated into it.
        while '\n' not in self._recv_buf:
            chunk = sock.recv(256)
            if not chunk:
                raise ConnectionError('rigctld connection closed')
            self._recv_buf += chunk.decode('ascii', errors='ignore')
        line, self._recv_buf = self._recv_buf.split('\n', 1)
        return line.strip()

    def run(self):
        sock = None
        while not self._stop_event.is_set():
            try:
                if sock is None:
                    sock = socket.create_connection((self._host, self._port), timeout=2)
                    sock.settimeout(2)
                sock.sendall(b'f\n')
                freq_hz = float(self._read_line(sock))
                self._on_freq_khz(freq_hz / 1000.0)

                if self._on_mode is not None:
                    sock.sendall(b'm\n')
                    mode = self._read_line(sock)
                    try:
                        passband_hz = int(self._read_line(sock))
                    except Exception:
                        passband_hz = None
                    self._on_mode(mode, passband_hz)
            except Exception as e:
                logging.debug('rigctl poll error: %s', e)
                if sock is not None:
                    try:
                        sock.close()
                    except Exception:
                        pass
                sock = None
                self._recv_buf = ''
                self._stop_event.wait(1.0)
                continue
            self._stop_event.wait(self._poll_interval)
        if sock is not None:
            try:
                sock.close()
            except Exception:
                pass


class LiveWFStream(KiwiSDRStream):
    """A single waterfall-only Kiwi connection that can be recentered on the fly.

    Kept as its own connection rather than merged onto LiveAudioStream's
    SND-type connection: live testing (both against a Web888-family Kiwi and
    a genuine KiwiSDR 2) showed the server never delivers W/F-tagged frames
    on a connection opened as SND, no matter what zoom/wf_speed/wf_comp
    commands are sent on it -- only a connection actually opened via the
    '/W/F' URL path ever gets waterfall data. A camped second connection
    (kiwi/client.py's `?camp` mechanism) does work for this on Kiwis with no
    per-IP connection limit, but gains nothing there over two independent
    connections, and is silently blocked at connection-admission time (~10s
    then killed, no error) on Kiwis that only allow one connection per
    source IP -- exactly the Kiwis (e.g. Wessex, KiwiSDR 2 firmware) this
    was originally meant to help. That's a hard server-side wall with no
    client-side workaround, so audio+waterfall together simply isn't
    possible on such Kiwis; this and LiveAudioStream stay as two ordinary
    independent connections, just both retuned in-process rather than one
    of them living in a separately-spawned kiwiclientd subprocess.
    """

    def __init__(self, options, initial_freq_khz, span_khz, row_queue):
        super().__init__()
        self._options = options
        self._type = 'W/F'
        self._freq_offset = 0
        self._freq = initial_freq_khz
        self._span_khz = span_khz
        self._zoom = zoom_for_span(span_khz)
        self._actual_span_khz = span_for_zoom(self._zoom)
        self._row_queue = row_queue
        self._pending_freq = None
        self._lock = threading.Lock()

    def _setup_rx_params(self):
        self.set_freq(self._freq)
        baseband_freq = self._remove_freq_offset(self._freq)
        self._set_zoom_cf(self._zoom, baseband_freq)
        self._set_maxdb_mindb(-10, -110)   # server-side range, doesn't affect our own rendering
        self._set_wf_speed(4)
        self._set_wf_comp(False)
        self._set_wf_interp(13)
        self.set_name(self._options.user)

    def retune(self, freq_khz):
        with self._lock:
            self._pending_freq = freq_khz

    def _process_waterfall_samples(self, seq, samples):
        with self._lock:
            pending = self._pending_freq
            self._pending_freq = None
        if pending is not None and pending != self._freq:
            self._freq = pending
            try:
                self._set_zoom_cf(self._zoom, self._remove_freq_offset(self._freq))
            except Exception as e:
                logging.debug('retune failed: %s', e)

        dbm = np.array(samples, dtype=np.float64) - 255.0
        center = self._remove_freq_offset(self._freq)
        row = {
            'dbm': dbm,
            'start': center - self._actual_span_khz / 2,
            'stop': center + self._actual_span_khz / 2,
            'center': center,
        }
        try:
            self._row_queue.put_nowait(row)
        except queue.Full:
            try:
                self._row_queue.get_nowait()
            except queue.Empty:
                pass
            try:
                self._row_queue.put_nowait(row)
            except queue.Full:
                pass


class LiveAudioStream(KiwiSDRStream):
    """A single SND-type Kiwi connection: demodulated/IQ audio played to a
    local sound device, with live retune/mode-change support driven by
    rigctl polling. Runs in-process (its own thread pair via KiwiWorker)
    alongside a separate LiveWFStream -- ported from kiwiclientd.py's
    KiwiSoundRecorder so kiwipanadapter no longer needs to spawn
    kiwiclientd.py as a subprocess or relay frequency/mode into it over a
    mirrored local rigctld; this object is just retuned/remoded directly.
    """

    def __init__(self, options, initial_freq_khz, modulation, lowcut, highcut):
        super().__init__()
        self._options = options
        self._type = 'SND'
        self._freq_offset = 0
        self._freq = initial_freq_khz
        self._pending_freq = None
        self._pending_mode = None
        self._lock = threading.Lock()

        # Live demod mode -- unlike a static CLI-driven recorder, this is
        # meant to be updated at runtime (set_mode()) as a real rig's rigctld
        # reports mode changes, so it's kept as plain instance state rather
        # than read from self._options each time.
        self._modulation = modulation
        self._lowcut = lowcut
        self._highcut = highcut

        self._ifreq = options.ifreq
        self._start_ts = None
        self._start_time = None
        self._resampler = None
        self._output_sample_rate = 0

        # Audio queue for non-blocking playback
        self._audio_queue = Queue(maxsize=10)
        self._playback_thread = None
        self._playback_running = False
        self._pending_audio = None

        # Playback rate adjustment tracking
        self._pending_audio_history = []
        self._playback_rate_adjustment = 1.0
        self._last_rate_check_time = None

        # close() can be called from two different threads for the same
        # instance -- the GUI thread directly (PanadapterApp._stop_stream)
        # and this stream's own KiwiWorker reader thread as part of its own
        # cleanup once it notices the run_event was cleared -- guard so the
        # actual player teardown only ever runs once.
        self._close_lock = threading.Lock()
        self._closed = False

    # -- retuning: replaces the old separate-process rigctld-mirror RPC.
    # Both pending values are drained and applied together in
    # _process_audio_samples (the connection's single reader thread),
    # comparing against the stream's current live freq/mode -- this is what
    # dedupes redundant re-sends now that there's no second process that
    # needs an explicit resync after a restart. --------------------------

    def retune(self, freq_khz):
        with self._lock:
            self._pending_freq = freq_khz

    def set_mode(self, mod, passband_hz):
        if mod:
            mod = mod.lower()
            if mod == 'pktusb':
                # FreeDV/hamlib may request Icom-style "packet over USB",
                # which KiwiSDR has no concept of -- treat it as plain USB
                # (same fix as kiwi/rigctld.py's _set_modulation).
                mod = 'usb'
        with self._lock:
            self._pending_mode = (mod, passband_hz)

    def _apply_pending_retune(self):
        with self._lock:
            pending_freq = self._pending_freq
            self._pending_freq = None
            pending_mode = self._pending_mode
            self._pending_mode = None

        mode_changed = False
        if pending_mode is not None:
            mod, passband_hz = pending_mode
            if mod and (mod != self._modulation or passband_hz != self._highcut):
                self._modulation = mod
                self._lowcut = None
                self._highcut = passband_hz
                mode_changed = True

        freq_changed = pending_freq is not None and pending_freq != self._freq
        if freq_changed:
            self._freq = pending_freq

        if freq_changed or mode_changed:
            try:
                lowcut = self._lowcut
                if self._modulation == 'am':
                    lowcut = -self._highcut if lowcut is not None else lowcut
                self.set_mod(self._modulation, lowcut, self._highcut, self._freq)
            except Exception as e:
                logging.debug('audio retune failed: %s', e)

    def _update_playback_rate_adjustment(self):
        """Adjust playback rate based on pending buffer accumulation."""
        current_time = time.time()
        if self._last_rate_check_time is None or (current_time - self._last_rate_check_time) < 2.0:
            return
        self._last_rate_check_time = current_time

        pending_size = len(self._pending_audio) if self._pending_audio is not None else 0
        self._pending_audio_history.append(pending_size)
        if len(self._pending_audio_history) > 10:
            self._pending_audio_history.pop(0)
        if len(self._pending_audio_history) < 3:
            return

        recent_avg = sum(self._pending_audio_history[-3:]) / 3.0
        older_avg = sum(self._pending_audio_history[-6:-3]) / 3.0 if len(self._pending_audio_history) >= 6 else recent_avg
        pending_seconds = pending_size / (self._output_sample_rate * 2) if pending_size > 0 else 0

        if recent_avg > older_avg * 1.2 and pending_seconds > 0.5:
            self._playback_rate_adjustment = min(1.005, self._playback_rate_adjustment + 0.001)
            logging.info("Playback rate adjustment: %.4f (buffer: %.2fs, growing)" %
                        (self._playback_rate_adjustment, pending_seconds))
        elif recent_avg < older_avg * 0.8 and self._playback_rate_adjustment > 1.0:
            self._playback_rate_adjustment = max(1.0, self._playback_rate_adjustment - 0.001)
            logging.info("Playback rate adjustment: %.4f (buffer: %.2fs, shrinking)" %
                        (self._playback_rate_adjustment, pending_seconds))

    def _queue_audio(self, samples):
        """Queue audio samples for non-blocking playback. Accumulates if queue is full."""
        self._update_playback_rate_adjustment()

        if self._playback_rate_adjustment != 1.0:
            try:
                if HAS_RESAMPLER:
                    if not hasattr(self, '_playback_resampler'):
                        channels = 1 if len(samples.shape) == 1 else samples.shape[1]
                        self._playback_resampler = Resampler(channels=channels, converter_type='sinc_fastest')
                    samples = self._playback_resampler.process(samples, ratio=self._playback_rate_adjustment)
                else:
                    n = len(samples)
                    ratio = self._playback_rate_adjustment
                    xa = np.arange(round(n * ratio)) / ratio
                    xp = np.arange(n)
                    if len(samples.shape) == 1:
                        samples = np.interp(xa, xp, samples).astype(samples.dtype)
                    else:
                        new_samples = np.zeros((len(xa), samples.shape[1]), dtype=samples.dtype)
                        for ch in range(samples.shape[1]):
                            new_samples[:, ch] = np.interp(xa, xp, samples[:, ch])
                        samples = new_samples
            except Exception as e:
                logging.error("Playback rate adjustment failed: %s" % e)

        if self._pending_audio is not None:
            self._pending_audio = np.concatenate((self._pending_audio, samples), axis=0)
        else:
            self._pending_audio = samples

        chunk_size = 8192
        while self._pending_audio is not None and len(self._pending_audio) > 0:
            if len(self._pending_audio) <= chunk_size:
                chunk = self._pending_audio
                remaining = None
            else:
                chunk = self._pending_audio[:chunk_size]
                remaining = self._pending_audio[chunk_size:]
            try:
                self._audio_queue.put(chunk, block=False)
                self._pending_audio = remaining
            except Exception:
                break

    def _playback_thread_func(self):
        """Separate thread for audio playback to avoid blocking rigctl retuning."""
        while self._playback_running:
            try:
                samples = self._audio_queue.get(timeout=0.1)
                if samples is not None:
                    self._player.play(samples)
            except Empty:
                continue
            except Exception as e:
                logging.error("Playback error: %s" % e)

    def _init_player(self):
        # Shares close()'s lock -- this can run on this stream's own reader
        # thread (a genuine sample-rate change) at the same time close() is
        # invoked from the GUI thread (SDR switch) or from this stream's own
        # KiwiWorker cleanup once the run_event is cleared; both touch
        # _player/_playback_thread and PulseAudio/PipeWire's client library
        # isn't safe for concurrent use of those, so serialize through the
        # same lock rather than just this method's own internal ordering.
        with self._close_lock:
            if self._closed:
                return   # stream is being torn down, no point starting new audio

            # Stop the old playback thread and confirm it's genuinely finished
            # (real join, no timeout) *before* touching the old player -- the
            # thread may be mid player.play() right now, and exiting the player
            # out from under an in-flight play() call crashes the whole process
            # at the native soundcard/PipeWire level, not a catchable Python
            # exception. Only safe to skip when there's no previous thread yet
            # (first call).
            if self._playback_running:
                self._playback_running = False
                if self._playback_thread:
                    self._playback_thread.join()
            if hasattr(self, '_player'):
                try:
                    self._player.__exit__(exc_type=None, exc_value=None, traceback=None)
                except Exception as e:
                    logging.debug('failed to close previous audio player: %s', e)

            options = self._options
            speaker = sc.get_speaker(options.sounddevice)
            rate = self._output_sample_rate
            if speaker is None:
                if not options.sounddevice:
                    logging.warning('Using default sound device. Specify --snddev?')
                else:
                    logging.warning('Could not find sound device "%s", using default', options.sounddevice)
                speaker = sc.default_speaker()

            # pulseaudio has sporadic failures, retry a few times
            for i in range(0, 10):
                try:
                    # Small blocksize to avoid long blocking in play() which delays retunes
                    self._player = speaker.player(samplerate=rate, blocksize=self._options.blocksize)
                    self._player.__enter__()
                    break
                except Exception as ex:
                    logging.warning('speaker.player failed with %s', ex)
                    time.sleep(0.1)

            self._playback_running = True
            self._playback_thread = threading.Thread(target=self._playback_thread_func, daemon=True)
            self._playback_thread.start()

    def _setup_rx_params(self):
        self.set_name(self._options.user)

        lowcut = self._lowcut
        if self._modulation == 'am':
            # For AM, ignore the low pass filter cutoff
            lowcut = -self._highcut if lowcut is not None else lowcut
        self.set_mod(self._modulation, lowcut, self._highcut, self._freq)
        if self._options.agc_gain is not None:
            self.set_agc(on=False, gain=self._options.agc_gain)
        else:
            self.set_agc(on=True)
        if self._options.compression is False:
            self._set_snd_comp(False)
        if self._options.nb is True:
            gate = self._options.nb_gate
            if gate < 100 or gate > 5000:
                gate = 100
            thresh = self._options.nb_thresh
            if thresh < 0 or thresh > 100:
                thresh = 50
            self.set_noise_blanker(gate, thresh)
        if self._options.de_emp is True:
            self.set_de_emp(1)
        self._output_sample_rate = int(self._sample_rate)
        if self._options.resample > 0:
            self._output_sample_rate = self._options.resample
            self._ratio = float(self._output_sample_rate) / self._sample_rate
            logging.info('resampling from %g to %d Hz (ratio=%f)' % (self._sample_rate, self._options.resample, self._ratio))
            if not HAS_RESAMPLER:
                logging.info("libsamplerate not available: linear interpolation is used for low-quality resampling. "
                             "(pip/pip3 install samplerate)")
        if self._ifreq is not None:
            if self._modulation != 'iq':
                logging.warning('Option --if %.1f only valid for IQ modulation, ignored' % self._ifreq)
            elif self._output_sample_rate < self._ifreq * 4:
                logging.warning('Sample rate %.1f is not enough for --if %.1f, ignored. Use --resample %.1f' % (
                    self._output_sample_rate, self._ifreq, self._ifreq * 4))
        self._init_player()

    def _process_audio_samples(self, seq, samples, rssi, fmt):
        self._apply_pending_retune()
        drift_correction = self._track_sample_rate_drift(len(samples))

        if self._options.resample > 0:
            corrected_ratio = self._ratio * drift_correction
            if HAS_RESAMPLER:
                if self._resampler is None:
                    self._resampler = Resampler(converter_type='sinc_best')
                samples = np.round(self._resampler.process(samples, ratio=corrected_ratio)).astype(np.int16)
            else:
                n = len(samples)
                xa = np.arange(round(n * corrected_ratio)) / corrected_ratio
                xp = np.arange(n)
                samples = np.round(np.interp(xa, xp, samples)).astype(np.int16)

        fsamples = samples.astype(np.float32)
        fsamples /= 32768
        self._queue_audio(fsamples)

    def _process_stereo_samples_raw(self, seq, data):
        self._apply_pending_retune()
        n = len(data) // 4

        if self._options.resample == 0 or HAS_RESAMPLER:
            s = np.ndarray((n, 2), dtype='>h', buffer=data).astype(np.float32) / 32768

        if self._options.resample > 0:
            if HAS_RESAMPLER:
                if self._resampler is None:
                    self._resampler = Resampler(channels=2, converter_type='sinc_best')
                s = self._resampler.process(s, ratio=self._ratio)
            else:
                m = int(round(n * self._ratio))
                xa = np.arange(m) / self._ratio
                xp = np.arange(n)
                s = np.ndarray((m, 2), dtype=np.float32)
                s[:, 0] = np.interp(xa, xp, data[0::2] / 32768)
                s[:, 1] = np.interp(xa, xp, data[1::2] / 32768)

        if self._ifreq is not None and self._output_sample_rate >= 4 * self._ifreq:
            cs = s.view(dtype=np.complex64)
            l = len(cs)
            stopph = self.startph + 2 * np.pi * l * self._ifreq / self._output_sample_rate
            steps = 1j * np.linspace(self.startph, stopph, l, endpoint=False, dtype=np.float32)
            s = (cs * np.exp(steps)[:, None]).view(np.float32)
            self.startph = stopph % (2 * np.pi)

        self._queue_audio(s)

    # phase for frequency shift
    startph = np.float32(0)

    def _process_iq_samples(self, seq, samples, rssi, gps, fmt):
        self._apply_pending_retune()
        if self._options.resample == 0 or HAS_RESAMPLER:
            s = np.ndarray((len(samples), 2), dtype=np.float32)
            s[:, 0] = np.real(samples).astype(np.float32) / 32768
            s[:, 1] = np.imag(samples).astype(np.float32) / 32768

        if self._options.resample > 0:
            if HAS_RESAMPLER:
                if self._resampler is None:
                    self._resampler = Resampler(channels=2, converter_type='sinc_best')
                s = self._resampler.process(s, ratio=self._ratio)
            else:
                n = len(samples)
                m = int(round(n * self._ratio))
                xa = np.arange(m) / self._ratio
                xp = np.arange(n)
                s = np.ndarray((m, 2), dtype=np.float32)
                s[:, 0] = np.interp(xa, xp, np.real(samples).astype(np.float32) / 32768)
                s[:, 1] = np.interp(xa, xp, np.imag(samples).astype(np.float32) / 32768)

        if self._ifreq is not None and self._output_sample_rate >= 4 * self._ifreq:
            cs = s.view(dtype=np.complex64)
            l = len(cs)
            stopph = self.startph + 2 * np.pi * l * self._ifreq / self._output_sample_rate
            steps = 1j * np.linspace(self.startph, stopph, l, endpoint=False, dtype=np.float32)
            s = (cs * np.exp(steps)[:, None]).view(np.float32)
            self.startph = stopph % (2 * np.pi)

        self._queue_audio(s)

    def _on_sample_rate_change(self):
        if self._options.resample == 0:
            if self._output_sample_rate == int(self._sample_rate):
                # Rate genuinely unchanged -- don't tear down and rebuild the
                # audio player (new PipeWire/sound device node, restarted
                # playback thread) just because the Kiwi re-sent a
                # 'sample_rate' message, e.g. in response to a redundant
                # 'SET mod=...' triggered by a repeated rigctl mode-set.
                return
            self._output_sample_rate = int(self._sample_rate)
            self._init_player()

    def close(self):
        # _init_player() only closes the *previous* player when called again
        # on the same instance (a real sample-rate change) -- when this whole
        # stream object is being discarded instead (SDR switch, app close),
        # nothing else ever stops the playback thread or exits the sound
        # device player, leaking one zombie PipeWire stream per switch with
        # nothing to ever stop it since it's a daemon thread.
        #
        # Deliberately synchronous (blocks the caller -- the GUI thread on an
        # SDR switch -- for however long the playback thread takes to notice
        # and finish, normally well under a second): a background-thread
        # version was tried first to avoid that brief GUI pause, but it let
        # this old player's teardown run concurrently with the *new*
        # LiveAudioStream's _init_player() setting up its own player during
        # a switch -- PulseAudio/PipeWire's client library isn't safe for
        # that and aborted the whole process with a native assertion
        # failure (not a catchable Python exception). Blocking here until
        # the old player is genuinely gone, before PanadapterApp._start_stream()
        # can create the new one, is what actually avoids the race -- a
        # short pause beats a process crash.
        with self._close_lock:
            if not self._closed:
                self._closed = True
                self._playback_running = False
                if self._playback_thread:
                    self._playback_thread.join()
                if hasattr(self, '_player'):
                    try:
                        self._player.__exit__(exc_type=None, exc_value=None, traceback=None)
                    except Exception as e:
                        logging.debug('failed to close audio player: %s', e)
        super().close()


class SdrEntryDialog(tk.Toplevel):
    """Small modal form for one SDR's name/host/port. Sets self.result to a dict, or leaves it None if cancelled."""

    def __init__(self, parent, entry=None):
        super().__init__(parent)
        self.title('SDR entry')
        self.transient(parent)
        self.resizable(False, False)
        self.result = None

        self._name_var = tk.StringVar(value=entry['name'] if entry else '')
        self._host_var = tk.StringVar(value=entry['host'] if entry else '')
        self._port_var = tk.StringVar(value=str(entry['port']) if entry else '')
        self._mimic_var = tk.BooleanVar(value=bool(entry.get('mimic_browser')) if entry else False)
        self._no_sound_var = tk.BooleanVar(value=bool(entry.get('no_sound')) if entry else False)
        self._disabled_var = tk.BooleanVar(value=bool(entry.get('disabled')) if entry else False)

        form = ttk.Frame(self)
        form.pack(padx=8, pady=8)
        fields = [('Name:', self._name_var), ('Host:', self._host_var), ('Port:', self._port_var)]
        for row, (label, var) in enumerate(fields):
            ttk.Label(form, text=label).grid(row=row, column=0, sticky='e', pady=2)
            ttk.Entry(form, textvariable=var, width=28).grid(row=row, column=1, pady=2)
        ttk.Checkbutton(form, text='Mimic browser (for single-IP-restricted Kiwis)',
                         variable=self._mimic_var).grid(row=len(fields), column=0, columnspan=2, sticky='w', pady=(4, 0))
        ttk.Checkbutton(form, text='No sound (waterfall only)',
                         variable=self._no_sound_var).grid(row=len(fields) + 1, column=0, columnspan=2, sticky='w')
        ttk.Checkbutton(form, text='Disabled (hide from SDR selector, keep in this list)',
                         variable=self._disabled_var).grid(row=len(fields) + 2, column=0, columnspan=2, sticky='w')

        btns = ttk.Frame(self)
        btns.pack(pady=(0, 8))
        ttk.Button(btns, text='OK', command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text='Cancel', command=self.destroy).pack(side='left')

        self.grab_set()
        self.wait_window(self)

    def _ok(self):
        name = self._name_var.get().strip()
        host = self._host_var.get().strip()
        try:
            port = int(self._port_var.get().strip())
        except ValueError:
            return
        disabled = self._disabled_var.get()
        # A leading '#' typed directly into the name (matching the
        # sdr_list.txt file convention this dialog is a GUI for) is treated
        # the same as ticking the Disabled checkbox, not left as literal
        # name text -- otherwise the saved file and the in-memory entry
        # disagree (name still starts with '#' but disabled stays False),
        # and reloading the file would silently strip the '#' and flip
        # disabled to True, changing both the name and the flag.
        if name.startswith('#'):
            name = name[1:].strip()
            disabled = True
        if not name or not host:
            return
        self.result = {'name': name, 'host': host, 'port': port,
                       'mimic_browser': self._mimic_var.get(), 'no_sound': self._no_sound_var.get(),
                       'disabled': disabled}
        self.destroy()


class SdrListDialog(tk.Toplevel):
    """Add/edit/delete SDR entries; changes are written straight back to sdr_list.txt."""

    def __init__(self, parent, sdr_list, list_path, on_change):
        super().__init__(parent)
        self.title('Manage SDRs')
        self.transient(parent)
        self._sdr_list = sdr_list
        self._list_path = list_path
        self._on_change = on_change

        self._listbox = tk.Listbox(self, width=44, height=8)
        self._listbox.pack(side='top', fill='both', expand=True, padx=8, pady=8)
        self._refresh_listbox()

        btns = ttk.Frame(self)
        btns.pack(side='top', fill='x', padx=8, pady=(0, 8))
        ttk.Button(btns, text='Add', command=self._add).pack(side='left')
        ttk.Button(btns, text='Edit', command=self._edit).pack(side='left', padx=4)
        ttk.Button(btns, text='Delete', command=self._delete).pack(side='left')
        ttk.Button(btns, text='Close', command=self.destroy).pack(side='right')

        self.grab_set()

    def _refresh_listbox(self):
        self._listbox.delete(0, 'end')
        for s in self._sdr_list:
            mimic = '  [mimic browser]' if s.get('mimic_browser') else ''
            no_sound = '  [no sound]' if s.get('no_sound') else ''
            disabled = '  [disabled]' if s.get('disabled') else ''
            self._listbox.insert('end', '%s  (%s:%s)%s%s%s' % (s['name'], s['host'], s['port'], mimic, no_sound, disabled))

    def _save(self):
        save_sdr_list(self._list_path, self._sdr_list)
        self._refresh_listbox()
        self._on_change()

    def _add(self):
        entry = SdrEntryDialog(self).result
        if entry:
            self._sdr_list.append(entry)
            self._save()

    def _edit(self):
        sel = self._listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        entry = SdrEntryDialog(self, self._sdr_list[idx]).result
        if entry:
            self._sdr_list[idx] = entry
            self._save()

    def _delete(self):
        sel = self._listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        if len(self._sdr_list) <= 1:
            return   # keep at least one entry
        del self._sdr_list[idx]
        self._save()


class PanadapterApp:
    def __init__(self, root, options):
        self._options = options
        self._root = root
        self._sdr_list = load_sdr_list(options.sdr_list)
        if not self._sdr_list:
            raise Exception('No SDRs in %s -- add at least one "name host port" line' % options.sdr_list)
        enabled_sdrs = self._enabled_sdrs()
        if not enabled_sdrs:
            raise Exception('All SDRs in %s are disabled -- enable at least one' % options.sdr_list)
        self._initial_sdr = next((s for s in enabled_sdrs if s['name'] == options.last_sdr), enabled_sdrs[0])

        self._mindb = options.mindb
        self._maxdb = options.maxdb
        # S-meter scale is deliberately independent of the waterfall's own
        # mindb/maxdb -- the right-click sensitivity menu below adjusts only
        # waterfall brightness/contrast, it must never move the S-meter's
        # tick positions or bar-fill calibration.
        self._smeter_mindb = options.mindb
        self._smeter_maxdb = options.maxdb
        self._smeter_decay = options.smeter_decay
        self._smeter_cal_db = options.smeter_cal_db
        self._smeter_peak_hold_sec = options.smeter_peak_hold_sec
        self._smeter_peak_decay = options.smeter_peak_decay_db_sec
        self._smeter_passband_center_hz = options.smeter_passband_center_hz
        self._smeter_passband_bw_hz = options.smeter_passband_bw_hz
        # Waterfall auto-level: floating [noise-floor, noise-floor+range] window.
        # Inspired by FreeDV-GUI's PlotWaterfall (src/gui/controls/plot_waterfall.cpp),
        # but anchored to a low percentile of the row (an estimated noise floor)
        # rather than the peak -- peak-anchoring means a single strong bin (a
        # tune-up carrier, a birdie, a distant strong station elsewhere in the
        # span) instantly redefines the window and can push the actual signal
        # of interest below black. A percentile is robust to a handful of such
        # outlier bins regardless of where in the span they sit. The floor
        # estimate is smoothed (EMA) so it doesn't jitter row to row; the
        # headroom above it is a fixed range. On by default; can be overridden
        # via the right-click sensitivity menu.
        self._wf_auto = True
        self._wf_auto_range_db = options.wf_auto_range_db
        self._wf_auto_beta = options.wf_auto_beta
        self._wf_auto_percentile = options.wf_auto_percentile
        self._wf_auto_floor_dbm = None
        self._freq_major_khz = options.freq_major_khz
        self._freq_minor_khz = options.freq_minor_khz
        self._current_freq_khz = None
        self._freq_lock = threading.Lock()
        self._row_queue = queue.Queue(maxsize=2)
        self._img_buf = np.zeros((MAX_HISTORY_ROWS, WF_NATIVE_BINS, 3), dtype=np.uint8)
        self._photo = None
        self._worker = None
        self._run_event = None
        self._wf_stream = None
        self._audio_worker = None
        self._audio_run_event = None
        self._audio_stream = None
        self._last_signal_dbm = None
        self._smeter_dbm = None
        self._smeter_last_ts = None
        self._smeter_peak_dbm = None
        self._smeter_peak_set_ts = None
        self._smeter_peak_last_ts = None
        self._last_start = None
        self._last_stop = None
        self._active_sdr = None
        self._reconnect_retry_count = 0
        self._reconnect_after_id = None
        self._stream_start_ts = None

        root.title('Kiwi Panadapter')
        self._build_ui()
        root.update_idletasks()   # so winfo_width/height are accurate before the first row arrives

        self._rigctl_poller = RigctlPoller(options.rigctl_host, options.rigctl_port,
                                            self._on_rigctl_freq, on_mode=self._on_rigctl_mode)
        self._rigctl_poller.start()

        self._start_stream(self._initial_sdr)
        self._active_sdr = self._initial_sdr
        root.protocol('WM_DELETE_WINDOW', self._on_close)
        self._poll_queue()
        self._poll_reconnect()

    def _build_ui(self):
        screen_w = self._root.winfo_screenwidth()
        geometry = '%dx%d' % (screen_w, self._options.window_height)
        if self._options.window_x is not None and self._options.window_y is not None:
            geometry += '+%d+%d' % (self._options.window_x, self._options.window_y)
        self._root.geometry(geometry)

        # Fixed-height widgets (top bar, S-meter bar) must be packed to their
        # side *before* the expanding waterfall canvas, otherwise Tk's pack
        # geometry manager starves them of space first as the window shrinks
        # instead of shrinking only the expandable canvas.
        top = ttk.Frame(self._root)
        top.pack(side='top', fill='x', padx=4, pady=4)

        ttk.Label(top, text='SDR:').pack(side='left')
        self._sdr_var = tk.StringVar(value=self._initial_sdr['name'])
        combo_width = max((len(s['name']) for s in self._sdr_list), default=10) + 2
        self._sdr_combo = ttk.Combobox(top, textvariable=self._sdr_var, state='readonly',
                                        width=combo_width,
                                        values=[s['name'] for s in self._enabled_sdrs()])
        self._sdr_combo.pack(side='left', padx=4)
        self._sdr_combo.bind('<<ComboboxSelected>>', self._on_sdr_change)
        ttk.Button(top, text='Manage...', command=self._open_sdr_manager).pack(side='left')

        self._status_var = tk.StringVar(value='connecting...')
        ttk.Label(top, textvariable=self._status_var).pack(side='left', padx=12)

        self._freq_var = tk.StringVar(value='-- kHz')
        ttk.Label(top, textvariable=self._freq_var, font=('TkFixedFont', 11, 'bold')).pack(side='right')

        # Fixed-height widgets must be packed to their side *before* the
        # expanding waterfall canvas, otherwise Tk's pack geometry manager
        # starves them of space first as the window shrinks instead of
        # shrinking only the expandable canvas.
        meter = ttk.Frame(self._root)
        meter.pack(side='bottom', fill='x', padx=4, pady=(2, 4))
        ttk.Label(meter, text='S:').pack(side='left')
        self._dbm_var = tk.StringVar(value='-- dBm')
        # Fixed width so the S-meter canvas next to it (fill='x', expand=True)
        # doesn't resize when the dBm text's digit count changes (e.g. -99 -> -100).
        ttk.Label(meter, textvariable=self._dbm_var, width=8, anchor='e').pack(side='right', padx=8)
        self._smeter_canvas = tk.Canvas(meter, height=28, highlightthickness=0, bg='black')
        self._smeter_canvas.pack(side='left', fill='x', expand=True, padx=4)

        self._freqaxis_canvas = tk.Canvas(self._root, height=20, highlightthickness=0, bg='black')
        self._freqaxis_canvas.pack(side='top', fill='x')

        self._canvas = tk.Canvas(self._root, highlightthickness=0, bg='black')
        self._canvas.pack(side='top', fill='both', expand=True)
        self._image_id = self._canvas.create_image(0, 0, anchor='nw')
        self._canvas.bind('<Configure>', self._on_resize)
        self._sensitivity_var = tk.StringVar(value='Auto (adaptive)')
        self._canvas.bind('<Button-3>', self._show_sensitivity_menu)

    # -- SDR connection management -------------------------------------------------

    def _start_wf_connection(self, sdr_entry, freq, mimic_browser, ws_timestamp=None):
        wf_opt = make_stream_options(sdr_entry['host'], sdr_entry['port'], self._options,
                                      ws_offset=0, mimic_browser=mimic_browser, ws_timestamp=ws_timestamp)
        self._wf_stream = LiveWFStream(wf_opt, freq, self._options.span, self._row_queue)
        self._run_event = threading.Event()
        self._run_event.set()
        wf_camp_wait_event = threading.Event()
        wf_camp_wait_event.set()
        self._worker = KiwiWorker(args=(self._wf_stream, wf_opt, True, False, self._run_event, wf_camp_wait_event))
        self._worker.start()

    def _start_audio_connection(self, sdr_entry, freq, mimic_browser, ws_timestamp=None):
        audio_opt = make_stream_options(sdr_entry['host'], sdr_entry['port'], self._options,
                                         ws_offset=1, mimic_browser=mimic_browser, ws_timestamp=ws_timestamp)
        self._audio_stream = LiveAudioStream(audio_opt, freq, self._options.modulation,
                                              self._options.lp_cut, self._options.hp_cut)
        self._audio_run_event = threading.Event()
        self._audio_run_event.set()
        audio_camp_wait_event = threading.Event()
        audio_camp_wait_event.set()
        self._audio_worker = KiwiWorker(args=(self._audio_stream, audio_opt, True, False,
                                               self._audio_run_event, audio_camp_wait_event))
        self._audio_worker.start()

    def _start_stream(self, sdr_entry):
        with self._freq_lock:
            freq = self._current_freq_khz if self._current_freq_khz is not None else self._options.default_freq
        mimic_browser = sdr_entry.get('mimic_browser', False)
        no_sound = sdr_entry.get('no_sound', False)

        if no_sound:
            # Audio channel intentionally skipped for this SDR (e.g.
            # Weston's still-unexplained ~10s audio-channel disconnect,
            # investigation parked) -- waterfall only, no pairing needed.
            self._start_wf_connection(sdr_entry, freq, mimic_browser)
        elif mimic_browser:
            # A real browser always opens its SND connection before its W/F
            # one (confirmed via packet capture, 2026-07-30: SND SYN then
            # W/F SYN ~249ms later) -- live-tested as working reliably in
            # that order; opening W/F first (this app's normal order below)
            # was observed to get audio's SND connection rejected on a
            # single-IP-restricted Kiwi even with full header mimicry, so
            # match the tested order here rather than the normal one.
            #
            # A real browser's SND and W/F sockets both carry the *same*
            # page-load ws_timestamp -- share one here too (instead of the
            # default per-connection ws_offset split) so the pair looks like
            # one browser tab rather than two unrelated sessions from the
            # same IP, which single-IP admission logic seems to key off.
            shared_ts = int(time.time() + os.getpid()) & 0xffffffff
            self._start_audio_connection(sdr_entry, freq, mimic_browser, ws_timestamp=shared_ts)
            time.sleep(0.25)
            self._start_wf_connection(sdr_entry, freq, mimic_browser, ws_timestamp=shared_ts)
        else:
            self._start_wf_connection(sdr_entry, freq, mimic_browser)
            self._start_audio_connection(sdr_entry, freq, mimic_browser)

        self._status_var.set('connecting to %s...' % sdr_entry['name'])
        self._stream_start_ts = time.time()

    def _stop_stream(self):
        if self._reconnect_after_id is not None:
            try:
                self._root.after_cancel(self._reconnect_after_id)
            except Exception:
                pass
            self._reconnect_after_id = None
        if self._worker is not None:
            self._run_event.clear()
            try:
                self._wf_stream.close()
            except Exception:
                pass
            self._worker.join(timeout=2)
            self._worker = None
            self._wf_stream = None
        if self._audio_worker is not None:
            self._audio_run_event.clear()
            try:
                self._audio_stream.close()
            except Exception:
                pass
            self._audio_worker.join(timeout=2)
            self._audio_worker = None
            self._audio_stream = None

    def _poll_reconnect(self):
        # Some Kiwis' admission of a second (mimic_browser) connection isn't
        # 100% reliable even with full browser mimicry -- live-tested at
        # ~83% in isolation, but retrying just the one side that died against
        # an already-open, aging companion connection was observed live to
        # fail every single time (6/6) -- consistent with the Kiwi expecting
        # the companion to arrive within a short window of the first
        # connection, the same way a real browser's own pair always does.
        # So a detected failure on either side tears down *both* and
        # restarts the whole pair together, close in time again, rather than
        # patching just the side that died.
        if self._active_sdr is not None and self._reconnect_after_id is None:
            wf_down = (self._worker is not None and self._run_event is not None
                       and not self._run_event.is_set())
            audio_down = (self._audio_worker is not None and self._audio_run_event is not None
                          and not self._audio_run_event.is_set())
            if wf_down or audio_down:
                self._schedule_reconnect()
            elif (self._reconnect_retry_count > 0 and self._stream_start_ts is not None
                  and time.time() - self._stream_start_ts >= RECONNECT_HEALTHY_RESET_SEC):
                logging.info('connection to %s has been up %.0fs, resetting retry counter',
                             self._active_sdr['name'], time.time() - self._stream_start_ts)
                self._reconnect_retry_count = 0
        self._root.after(1000, self._poll_reconnect)

    def _schedule_reconnect(self):
        if self._reconnect_retry_count >= MAX_RECONNECT_RETRIES:
            logging.warning('connection to %s failed %d times in a row, giving up automatic retry -- '
                             'reselect the SDR to try again', self._active_sdr['name'], self._reconnect_retry_count)
            return
        self._reconnect_retry_count += 1
        logging.info('connection to %s dropped, retrying both sides together (%d/%d)...',
                     self._active_sdr['name'], self._reconnect_retry_count, MAX_RECONNECT_RETRIES)

        def do_reconnect():
            self._reconnect_after_id = None
            if self._active_sdr is None:
                return   # SDR was switched away while we were waiting
            sdr_entry = self._active_sdr
            # Tear down whichever side is still up too -- restarting only the
            # dead side while leaving a now-aging companion connection in
            # place is exactly the pattern that was observed to never work.
            if self._worker is not None:
                self._run_event.clear()
                try:
                    self._wf_stream.close()
                except Exception:
                    pass
                self._worker.join(timeout=2)
                self._worker = None
                self._wf_stream = None
            if self._audio_worker is not None:
                self._audio_run_event.clear()
                try:
                    self._audio_stream.close()
                except Exception:
                    pass
                self._audio_worker.join(timeout=2)
                self._audio_worker = None
                self._audio_stream = None
            self._start_stream(sdr_entry)

        self._reconnect_after_id = self._root.after(int(RECONNECT_RETRY_DELAY_SEC * 1000), do_reconnect)

    def _on_sdr_change(self, _event):
        name = self._sdr_var.get()
        entry = next((s for s in self._sdr_list if s['name'] == name), None)
        if entry is None:
            return
        self._stop_stream()
        while True:
            try:
                self._row_queue.get_nowait()
            except queue.Empty:
                break
        self._img_buf[:] = 0
        self._smeter_dbm = None
        self._smeter_last_ts = None
        self._smeter_peak_dbm = None
        self._smeter_peak_set_ts = None
        self._smeter_peak_last_ts = None
        self._wf_auto_floor_dbm = None
        self._reconnect_retry_count = 0
        self._start_stream(entry)
        self._active_sdr = entry
        try:
            save_config_value(self._options.config, 'last_sdr', entry['name'])
        except Exception as e:
            logging.debug('failed to save last_sdr: %s', e)

    def _enabled_sdrs(self):
        return [s for s in self._sdr_list if not s.get('disabled')]

    def _open_sdr_manager(self):
        SdrListDialog(self._root, self._sdr_list, self._options.sdr_list, self._on_sdr_list_changed)

    def _on_sdr_list_changed(self):
        enabled = self._enabled_sdrs()
        names = [s['name'] for s in enabled]
        self._sdr_combo['values'] = names
        self._sdr_combo.config(width=max((len(n) for n in names), default=10) + 2)
        current_name = self._sdr_var.get()
        entry = next((s for s in enabled if s['name'] == current_name), None)
        if entry is None and enabled:
            entry = enabled[0]
            self._sdr_var.set(entry['name'])
        if entry is not None and entry != self._active_sdr:
            self._on_sdr_change(None)

    # -- frequency/mode tracking ------------------------------------------------------

    def _on_rigctl_freq(self, freq_khz):
        with self._freq_lock:
            changed = self._current_freq_khz != freq_khz
            self._current_freq_khz = freq_khz
        if changed:
            if self._wf_stream is not None:
                self._wf_stream.retune(freq_khz)
            if self._audio_stream is not None:
                self._audio_stream.retune(freq_khz)

    def _on_rigctl_mode(self, mode, passband_hz):
        if self._audio_stream is not None:
            self._audio_stream.set_mode(mode, passband_hz)

    # -- GUI update loop --------------------------------------------------------------

    def _poll_queue(self):
        latest = None
        try:
            while True:
                latest = self._row_queue.get_nowait()
        except queue.Empty:
            pass

        if latest is not None:
            self._status_var.set('connected')
            self._freq_var.set('%.3f kHz' % latest['center'])
            self._ingest_row(latest)
            self._redraw()

        self._root.after(150, self._poll_queue)

    def _ingest_row(self, row):
        calibrated = row['dbm'] + WF_CAL
        if self._wf_auto:
            floor = float(np.percentile(calibrated, self._wf_auto_percentile))
            if self._wf_auto_floor_dbm is None:
                self._wf_auto_floor_dbm = floor
            else:
                self._wf_auto_floor_dbm = (self._wf_auto_beta * self._wf_auto_floor_dbm
                                            + (1.0 - self._wf_auto_beta) * floor)
            lo = self._wf_auto_floor_dbm
            hi = lo + max(self._wf_auto_range_db, 1.0)
        else:
            lo, hi = self._mindb, self._maxdb

        dbm = np.clip(calibrated, lo, hi)
        idx = ((dbm - lo) / (hi - lo) * 255).astype(np.uint8)
        rgb_row = COLORMAP[idx]

        self._img_buf[1:] = self._img_buf[:-1]
        self._img_buf[0] = rgb_row

        self._last_start = row['start']
        self._last_stop = row['stop']

        center_khz = row['center']
        n_bins = len(row['dbm'])
        span_khz = row['stop'] - row['start']

        # S-meter passband is an offset+bandwidth from the dial frequency,
        # not the dial frequency itself -- for SSB/FreeDV the dial frequency
        # sits at the suppressed-carrier edge, outside the actual signal.
        # Configurable so it can be tailored to whatever passband FreeDV (or
        # any other mode) actually occupies (config: smeter_passband_center_hz,
        # smeter_passband_bw_hz).
        pb_center_khz = self._smeter_passband_center_hz / 1000.0
        pb_half_khz = self._smeter_passband_bw_hz / 2000.0
        lo_khz = center_khz + pb_center_khz - pb_half_khz
        hi_khz = center_khz + pb_center_khz + pb_half_khz

        lo_idx = int(round((lo_khz - row['start']) / span_khz * (n_bins - 1)))
        hi_idx = int(round((hi_khz - row['start']) / span_khz * (n_bins - 1)))
        lo_idx, hi_idx = sorted((lo_idx, hi_idx))
        lo_idx = max(0, min(n_bins - 1, lo_idx))
        hi_idx = max(0, min(n_bins - 1, hi_idx))
        # Total power across the passband, not the single strongest bin: a
        # real S-meter (analog AGC, or a webSDR's) responds to total energy
        # through its receive filter. That's the same as a lone tone's power
        # for a single-carrier SSB voice signal, but for a multi-carrier
        # digital mode (FreeDV COFDM etc, power spread across many subcarrier
        # bins) taking just the max bin badly undercounts the real level.
        bin_dbm = row['dbm'][lo_idx:hi_idx + 1] + WF_CAL
        instantaneous_dbm = 10.0 * np.log10(np.sum(np.power(10.0, bin_dbm / 10.0))) + self._smeter_cal_db

        now = time.time()
        if self._smeter_dbm is None or instantaneous_dbm >= self._smeter_dbm:
            self._smeter_dbm = instantaneous_dbm   # fast attack: jump up immediately
        else:
            dt = (now - self._smeter_last_ts) if self._smeter_last_ts is not None else 0.0
            max_fall = self._smeter_decay * dt
            self._smeter_dbm = max(instantaneous_dbm, self._smeter_dbm - max_fall)   # slow decay
        self._smeter_last_ts = now
        self._last_signal_dbm = self._smeter_dbm

        # Peak-hold: tracks the raw instantaneous reading (not the smoothed
        # self._smeter_dbm above), frozen for smeter_peak_hold_sec after each
        # new peak, then falling slowly. Row-sampled instantaneous readings can
        # miss brief SSB syllabic peaks between waterfall rows -- holding the
        # peak visually makes those still readable rather than blinking past.
        if self._smeter_peak_dbm is None or instantaneous_dbm >= self._smeter_peak_dbm:
            self._smeter_peak_dbm = instantaneous_dbm
            self._smeter_peak_set_ts = now
        elif (now - self._smeter_peak_set_ts) >= self._smeter_peak_hold_sec:
            dt = (now - self._smeter_peak_last_ts) if self._smeter_peak_last_ts is not None else 0.0
            max_fall = self._smeter_peak_decay * dt
            self._smeter_peak_dbm = max(instantaneous_dbm, self._smeter_peak_dbm - max_fall)
        self._smeter_peak_last_ts = now

    def _on_resize(self, _event):
        self._redraw()

    def _sensitivity_presets(self):
        # Presets are offsets from the configured mindb/maxdb (the "Normal"
        # baseline), not absolute dBm, so they stay sensible regardless of a
        # given SDR/antenna's actual gain chain.
        base_min, base_max = self._options.mindb, self._options.maxdb
        return [
            ('Low (strong signals)', base_min + 20, base_max + 20),
            ('Normal', base_min, base_max),
            ('High (quiet bands)', base_min - 20, base_max - 20),
        ]

    def _show_sensitivity_menu(self, event):
        menu = tk.Menu(self._root, tearoff=0)
        for label, mindb, maxdb in self._sensitivity_presets():
            menu.add_radiobutton(
                label=label, variable=self._sensitivity_var, value=label,
                command=lambda mn=mindb, mx=maxdb: self._set_sensitivity(mn, mx))
        menu.add_radiobutton(
            label='Auto (adaptive)', variable=self._sensitivity_var, value='Auto (adaptive)',
            command=self._set_auto_sensitivity)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _set_auto_sensitivity(self):
        self._wf_auto = True
        self._wf_auto_floor_dbm = None

    def _set_sensitivity(self, mindb, maxdb):
        self._wf_auto = False
        self._mindb = mindb
        self._maxdb = maxdb
        self._redraw()

    def _redraw(self):
        canvas_w = max(1, self._canvas.winfo_width())
        canvas_h = max(1, self._canvas.winfo_height())
        display_rows = min(canvas_h, MAX_HISTORY_ROWS)
        img = nearest_resize(self._img_buf[:display_rows], canvas_h, canvas_w)

        header = ('P6\n%d %d\n255\n' % (canvas_w, canvas_h)).encode('ascii')
        ppm = header + img.tobytes()
        photo = tk.PhotoImage(width=canvas_w, height=canvas_h, data=ppm, format='PPM')
        self._canvas.itemconfig(self._image_id, image=photo)
        self._photo = photo   # keep a reference, Tk drops images with no owner

        if self._last_signal_dbm is not None:
            self._dbm_var.set('%.0f dBm' % self._last_signal_dbm)
            self._draw_smeter(self._last_signal_dbm, self._smeter_peak_dbm)

        if self._last_start is not None:
            self._draw_freq_axis(self._last_start, self._last_stop)

    def _draw_freq_axis(self, start_khz, stop_khz):
        # Axis sits above the waterfall, so ticks point down toward it (at
        # the strip's bottom edge) with labels above them.
        c = self._freqaxis_canvas
        c.delete('all')
        w = max(1, c.winfo_width())
        h = max(1, c.winfo_height())
        span = stop_khz - start_khz
        if span <= 0:
            return

        for f in tick_positions(start_khz, stop_khz, self._freq_minor_khz):
            x = int((f - start_khz) / span * w)
            c.create_line(x, h, x, h - 6, fill='#a0a0a0', width=2)

        label_fmt = '%.3f' if self._freq_major_khz < 1 else '%.0f'
        for f in tick_positions(start_khz, stop_khz, self._freq_major_khz):
            x = int((f - start_khz) / span * w)
            c.create_line(x, h, x, h - 6, fill='#a0a0a0', width=2)
            c.create_text(x, h - 7, text=label_fmt % f, fill='white', anchor='s', font=('TkFixedFont', 7))

        with self._freq_lock:
            freq = self._current_freq_khz
        if freq is not None and start_khz <= freq <= stop_khz:
            x = int((freq - start_khz) / span * w)
            c.create_line(x, 0, x, h, fill='#ff00ff', width=1)

    def _draw_smeter(self, dbm, peak_dbm=None):
        c = self._smeter_canvas
        c.delete('all')
        w_total = max(1, c.winfo_width())
        h_total = max(1, c.winfo_height())
        bar_h = 6
        bar_top = h_total - bar_h

        def frac_of(val):
            return max(0.0, min(1.0, (val - self._smeter_mindb) / (self._smeter_maxdb - self._smeter_mindb)))

        # Peak-hold bar, drawn first/underneath in a dimmed stipple fill so it
        # reads as a distinct layer -- only the portion beyond the current-level
        # bar (drawn on top, below) stays visible, as a long-hang "tail".
        if peak_dbm is not None:
            peak_w = int(frac_of(peak_dbm) * w_total)
            c.create_rectangle(0, bar_top, peak_w, h_total, fill='#ff3030', width=0, stipple='gray50')

        w = int(frac_of(dbm) * w_total)
        c.create_rectangle(0, bar_top, w, h_total, fill='#00ff00', width=0)
        # S-unit ticks: S9 = -73 dBm, 6 dB/S-unit below S9, 10 dB/S-unit ("+" values) above.
        # Labels/ticks live above the bar so the bar itself stays a slim strip underneath.
        s_points = [('S%d' % n, -73 - 6 * (9 - n)) for n in range(1, 10)]
        plus_points = [('+%d' % p, -73 + p) for p in (10, 20, 30, 40)]
        for label, ref_dbm in s_points + plus_points:
            x = int(max(0.0, min(1.0, (ref_dbm - self._smeter_mindb) / (self._smeter_maxdb - self._smeter_mindb))) * w_total)
            c.create_line(x, 0, x, bar_top, fill='#808080')
            c.create_text(x + 2, 0, text=label, fill='white', anchor='n', font=('TkFixedFont', 7))

    def _on_close(self):
        try:
            save_config_value(self._options.config, 'window_height', self._root.winfo_height())
            save_config_value(self._options.config, 'window_x', self._root.winfo_x())
            save_config_value(self._options.config, 'window_y', self._root.winfo_y())
        except Exception as e:
            logging.debug('failed to save window geometry: %s', e)
        self._rigctl_poller.stop()
        self._stop_stream()
        self._root.destroy()


def parse_args():
    # First pass: find --config (if given) before building the real parser,
    # so config file values can become its defaults -- CLI flags still win.
    pre = argparse.ArgumentParser(add_help=False)
    pre.add_argument('--config', default=DEFAULT_CONFIG)
    pre_args, _ = pre.parse_known_args()
    cfg = load_config(pre_args.config)

    p = argparse.ArgumentParser(description=__doc__, parents=[pre])
    p.add_argument('--rigctl-host', default=cfg.get('rigctl_host', '127.0.0.1'),
                    help='rigctld host to follow for frequency/mode, same as FreeDV (config: rigctl_host, default 127.0.0.1)')
    p.add_argument('--rigctl-port', type=int, default=cfg.get('rigctl_port', 6400),
                    help='rigctld port to follow for frequency/mode (config: rigctl_port, default 6400)')
    p.add_argument('--span', dest='span', type=float, default=cfg.get('span_khz', 50.0),
                    help='total span in kHz shown, centered on the tracked frequency (config: span_khz, default 50 = +/-25kHz)')
    p.add_argument('--mindb', type=float, default=cfg.get('mindb', -120.0),
                    help='waterfall/S-meter noise floor in dBm (config: mindb, default -120)')
    p.add_argument('--maxdb', type=float, default=cfg.get('maxdb', -40.0),
                    help='waterfall/S-meter full-scale in dBm (config: maxdb, default -40)')
    p.add_argument('--smeter-decay', dest='smeter_decay', type=float,
                    default=cfg.get('smeter_decay_db_sec', 20.0),
                    help='S-meter decay rate in dB/sec after a peak; attack is instant (config: smeter_decay_db_sec, default 20)')
    p.add_argument('--smeter-cal', dest='smeter_cal_db', type=float,
                    default=cfg.get('smeter_cal_db', 12.0),
                    help='S-meter calibration offset in dB, added to the computed reading -- tune '
                         'this against a trusted reference (e.g. a webSDR on the same signal) '
                         '(config: smeter_cal_db, default 12 = +2 S-units)')
    p.add_argument('--smeter-peak-hold', dest='smeter_peak_hold_sec', type=float,
                    default=cfg.get('smeter_peak_hold_sec', 3.0),
                    help='seconds a peak-hold reading stays frozen before it starts decaying '
                         '(config: smeter_peak_hold_sec, default 3)')
    p.add_argument('--smeter-peak-decay', dest='smeter_peak_decay_db_sec', type=float,
                    default=cfg.get('smeter_peak_decay_db_sec', 2.0),
                    help='peak-hold decay rate in dB/sec once the hold time has elapsed '
                         '(config: smeter_peak_decay_db_sec, default 2)')
    p.add_argument('--smeter-passband-center', dest='smeter_passband_center_hz', type=float,
                    default=cfg.get('smeter_passband_center_hz', 1500.0),
                    help='S-meter passband center offset from dial frequency, in Hz -- e.g. 1500 for '
                         'a typical USB/FreeDV passband, negative for LSB (config: smeter_passband_center_hz, default 1500)')
    p.add_argument('--smeter-passband-bw', dest='smeter_passband_bw_hz', type=float,
                    default=cfg.get('smeter_passband_bw_hz', 2400.0),
                    help='S-meter passband bandwidth in Hz, centered on smeter_passband_center_hz -- '
                         'tailor this to the actual bandwidth of the FreeDV mode in use '
                         '(config: smeter_passband_bw_hz, default 2400)')
    p.add_argument('--wf-auto-range', dest='wf_auto_range_db', type=float,
                    default=cfg.get('wf_auto_range_db', 50.0),
                    help='waterfall auto-level headroom in dB above the estimated noise floor, when "Auto (adaptive)" '
                         'is selected from the right-click sensitivity menu (config: wf_auto_range_db, default 50)')
    p.add_argument('--wf-auto-beta', dest='wf_auto_beta', type=float,
                    default=cfg.get('wf_auto_beta', 0.9),
                    help='waterfall auto-level smoothing factor (0-1, higher = slower/steadier) for the estimated '
                         'noise floor (config: wf_auto_beta, default 0.9)')
    p.add_argument('--wf-auto-percentile', dest='wf_auto_percentile', type=float,
                    default=cfg.get('wf_auto_percentile', 10.0),
                    help='percentile of the row used as the waterfall auto-level noise-floor estimate -- low enough '
                         'to be robust against a handful of strong outlier bins (a carrier, a birdie, a distant '
                         'strong station) anywhere in the visible span (config: wf_auto_percentile, default 10)')
    p.add_argument('--freq-major', dest='freq_major_khz', type=float, default=cfg.get('freq_major_khz', 5.0),
                    help='major (labeled) frequency axis tick spacing in kHz (config: freq_major_khz, default 5)')
    p.add_argument('--freq-minor', dest='freq_minor_khz', type=float, default=cfg.get('freq_minor_khz', 1.0),
                    help='minor (unlabeled) frequency axis tick spacing in kHz (config: freq_minor_khz, default 1)')
    p.add_argument('--window-height', dest='window_height', type=int,
                    default=cfg.get('window_height', DEFAULT_WINDOW_HEIGHT),
                    help='initial window height in pixels; saved back to the config on graceful exit (config: window_height)')
    p.add_argument('--window-x', dest='window_x', type=int, default=cfg.get('window_x', None),
                    help='initial window X position in pixels; saved back to the config on graceful exit. '
                         'Requires a window manager that honors client-requested position -- under native Wayland this is '
                         'typically ignored, hence GDK_BACKEND=x11/XWayland (config: window_x)')
    p.add_argument('--window-y', dest='window_y', type=int, default=cfg.get('window_y', None),
                    help='initial window Y position in pixels; saved back to the config on graceful exit (config: window_y)')
    p.add_argument('--sdr-list', default=DEFAULT_SDR_LIST, help='flat text file of "name host port" SDR entries')
    p.add_argument('--last-sdr', dest='last_sdr', default=cfg.get('last_sdr', None),
                    help='name of the SDR entry selected last session; used as the initial selection, saved back '
                         'to the config whenever the SDR dropdown changes (config: last_sdr)')
    p.add_argument('--user', default='kiwipanadapter', help='client name reported to the Kiwi')
    p.add_argument('--default-freq', dest='default_freq', type=float, default=cfg.get('default_freq', 14200.0),
                    help='initial center frequency (kHz) used until the first rigctl poll arrives (config: default_freq)')
    p.add_argument('--modulation', default=cfg.get('modulation', 'usb'),
                    help='demodulation mode used for local audio playback until the first rigctl mode '
                         'update arrives -- am/amn/amw/sam/lsb/lsn/usb/usn/cw/cwn/nbfm/nnfm/iq etc '
                         '(config: modulation, default usb)')
    p.add_argument('--snddev', '--sound-device', dest='sounddevice', default=cfg.get('sounddevice', ''),
                    help='sound device to play Kiwi audio on, e.g. a virtual sink name -- run --ls-snd to '
                         'list available devices (config: sounddevice)')
    p.add_argument('--ls-snd', '--list-sound-devices', dest='list_sound_devices', action='store_true',
                    default=False, help='list available sound devices and exit')
    p.add_argument('--ncomp', '--no-compression', dest='ncomp', action='store_true',
                    default=cfg.get('ncomp', False),
                    help="don't use audio compression -- better quality for a data-mode decoder like FreeDV, "
                         "at the cost of ~2x audio bandwidth to the Kiwi (config: ncomp, default false)")
    p.add_argument('-L', '--lp-cut', dest='lp_cut', type=float, default=cfg.get('lp_cut', None),
                    help='low-pass cutoff frequency, in Hz -- overridden by any live rigctl mode/passband '
                         'update once one arrives (config: lp_cut)')
    p.add_argument('-H', '--hp-cut', dest='hp_cut', type=float, default=cfg.get('hp_cut', None),
                    help='high-pass cutoff frequency, in Hz -- overridden by any live rigctl mode/passband '
                         'update once one arrives (config: hp_cut)')
    p.add_argument('-g', '--agc-gain', dest='agc_gain', type=float, default=cfg.get('agc_gain', None),
                    help='AGC gain; if set, AGC is turned off (config: agc_gain)')
    p.add_argument('--blocksize', dest='blocksize', type=int, default=cfg.get('blocksize', 512),
                    help='sound player blocksize in frames -- kept small so play() doesn\'t block retunes '
                         'for long (config: blocksize, default 512)')
    p.add_argument('--nb', dest='nb', action='store_true', default=cfg.get('nb', False),
                    help='enable noise blanker with default parameters (config: nb)')
    p.add_argument('--nb-gate', dest='nb_gate', type=int, default=cfg.get('nb_gate', 100),
                    help='noise blanker gate time in usec, 100-5000 (config: nb_gate, default 100)')
    p.add_argument('--nb-thresh', dest='nb_thresh', type=int, default=cfg.get('nb_thresh', 50),
                    help='noise blanker threshold in percent, 0-100 (config: nb_thresh, default 50)')
    p.add_argument('--de-emp', dest='de_emp', action='store_true', default=cfg.get('de_emp', False),
                    help='enable de-emphasis (config: de_emp)')
    p.add_argument('--resample', dest='resample', type=int, default=cfg.get('resample', 0),
                    help='resample audio output to this rate in Hz, 0 = no resampling (config: resample)')
    p.add_argument('--if', dest='ifreq', type=float, default=cfg.get('ifreq', None),
                    help='intermediate frequency shift in Hz, only valid with modulation=iq -- for '
                         'IQ-in/IQ-out workflows such as feeding raw I/Q into FreeDV transmit (config: ifreq)')
    p.add_argument('--log-level', default='warn', choices=['debug', 'info', 'warn', 'error'])
    return p.parse_args()


def main():
    options = parse_args()
    if options.list_sound_devices:
        print(sc.all_speakers())
        return
    logging.basicConfig(level=logging.getLevelName(options.log_level.upper()),
                         format='%(asctime)-15s %(message)s')
    root = tk.Tk()
    PanadapterApp(root, options)
    root.mainloop()


if __name__ == '__main__':
    main()
