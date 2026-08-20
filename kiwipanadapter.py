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
import http.client
import logging
import math
import os
import queue
import re
import signal
import socket
import subprocess
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

HAS_XLIB = True
try:
    from Xlib import display as xlib_display
except ImportError:
    HAS_XLIB = False

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
THEME_POLL_MS = 5000  # how often to re-check the desktop's light/dark setting
RIG_STALE_TIMEOUT_SEC = 5.0  # how long without a successful rigctl poll (Auto mode) before the
                              # frequency readout switches to "No rig data" -- RigctlPoller's own
                              # connect/read failures only ever log at debug level, so without this
                              # a dead/not-yet-responsive rigctld link is otherwise silently invisible:
                              # the waterfall just sits on default_freq showing perfectly normal-looking
                              # (but meaningless) data forever, with no on-screen sign anything's wrong.
FINE_TUNE_STEP_HZ = 5.0  # per-click Manual-mode nudge from the </> fine-tune buttons
SNAP_POLL_MS = 3000  # how often to re-check the snap-target window's geometry (snap_below_title) --
                      # deliberately not fast: the use case (another app's window growing/shrinking
                      # as content is added) has no need for frame-perfect tracking, just needs to
                      # eventually catch up.
SNAP_TOP_OVERLAP_PX_DEFAULT = 2  # default for snap_top_overlap_px (config/--snap-top-overlap) --
                          # tucks this many pixels up under the snap target's reported bottom edge.
                          # live-observed a few pixels of visible gap between the two even with a
                          # target window that had a fully settled, unchanging geometry, so it isn't
                          # just poll staleness -- a small amount of deliberate overlap costs nothing
                          # (target's own rendering just covers this window's very top edge). Made
                          # configurable rather than a fixed constant: the actual gap/overlap turned
                          # out to be WM/decoration/scaling-dependent -- one machine needed a large
                          # negative value here to stop the target window's own content (titlebar/
                          # border) from overlapping down onto this window's controls.
STREAM_STALE_TIMEOUT_SEC = 10.0  # how long a stream can go without delivering any actual
                                  # data before it's treated as dead and reconnected -- a TCP
                                  # socket can stay open (run_event still set, _poll_reconnect's
                                  # existing wf_down/audio_down checks both blind to this) while
                                  # the Kiwi has silently stopped sending on it. Live-observed:
                                  # W/F kept updating normally (status showed "Connected") while
                                  # the SND side had gone silent -- no sound until a manual
                                  # Stop/Start. Checked per-side so a stalled audio channel alone
                                  # is enough to trigger a reconnect even though W/F looks fine.

# Control-bar tint per theme -- ttk Frame/Label don't inherit the desktop
# theme's own background/text colors like the Buttons/Comboboxes left at
# their default appearance do, so these need to be picked explicitly and
# re-applied if the desktop theme changes while running.
CONTROL_BAR_COLORS = {
    'light': {'bg': '#dce9f5', 'fg': '#000000'},
    'dark':  {'bg': '#2b3a4a', 'fg': '#e8e8e8'},
}


def _detect_dark_theme():
    """Best-effort light/dark detection for the desktop color scheme.
    KDE Plasma/Breeze first, falling back to GTK/GNOME's gsettings.
    Defaults to light (False) if nothing can be read.

    KDE's ColorScheme/LookAndFeelPackage keys can live in either
    ~/.config/kdeglobals (session overrides) or ~/.config/kdedefaults/
    kdeglobals (distro-set defaults, used as-is when the user never
    overrode them) -- e.g. a stock Breeze Dark session was observed here
    with only 'LookAndFeelPackage=org.kde.breezedark.desktop' in the first
    file and the actual 'ColorScheme=BreezeDark' in the second, so both
    need checking and neither alone is reliable."""
    hint_found = False
    for path in (os.path.expanduser('~/.config/kdeglobals'),
                 os.path.expanduser('~/.config/kdedefaults/kdeglobals')):
        try:
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('ColorScheme=') or line.startswith('LookAndFeelPackage='):
                        hint_found = True
                        if 'dark' in line.lower():
                            return True
        except OSError:
            continue
    if hint_found:
        return False
    try:
        out = subprocess.run(['gsettings', 'get', 'org.gnome.desktop.interface', 'color-scheme'],
                              capture_output=True, text=True, timeout=1)
        if out.returncode == 0:
            return 'dark' in out.stdout.lower()
    except (OSError, subprocess.SubprocessError):
        pass
    return False

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

# KiwiSDR's own server source (support/stats.cpp, github.com/jks-prv/KiwiSDR)
# runs an "External API" check EXT_API_DECISION_SECS (10s) after each
# connection arrives: if that source IP hasn't been served >=
# EXT_API_DECISION_SERVED (3) plain HTTP requests (the index page + its JS/
# CSS assets, exactly what a real browser tab fetches before ever opening a
# WebSocket), the connection is tagged 'ext_api' (non-Kiwi app) and, on
# Kiwis with ext_api_nchans configured low (0 on Weston), gets a clean
# too_busy kick -- repeating every ~10s since each reconnect resets the
# 10s clock. None of mimic_browser's other header/protocol mimicry touches
# this counter, which is why they had no effect on that kick. This fetches
# the index page plus a couple of its referenced assets first, so the same
# source IP clears the served>=3 threshold before any WS connects.
BROWSER_MIMIC_PREFETCH_ASSET_RE = re.compile(r'''(?:src|href)=["']([^"'?]+\.(?:js|css))["']''')


def _browser_mimic_fetch(host, port, url, headers, timeout):
    """One GET on its own fresh connection. Despite advertising
    'Connection: keep-alive', a real KiwiSDR's embedded Mongoose server was
    observed live (websdr.uk:8076) to reliably drop the socket after the
    first request of a reused connection (RemoteDisconnected, 3/3) -- so
    each request gets its own connection rather than trying to pipeline."""
    conn = http.client.HTTPConnection(host, port, timeout=timeout)
    try:
        conn.request('GET', url, headers=headers)
        resp = conn.getresponse()
        return resp.read()
    finally:
        conn.close()


def browser_mimic_prefetch(host, port, timeout=3.0):
    headers = {}
    for h in BROWSER_MIMIC_HEADERS:
        name, _, value = h.partition(': ')
        headers[name] = value

    try:
        body = _browser_mimic_fetch(host, port, '/', headers, timeout).decode('utf-8', errors='replace')
    except Exception as e:
        logging.debug('mimic_browser prefetch of %s:%s/ failed: %s', host, port, e)
        return

    asset_urls = []
    for m in BROWSER_MIMIC_PREFETCH_ASSET_RE.finditer(body):
        url = m.group(1)
        if url.startswith('http') or url.startswith('//'):
            continue
        if not url.startswith('/'):
            url = '/' + url
        if url not in asset_urls:
            asset_urls.append(url)

    for url in asset_urls[:3]:
        try:
            _browser_mimic_fetch(host, port, url, headers, timeout)
        except Exception as e:
            logging.debug('mimic_browser prefetch of %s:%s%s failed: %s', host, port, url, e)


def parse_bool(val):
    return val.strip().lower() in ('1', 'true', 'yes', 'on')


def parse_float_list(val):
    return [float(x.strip()) for x in val.split(',') if x.strip()]


# Amateur band names offered by the Band combo, in the order they're listed --
# each has a matching 'band_<name>_khz' CONFIG_SCHEMA/argparse entry below.
# Default centers are just sane, easily-edited placeholders (a mix of typical
# SSB/data calling areas), not an authoritative band plan.
BAND_NAMES = ['10m', '12m', '15m', '17m', '20m', '30m', '40m', '60m', '80m', '160m']
BAND_DEFAULT_KHZ = {
    '10m': 28400.0, '12m': 24920.0, '15m': 21200.0, '17m': 18100.0, '20m': 14200.0,
    '30m': 10130.0, '40m': 7100.0, '60m': 5340.0, '80m': 3700.0, '160m': 1900.0,
}
# Conventional voice mode per band -- LSB below 10 MHz, USB above, except 60m
# (channelized, USB by international convention despite being below 10 MHz).
# Applied as the Mode combo's default whenever Band changes -- still
# overridable afterwards via the Mode combo itself.
BAND_DEFAULT_MODE = {
    '10m': 'usb', '12m': 'usb', '15m': 'usb', '17m': 'usb', '20m': 'usb',
    '30m': 'usb', '40m': 'lsb', '60m': 'usb', '80m': 'lsb', '160m': 'lsb',
}
# Approximate amateur band edges (kHz), used only to figure out which Band
# combo entry a given frequency falls in (see _toggle_auto_manual carrying
# the current Auto/rigctl frequency into Manual) -- not authoritative for
# any regulatory purpose, just wide enough to cover typical allocations.
BAND_RANGES_KHZ = {
    '160m': (1800.0, 2000.0), '80m': (3500.0, 4000.0), '60m': (5330.0, 5410.0),
    '40m': (7000.0, 7300.0), '30m': (10100.0, 10150.0), '20m': (14000.0, 14350.0),
    '17m': (18068.0, 18168.0), '15m': (21000.0, 21450.0), '12m': (24890.0, 24990.0),
    '10m': (28000.0, 29700.0),
}


def band_for_freq(freq_khz):
    for name, (lo, hi) in BAND_RANGES_KHZ.items():
        if lo <= freq_khz <= hi:
            return name
    return None

# Mode combo presets -- a single combo replaces the old separate Mode
# (USB/LSB/AM) + B/W (SSB/FreeDV/CW/...) pair. Each entry is a (center_hz,
# width_hz) audio passband, configurable via 'bw_<name>_center_hz'/
# 'bw_<name>_width_hz' -- the underlying demod (which sideband, or AM) is no
# longer part of the combo selection at all: MODE_AM_NAMES entries always
# demod as AM (center_hz unused there -- _compute_bw_passband/
# LiveAudioStream's own AM handling both force lowcut = -highcut regardless,
# so only width_hz matters); every other entry demods as USB/LSB, resolved
# live from the tuned band's convention (BAND_DEFAULT_MODE) and optionally
# flipped by the "reverse sideband" checkbox -- never stored in the combo
# itself. 'FDV1' defaults to 1500/1600 -- the actual FreeDV passband this
# has always used in real use (matches smeter_passband_center_hz/
# smeter_passband_bw_hz in panadapter.conf.example, not this file's own
# generic --smeter-passband-bw CLI default of 2400); 'FDV2' is a narrower
# FreeDV variant (e.g. the narrower digital modes);
# 'CW' defaults to a narrow filter around a typical sidetone pitch;
# 'SSBN'/'SSBW' are narrow/wide SSB alternatives to 'SSB'; 'AMN'/'AM'/'AMW'
# are narrow/normal/wide AM alternatives, spaced like a typical rig's AM
# filter set (narrow for crowded conditions, wide for higher fidelity).
# Auto mode uses whichever entry is currently selected here too (see
# _on_rigctl_mode) -- it's no longer locked to a fixed hardcoded shape.
MODE_NAMES = ['FDV1', 'FDV2', 'SSB', 'SSBN', 'SSBW', 'AM', 'AMN', 'AMW', 'CW']
MODE_AM_NAMES = {'AM', 'AMN', 'AMW'}
BW_DEFAULT_HZ = {
    'FDV1': (1500.0, 1600.0),
    'FDV2': (1500.0, 1000.0),
    'SSB': (1500.0, 3000.0),
    'SSBN': (1200.0, 2400.0),
    'SSBW': (2000.0, 4000.0),
    'AM': (0.0, 6000.0),
    'AMN': (0.0, 4000.0),
    'AMW': (0.0, 12000.0),
    'CW': (750.0, 500.0),
}


def validate_mode_name(value, config_key, fallback):
    """A Mode combo config value (manual_mode/auto_mode) that isn't a known
    MODE_NAMES entry -- e.g. a pre-merge config's raw sideband ('usb'/'lsb'/
    'am') from before Mode+B/W were combined into one combo, or just a typo
    -- would otherwise be an invalid selection the readonly combo can't
    actually display. Map it onto the given fallback instead, preferring
    'AM' when the stale value at least says 'am'."""
    if value in MODE_NAMES:
        return value
    resolved = 'AM' if value.lower() == 'am' else fallback
    logging.info('%s %r from config is not a known Mode preset, using %s instead', config_key, value, resolved)
    return resolved

# Mirrors kiwi/client.py's own (private, per-instance) _default_passbands
# table -- used here only to draw the yellow passband indicator for Auto/
# rigctl-driven modes, where only a highcut width (not a full lowcut/highcut
# pair) is ever known locally; never sent to the server.
DEFAULT_PASSBANDS_HZ = {
    'lsb': (-2700, -300), 'lsn': (-2400, -300),
    'usb': (300, 2700), 'usn': (300, 2400),
    'cw': (300, 700), 'cwn': (470, 530),
    'nbfm': (-6000, 6000), 'nnfm': (-3000, 3000),
}

DEFAULT_ZOOM_STEPS_KHZ = [250.0, 100.0, 50.0, 20.0, 10.0]

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
    'radio_capture_device': str,
    'rx_source_mode': str,
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
    'auto_mode_by_band': parse_bool,
    'reverse_sideband': parse_bool,
    'hide_titlebar': parse_bool,
    'snap_below_title': str,
    'snap_bottom_margin_px': int,
    'snap_top_overlap_px': int,
    'sdr_freq_offset_hz': float,
    'manual_active': parse_bool,
    'manual_freq_khz': float,
    'manual_band': str,
    'manual_mode': str,
    'auto_mode': str,
    'zoom_span_khz': float,
    'zoom_steps_khz': parse_float_list,
}
for _name in BAND_NAMES:
    CONFIG_SCHEMA['band_%s_khz' % _name] = float
    # Per-band "where you left off" memory (see _on_band_change) -- distinct
    # from band_<name>_khz above, which is the fixed preset center. Absent
    # until a band's actually been visited and left in Manual.
    CONFIG_SCHEMA['band_%s_last_khz' % _name] = float
for _name in MODE_NAMES:
    CONFIG_SCHEMA['bw_%s_center_hz' % _name.lower()] = float
    CONFIG_SCHEMA['bw_%s_width_hz' % _name.lower()] = float


# Generous ceiling comfortably above every real per-Kiwi MAX_FREQ seen so
# far (30000/30720/32000 kHz) -- just enough to catch an obviously-wrong
# frequency (a stray VHF/UHF value, a unit mixup) before it's ever committed
# to self._current_freq_khz/self._manual_freq_khz. Either can become the
# *initial* frequency of the next connection -- any SDR, any session, since
# manual_freq_khz is persisted to panadapter.conf -- where a bad value
# crashes LiveAudioStream/LiveWFStream's _setup_rx_params() immediately, on
# every single connection attempt from then on, not just the one bad retune
# (hit live 2026-08-09: a stray rigctl value during dummy-rig CAT testing
# got carried into manual_freq_khz via the Auto->Manual carry-over feature,
# persisted to disk, and broke every subsequent connection on every restart
# until this validation was added).
PLAUSIBLE_MAX_FREQ_KHZ = 40000.0


def is_plausible_freq_khz(freq_khz):
    return freq_khz is not None and 0.0 <= freq_khz <= PLAUSIBLE_MAX_FREQ_KHZ


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


def nice_tick_step(span_khz, target_ticks=8):
    """Pick a "nice" (1-2-5 progression) major tick step for a given span, so
    the frequency axis stays readable across widely different Span levels
    (10 kHz to 250+ kHz) instead of the old fixed 5/1 kHz spacing crowding or
    thinning out. Minor step subdivides the major step into a round number
    matching its leading digit -- 1 and 5 split cleanly into 5 (0.2/1 sub-
    steps), but 2 doesn't (2/5 = 0.4, not a round number to read by eye), so
    it splits into 4 (0.5 sub-steps) instead."""
    if span_khz <= 0:
        return (1.0, 5.0)
    raw = span_khz / target_ticks
    exp = math.floor(math.log10(raw))
    base = 10 ** exp
    major = 10 * base
    divisions = 5
    mult_divisions = {1: 5, 2: 4, 5: 5, 10: 5}
    for mult in (1, 2, 5, 10):
        step = mult * base
        if step >= raw:
            major = step
            divisions = mult_divisions[mult]
            break
    return (major / divisions, major)


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
            f.write("# Derive Auto-mode sideband (LSB/USB) from the tuned band's convention\n")
            f.write("# instead of trusting whatever mode rigctl reports -- needed when the rig\n")
            f.write("# (e.g. a plain Hamlib Dummy backend) never actually sets LSB below 10MHz.\n")
            f.write("auto_mode_by_band  false\n")
            f.write("# Flips the band-convention sideband picked above (and Manual mode's own\n")
            f.write("# same band-convention lookup) -- an escape hatch for the rare occasion the\n")
            f.write("# conventional sideband isn't what's wanted.\n")
            f.write("reverse_sideband  false\n")
            f.write("# Remove this window's titlebar (saves vertical space, needs python-xlib) --\n")
            f.write("# stays fully window-manager-managed, just has no titlebar left to drag by.\n")
            f.write("# Implied by snap_below_title below whenever that's set.\n")
            f.write("hide_titlebar  false\n")
            f.write("# Continuously reposition below the first window whose title contains this,\n")
            f.write("# spanning full screen width and filling down to the screen bottom. Unset\n")
            f.write("# (no line below) disables it -- uncomment and adjust to enable:\n")
            f.write("# snap_below_title  FreeDV Reporter\n")
            f.write("# Pixels of screen bottom left uncovered by snap_below_title, so an\n")
            f.write("# auto-hide taskbar's edge-hover trigger stays reachable.\n")
            f.write("snap_bottom_margin_px  4\n")
            f.write("# Pixels this window tucks up under snap_below_title's target's reported\n")
            f.write("# bottom edge -- machine/theme/scaling dependent, tune by eye: too small\n")
            f.write("# leaves a visible gap, too large lets the target's own titlebar/border\n")
            f.write("# overlap down onto this window's controls.\n")
            f.write("snap_top_overlap_px  %d\n" % SNAP_TOP_OVERLAP_PX_DEFAULT)
            f.write("# Calibration trim (Hz) added to the SDR's actual tuned frequency only --\n")
            f.write("# corrects a fixed audio-tone offset FreeDV hears, e.g. Kiwi clock error.\n")
            f.write("# Adjustable live via the </> buttons either side of the freq readout.\n")
            f.write("sdr_freq_offset_hz  0\n")
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
            f.write("\n# Manual tuning (Auto/Manual toggle) -- last state, restored at startup.\n")
            f.write("# Auto and Manual each remember their own last-used Mode combo selection\n")
            f.write("# separately (auto_mode/manual_mode) -- switching between them, or\n")
            f.write("# restarting, always resumes each one right where it was left.\n")
            f.write("manual_active   false\n")
            f.write("manual_freq_khz %s\n" % BAND_DEFAULT_KHZ['40m'])
            f.write("manual_band     40m\n")
            f.write("manual_mode     SSB\n")
            f.write("auto_mode       FDV1\n")
            f.write("zoom_span_khz   50\n")
            f.write("zoom_steps_khz  %s\n" % ','.join(str(int(s)) for s in DEFAULT_ZOOM_STEPS_KHZ))
            f.write("\n# Band combo centers (kHz) -- edit freely, these are just placeholders\n")
            for _name in BAND_NAMES:
                f.write("band_%-6s %s\n" % (_name + '_khz', BAND_DEFAULT_KHZ[_name]))
            f.write("\n# Mode combo passband presets (Hz)\n")
            for _name in MODE_NAMES:
                center, width = BW_DEFAULT_HZ[_name]
                key = _name.lower()
                f.write("bw_%s_center_hz  %s\n" % (key, center))
                f.write("bw_%s_width_hz   %s\n" % (key, width))
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


def _pw_link_list():
    """Snapshot of the current PipeWire graph's links as {dest_port: {src_ports}},
    parsed from 'pw-link -l' (same '<port>' / '  |<- <src>' / '  |-> <dst>'
    format freedv-start-leno's own pw-link-ls/pw-link-del awk functions
    parse). Only the '|<-' half is kept (each link appears twice, once from
    each endpoint's perspective) so callers can check current state before
    connecting/disconnecting. Returns {} on any pw-link failure."""
    try:
        out = subprocess.run(['pw-link', '-l'], capture_output=True, text=True, timeout=2).stdout
    except Exception as e:
        logging.warning('pw-link -l failed: %s', e)
        return {}
    links = {}
    prev = None
    for line in out.splitlines():
        if line.startswith((' ', '\t')):
            arrow = line.strip()
            if arrow.startswith('|<-') and prev:
                links.setdefault(prev, set()).add(arrow[3:].strip())
        else:
            prev = line.strip()
    return links


def _pw_node_ports(node, direction):
    """'node:port' strings for the given node ('o' = pw-link -o, its output/
    source ports; 'i' = pw-link -i, its input/sink ports), sorted so FL comes
    before FR. Returns [] if the node isn't currently in the PipeWire graph
    (not running, wrong name, hardware unplugged) or pw-link fails."""
    try:
        out = subprocess.run(['pw-link', '-o' if direction == 'o' else '-i'],
                              capture_output=True, text=True, timeout=2).stdout
    except Exception as e:
        logging.warning('pw-link -%s failed: %s', direction, e)
        return []
    prefix = node + ':'
    return sorted(p for p in out.splitlines() if p.startswith(prefix))


def _pw_link_set(src_ports, dst_ports, connect):
    """Idempotently connect/disconnect src_ports<->dst_ports (paired
    positionally; a single-port src is paired with every dst port). Skips
    pairs already in the desired state, so repeat calls are silent no-ops.
    Returns False if either side is empty or any pw-link call failed."""
    if not src_ports or not dst_ports:
        return False
    if len(src_ports) == 1 < len(dst_ports):
        pairs = [(src_ports[0], d) for d in dst_ports]
    else:
        pairs = list(zip(src_ports, dst_ports))
    current = _pw_link_list()
    ok = True
    for s, d in pairs:
        linked = s in current.get(d, ())
        if connect == linked:
            continue
        cmd = ['pw-link'] + (['-d'] if not connect else []) + [s, d]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=2)
            if r.returncode != 0:
                logging.warning('%s failed: %s', ' '.join(cmd), r.stderr.strip())
                ok = False
        except Exception as e:
            logging.warning('%s raised %s', ' '.join(cmd), e)
            ok = False
    return ok


_XWININFO_ID_RE = re.compile(r'^\s*(0x[0-9a-fA-F]+)\s+"([^"]*)"')
_XWININFO_GEOM_RE = re.compile(
    r'Absolute upper-left X:\s*(-?\d+).*?Absolute upper-left Y:\s*(-?\d+).*?'
    r'Width:\s*(\d+).*?Height:\s*(\d+)', re.DOTALL)


def _remove_titlebar(root_tk):
    """Strip this window's titlebar/border by setting _MOTIF_WM_HINTS --
    the same mechanism KDE's own per-window "No titlebar and frame" rule
    uses -- rather than Tk's overrideredirect(). overrideredirect() pulls
    the window entirely out of the WM's normal management, which was
    live-observed under KWin/Plasma Wayland to break an auto-hide taskbar's
    own reveal-on-top behavior (both end up fighting over an always-above
    compositor layer, the panel only briefly/partially showing before
    getting covered again). Motif hints keep the window fully WM-managed
    -- normal stacking, still in the taskbar/Alt+Tab, the auto-hide panel
    reveals correctly over it -- and only strip the visual chrome. Needs
    python-xlib (a separate raw X11 connection from Tk's own Tcl/Tk one);
    logs a warning and leaves the titlebar in place if that's not
    installed, rather than falling back to overrideredirect's known-broken
    behavior for this use case."""
    if not HAS_XLIB:
        logging.warning('hide_titlebar/snap_below_title requested but python-xlib is not installed -- '
                         'titlebar will not be removed (pip install python-xlib)')
        return
    try:
        disp = xlib_display.Display()
        try:
            # winfo_id() is NOT the window the WM actually manages/decorates
            # on this Tk build -- live-verified via xwininfo -tree: Tk
            # inserts its own internal wrapper window as the real top-level
            # (carries WM_NAME/WM_CLASS, is what xwininfo/the WM see as
            # "the" window) and winfo_id() returns an unnamed *child* of
            # that instead. Setting the hint there is silently ineffective
            # (readable back fine on our own connection, but the WM never
            # sees it since it isn't watching that window). Walk up the
            # parent chain to the true top-level -- the window whose parent
            # is the root -- regardless of how many wrapper layers sit
            # below it.
            root_id = disp.screen().root.id
            window = disp.create_resource_object('window', root_tk.winfo_id())
            while True:
                parent = window.query_tree().parent
                if parent.id == root_id:
                    break
                window = parent
            motif_hints = disp.intern_atom('_MOTIF_WM_HINTS')
            # 5 x CARD32: flags, functions, decorations, input_mode, status.
            # flags=2 (MWM_HINTS_DECORATIONS is the only field being set),
            # decorations=0 (none) -- functions/input_mode/status unused here.
            window.change_property(motif_hints, motif_hints, 32, [2, 0, 0, 0, 0])
            disp.sync()
        finally:
            disp.close()
    except Exception as e:
        logging.warning('failed to remove titlebar via _MOTIF_WM_HINTS: %s', e)


def _find_window_id(title_substr):
    """First top-level window whose title contains title_substr (case-
    sensitive, matching e.g. 'FreeDV Reporter' -- FreeDVReporterDialog's own
    title, gui/dialogs/freedv_reporter.cpp -- exactly, including any
    "(configname)" suffix). Returns None if none matches or xwininfo fails.
    Shells out rather than adding an X11 library dependency (python-xlib
    etc.) just for this -- consistent with this file's existing PipeWire
    helpers above, and this only needs to run a few times a minute at most
    (see SNAP_POLL_MS)."""
    try:
        out = subprocess.run(['xwininfo', '-root', '-tree'], capture_output=True, text=True, timeout=2).stdout
    except Exception as e:
        logging.debug('xwininfo -tree failed: %s', e)
        return None
    for line in out.splitlines():
        m = _XWININFO_ID_RE.match(line)
        if m and title_substr in m.group(2):
            return m.group(1)
    return None


def _get_window_geometry(win_id):
    """(x, y, width, height) in absolute screen coordinates for an X11
    window id (as returned by _find_window_id), or None if the window's
    gone or xwininfo fails."""
    try:
        out = subprocess.run(['xwininfo', '-id', win_id], capture_output=True, text=True, timeout=2).stdout
    except Exception as e:
        logging.debug('xwininfo -id %s failed: %s', win_id, e)
        return None
    m = _XWININFO_GEOM_RE.search(out)
    if not m:
        return None
    return tuple(int(g) for g in m.groups())


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
        self._pending_span_khz = None
        self._lock = threading.Lock()
        # Set at construction (rather than left None) so a fresh stream gets
        # one full STREAM_STALE_TIMEOUT_SEC grace period to complete its
        # handshake and deliver a first row before _poll_reconnect could
        # treat it as stalled.
        self._last_data_ts = time.time()

    def _setup_rx_params(self):
        # self.MAX_FREQ (kiwi/client.py's KiwiSDRStream) starts at the 30 MHz
        # default set before any connection exists, and only gets corrected
        # to this Kiwi's real per-unit value -- e.g. 32 MHz, an admin-
        # configurable "max_freq" setting some Kiwis use -- once the
        # server's own 'bandwidth' MSG has been processed during the
        # handshake that precedes this call. Recompute zoom/span here rather
        # than trusting the __init__-time guess: using the wrong constant is
        # invisible exactly at the tuned/center frequency (zero offset times
        # any wrong scale is still zero) but produces a growing frequency
        # error away from center -- e.g. 30 vs 32 MHz is a 6.25% span error.
        self._zoom = zoom_for_span(self._span_khz, max_freq_khz=self.MAX_FREQ)
        self._actual_span_khz = span_for_zoom(self._zoom, max_freq_khz=self.MAX_FREQ)
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

    def set_span(self, span_khz):
        with self._lock:
            self._pending_span_khz = span_khz

    def _process_waterfall_samples(self, seq, samples):
        self._last_data_ts = time.time()
        with self._lock:
            pending = self._pending_freq
            self._pending_freq = None
            pending_span = self._pending_span_khz
            self._pending_span_khz = None

        zoom_changed = False
        if pending_span is not None and pending_span != self._span_khz:
            self._span_khz = pending_span
            self._zoom = zoom_for_span(pending_span, max_freq_khz=self.MAX_FREQ)
            self._actual_span_khz = span_for_zoom(self._zoom, max_freq_khz=self.MAX_FREQ)
            zoom_changed = True

        freq_changed = False
        if pending is not None and pending != self._freq:
            # Validate before committing to self._freq -- row['center'] below
            # re-derives from self._freq on *every* row regardless of
            # whether a retune just happened, unguarded by any try/except.
            # A bad rigctl-reported frequency (out of this Kiwi's tunable
            # range -- e.g. a stray VHF value, or a unit mixup) getting
            # stuck there would raise on every single subsequent row
            # forever (this exact traceback, seen live 2026-08-07) instead
            # of just failing this one retune attempt.
            try:
                self._remove_freq_offset(pending)
            except Exception as e:
                logging.warning('ignoring invalid retune to %.3f kHz: %s', pending, e)
            else:
                self._freq = pending
                freq_changed = True

        if freq_changed or zoom_changed:
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
        self._pending_manual = None
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
        # See LiveWFStream._last_data_ts -- same purpose, stamped in
        # _queue_audio() (the single choke point all three sample-format
        # handlers funnel through) rather than per-handler.
        self._last_data_ts = time.time()

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
        """Not currently called (2026-08-07) -- PanadapterApp._on_rigctl_mode
        uses set_manual_passband() below instead, so Auto mode always uses
        the FreeDV B/W preset's passband rather than rigctl's raw reported
        width. Left in place rather than removed since that's an explicit
        "for now" simplification, easy to revert by pointing
        _on_rigctl_mode back at this."""
        if mod:
            mod = mod.lower()
            if mod == 'pktusb':
                # FreeDV/hamlib may request Icom-style "packet over USB",
                # which KiwiSDR has no concept of -- treat it as plain USB
                # (same fix as kiwi/rigctld.py's _set_modulation).
                mod = 'usb'
        with self._lock:
            self._pending_mode = (mod, passband_hz)

    def set_manual_passband(self, mod, lowcut_hz, highcut_hz):
        """Independent passband path for the Manual Mode/B-W combos -- unlike
        set_mode() above (driven by rigctl's single passband-width value,
        lowcut always reset to None/server-default), this takes an explicit
        lowcut/highcut pair so a preset like CW can center its narrow filter
        away from the dial frequency. Kept as a separate pending slot rather
        than reshaping _pending_mode so the rigctl-driven Auto path above is
        untouched."""
        if mod:
            mod = mod.lower()
            if mod == 'pktusb':
                mod = 'usb'
        with self._lock:
            self._pending_manual = (mod, lowcut_hz, highcut_hz)

    def _apply_pending_retune(self):
        with self._lock:
            pending_freq = self._pending_freq
            self._pending_freq = None
            pending_mode = self._pending_mode
            self._pending_mode = None
            pending_manual = self._pending_manual
            self._pending_manual = None

        mode_changed = False
        if pending_manual is not None:
            mod, lowcut_hz, highcut_hz = pending_manual
            if mod and (mod != self._modulation or lowcut_hz != self._lowcut or highcut_hz != self._highcut):
                self._modulation = mod
                self._lowcut = lowcut_hz
                self._highcut = highcut_hz
                mode_changed = True
        elif pending_mode is not None:
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
        self._last_data_ts = time.time()
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

        # Wide/tall enough that a full "name  (host:port)  [mimic browser]
        # [no sound] [disabled]" line and the current SDR count both fit
        # without cropping or needing an initial resize.
        self._listbox = tk.Listbox(self, width=90, height=14)
        self._listbox.pack(side='top', fill='both', expand=True, padx=12, pady=12)
        self._refresh_listbox()

        btns = ttk.Frame(self)
        btns.pack(side='top', fill='x', padx=12, pady=(0, 12))
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


class _Tooltip:
    """Minimal hover tooltip -- Tkinter has no built-in equivalent. text_fn
    is called fresh each time the tooltip is shown, so it can reflect
    whatever the widget's current state/text is at that moment rather than
    being fixed at setup time."""

    def __init__(self, widget, text_fn, delay_ms=500):
        self._widget = widget
        self._text_fn = text_fn
        self._delay_ms = delay_ms
        self._after_id = None
        self._tip = None
        widget.bind('<Enter>', self._on_enter, add='+')
        widget.bind('<Leave>', self._on_leave, add='+')
        widget.bind('<ButtonPress>', self._on_leave, add='+')

    def _on_enter(self, _event):
        self._after_id = self._widget.after(self._delay_ms, self._show)

    def _on_leave(self, _event):
        if self._after_id is not None:
            self._widget.after_cancel(self._after_id)
            self._after_id = None
        self._hide()

    def _show(self):
        self._after_id = None
        if self._tip is not None:
            return
        x = self._widget.winfo_rootx()
        y = self._widget.winfo_rooty() + self._widget.winfo_height() + 4
        self._tip = tk.Toplevel(self._widget)
        self._tip.wm_overrideredirect(True)
        tk.Label(self._tip, text=self._text_fn(), background='#ffffe0', relief='solid',
                 borderwidth=1, font=('TkDefaultFont', 8)).pack(ipadx=4, ipady=2)
        # Keep the tooltip fully on-screen -- a widget packed hard against
        # the window's right edge (e.g. the SDR trim buttons) would
        # otherwise open a tooltip that runs off the screen and gets
        # truncated, since this is an undecorated override-redirect
        # Toplevel with no window manager to clip/reposition it. Measure
        # the actual rendered width (needs the label already packed above)
        # and clamp x so the tooltip's right edge never passes the screen.
        self._tip.update_idletasks()
        screen_w = self._widget.winfo_screenwidth()
        tip_w = self._tip.winfo_reqwidth()
        if x + tip_w > screen_w:
            x = max(0, screen_w - tip_w)
        self._tip.wm_geometry('+%d+%d' % (x, y))

    def _hide(self):
        if self._tip is not None:
            self._tip.destroy()
            self._tip = None


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
        # Calibration trim (Hz) added to the tracked dial frequency only at
        # the point of actually tuning the SDR -- corrects a fixed audio-tone
        # offset FreeDV hears (e.g. Kiwi clock error), without touching the
        # dial frequency used for the readout, band detection, or passband
        # indicator, all of which stay referenced to the true frequency.
        self._sdr_freq_offset_hz = options.sdr_freq_offset_hz
        # Timestamp of the last successful (plausible) rigctl poll -- None
        # means Auto has never had one yet since (re)start. Used only to
        # detect a stale/dead rig link for the "No rig data" readout warning
        # in _poll_queue; not used for anything retune-related.
        self._last_rig_update_ts = None
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
        self._stopped = False

        # Manual tuning state -- self._manual is the single global Auto/Manual
        # gate; while True, _on_rigctl_freq/_on_rigctl_mode below are ignored
        # and Band/drag-tune own the frequency instead (Mode stays live in
        # both -- see self._auto_mode/self._manual_mode below). The
        # remembered manual_*/auto_mode values persist to config immediately
        # on change (like last_sdr) so a short trip back to Auto and forth,
        # or a full app restart, never loses them.
        # Which source feeds FreeDV's FDV_RX_in sink: 'RX' (real rig, via
        # options.radio_capture_device) or 'SDR' (this panadapter's own
        # audio, via FDV_PAN). Audio-only -- unrelated to _manual above.
        self._rx_source = options.rx_source_mode
        self._manual = options.manual_active
        self._manual_band = options.manual_band
        # Auto and Manual each remember their own last-used Mode combo
        # selection independently (auto_mode/manual_mode config keys) -- the
        # combo itself is one shared widget, but which of these two it's
        # currently showing/editing depends on self._manual (see _build_ui,
        # _on_mode_change, _toggle_auto_manual).
        self._manual_mode = validate_mode_name(options.manual_mode, 'manual_mode', 'SSB')
        self._auto_mode = validate_mode_name(options.auto_mode, 'auto_mode', 'FDV1')
        self._reverse_sideband = options.reverse_sideband
        self._zoom_span_khz = options.zoom_span_khz
        self._zoom_steps_khz = options.zoom_steps_khz
        self._band_khz = {name: getattr(options, 'band_%s_khz' % name) for name in BAND_NAMES}
        # "Where you left off" per band -- populated as bands are left (see
        # _on_band_change) and saved on close, so switching back to a band
        # within the same session (or a later one) returns to the exact
        # frequency you were on there, not just the fixed preset above.
        self._band_last_freq_khz = {name: getattr(options, 'band_%s_last_khz' % name)
                                     for name in BAND_NAMES
                                     if getattr(options, 'band_%s_last_khz' % name) is not None}

        self._manual_freq_khz = options.manual_freq_khz
        if not is_plausible_freq_khz(self._manual_freq_khz):
            # Fall back to wherever manual_band itself says, not just a
            # generic default_freq -- otherwise the Band combo shows one
            # band while the actual tuned frequency silently belongs to a
            # different one, which looks exactly like "Band is being
            # ignored" the next time it's selected (nothing changes, since
            # the combo already matches self._manual_band and _on_band_change
            # treats re-selecting the current band as a no-op).
            self._manual_freq_khz = self._band_last_freq_khz.get(
                self._manual_band, self._band_khz.get(self._manual_band, options.default_freq))
            logging.warning('manual_freq_khz %s from config is implausible, using %.3f kHz for band %s instead',
                             options.manual_freq_khz, self._manual_freq_khz, self._manual_band)
            try:
                save_config_value(options.config, 'manual_freq_khz', self._manual_freq_khz)
            except Exception as e:
                logging.debug('failed to save corrected manual_freq_khz: %s', e)
        else:
            # manual_freq_khz is itself a perfectly plausible frequency, but
            # may still not actually belong to manual_band (e.g. stale cruft
            # from before this consistency checking existed) -- the
            # _on_band_change/drag self-heals only fire on a later live
            # action, so a straight restart would otherwise keep showing the
            # stale band forever. Trust the frequency as ground truth here
            # and correct the band label to match it, not the other way round.
            actual_band = band_for_freq(self._manual_freq_khz)
            if actual_band is not None and actual_band != self._manual_band:
                logging.warning('manual_band %s from config does not match manual_freq_khz %.3f kHz -- correcting to %s',
                                 self._manual_band, self._manual_freq_khz, actual_band)
                self._manual_band = actual_band
                try:
                    save_config_value(options.config, 'manual_band', actual_band)
                except Exception as e:
                    logging.debug('failed to save corrected manual_band: %s', e)
        self._bw_hz = {name: (getattr(options, 'bw_%s_center_hz' % name.lower()),
                               getattr(options, 'bw_%s_width_hz' % name.lower())) for name in MODE_NAMES}
        # Transient drag-to-tune state (see _on_wf_drag_*) -- not persisted.
        self._drag_start_x = None
        self._drag_start_freq_khz = None
        self._drag_freq_khz = None
        self._drag_last_dx = 0

        # Currently-active demod passband, as lowcut/highcut Hz offsets from
        # the dial frequency -- kept in sync by _apply_manual_passband
        # (Manual) and _on_rigctl_mode (Auto), purely to draw the yellow
        # passband indicator; never fed back into any retune logic.
        self._pb_lowcut_hz = None
        self._pb_highcut_hz = None

        if self._manual:
            self._current_freq_khz = self._manual_freq_khz

        root.title('Kiwi Panadapter')
        self._build_ui()

        # Apply the persisted RX/SDR source to the live PipeWire graph --
        # nothing else in this system ever links FDV_PAN/radio_capture_device
        # into FDV_RX_in (freedv-links has no such entry, and
        # freedv-start-leno's restore_links step runs before this app even
        # starts), so this is the only place it happens. Self-heal to SDR
        # (always available, since it's just this app's own audio) if RX was
        # persisted but the radio device isn't actually present -- keeps a
        # no-radio machine's copy of the config starting in a working state.
        if not self._apply_rx_source(self._rx_source):
            logging.warning('radio_capture_device unavailable at startup -- falling back to SDR RX source')
            self._rx_source = 'SDR'
            self._apply_rx_source('SDR')
            self._rx_source_var.set('SDR')
            self._rx_source_btn.configure(style='Amber.TButton')
            try:
                save_config_value(self._options.config, 'rx_source_mode', 'SDR')
            except Exception as e:
                logging.debug('failed to save rx_source_mode: %s', e)

        root.update_idletasks()   # so winfo_width/height are accurate before the first row arrives

        self._rigctl_poller = RigctlPoller(options.rigctl_host, options.rigctl_port,
                                            self._on_rigctl_freq, on_mode=self._on_rigctl_mode)
        self._rigctl_poller.start()

        self._start_stream(self._initial_sdr)
        self._active_sdr = self._initial_sdr
        root.protocol('WM_DELETE_WINDOW', self._on_close)
        self._poll_queue()
        self._poll_reconnect()
        if options.snap_below_title:
            self._poll_snap_target()

    def _correct_window_position(self, target_x, target_y):
        """Some window managers (observed: KWin/XWayland under Plasma
        Wayland) render a requested self._root.geometry('+x+y') a title
        bar's height lower than asked -- ICCCM's default NorthWest gravity
        is supposed to keep the client's own top-left fixed with the WM's
        decoration extending outward from it, but this WM instead offsets
        the client by the decoration height on top of the requested
        position. Since _on_close() saves back whatever winfo_x/y report,
        and that's the same (accurate) position the window actually
        rendered at, this was otherwise invisible -- it just looks like a
        correctly-saved position that's wrong. Measure the real error once,
        live, and correct for it, rather than hardcoding a decoration-
        height guess that would only be right for one theme/WM."""
        self._root.update()   # let the WM finish reparenting/decorating before measuring
        actual_x, actual_y = self._root.winfo_x(), self._root.winfo_y()
        error_x, error_y = actual_x - target_x, actual_y - target_y
        if error_x or error_y:
            logging.debug('window position landed %+d,%+d off target (%d,%d) -- correcting',
                          error_x, error_y, target_x, target_y)
            self._root.geometry('+%d+%d' % (target_x - error_x, target_y - error_y))

    def _build_ui(self):
        hiding_titlebar = self._options.hide_titlebar or self._options.snap_below_title
        if hiding_titlebar:
            # withdraw() first -- the WM only reads _MOTIF_WM_HINTS when a
            # window is first mapped, so setting it after that point (a
            # plain, already-mapped root) was live-verified to be silently
            # ineffective (titlebar stays, even though the property itself
            # is correctly set and readable). Set the real geometry now
            # too, still withdrawn, so the eventual deiconify() below maps
            # it directly at its final position/size instead of flashing
            # at some default one first.
            self._root.withdraw()
        screen_w = self._root.winfo_screenwidth()
        geometry = '%dx%d' % (screen_w, self._options.window_height)
        if self._options.window_x is not None and self._options.window_y is not None:
            geometry += '+%d+%d' % (self._options.window_x, self._options.window_y)
        self._root.geometry(geometry)
        if hiding_titlebar:
            # snap_below_title implies hiding the titlebar too -- there'd
            # be no way to tell a user-owned titlebar apart from this
            # window's own fully-automatic positioning otherwise.
            # update_idletasks() forces the window to exist as an X
            # resource without actually mapping it yet (still withdrawn).
            self._root.update_idletasks()
            _remove_titlebar(self._root)
            self._root.deiconify()
        if self._options.window_x is not None and self._options.window_y is not None:
            self._correct_window_position(self._options.window_x, self._options.window_y)

        # Fixed-height widgets (top control bar, S-meter bar, freq-axis bar)
        # must be packed to their side *before* the expanding waterfall
        # canvas, otherwise Tk's pack geometry manager starves them of space
        # first as the window shrinks instead of shrinking only the
        # expandable canvas.
        # Tinted background on the control bar itself, so the buttons and
        # combos (left at the theme's own default appearance) visually stand
        # out against it -- ttk widgets don't take a plain bg= like classic
        # tk ones, so this needs a named style applied to the frame and its
        # plain (non-button/combo) Label children, or the labels would keep
        # showing the old theme background as a mismatched box around them.
        # The tint itself tracks the desktop's light/dark setting (see
        # _apply_control_bar_theme) rather than being fixed, so it stays
        # readable under a dark Breeze theme too.
        self._style = ttk.Style(self._root)
        style = self._style
        # Flat, like the other control-bar labels (a sunken/bordered box was
        # tried and looked cluttered in the tight bar). Green while actually
        # streaming data (Connected), amber for every other state
        # (Connecting/Disconnecting/Stopped) -- same green=good/amber=not-
        # quite convention as the RX/SDR toggle below. Both pinned to fixed
        # colors rather than tracking the dark-mode tint -- the
        # Buttons/Comboboxes beside it stay at Tk's native (light) look
        # regardless of the desktop theme, so a dark status box just clashed
        # with them instead of reading as "matching the theme". See
        # _set_status.
        style.configure('StatusGreen.TLabel', padding=(4, 1), background='#4caf50', foreground='#000000')
        style.configure('StatusAmber.TLabel', padding=(4, 1), background='#ffb300', foreground='#000000')
        self._theme_dark = None
        self._apply_control_bar_theme()
        # RX/SDR source toggle: green while FreeDV listens to the real
        # radio, amber while it's listening to this panadapter instead --
        # amber as the "not the radio, don't forget" color.
        style.configure('Green.TButton', background='#4caf50')
        style.map('Green.TButton', background=[('active', '#66bb6a'), ('disabled', '#a5d6a7')])
        style.configure('Amber.TButton', background='#ffb300')
        style.map('Amber.TButton', background=[('active', '#ffc107'), ('disabled', '#ffe082')])

        top = ttk.Frame(self._root, style='Control.TFrame')
        top.pack(side='top', fill='x', padx=4, pady=4)

        # Packed first (side='right') so it claims its space before any of
        # the left-packed controls below -- otherwise, on a narrow screen,
        # a growing left side (more combos added over time) can exhaust the
        # bar's width and get this pushed off/cropped instead of just
        # squeezing the left-side controls, which is the much less
        # important side to lose room to. The fine-tune buttons are packed
        # as part of this same right-hand group, both to the left of the
        # freq label -- these trim the actual SDR tuning
        # (sdr_freq_offset_hz), not the tracked dial frequency, so they're
        # active in both Auto and Manual.
        freq_frame = ttk.Frame(top, style='Control.TFrame')
        freq_frame.pack(side='right')
        self._freq_down_btn = ttk.Button(freq_frame, text='◄', width=2,
                                          command=lambda: self._nudge_sdr_offset(-FINE_TUNE_STEP_HZ))
        self._freq_down_btn.pack(side='left', padx=(0, 2))
        _Tooltip(self._freq_down_btn, lambda: 'SDR trim %+g Hz (currently %+g Hz)' % (
            -FINE_TUNE_STEP_HZ, self._sdr_freq_offset_hz))
        self._freq_up_btn = ttk.Button(freq_frame, text='►', width=2,
                                        command=lambda: self._nudge_sdr_offset(FINE_TUNE_STEP_HZ))
        self._freq_up_btn.pack(side='left', padx=(0, 4))
        _Tooltip(self._freq_up_btn, lambda: 'SDR trim %+g Hz (currently %+g Hz)' % (
            FINE_TUNE_STEP_HZ, self._sdr_freq_offset_hz))
        self._freq_var = tk.StringVar(value='-- kHz')
        ttk.Label(freq_frame, textvariable=self._freq_var, font=('TkFixedFont', 11, 'bold'),
                  style='Control.TLabel').pack(side='left')

        ttk.Label(top, text='SDR:', style='Control.TLabel').pack(side='left')
        self._sdr_var = tk.StringVar(value=self._initial_sdr['name'])
        combo_width = max((len(s['name']) for s in self._sdr_list), default=10) + 2
        self._sdr_combo = ttk.Combobox(top, textvariable=self._sdr_var, state='readonly',
                                        width=combo_width,
                                        values=[s['name'] for s in self._enabled_sdrs()])
        self._sdr_combo.pack(side='left', padx=4)
        self._sdr_combo.bind('<<ComboboxSelected>>', self._on_sdr_change)

        self._status_var = tk.StringVar(value='Connecting')
        # Fixed width (like the S-meter's dBm label below) so
        # Connecting/Disconnecting/Connected/Stopped text changes don't shift Manage/
        # Stop/Auto/the combos left and right as the status changes.
        self._status_label = ttk.Label(top, textvariable=self._status_var, width=21, anchor='w',
                                        style='StatusAmber.TLabel')
        self._status_label.pack(side='left', padx=2)

        ttk.Button(top, text='Manage...', command=self._open_sdr_manager).pack(side='left', padx=2)

        self._stop_btn_var = tk.StringVar(value='Stop')
        ttk.Button(top, textvariable=self._stop_btn_var, command=self._toggle_stream, width=6).pack(side='left', padx=2)

        # Shows the current state (Auto/Manual), not the click target -- a
        # tooltip spells out the action since the label alone no longer does.
        # Green/amber same as the status label and RX/SDR toggle -- Auto
        # (following the rig) is the "normal" green state, Manual amber.
        self._auto_btn_var = tk.StringVar(value=('Manual' if self._manual else 'Auto'))
        self._auto_btn = ttk.Button(top, textvariable=self._auto_btn_var, command=self._toggle_auto_manual,
                                     width=7, style=('Amber.TButton' if self._manual else 'Green.TButton'))
        self._auto_btn.pack(side='left', padx=2)
        _Tooltip(self._auto_btn, lambda: 'Click to switch to %s' % (
            'Auto' if self._auto_btn_var.get() == 'Manual' else 'Manual'))

        self._rx_source_var = tk.StringVar(value=self._rx_source)
        self._rx_source_btn = ttk.Button(top, textvariable=self._rx_source_var, command=self._toggle_rx_source,
                                          width=4,
                                          style=('Green.TButton' if self._rx_source == 'RX' else 'Amber.TButton'))
        self._rx_source_btn.pack(side='left', padx=2)
        _Tooltip(self._rx_source_btn, lambda: 'FreeDV RX audio: %s (click for %s)' % (
            self._rx_source_var.get(), 'SDR' if self._rx_source_var.get() == 'RX' else 'RX'))

        manual_combo_state = 'readonly' if self._manual else 'disabled'

        ttk.Label(top, text='Span:', style='Control.TLabel').pack(side='left')
        self._zoom_labels = [self._fmt_zoom_label(k) for k in self._zoom_steps_khz]
        self._zoom_label_khz = dict(zip(self._zoom_labels, self._zoom_steps_khz))
        self._zoom_var = tk.StringVar(value=self._fmt_zoom_label(self._zoom_span_khz))
        if self._zoom_var.get() not in self._zoom_label_khz:
            self._zoom_labels = [self._zoom_var.get()] + self._zoom_labels
            self._zoom_label_khz[self._zoom_var.get()] = self._zoom_span_khz
        self._zoom_combo = ttk.Combobox(top, textvariable=self._zoom_var, state='readonly',
                                         width=7, values=self._zoom_labels)
        self._zoom_combo.pack(side='left', padx=(2, 4))
        self._zoom_combo.bind('<<ComboboxSelected>>', self._on_zoom_change)

        ttk.Label(top, text='Band:', style='Control.TLabel').pack(side='left')
        self._band_var = tk.StringVar(value=self._manual_band)
        self._band_combo = ttk.Combobox(top, textvariable=self._band_var, state=manual_combo_state,
                                         width=5, values=BAND_NAMES)
        self._band_combo.pack(side='left', padx=(2, 4))
        self._band_combo.bind('<<ComboboxSelected>>', self._on_band_change)

        # Unlike Band (Manual-only -- Auto's frequency comes from rigctl,
        # not a Band pick), Mode stays enabled in both Auto and Manual: it
        # now only selects passband shape (see _on_rigctl_mode), which Auto
        # needs to choose too (e.g. FDV1 vs the narrower FDV2), not a
        # frequency/sideband decision that only Manual owns. The combo shows
        # self._auto_mode or self._manual_mode depending on which is
        # currently active -- _on_mode_change/_toggle_auto_manual keep the
        # two in sync with it as that switches.
        ttk.Label(top, text='Mode:', style='Control.TLabel').pack(side='left')
        self._mode_var = tk.StringVar(value=(self._manual_mode if self._manual else self._auto_mode))
        self._mode_combo = ttk.Combobox(top, textvariable=self._mode_var, state='readonly',
                                         width=6, values=MODE_NAMES)
        self._mode_combo.pack(side='left', padx=(2, 4))
        self._mode_combo.bind('<<ComboboxSelected>>', self._on_mode_change)

        # Sideband (USB/LSB) is never picked directly any more -- every SSB-
        # family Mode entry resolves it live from the tuned band's own
        # convention (BAND_DEFAULT_MODE). This is the escape hatch for the
        # rare case that's wrong for what's actually wanted, active in both
        # Auto and Manual -- always enabled, unlike the combos above.
        self._reverse_sideband_var = tk.BooleanVar(value=self._reverse_sideband)
        self._reverse_sideband_chk = ttk.Checkbutton(top, text='Rev', variable=self._reverse_sideband_var,
                                                       command=self._on_reverse_sideband_change)
        self._reverse_sideband_chk.pack(side='left', padx=(0, 4))
        _Tooltip(self._reverse_sideband_chk, lambda: 'Reverse sideband -- flip the band-convention '
                 'LSB/USB choice (currently %s)' % ('on' if self._reverse_sideband_var.get() else 'off'))

        # S-meter sits between the control bar and the freq-axis bar, and
        # matches the freq-axis bar's height, so that if the window's bottom
        # ends up slid down behind a system panel on a short screen, it's
        # the waterfall's own bottom edge that gets clipped, not the S-meter
        # reading.
        meter = ttk.Frame(self._root)
        meter.pack(side='top', fill='x', padx=4, pady=(0, 2))
        ttk.Label(meter, text='S:').pack(side='left')
        self._dbm_var = tk.StringVar(value='-- dBm')
        # Fixed width so the S-meter canvas next to it (fill='x', expand=True)
        # doesn't resize when the dBm text's digit count changes (e.g. -99 -> -100).
        ttk.Label(meter, textvariable=self._dbm_var, width=8, anchor='e').pack(side='right', padx=8)
        self._smeter_canvas = tk.Canvas(meter, height=20, highlightthickness=0, bg='black')
        self._smeter_canvas.pack(side='left', fill='x', expand=True, padx=4)

        self._freqaxis_canvas = tk.Canvas(self._root, height=20, highlightthickness=0, bg='black')
        self._freqaxis_canvas.pack(side='top', fill='x')

        self._canvas = tk.Canvas(self._root, highlightthickness=0, bg='black')
        self._canvas.pack(side='top', fill='both', expand=True)
        self._image_id = self._canvas.create_image(0, 0, anchor='nw')
        self._canvas.bind('<Configure>', self._on_resize)
        self._sensitivity_var = tk.StringVar(value='Auto (adaptive)')
        self._canvas.bind('<Button-3>', self._show_sensitivity_menu)
        self._canvas.bind('<ButtonPress-1>', self._on_wf_press)
        self._canvas.bind('<B1-Motion>', self._on_wf_drag)
        self._canvas.bind('<ButtonRelease-1>', self._on_wf_release)

        # Save window geometry live (debounced), not only at clean exit --
        # a launcher (freedv-start) closing this process via a desktop-icon
        # -launched FreeDV can tear the whole app down through a systemd/DE
        # session scope that follows SIGTERM with SIGKILL fast enough that
        # _on_close() never gets to run (or doesn't finish) -- a race a
        # plain terminal-launched process never hits. Saving proactively
        # while the window is open sidesteps needing a clean shutdown to
        # ever actually happen at all.
        self._geometry_save_after_id = None
        self._root.bind('<Configure>', self._on_root_configure)

        self._snap_target_id = None
        self._snap_last_geom = None

    # -- SDR connection management -------------------------------------------------

    def _start_wf_connection(self, sdr_entry, freq, mimic_browser, ws_timestamp=None):
        wf_opt = make_stream_options(sdr_entry['host'], sdr_entry['port'], self._options,
                                      ws_offset=0, mimic_browser=mimic_browser, ws_timestamp=ws_timestamp)
        self._wf_stream = LiveWFStream(wf_opt, freq, self._zoom_span_khz, self._row_queue)
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

    def _apply_rx_source(self, mode):
        """mode: 'RX' or 'SDR'. Idempotently repoints FDV_RX_in's playback
        ports at either the configured radio_capture_device ('RX') or
        FDV_PAN's monitor -- this panadapter's own audio ('SDR'), and
        disconnects the other. Doesn't touch rigctl/frequency routing at
        all. Returns False (logging a warning, changing nothing) if 'RX' was
        requested but radio_capture_device is unset or not currently present
        in the PipeWire graph."""
        rx_in = _pw_node_ports('FDV_RX_in', 'i')
        pan = _pw_node_ports('FDV_PAN', 'o')
        radio_dev = self._options.radio_capture_device
        # _pw_node_ports() matches on the bare node name and appends ':'
        # itself -- strip any port suffix (e.g. a "node:port" string copied
        # straight out of 'pw-link -o' output, which is how this value is
        # documented/likely to be filled in) so the match doesn't silently
        # fail against a name that's technically correct but has an extra
        # ":port" tacked on.
        radio_node = radio_dev.split(':', 1)[0] if radio_dev else radio_dev
        radio = _pw_node_ports(radio_node, 'o') if radio_node else []
        if mode == 'RX':
            if not radio_dev:
                logging.warning('rx_source_mode RX requested but radio_capture_device is not configured')
                return False
            if not radio:
                logging.warning('radio_capture_device "%s" not found in the PipeWire graph', radio_dev)
                return False
            _pw_link_set(radio, rx_in, connect=True)
            _pw_link_set(pan, rx_in, connect=False)
            return True
        else:
            _pw_link_set(pan, rx_in, connect=True)
            if radio:
                _pw_link_set(radio, rx_in, connect=False)
            return True

    def _set_status(self, text):
        """Sets the status text and its background -- green for 'Connected'
        (actually streaming data), amber for everything else (Connecting/
        Disconnecting/Stopped)."""
        self._status_var.set(text)
        self._status_label.configure(style=('StatusGreen.TLabel' if text == 'Connected' else 'StatusAmber.TLabel'))

    def _start_stream(self, sdr_entry):
        with self._freq_lock:
            dial_freq = self._current_freq_khz if self._current_freq_khz is not None else self._options.default_freq
        freq = self._sdr_tune_freq(dial_freq)
        mimic_browser = sdr_entry.get('mimic_browser', False)
        no_sound = sdr_entry.get('no_sound', False)

        if mimic_browser:
            browser_mimic_prefetch(sdr_entry['host'], sdr_entry['port'])

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

        # Re-sync the freshly created streams to whatever self._current_freq_khz
        # holds *now*, not just the value read at the top of this function --
        # connection setup above (browser-mimic prefetch, the mimic_browser
        # 0.25s stagger, the handshake itself) can take long enough for one or
        # more rigctl polls to land in between, updating self._current_freq_khz
        # while self._wf_stream/self._audio_stream were still None. Since
        # _on_rigctl_freq only retunes when the value *changes*, and a static
        # rig frequency never changes again on later polls, a retune missed
        # this way was otherwise never retried -- the stream stayed on its
        # construction-time freq forever, only fixed by chance (a later
        # actual frequency change, or recreating the streams via Stop/Start,
        # an SDR switch, or a reconnect). Live-diagnosed 2026-08-14: stuck on
        # default_freq with rigctl polling successfully the whole time.
        if not self._manual:
            with self._freq_lock:
                freq_now = self._current_freq_khz
            if freq_now is not None:
                if self._wf_stream is not None:
                    self._wf_stream.retune(self._sdr_tune_freq(freq_now))
                if self._audio_stream is not None:
                    self._audio_stream.retune(self._sdr_tune_freq(freq_now))

        self._set_status('Connecting')
        self._stream_start_ts = time.time()
        if self._manual:
            # A freshly (re)created LiveAudioStream always starts with the
            # global default modulation/passband -- reapply Manual's own
            # Mode/B-W selection on top of it (SDR switch, Start, reconnect).
            self._apply_manual_passband()

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
            # wf_down/audio_down above only catch a socket that's actually
            # closed -- a Kiwi can also leave the TCP connection up while
            # silently no longer sending on it (run_event stays set forever
            # in that case), which live-showed as "Connected" with a normal
            # waterfall but dead audio until a manual Stop/Start. Catch that
            # here by timing out on *data*, not just socket state, checked
            # independently per side.
            now = time.time()
            wf_stale = (self._worker is not None and self._wf_stream is not None
                        and now - self._wf_stream._last_data_ts > STREAM_STALE_TIMEOUT_SEC)
            audio_stale = (self._audio_worker is not None and self._audio_stream is not None
                           and now - self._audio_stream._last_data_ts > STREAM_STALE_TIMEOUT_SEC)
            if wf_down or audio_down or wf_stale or audio_stale:
                if wf_stale or audio_stale:
                    logging.warning('%s stream on %s stalled (no data for %.0fs), reconnecting',
                                     'W/F' if wf_stale else 'audio', self._active_sdr['name'],
                                     STREAM_STALE_TIMEOUT_SEC)
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

    def _reset_display_state(self):
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

    def _on_sdr_change(self, _event):
        name = self._sdr_var.get()
        entry = next((s for s in self._sdr_list if s['name'] == name), None)
        if entry is None:
            return
        try:
            save_config_value(self._options.config, 'last_sdr', entry['name'])
        except Exception as e:
            logging.debug('failed to save last_sdr: %s', e)
        if self._stopped:
            return   # just remember the selection -- Start will connect to it
        # The combobox already shows the newly-picked name the instant it's
        # selected (that's just how Combobox works) -- hold the display back
        # on the still-active SDR while actually disconnecting from it, and
        # only swap to the new name once we really start connecting to it,
        # so the box always reflects what's actually live, not what's queued.
        if self._active_sdr is not None:
            self._sdr_var.set(self._active_sdr['name'])
        # Selecting the dropdown item leaves the Combobox's whole displayed
        # text highlighted (Entry-internal selection state, independent of
        # the textvariable) -- reassigning the variable above doesn't clear
        # it, so the stale selection range then lands over only part of
        # whatever text is showing next, painting a spurious highlighted
        # band. Clear it explicitly every time this changes programmatically.
        self._sdr_combo.selection_clear()
        # _stop_stream() blocks on up to two thread joins (2s each) -- paint
        # this now, before that blocks the mainloop, so the click doesn't
        # look like it did nothing for a couple of seconds. update_idletasks()
        # alone wasn't enough to force the actual repaint out to the display
        # before the blocking joins below ran; update() forces that.
        self._set_status('Disconnecting')
        self._root.update()
        self._stop_stream()
        self._reset_display_state()
        self._reconnect_retry_count = 0
        self._sdr_var.set(entry['name'])
        self._sdr_combo.selection_clear()
        self._start_stream(entry)
        self._active_sdr = entry

    def _apply_control_bar_theme(self):
        """Re-check the desktop's light/dark setting and re-tint the control
        bar if it changed, then reschedule itself -- so a Breeze theme
        switch while the app is running is picked up live, not just at
        startup."""
        dark = _detect_dark_theme()
        if dark != self._theme_dark:
            self._theme_dark = dark
            colors = CONTROL_BAR_COLORS['dark' if dark else 'light']
            self._style.configure('Control.TFrame', background=colors['bg'])
            self._style.configure('Control.TLabel', background=colors['bg'], foreground=colors['fg'])
            # The bar Frames are packed with their own padx/pady margin
            # (e.g. top.pack(..., padx=4, pady=4)) -- that margin is bare
            # root window background showing through around the Frame, not
            # covered by Control.TFrame's own styling at all, so it stayed
            # the native (light) Tk background on all four sides even once
            # the Frame itself was correctly tinted. self._root is a plain
            # tk widget (not ttk), so it takes background directly.
            self._root.configure(background=colors['bg'])
            # StatusGreen/StatusAmber.TLabel are deliberately left out here
            # -- pinned to fixed colors in _build_ui (see comment there).
        self._root.after(THEME_POLL_MS, self._apply_control_bar_theme)

    def _toggle_stream(self):
        if self._stopped:
            name = self._sdr_var.get()
            entry = next((s for s in self._sdr_list if s['name'] == name), None)
            if entry is None:
                return
            self._reset_display_state()
            self._reconnect_retry_count = 0
            self._start_stream(entry)
            self._active_sdr = entry
            self._stopped = False
            self._stop_btn_var.set('Stop')
        else:
            self._set_status('Disconnecting')
            self._root.update()
            self._stop_stream()
            self._active_sdr = None
            self._stopped = True
            self._reset_display_state()
            self._redraw()
            self._freq_var.set('-- kHz')
            self._dbm_var.set('-- dBm')
            self._set_status('Stopped')
            self._stop_btn_var.set('Start')

    # -- Auto/Manual toggle + Zoom/Band/Mode/B-W combos -------------------------------

    @staticmethod
    def _fmt_zoom_label(nominal_khz):
        # Labels with the span the Kiwi will actually deliver, not the raw
        # requested value -- the Kiwi only offers power-of-two zoom steps,
        # so e.g. a nominal "10 kHz" request really yields ~14.6 kHz on
        # screen. The combo's stored value stays the nominal request (which
        # resolves to the same zoom level either way -- see zoom_for_span/
        # span_for_zoom), this only fixes the displayed text.
        actual_khz = span_for_zoom(zoom_for_span(nominal_khz))
        return ('%d kHz' % round(actual_khz))

    def _set_manual_combo_states(self, manual):
        # Only Band is gated by Auto/Manual -- Mode and the reverse-sideband
        # checkbox both stay enabled in either (see their own build-time
        # comments in _build_ui for why).
        self._band_combo.config(state=('readonly' if manual else 'disabled'))

    def _toggle_rx_source(self):
        new_mode = 'SDR' if self._rx_source == 'RX' else 'RX'
        if not self._apply_rx_source(new_mode):
            # Graceful failure (no radio_capture_device configured/present):
            # _apply_rx_source already logged why. State/config/PipeWire
            # links are left exactly as they were -- nothing to undo here.
            return
        self._rx_source = new_mode
        self._rx_source_var.set(new_mode)
        self._rx_source_btn.configure(style=('Green.TButton' if new_mode == 'RX' else 'Amber.TButton'))
        try:
            save_config_value(self._options.config, 'rx_source_mode', new_mode)
        except Exception as e:
            logging.debug('failed to save rx_source_mode: %s', e)

    def _toggle_auto_manual(self):
        if self._manual:
            self._manual = False
            self._auto_btn_var.set('Auto')
            self._mode_var.set(self._auto_mode)
        else:
            # Carry the current Auto (rigctl-driven) frequency/band into
            # Manual, rather than jumping to wherever Manual was last left --
            # lets you flip to Manual mid-FreeDV-session to check adjacent
            # frequencies without losing your place. No equivalent needed
            # the other way: Auto always reflects wherever the rig currently
            # is regardless of what Manual was just doing.
            with self._freq_lock:
                current_freq = self._current_freq_khz
            if not is_plausible_freq_khz(current_freq):
                if current_freq is not None:
                    logging.warning('not carrying implausible Auto frequency %.3f kHz into Manual', current_freq)
                current_freq = None
            if current_freq is not None:
                detected_band = band_for_freq(current_freq)
                if detected_band is not None and detected_band != self._manual_band:
                    # Save the band we're leaving its own last-used frequency
                    # first, same as _on_band_change does -- otherwise its
                    # old self._manual_freq_khz value is simply lost/overwritten
                    # below rather than remembered for a return visit.
                    self._band_last_freq_khz[self._manual_band] = self._manual_freq_khz
                    try:
                        save_config_value(self._options.config,
                                           'band_%s_last_khz' % self._manual_band, self._manual_freq_khz)
                    except Exception as e:
                        logging.debug('failed to save band_%s_last_khz: %s', self._manual_band, e)
                    self._manual_band = detected_band
                    self._band_var.set(detected_band)
                    try:
                        save_config_value(self._options.config, 'manual_band', detected_band)
                    except Exception as e:
                        logging.debug('failed to save manual_band: %s', e)
                self._manual_freq_khz = current_freq
                try:
                    save_config_value(self._options.config, 'manual_freq_khz', current_freq)
                except Exception as e:
                    logging.debug('failed to save manual_freq_khz: %s', e)
            self._manual = True
            self._auto_btn_var.set('Manual')
            self._mode_var.set(self._manual_mode)
        self._auto_btn.configure(style=('Amber.TButton' if self._manual else 'Green.TButton'))
        try:
            save_config_value(self._options.config, 'manual_active', self._manual)
        except Exception as e:
            logging.debug('failed to save manual_active: %s', e)
        self._set_manual_combo_states(self._manual)
        if self._manual:
            self._apply_manual_state()

    def _on_zoom_change(self, _event):
        label = self._zoom_var.get()
        span_khz = self._zoom_label_khz.get(label)
        if span_khz is None:
            return
        self._zoom_span_khz = span_khz
        try:
            save_config_value(self._options.config, 'zoom_span_khz', span_khz)
        except Exception as e:
            logging.debug('failed to save zoom_span_khz: %s', e)
        if self._wf_stream is not None:
            self._wf_stream.set_span(span_khz)

    def _on_band_change(self, _event):
        name = self._band_var.get()
        if name == self._manual_band:
            return   # re-selecting the already-active band -- nothing to do
        last_khz = self._band_last_freq_khz.get(name)
        if last_khz is not None and band_for_freq(last_khz) != name:
            # Self-heal a stale/corrupted "last" entry -- e.g. one saved
            # under the wrong band's key by the drag-out-of-range bug above,
            # before that was fixed -- rather than trusting it forever.
            logging.warning('band_%s_last_khz (%.3f kHz) does not actually belong to %s, ignoring it', name, last_khz, name)
            del self._band_last_freq_khz[name]
            last_khz = None
        freq_khz = last_khz if last_khz is not None else self._band_khz.get(name)
        if freq_khz is None:
            return
        if last_khz is None and freq_khz is not None:
            # Replace the corrected value in the file too (if we just healed
            # a bad entry above), so it doesn't keep reappearing every
            # restart -- band_<name>_last_khz always ends up either a real
            # remembered frequency or this band's own preset, never stale.
            try:
                save_config_value(self._options.config, 'band_%s_last_khz' % name, freq_khz)
            except Exception as e:
                logging.debug('failed to save band_%s_last_khz: %s', name, e)

        # Remember exactly where we're leaving this band, for a same-session
        # (and, since it's saved to config too, a later-session) return.
        self._band_last_freq_khz[self._manual_band] = self._manual_freq_khz
        try:
            save_config_value(self._options.config, 'band_%s_last_khz' % self._manual_band, self._manual_freq_khz)
        except Exception as e:
            logging.debug('failed to save band_%s_last_khz: %s', self._manual_band, e)

        self._manual_band = name
        try:
            save_config_value(self._options.config, 'manual_band', name)
        except Exception as e:
            logging.debug('failed to save manual_band: %s', e)

        # No sideband to update here any more -- Mode entries resolve
        # LSB/USB live from self._manual_band (just updated above), so
        # _apply_manual_passband() below already picks up the new band's
        # convention on its own.
        if self._manual:
            self._set_manual_freq(freq_khz)
            self._apply_manual_passband()
        else:
            self._manual_freq_khz = freq_khz
            try:
                save_config_value(self._options.config, 'manual_freq_khz', freq_khz)
            except Exception as e:
                logging.debug('failed to save manual_freq_khz: %s', e)

    def _on_mode_change(self, _event):
        # Updates whichever of auto_mode/manual_mode is currently active --
        # the other one is left untouched, so switching back later still
        # finds it exactly where it was (see _toggle_auto_manual).
        selected = self._mode_var.get()
        if self._manual:
            self._manual_mode = selected
            key = 'manual_mode'
        else:
            self._auto_mode = selected
            key = 'auto_mode'
        try:
            save_config_value(self._options.config, key, selected)
        except Exception as e:
            logging.debug('failed to save %s: %s', key, e)
        if self._manual:
            self._apply_manual_passband()
        # Auto mode picks this up on its own next rigctl poll tick
        # (_on_rigctl_mode, RigctlPoller's own 0.5s cadence), same as
        # _on_reverse_sideband_change below -- no explicit re-apply needed
        # here for that case.

    def _on_reverse_sideband_change(self):
        self._reverse_sideband = self._reverse_sideband_var.get()
        try:
            save_config_value(self._options.config, 'reverse_sideband', self._reverse_sideband)
        except Exception as e:
            logging.debug('failed to save reverse_sideband: %s', e)
        if self._manual:
            self._apply_manual_passband()
        # Auto mode picks this up on its own next rigctl poll tick
        # (_on_rigctl_mode, RigctlPoller's own 0.5s cadence) -- no explicit
        # re-apply needed here for that case.

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

    def _sdr_tune_freq(self, dial_freq_khz):
        """The single choke point where the tracked dial frequency (true rig
        frequency in Auto, or the user-set frequency in Manual) is converted
        to what's actually sent to the Kiwi -- everywhere else (readout, band
        detection, passband indicator) stays referenced to dial_freq_khz
        itself, so the trim only ever shifts where the SDR listens, not what
        kiwipanadapter believes it's tuned to."""
        return dial_freq_khz + self._sdr_freq_offset_hz / 1000.0

    def _nudge_sdr_offset(self, delta_hz):
        self._sdr_freq_offset_hz += delta_hz
        try:
            save_config_value(self._options.config, 'sdr_freq_offset_hz', self._sdr_freq_offset_hz)
        except Exception as e:
            logging.debug('failed to save sdr_freq_offset_hz: %s', e)
        with self._freq_lock:
            current_freq = self._current_freq_khz
        if current_freq is not None:
            if self._wf_stream is not None:
                self._wf_stream.retune(self._sdr_tune_freq(current_freq))
            if self._audio_stream is not None:
                self._audio_stream.retune(self._sdr_tune_freq(current_freq))

    def _on_rigctl_freq(self, freq_khz):
        if self._manual:
            return   # Manual owns the frequency -- ignore FreeDV/rigctl until switched back to Auto
        if not is_plausible_freq_khz(freq_khz):
            logging.warning('ignoring implausible rigctl frequency %.3f kHz', freq_khz)
            return
        self._last_rig_update_ts = time.time()
        with self._freq_lock:
            changed = self._current_freq_khz != freq_khz
            self._current_freq_khz = freq_khz
        if changed:
            if self._wf_stream is not None:
                self._wf_stream.retune(self._sdr_tune_freq(freq_khz))
            if self._audio_stream is not None:
                self._audio_stream.retune(self._sdr_tune_freq(freq_khz))

    def _on_rigctl_mode(self, mode, passband_hz):
        if self._manual:
            return   # Manual owns the mode/passband -- ignore FreeDV/rigctl until switched back to Auto
        if mode:
            # The passband shape comes from the Mode combo's Auto-side
            # selection (self._auto_mode -- tracked separately from Manual's
            # own self._manual_mode, see _on_mode_change) rather than
            # whatever rigctl reports as passband_hz: FreeDV's own modem
            # passband is a fixed shape regardless of which sideband the rig
            # happens to be set to for band convention (e.g. LSB below
            # 10MHz, USB above/on 60m), and different FreeDV modes need
            # different widths (e.g. FDV1 vs the narrower FDV2) that rigctl
            # has no way to report anyway. Mode's sideband (which of LSB/USB
            # to actually demodulate, for every non-AM-family entry) still
            # comes from hamlib as the source of truth here, same as always
            # -- only the passband shape is overridden.
            if self._options.auto_mode_by_band:
                # Some rigs (e.g. a plain Hamlib Dummy backend, never given
                # an explicit SET_MODE) just sit on one fixed mode regardless
                # of band -- that reads as "stuck on USB" once tuned below
                # 10MHz, where convention is LSB. Override with the band's
                # conventional sideband instead of trusting rigctl here.
                with self._freq_lock:
                    current_freq = self._current_freq_khz
                band = band_for_freq(current_freq) if current_freq is not None else None
                mode = BAND_DEFAULT_MODE.get(band, mode)
            if self._auto_mode in MODE_AM_NAMES:
                # An AM-family Mode selection overrides whatever sideband
                # rigctl/band convention gave, same as Manual's
                # _effective_demod -- AM has no sideband of its own.
                mode = 'am'
            elif self._reverse_sideband and mode.lower() in ('usb', 'lsb'):
                mode = 'lsb' if mode.lower() == 'usb' else 'usb'
            lowcut_hz, highcut_hz = self._compute_bw_passband(mode, self._auto_mode)
            self._pb_lowcut_hz = lowcut_hz
            self._pb_highcut_hz = highcut_hz
            if self._audio_stream is not None:
                self._audio_stream.set_manual_passband(mode, lowcut_hz, highcut_hz)

    def _set_manual_freq(self, freq_khz, save=True):
        """Apply a new Manual-mode frequency (from Band select or drag-release)
        via the same retune path _on_rigctl_freq uses for Auto -- live-applies
        only if a stream currently exists (no-op while stopped, matching
        _on_sdr_change's "just remember it" precedent)."""
        if not is_plausible_freq_khz(freq_khz):
            logging.warning('ignoring implausible manual frequency %.3f kHz', freq_khz)
            return
        self._manual_freq_khz = freq_khz
        if save:
            try:
                save_config_value(self._options.config, 'manual_freq_khz', freq_khz)
            except Exception as e:
                logging.debug('failed to save manual_freq_khz: %s', e)
        with self._freq_lock:
            self._current_freq_khz = freq_khz
        if self._wf_stream is not None:
            self._wf_stream.retune(self._sdr_tune_freq(freq_khz))
        if self._audio_stream is not None:
            self._audio_stream.retune(self._sdr_tune_freq(freq_khz))

    def _compute_bw_passband(self, mode, bw_name):
        """center/width (self._bw_hz, a positive offset+width from the dial
        frequency) -> a properly-signed (lowcut_hz, highcut_hz) pair for the
        given mode. Correct as-is for USB/CW, but the Kiwi expects a
        *negative* low_cut/high_cut range for LSB (its own default_passbands
        table uses e.g. usb=[300,2700] vs lsb=[-2700,-300], a mirror image --
        kiwi/client.py sends whatever sign it's given as a literal RF-offset
        filter, it doesn't infer/flip anything from mod itself), and AM ends
        up symmetric (matches LiveAudioStream's own passband negation for
        AM, done again here just for the indicator to track it too)."""
        center_hz, width_hz = self._bw_hz.get(bw_name, (0.0, 2400.0))
        lowcut_hz = center_hz - width_hz / 2.0
        highcut_hz = center_hz + width_hz / 2.0
        mod_key = (mode or '').lower()
        if mod_key == 'lsb':
            lowcut_hz, highcut_hz = -highcut_hz, -lowcut_hz
        elif mod_key == 'am':
            lowcut_hz = -highcut_hz
        return lowcut_hz, highcut_hz

    def _effective_demod(self, mode_name, band):
        """Mode combo entry -> actual Kiwi demod type ('usb'/'lsb'/'am').
        AM-family entries always demod as AM; every other entry resolves
        USB/LSB live from the given band's convention (BAND_DEFAULT_MODE),
        flipped by the reverse-sideband checkbox if set."""
        if mode_name in MODE_AM_NAMES:
            return 'am'
        demod = BAND_DEFAULT_MODE.get(band, 'usb')
        if self._reverse_sideband:
            demod = 'lsb' if demod == 'usb' else 'usb'
        return demod

    def _apply_manual_passband(self):
        """(Re-)send the current Mode combo selection to the audio stream --
        called whenever Mode/Band/the reverse-sideband checkbox changes, and
        when switching into Manual. No-op while stopped (no audio stream to
        send to)."""
        if self._audio_stream is None:
            return
        demod = self._effective_demod(self._manual_mode, self._manual_band)
        lowcut_hz, highcut_hz = self._compute_bw_passband(demod, self._manual_mode)
        self._pb_lowcut_hz = lowcut_hz
        self._pb_highcut_hz = highcut_hz
        self._audio_stream.set_manual_passband(demod, lowcut_hz, highcut_hz)

    def _apply_manual_state(self):
        """Re-apply the remembered Manual freq + Mode when switching Auto ->
        Manual, so Manual resumes exactly where it left off."""
        self._set_manual_freq(self._manual_freq_khz, save=False)
        self._apply_manual_passband()

    # -- GUI update loop --------------------------------------------------------------

    def _poll_queue(self):
        latest = None
        try:
            while True:
                latest = self._row_queue.get_nowait()
        except queue.Empty:
            pass

        if latest is not None:
            self._set_status('Connected')
            self._freq_var.set('%.3f kHz' % latest['center'])
            self._ingest_row(latest)
            self._redraw()

        # The Kiwi keeps streaming perfectly normal-looking waterfall rows
        # regardless of whether rigctl is actually reachable -- the numeric
        # readout above would otherwise just look confidently correct while
        # secretly still parked on default_freq. Overridden every tick
        # (rather than only when latest is set) since rows keep arriving
        # even while the rig link is dead.
        if (not self._manual) and (not self._stopped) and (
                self._last_rig_update_ts is None
                or time.time() - self._last_rig_update_ts > RIG_STALE_TIMEOUT_SEC):
            self._freq_var.set('No rig data')

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

    def _on_root_configure(self, _event):
        if self._options.snap_below_title:
            return   # position is fully derived/automatic -- nothing user-set to persist
        if self._geometry_save_after_id is not None:
            self._root.after_cancel(self._geometry_save_after_id)
        self._geometry_save_after_id = self._root.after(800, self._save_window_geometry)

    def _save_window_geometry(self):
        self._geometry_save_after_id = None
        try:
            save_config_value(self._options.config, 'window_height', self._root.winfo_height())
            save_config_value(self._options.config, 'window_x', self._root.winfo_x())
            save_config_value(self._options.config, 'window_y', self._root.winfo_y())
        except Exception as e:
            logging.debug('failed to save window geometry: %s', e)

    def _poll_snap_target(self):
        """snap_below_title: keep this window glued directly below the
        first window whose title contains the configured substring (e.g.
        FreeDV's own Reporter dialog), spanning full screen width and
        filling down to the screen bottom -- so as that window grows
        (more stations reported) or shrinks, this one gives up/reclaims
        exactly the space it needs. Deliberately low-rate (SNAP_POLL_MS)
        and only re-applies geometry when it's actually changed, both to
        stay cheap and to avoid fighting a live drag/resize of *this*
        window if hide_titlebar somehow isn't in effect."""
        if self._snap_target_id is None:
            self._snap_target_id = _find_window_id(self._options.snap_below_title)
            if self._snap_target_id is None:
                logging.debug('snap_below_title %r: no matching window found (yet)',
                              self._options.snap_below_title)
        if self._snap_target_id is not None:
            geom = _get_window_geometry(self._snap_target_id)
            if geom is None:
                # Gone (closed, or was never real) -- drop it and re-search
                # next tick rather than sitting on a dead id forever.
                self._snap_target_id = None
            else:
                # x/width intentionally ignored -- this window always spans
                # full screen width regardless of the target's own, matching
                # its own existing always-full-width design (see _build_ui).
                _target_x, target_y, _target_w, target_h = geom
                screen_w = self._root.winfo_screenwidth()
                screen_h = self._root.winfo_screenheight()
                new_y = target_y + target_h - self._options.snap_top_overlap_px
                # Leave a small strip of the true screen edge uncovered --
                # otherwise this window sits exactly on top of the one
                # pixel row an auto-hide taskbar needs the mouse to reach
                # to trigger its own reveal, making it unreachable while
                # this window is up.
                new_h = max(60, screen_h - new_y - self._options.snap_bottom_margin_px)
                new_geom = (screen_w, new_h, new_y)
                if new_geom != self._snap_last_geom:
                    self._snap_last_geom = new_geom
                    self._root.geometry('%dx%d+0+%d' % new_geom)
        self._root.after(SNAP_POLL_MS, self._poll_snap_target)

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
            if self._drag_freq_khz is not None:
                self._redraw_freq_axis_only()
            else:
                self._draw_freq_axis(self._last_start, self._last_stop)

    def _redraw_freq_axis_only(self):
        """Cheap freq-axis-strip-only redraw used while drag-panning -- the
        waterfall image itself is already panned in place via canvas.coords,
        no need to rebuild it here."""
        if self._drag_freq_khz is None or self._last_start is None:
            return
        span = self._last_stop - self._last_start
        self._draw_freq_axis(self._drag_freq_khz - span / 2, self._drag_freq_khz + span / 2,
                              marker_freq=self._drag_freq_khz, marker_color='red')

    def _draw_freq_axis(self, start_khz, stop_khz, marker_freq=None, marker_color='#ff00ff'):
        # Axis sits above the waterfall, so ticks point down toward it (at
        # the strip's bottom edge) with labels above them.
        c = self._freqaxis_canvas
        c.delete('all')
        # Deliberately self._canvas's width, not c's own -- the waterfall
        # image (and all the drag-pan pixel math in _on_wf_drag/_on_wf_release/
        # _shift_img_buf) is authoritatively sized off self._canvas.winfo_width().
        # Both canvases are laid out to always be the same width, but tick/
        # marker math drifting out of step with the image if that ever isn't
        # exactly true (even by a pixel) is exactly the kind of small,
        # drag-distance-proportional misalignment reported against a real
        # carrier -- querying the same canvas everywhere removes that
        # possibility outright rather than relying on two widgets staying in
        # sync.
        w = max(1, self._canvas.winfo_width())
        h = max(1, c.winfo_height())
        span = stop_khz - start_khz
        if span <= 0:
            return

        minor_khz, major_khz = nice_tick_step(span)

        for f in tick_positions(start_khz, stop_khz, minor_khz):
            x = int((f - start_khz) / span * w)
            c.create_line(x, h, x, h - 6, fill='#a0a0a0', width=2)

        label_fmt = '%.3f' if major_khz < 1 else '%.0f'
        for f in tick_positions(start_khz, stop_khz, major_khz):
            x = int((f - start_khz) / span * w)
            c.create_line(x, h, x, h - 6, fill='#a0a0a0', width=2)
            c.create_text(x, h - 7, text=label_fmt % f, fill='white', anchor='s', font=('TkFixedFont', 7))

        if marker_freq is None:
            with self._freq_lock:
                marker_freq = self._current_freq_khz
        if marker_freq is not None and start_khz <= marker_freq <= stop_khz:
            x = int((marker_freq - start_khz) / span * w)
            c.create_line(x, 0, x, h, fill=marker_color, width=2)

        # Passband indicator: a thin yellow line just above the waterfall's
        # top edge (this strip's bottom row), spanning the active demod
        # filter's lowcut..highcut, positioned relative to the dial/marker
        # frequency -- its length is the bandwidth, its position is where
        # that passband actually sits in absolute frequency.
        if marker_freq is not None and self._pb_lowcut_hz is not None and self._pb_highcut_hz is not None:
            lo_khz = marker_freq + self._pb_lowcut_hz / 1000.0
            hi_khz = marker_freq + self._pb_highcut_hz / 1000.0
            x0 = int((lo_khz - start_khz) / span * w)
            x1 = int((hi_khz - start_khz) / span * w)
            if x1 != x0:
                c.create_line(x0, h - 1, x1, h - 1, fill='yellow', width=3)

    # -- drag-to-tune: grab-and-pan the waterfall under a fixed center marker -------

    def _shift_img_buf(self, canvas_dx):
        """Bake a drag's visual pan (canvas.coords, purely cosmetic and reset
        on release) permanently into self._img_buf's actual pixel columns,
        so already-buffered history rows line up with the new tuned center
        instead of reverting to their old (pre-drag) alignment the instant
        the live preview's coords offset is reset. canvas_dx is in on-screen
        canvas pixels; self._img_buf is at the smaller native WF_NATIVE_BINS
        resolution, so it's converted first."""
        if not canvas_dx:
            return
        canvas_w = max(1, self._canvas.winfo_width())
        native_w = self._img_buf.shape[1]
        native_dx = int(round(canvas_dx * native_w / canvas_w))
        if native_dx == 0:
            return
        if abs(native_dx) >= native_w:
            self._img_buf[:] = 0
            return
        self._img_buf[:] = np.roll(self._img_buf, native_dx, axis=1)
        if native_dx > 0:
            self._img_buf[:, :native_dx] = 0
        else:
            self._img_buf[:, native_dx:] = 0

    def _on_wf_press(self, event):
        if not self._manual:
            return
        self._drag_start_x = event.x
        self._drag_last_dx = 0
        with self._freq_lock:
            self._drag_start_freq_khz = self._current_freq_khz

    def _on_wf_drag(self, event):
        if not self._manual or self._drag_start_x is None or self._drag_start_freq_khz is None:
            return
        canvas_w = max(1, self._canvas.winfo_width())
        span_khz = (self._last_stop - self._last_start) if self._last_start is not None else self._zoom_span_khz
        dx = event.x - self._drag_start_x
        self._drag_last_dx = dx
        self._drag_freq_khz = self._drag_start_freq_khz - (dx / canvas_w) * span_khz
        self._canvas.coords(self._image_id, dx, 0)
        self._redraw_freq_axis_only()

    def _on_wf_release(self, event):
        if not self._manual or self._drag_start_x is None:
            return
        final_freq = self._drag_freq_khz
        dx = self._drag_last_dx
        self._drag_start_x = None
        self._drag_start_freq_khz = None
        self._drag_freq_khz = None
        self._drag_last_dx = 0
        if final_freq is not None:
            self._shift_img_buf(dx)
            if self._last_start is not None:
                span = self._last_stop - self._last_start
                # Optimistic re-centering so the very next redraw (before the
                # first real post-retune row arrives) is already self-
                # consistent -- overwritten for real a moment later once
                # LiveWFStream's own _process_waterfall_samples reports the
                # genuine new start/stop.
                self._last_start = final_freq - span / 2
                self._last_stop = final_freq + span / 2
            # Dragging can easily land well outside self._manual_band's own
            # range (e.g. at a wide Span) -- keep Band in sync with reality
            # rather than letting it silently drift stale, which would then
            # get persisted as if the new frequency belonged to the old band
            # (hit live 2026-08-09: a drag on 40m at 250kHz span landed in
            # 20m territory, got saved as band_40m_last_khz, and the next
            # startup showed Band=40m while actually tuned to a 20m frequency).
            detected_band = band_for_freq(final_freq)
            if detected_band is not None and detected_band != self._manual_band:
                self._manual_band = detected_band
                self._band_var.set(detected_band)
                try:
                    save_config_value(self._options.config, 'manual_band', detected_band)
                except Exception as e:
                    logging.debug('failed to save manual_band: %s', e)
            self._set_manual_freq(final_freq)
        self._canvas.coords(self._image_id, 0, 0)
        self._redraw()

    def _draw_smeter(self, dbm, peak_dbm=None):
        c = self._smeter_canvas
        c.delete('all')
        w_total = max(1, c.winfo_width())
        h_total = max(1, c.winfo_height())
        bar_h = 4
        bar_top = h_total - bar_h

        def frac_of(val):
            return max(0.0, min(1.0, (val - self._smeter_mindb) / (self._smeter_maxdb - self._smeter_mindb)))

        # Peak-hold bar, drawn first/underneath in solid red so it reads as a
        # distinct layer -- only the portion beyond the current-level bar
        # (drawn on top, below) stays visible, as a long-hang "tail".
        if peak_dbm is not None:
            peak_w = int(frac_of(peak_dbm) * w_total)
            c.create_rectangle(0, bar_top, peak_w, h_total, fill='#ff3030', width=0)

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
        if self._geometry_save_after_id is not None:
            self._root.after_cancel(self._geometry_save_after_id)
            self._geometry_save_after_id = None
        self._save_window_geometry()
        if self._manual_band:
            # Capture wherever we're sitting on the current band too, not
            # just bands already left mid-session (see _on_band_change).
            try:
                save_config_value(self._options.config, 'band_%s_last_khz' % self._manual_band, self._manual_freq_khz)
            except Exception as e:
                logging.debug('failed to save band_%s_last_khz: %s', self._manual_band, e)
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
    p.add_argument('--auto-mode-by-band', dest='auto_mode_by_band', action='store_true',
                    default=cfg.get('auto_mode_by_band', False),
                    help='in Auto mode, derive LSB/USB from the tuned band convention instead of '
                         'trusting rigctl\'s reported mode -- works around rigs/Dummy backends that '
                         'never set LSB below 10MHz (config: auto_mode_by_band, default false)')
    p.add_argument('--reverse-sideband', dest='reverse_sideband', action='store_true',
                    default=cfg.get('reverse_sideband', False),
                    help='flip the band-convention LSB/USB choice used by every SSB-family Mode '
                         'entry, in both Auto and Manual -- an escape hatch for the rare case the '
                         'conventional sideband isn\'t what\'s wanted (config: reverse_sideband, default false)')
    p.add_argument('--hide-titlebar', dest='hide_titlebar', action='store_true',
                    default=cfg.get('hide_titlebar', False),
                    help='remove this window\'s titlebar/border (via _MOTIF_WM_HINTS, needs '
                         'python-xlib) to save vertical space -- stays fully window-manager-'
                         'managed (taskbar/Alt+Tab, stacking all unaffected), it just has no '
                         'titlebar left to drag by, so there\'s no way to reposition it except '
                         'editing window_x/window_y directly, or via --snap-below-title '
                         '(config: hide_titlebar, default false)')
    p.add_argument('--snap-below-title', dest='snap_below_title', default=cfg.get('snap_below_title', ''),
                    help='continuously reposition this window directly below the first window whose '
                         'title contains this substring (e.g. "FreeDV Reporter"), spanning full '
                         'screen width and filling down to the screen bottom -- re-checked every '
                         '%dms (not fast; the use case is another app\'s window growing/shrinking as '
                         'content is added, not live dragging). Implies --hide-titlebar (there\'d be '
                         'no way to tell the two apart otherwise -- the whole point is this window\'s '
                         'position is fully automatic). Empty (default) disables it (config: '
                         'snap_below_title)' % SNAP_POLL_MS)
    p.add_argument('--snap-bottom-margin', dest='snap_bottom_margin_px', type=int,
                    default=cfg.get('snap_bottom_margin_px', 4),
                    help='pixels of screen bottom left uncovered by --snap-below-title, so an '
                         'auto-hide taskbar\'s edge-hover trigger stays reachable -- this window '
                         'would otherwise cover the exact bottom pixel row the taskbar needs the '
                         'mouse to reach (config: snap_bottom_margin_px, default 4)')
    p.add_argument('--snap-top-overlap', dest='snap_top_overlap_px', type=int,
                    default=cfg.get('snap_top_overlap_px', SNAP_TOP_OVERLAP_PX_DEFAULT),
                    help='pixels this window tucks up under --snap-below-title\'s target\'s reported '
                         'bottom edge -- the WM-reported edge and the true visible edge of another '
                         'app\'s window don\'t always agree exactly, so this is machine/theme/scaling '
                         'dependent: too small (or negative) leaves a visible gap, too large lets the '
                         'target\'s own titlebar/border overlap down onto this window\'s controls -- '
                         'negative values are valid and just widen the gap further, useful if the '
                         'default already overlaps badly on a given machine (config: '
                         'snap_top_overlap_px, default %d)' % SNAP_TOP_OVERLAP_PX_DEFAULT)
    p.add_argument('--sdr-freq-offset', dest='sdr_freq_offset_hz', type=float,
                    default=cfg.get('sdr_freq_offset_hz', 0.0),
                    help='calibration trim in Hz added to the SDR\'s actual tuned frequency only '
                         '(corrects a fixed audio-tone offset FreeDV hears, e.g. Kiwi clock error) -- '
                         'live-adjustable via the </> buttons either side of the freq readout '
                         '(config: sdr_freq_offset_hz, default 0)')
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
    p.add_argument('--radio-capture-device', dest='radio_capture_device',
                    default=cfg.get('radio_capture_device', ''),
                    help='PipeWire capture node name for a real rig\'s RX audio, used by the RX/SDR toggle '
                         '-- empty means no radio configured (config: radio_capture_device)')
    p.add_argument('--rx-source-mode', dest='rx_source_mode', choices=['RX', 'SDR'],
                    default=cfg.get('rx_source_mode', 'RX'),
                    help='initial FreeDV RX audio source -- RX (real radio) or SDR (this panadapter) '
                         '(config: rx_source_mode, default RX)')
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
    p.add_argument('--manual-active', dest='manual_active', action='store_true',
                    default=cfg.get('manual_active', False),
                    help='start in Manual tuning mode instead of Auto (following rigctl) '
                         '(config: manual_active, default false)')
    p.add_argument('--manual-freq', dest='manual_freq_khz', type=float,
                    default=cfg.get('manual_freq_khz', BAND_DEFAULT_KHZ['40m']),
                    help='last/initial Manual-mode frequency in kHz (config: manual_freq_khz)')
    p.add_argument('--manual-band', dest='manual_band', default=cfg.get('manual_band', '40m'),
                    choices=BAND_NAMES, help='last/initial Band combo selection (config: manual_band)')
    p.add_argument('--manual-mode', dest='manual_mode', default=cfg.get('manual_mode', 'SSB'),
                    help='last/initial Mode combo selection while in Manual -- one of %s '
                         '(config: manual_mode)' % ','.join(MODE_NAMES))
    p.add_argument('--auto-mode', dest='auto_mode', default=cfg.get('auto_mode', 'FDV1'),
                    help='last/initial Mode combo selection while in Auto -- tracked separately '
                         'from --manual-mode so switching between Auto/Manual never loses either '
                         "one's own last selection (config: auto_mode)")
    p.add_argument('--zoom-span', dest='zoom_span_khz', type=float,
                    default=cfg.get('zoom_span_khz', cfg.get('span_khz', 50.0)),
                    help='last/initial Zoom combo span in kHz, used in both Auto and Manual '
                         '(config: zoom_span_khz)')
    p.add_argument('--zoom-steps', dest='zoom_steps_khz', type=parse_float_list,
                    default=cfg.get('zoom_steps_khz', DEFAULT_ZOOM_STEPS_KHZ),
                    help='comma list of Zoom combo span steps in kHz (config: zoom_steps_khz, '
                         'default %s)' % ','.join(str(int(s)) for s in DEFAULT_ZOOM_STEPS_KHZ))
    for _name in BAND_NAMES:
        _key = 'band_%s_khz' % _name
        p.add_argument('--%s' % _key.replace('_', '-'), dest=_key, type=float,
                        default=cfg.get(_key, BAND_DEFAULT_KHZ[_name]),
                        help='Band combo center frequency for %s, in kHz (config: %s)' % (_name, _key))
        _last_key = 'band_%s_last_khz' % _name
        p.add_argument('--%s' % _last_key.replace('_', '-'), dest=_last_key, type=float,
                        default=cfg.get(_last_key, None),
                        help='remembered last-used frequency for %s in kHz, used instead of the '
                             'preset above once this band has been visited (config: %s)' % (_name, _last_key))
    for _name in MODE_NAMES:
        _key = _name.lower()
        _default_center, _default_width = BW_DEFAULT_HZ[_name]
        p.add_argument('--bw-%s-center' % _key, dest='bw_%s_center_hz' % _key, type=float,
                        default=cfg.get('bw_%s_center_hz' % _key, _default_center),
                        help='Mode combo "%s" passband center offset from dial frequency, in Hz '
                             '(config: bw_%s_center_hz)' % (_name, _key))
        p.add_argument('--bw-%s-width' % _key, dest='bw_%s_width_hz' % _key, type=float,
                        default=cfg.get('bw_%s_width_hz' % _key, _default_width),
                        help='Mode combo "%s" passband width, in Hz (config: bw_%s_width_hz)' % (_name, _key))
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
    app = PanadapterApp(root, options)

    def _handle_shutdown_signal(signum, _frame):
        # Launchers (freedv-start/freedv-start-leno) tear this process down
        # with a plain 'kill -s QUIT' once FreeDV exits, rather than closing
        # the window -- that bypasses WM_DELETE_WINDOW entirely, and
        # SIGTERM/SIGQUIT's default disposition is immediate termination
        # with no Python-level cleanup, silently skipping _on_close()'s save
        # of window position/height and the current band's last frequency
        # every single time. Handle both explicitly and run the exact same
        # shutdown path instead. Safe to call mid-mainloop: Tkinter's own
        # after() timers (150ms-5s) already return control to Python often
        # enough for the interpreter to notice and run this promptly.
        logging.info('received signal %d, shutting down', signum)
        app._on_close()

    signal.signal(signal.SIGTERM, _handle_shutdown_signal)
    signal.signal(signal.SIGQUIT, _handle_shutdown_signal)
    root.mainloop()


if __name__ == '__main__':
    main()
