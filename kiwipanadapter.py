#!/usr/bin/env python3
## -*- python -*-
#
# Lightweight local panadapter: a live waterfall + S-meter for the band
# around whatever frequency FreeDV (via kiwiclientd's rigctl emulation)
# is currently tuned to. Deliberately avoids a browser and heavy GUI
# toolkits/plotting libraries to keep CPU/GPU load down; uses stock
# Tkinter only.
#
# The frequency is learned by polling kiwiclientd's rigctld TCP port
# (the same interface FreeDV itself talks to) -- this script never
# touches kiwiclientd directly, it's just another rigctl client.

import argparse
import logging
import math
import os
import queue
import shlex
import socket
import subprocess
import sys
import threading
import time
from types import SimpleNamespace

import numpy as np
import tkinter as tk
from tkinter import ttk

from kiwi.client import KiwiSDRStream
from kiwi.worker import KiwiWorker

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SDR_LIST = os.path.join(SCRIPT_DIR, 'sdr_list.txt')
DEFAULT_CONFIG = os.path.join(SCRIPT_DIR, 'panadapter.conf')
WF_NATIVE_BINS = 1024   # matches Kiwi's fixed waterfall bin count -- native buffer width
MAX_FREQ_KHZ = 30000.0  # Kiwi's full tunable range; zoom 0 spans this whole width
MAX_HISTORY_ROWS = 600  # native buffer height (scrollback); displayed height can be less or more
DEFAULT_WINDOW_HEIGHT = 300
WF_CAL = -13           # typical Kiwi waterfall calibration offset, dB

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
    'freq_major_khz': float,
    'freq_minor_khz': float,
    'window_height': int,
    'window_x': int,
    'window_y': int,
    'kiwiclientd_path': str,
    'kiwiclientd_args': str,
    'no_kiwiclientd': parse_bool,
    'kiwiclientd_rigctl_port': int,
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


def make_stream_options(host, port, user):
    """Minimal attribute set KiwiSDRStream/KiwiWorker need for a plain W/F connection."""
    return SimpleNamespace(
        server_host=host,
        server_port=port,
        password='',
        admin=False,
        tlimit_password='',
        user=user,
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
        modulation='am',
        lp_cut=None,
        hp_cut=None,
        wideband=False,
        ws_timestamp=int(time.time() + os.getpid()) & 0xffffffff,
        bad_cmd=False,
        sound=False,
        resample=0,
        nb=False,
        nb_test=False,
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
            f.write("freq_major_khz  5\n")
            f.write("freq_minor_khz  1\n")
            f.write("window_height   %d\n" % DEFAULT_WINDOW_HEIGHT)
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


def load_sdr_list(path):
    """Flat text file: 'name host port' per line, '#' comments, blank lines ignored."""
    if not os.path.exists(path):
        with open(path, 'w') as f:
            f.write("# name              host                     port\n")
            f.write("example             kiwisdr.example.com      8073\n")
    sdrs = []
    with open(path) as f:
        for line in f:
            line = line.split('#', 1)[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            host = parts[-2]
            port = int(parts[-1])
            name = ' '.join(parts[:-2]) if len(parts) > 2 else host
            sdrs.append({'name': name, 'host': host, 'port': port})
    return sdrs


def save_sdr_list(path, sdrs):
    """Rewrite the flat 'name host port' file from an in-memory list."""
    name_w = max((len(s['name']) for s in sdrs), default=4) + 2
    host_w = max((len(s['host']) for s in sdrs), default=4) + 2
    with open(path, 'w') as f:
        f.write("# name              host                     port\n")
        for s in sdrs:
            f.write("%-*s %-*s %s\n" % (name_w, s['name'], host_w, s['host'], s['port']))


class RigctlPoller(threading.Thread):
    """Polls a rigctld TCP port (a real hamlib rigctld talking to an actual radio,
    or kiwiclientd's own emulation) for the current frequency, same as FreeDV does.

    If mirror_target is given (host, port) of a second rigctld -- the locally
    managed kiwiclientd's own rigctld -- also polls mode and relays both
    frequency and mode there as SET commands on every tick. This is how
    kiwiclientd's SDR audio channel stays tuned to match a real radio that's
    the actual source of truth, since kiwiclientd has no way to follow an
    external rigctld on its own -- its only tuning input is its own local
    rigctld port.
    """

    def __init__(self, host, port, on_freq_khz, poll_interval=0.5, mirror_target=None):
        super().__init__(daemon=True)
        self._host = host
        self._port = port
        self._on_freq_khz = on_freq_khz
        self._poll_interval = poll_interval
        self._mirror_target = mirror_target
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

    def _push_to_mirror(self, freq_hz, mode, passband_hz):
        try:
            with socket.create_connection(self._mirror_target, timeout=2) as s:
                s.sendall(('F %d\n' % freq_hz).encode('ascii'))
                if mode:
                    cmd = ('M %s %d\n' % (mode, passband_hz)) if passband_hz else ('M %s\n' % mode)
                    s.sendall(cmd.encode('ascii'))
        except Exception as e:
            logging.debug('rigctl mirror push failed: %s', e)

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

                if self._mirror_target is not None:
                    sock.sendall(b'm\n')
                    mode = self._read_line(sock)
                    try:
                        passband_hz = int(self._read_line(sock))
                    except Exception:
                        passband_hz = None
                    self._push_to_mirror(freq_hz, mode, passband_hz)
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
    """A single waterfall-only Kiwi connection that can be recentered on the fly."""

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

        form = ttk.Frame(self)
        form.pack(padx=8, pady=8)
        fields = [('Name:', self._name_var), ('Host:', self._host_var), ('Port:', self._port_var)]
        for row, (label, var) in enumerate(fields):
            ttk.Label(form, text=label).grid(row=row, column=0, sticky='e', pady=2)
            ttk.Entry(form, textvariable=var, width=28).grid(row=row, column=1, pady=2)

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
        if not name or not host:
            return
        self.result = {'name': name, 'host': host, 'port': port}
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
            self._listbox.insert('end', '%s  (%s:%s)' % (s['name'], s['host'], s['port']))

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

        self._mindb = options.mindb
        self._maxdb = options.maxdb
        self._smeter_decay = options.smeter_decay
        self._smeter_cal_db = options.smeter_cal_db
        self._smeter_peak_hold_sec = options.smeter_peak_hold_sec
        self._smeter_peak_decay = options.smeter_peak_decay_db_sec
        self._smeter_passband_center_hz = options.smeter_passband_center_hz
        self._smeter_passband_bw_hz = options.smeter_passband_bw_hz
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
        self._last_signal_dbm = None
        self._smeter_dbm = None
        self._smeter_last_ts = None
        self._smeter_peak_dbm = None
        self._smeter_peak_set_ts = None
        self._smeter_peak_last_ts = None
        self._last_start = None
        self._last_stop = None
        self._kiwiclientd_proc = None
        self._active_sdr = None

        root.title('Kiwi Panadapter')
        self._build_ui()
        root.update_idletasks()   # so winfo_width/height are accurate before the first row arrives

        if not self._options.no_kiwiclientd:
            self._start_kiwiclientd(self._sdr_list[0])

        mirror_target = None
        if not self._options.no_kiwiclientd:
            kiwiclientd_target = ('127.0.0.1', self._options.kiwiclientd_rigctl_port)
            if (options.rigctl_host, options.rigctl_port) != kiwiclientd_target:
                mirror_target = kiwiclientd_target
        self._rigctl_poller = RigctlPoller(options.rigctl_host, options.rigctl_port, self._on_rigctl_freq,
                                            mirror_target=mirror_target)
        self._rigctl_poller.start()

        self._start_stream(self._sdr_list[0])
        self._active_sdr = self._sdr_list[0]
        root.protocol('WM_DELETE_WINDOW', self._on_close)
        self._poll_queue()

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
        self._sdr_var = tk.StringVar(value=self._sdr_list[0]['name'])
        combo_width = max((len(s['name']) for s in self._sdr_list), default=10) + 2
        self._sdr_combo = ttk.Combobox(top, textvariable=self._sdr_var, state='readonly',
                                        width=combo_width,
                                        values=[s['name'] for s in self._sdr_list])
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
        ttk.Label(meter, textvariable=self._dbm_var).pack(side='right', padx=8)
        self._smeter_canvas = tk.Canvas(meter, height=28, highlightthickness=0, bg='black')
        self._smeter_canvas.pack(side='left', fill='x', expand=True, padx=4)

        self._freqaxis_canvas = tk.Canvas(self._root, height=20, highlightthickness=0, bg='black')
        self._freqaxis_canvas.pack(side='top', fill='x')

        self._canvas = tk.Canvas(self._root, highlightthickness=0, bg='black')
        self._canvas.pack(side='top', fill='both', expand=True)
        self._image_id = self._canvas.create_image(0, 0, anchor='nw')
        self._canvas.bind('<Configure>', self._on_resize)
        self._sensitivity_var = tk.StringVar(value='Normal')
        self._canvas.bind('<Button-3>', self._show_sensitivity_menu)

    # -- SDR connection management -------------------------------------------------

    def _start_stream(self, sdr_entry):
        opt = make_stream_options(sdr_entry['host'], sdr_entry['port'], self._options.user)
        with self._freq_lock:
            freq = self._current_freq_khz if self._current_freq_khz is not None else self._options.default_freq
        self._wf_stream = LiveWFStream(opt, freq, self._options.span, self._row_queue)
        self._run_event = threading.Event()
        self._run_event.set()
        camp_wait_event = threading.Event()
        camp_wait_event.set()
        self._worker = KiwiWorker(args=(self._wf_stream, opt, True, False, self._run_event, camp_wait_event))
        self._worker.start()
        self._status_var.set('connecting to %s...' % sdr_entry['name'])

    def _stop_stream(self):
        if self._worker is None:
            return
        self._run_event.clear()
        try:
            self._wf_stream.close()
        except Exception:
            pass
        self._worker.join(timeout=2)
        self._worker = None
        self._wf_stream = None

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
        if not self._options.no_kiwiclientd:
            self._start_kiwiclientd(entry)
        self._start_stream(entry)
        self._active_sdr = entry

    def _open_sdr_manager(self):
        SdrListDialog(self._root, self._sdr_list, self._options.sdr_list, self._on_sdr_list_changed)

    def _on_sdr_list_changed(self):
        names = [s['name'] for s in self._sdr_list]
        self._sdr_combo['values'] = names
        self._sdr_combo.config(width=max((len(n) for n in names), default=10) + 2)
        current_name = self._sdr_var.get()
        entry = next((s for s in self._sdr_list if s['name'] == current_name), None)
        if entry is None and self._sdr_list:
            entry = self._sdr_list[0]
            self._sdr_var.set(entry['name'])
        if entry is not None and entry != self._active_sdr:
            self._on_sdr_change(None)

    # -- kiwiclientd lifecycle --------------------------------------------------------

    def _start_kiwiclientd(self, sdr_entry):
        self._stop_kiwiclientd()
        # Always bound to a local port dedicated to the managed kiwiclientd, distinct
        # from rigctl_host/rigctl_port (which may point at a real rigctld elsewhere,
        # e.g. talking to an actual radio) -- kiwipanadapter itself is the only
        # client of this port, relaying the true frequency/mode into it so
        # kiwiclientd's SDR audio channel stays tuned to match (see RigctlPoller's
        # mirror_target).
        argv = [sys.executable, self._options.kiwiclientd_path,
                '-s', sdr_entry['host'], '-p', str(sdr_entry['port']),
                '--rigctl-addr', '127.0.0.1',
                '--rigctl-port', str(self._options.kiwiclientd_rigctl_port),
                '--enable-rigctl']
        if self._options.kiwiclientd_args:
            argv += shlex.split(self._options.kiwiclientd_args)
        logging.info('starting kiwiclientd: %s', ' '.join(argv))
        try:
            self._kiwiclientd_proc = subprocess.Popen(argv, cwd=SCRIPT_DIR)
        except Exception as e:
            logging.error('failed to start kiwiclientd: %s', e)
            self._kiwiclientd_proc = None

    def _stop_kiwiclientd(self):
        if self._kiwiclientd_proc is None:
            return
        proc = self._kiwiclientd_proc
        self._kiwiclientd_proc = None
        proc.terminate()
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=2)

    # -- frequency tracking ---------------------------------------------------------

    def _on_rigctl_freq(self, freq_khz):
        with self._freq_lock:
            changed = self._current_freq_khz != freq_khz
            self._current_freq_khz = freq_khz
        if changed and self._wf_stream is not None:
            self._wf_stream.retune(freq_khz)

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
        dbm = np.clip(row['dbm'] + WF_CAL, self._mindb, self._maxdb)
        idx = ((dbm - self._mindb) / (self._maxdb - self._mindb) * 255).astype(np.uint8)
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
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _set_sensitivity(self, mindb, maxdb):
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
            c.create_line(x, h, x, h - 3, fill='#606060')

        label_fmt = '%.3f' if self._freq_major_khz < 1 else '%.0f'
        for f in tick_positions(start_khz, stop_khz, self._freq_major_khz):
            x = int((f - start_khz) / span * w)
            c.create_line(x, h, x, h - 6, fill='#a0a0a0')
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
            return max(0.0, min(1.0, (val - self._mindb) / (self._maxdb - self._mindb)))

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
            x = int(max(0.0, min(1.0, (ref_dbm - self._mindb) / (self._maxdb - self._mindb))) * w_total)
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
        self._stop_kiwiclientd()
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
                    help='kiwiclientd rigctld host (config: rigctl_host, default 127.0.0.1)')
    p.add_argument('--rigctl-port', type=int, default=cfg.get('rigctl_port', 6400),
                    help='kiwiclientd rigctld port (config: rigctl_port, default 6400)')
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
    p.add_argument('--user', default='kiwipanadapter', help='client name reported to the Kiwi')
    p.add_argument('--default-freq', dest='default_freq', type=float, default=cfg.get('default_freq', 14200.0),
                    help='initial center frequency (kHz) used until the first rigctl poll arrives (config: default_freq)')
    p.add_argument('--kiwiclientd-path', dest='kiwiclientd_path',
                    default=cfg.get('kiwiclientd_path', os.path.join(SCRIPT_DIR, 'kiwiclientd.py')),
                    help='path to kiwiclientd.py, started/restarted automatically for the selected SDR (config: kiwiclientd_path)')
    p.add_argument('--kiwiclientd-args', dest='kiwiclientd_args', default=cfg.get('kiwiclientd_args', ''),
                    help='extra arguments appended to the managed kiwiclientd invocation, e.g. "--snddev kiwisnd0" (config: kiwiclientd_args)')
    p.add_argument('--kiwiclientd-rigctl-port', dest='kiwiclientd_rigctl_port', type=int,
                    default=cfg.get('kiwiclientd_rigctl_port', 6400),
                    help='local port the managed kiwiclientd binds its own rigctld emulation to (always '
                         '127.0.0.1) -- kept separate from rigctl_host/rigctl_port so that can point at a '
                         'real rigctld elsewhere; kiwipanadapter relays the true frequency/mode into this '
                         'port so kiwiclientd\'s SDR audio channel stays tuned to match (config: kiwiclientd_rigctl_port)')
    p.add_argument('--no-kiwiclientd', dest='no_kiwiclientd', action='store_true',
                    default=cfg.get('no_kiwiclientd', False),
                    help="don't start/manage kiwiclientd at all -- use this only if you don't want an "
                         "SDR audio node available (config: no_kiwiclientd)")
    p.add_argument('--log-level', default='warn', choices=['debug', 'info', 'warn', 'error'])
    return p.parse_args()


def main():
    options = parse_args()
    logging.basicConfig(level=logging.getLevelName(options.log_level.upper()),
                         format='%(asctime)-15s %(message)s')
    root = tk.Tk()
    PanadapterApp(root, options)
    root.mainloop()


if __name__ == '__main__':
    main()
