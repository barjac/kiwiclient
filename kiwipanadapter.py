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
    'freq_major_khz': float,
    'freq_minor_khz': float,
    'window_height': int,
    'kiwiclientd_path': str,
    'kiwiclientd_args': str,
    'no_kiwiclientd': parse_bool,
}


def zoom_for_span(span_khz, max_freq_khz=30000.0, max_zoom=14):
    """Largest (most zoomed-in) Kiwi zoom level whose span still covers span_khz."""
    for z in range(max_zoom, -1, -1):
        if max_freq_khz / (2 ** z) >= span_khz:
            return z
    return 0


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
    """Polls a kiwiclientd rigctld TCP port for the current frequency, same as FreeDV does."""

    def __init__(self, host, port, on_freq_khz, poll_interval=0.5):
        super().__init__(daemon=True)
        self._host = host
        self._port = port
        self._on_freq_khz = on_freq_khz
        self._poll_interval = poll_interval
        self._stop_event = threading.Event()

    def stop(self):
        self._stop_event.set()

    def run(self):
        sock = None
        while not self._stop_event.is_set():
            try:
                if sock is None:
                    sock = socket.create_connection((self._host, self._port), timeout=2)
                    sock.settimeout(2)
                sock.sendall(b'f\n')
                buf = ''
                while '\n' not in buf:
                    chunk = sock.recv(256)
                    if not chunk:
                        raise ConnectionError('rigctld connection closed')
                    buf += chunk.decode('ascii', errors='ignore')
                freq_hz = float(buf.strip())
                self._on_freq_khz(freq_hz / 1000.0)
            except Exception as e:
                logging.debug('rigctl poll error: %s', e)
                if sock is not None:
                    try:
                        sock.close()
                    except Exception:
                        pass
                sock = None
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
            'start': center - self._span_khz / 2,
            'stop': center + self._span_khz / 2,
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
        self._last_start = None
        self._last_stop = None
        self._kiwiclientd_proc = None
        self._active_sdr = None

        root.title('Kiwi Panadapter')
        self._build_ui()
        root.update_idletasks()   # so winfo_width/height are accurate before the first row arrives

        if not self._options.no_kiwiclientd:
            self._start_kiwiclientd(self._sdr_list[0])

        self._rigctl_poller = RigctlPoller(options.rigctl_host, options.rigctl_port, self._on_rigctl_freq)
        self._rigctl_poller.start()

        self._start_stream(self._sdr_list[0])
        self._active_sdr = self._sdr_list[0]
        root.protocol('WM_DELETE_WINDOW', self._on_close)
        self._poll_queue()

    def _build_ui(self):
        screen_w = self._root.winfo_screenwidth()
        self._root.geometry('%dx%d' % (screen_w, self._options.window_height))

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
        self._smeter_canvas = tk.Canvas(meter, height=22, highlightthickness=0, bg='black')
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
        argv = [sys.executable, self._options.kiwiclientd_path,
                '-s', sdr_entry['host'], '-p', str(sdr_entry['port']),
                '--rigctl-addr', self._options.rigctl_host,
                '--rigctl-port', str(self._options.rigctl_port),
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
        bin_idx = int(round((center_khz - row['start']) / (row['stop'] - row['start']) * (len(row['dbm']) - 1)))
        bin_idx = max(0, min(len(row['dbm']) - 1, bin_idx))
        instantaneous_dbm = row['dbm'][bin_idx] + WF_CAL

        now = time.time()
        if self._smeter_dbm is None or instantaneous_dbm >= self._smeter_dbm:
            self._smeter_dbm = instantaneous_dbm   # fast attack: jump up immediately
        else:
            dt = (now - self._smeter_last_ts) if self._smeter_last_ts is not None else 0.0
            max_fall = self._smeter_decay * dt
            self._smeter_dbm = max(instantaneous_dbm, self._smeter_dbm - max_fall)   # slow decay
        self._smeter_last_ts = now
        self._last_signal_dbm = self._smeter_dbm

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
            self._draw_smeter(self._last_signal_dbm)

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

    def _draw_smeter(self, dbm):
        c = self._smeter_canvas
        c.delete('all')
        w_total = max(1, c.winfo_width())
        frac = max(0.0, min(1.0, (dbm - self._mindb) / (self._maxdb - self._mindb)))
        w = int(frac * w_total)
        color = '#00ff00' if dbm < -73 else ('#ffff00' if dbm < -43 else '#ff3030')
        c.create_rectangle(0, 0, w, 22, fill=color, width=0)
        # S-unit ticks: S9 = -73 dBm, 6 dB/S-unit below S9, 10 dB/S-unit ("+" values) above
        for label, ref_dbm in [('S1', -73 - 6 * 8), ('S5', -73 - 6 * 4), ('S9', -73), ('+20', -53), ('+40', -33)]:
            x = int(max(0.0, min(1.0, (ref_dbm - self._mindb) / (self._maxdb - self._mindb))) * w_total)
            c.create_line(x, 0, x, 22, fill='#808080')
            c.create_text(x + 2, 11, text=label, fill='white', anchor='w', font=('TkFixedFont', 7))

    def _on_close(self):
        try:
            height = self._root.winfo_height()
            save_config_value(self._options.config, 'window_height', height)
        except Exception as e:
            logging.debug('failed to save window height: %s', e)
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
    p.add_argument('--freq-major', dest='freq_major_khz', type=float, default=cfg.get('freq_major_khz', 5.0),
                    help='major (labeled) frequency axis tick spacing in kHz (config: freq_major_khz, default 5)')
    p.add_argument('--freq-minor', dest='freq_minor_khz', type=float, default=cfg.get('freq_minor_khz', 1.0),
                    help='minor (unlabeled) frequency axis tick spacing in kHz (config: freq_minor_khz, default 1)')
    p.add_argument('--window-height', dest='window_height', type=int,
                    default=cfg.get('window_height', DEFAULT_WINDOW_HEIGHT),
                    help='initial window height in pixels; saved back to the config on graceful exit (config: window_height)')
    p.add_argument('--sdr-list', default=DEFAULT_SDR_LIST, help='flat text file of "name host port" SDR entries')
    p.add_argument('--user', default='kiwipanadapter', help='client name reported to the Kiwi')
    p.add_argument('--default-freq', dest='default_freq', type=float, default=cfg.get('default_freq', 14200.0),
                    help='initial center frequency (kHz) used until the first rigctl poll arrives (config: default_freq)')
    p.add_argument('--kiwiclientd-path', dest='kiwiclientd_path',
                    default=cfg.get('kiwiclientd_path', os.path.join(SCRIPT_DIR, 'kiwiclientd.py')),
                    help='path to kiwiclientd.py, started/restarted automatically for the selected SDR (config: kiwiclientd_path)')
    p.add_argument('--kiwiclientd-args', dest='kiwiclientd_args', default=cfg.get('kiwiclientd_args', ''),
                    help='extra arguments appended to the managed kiwiclientd invocation, e.g. "--snddev kiwisnd0" (config: kiwiclientd_args)')
    p.add_argument('--no-kiwiclientd', dest='no_kiwiclientd', action='store_true',
                    default=cfg.get('no_kiwiclientd', False),
                    help="don't start/manage kiwiclientd -- use this for a real-radio setup where a "
                         "real rigctld (config: rigctl_host/rigctl_port) is already the frequency source "
                         "(config: no_kiwiclientd)")
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
