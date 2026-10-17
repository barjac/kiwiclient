# kiwipanadapter with freedv-rade-setup

These two hooks start kiwipanadapter together with FreeDV when FreeDV is
started from a radio's icon (or start script) made by
[freedv-rade-setup](https://github.com/barjac/freedv-rade-build), and stop
it when FreeDV closes.

## Install

Link all three into the radio's hooks folder (RADIO is the radio's folder name
under `~/.config/freedv-rade-setup/`, e.g. `ts-450s`):

    mkdir -p ~/.config/freedv-rade-setup/RADIO/hooks
    ln -s ~/GIT/kiwiclient/freedv-hooks/before-freedv ~/.config/freedv-rade-setup/RADIO/hooks/
    ln -s ~/GIT/kiwiclient/freedv-hooks/after-freedv  ~/.config/freedv-rade-setup/RADIO/hooks/
    ln -s ~/GIT/kiwiclient/freedv-hooks/env           ~/.config/freedv-rade-setup/RADIO/hooks/

Use links, not copies: the hooks find the kiwiclient folder through them,
and a `git pull` here then updates them.

## What they do

- `before-freedv` makes the extra `FDV_PAN` box (the panadapter's own
  audio), then starts `kiwipanadapter.py`. It tells the panadapter the
  radio's RX node (whatever the radio's `links` file feeds into
  `FDV_RX_in`, normally `radio-rx:capture_MONO`) and reads the headset from
  the same file, so `panadapter.conf` needs no sound device names. Its
  output goes to `kiwipanadapter.log` in the radio's folder. The Auto
  passband preset follows the FreeDV build: FDV2 for a RADE V2 build, FDV1
  otherwise (needs freedv-rade-setup from 17 Oct 2026 or later, whose start
  script sets `FREEDV_RADE`; with an older one the saved choice is used).
  Likewise the panadapter uses the rigctld chosen in the radio's setup (on
  the Pi itself or another computer: `FREEDV_RIG_HOST`) for whatever
  `panadapter.conf` leaves out: a `rigctl_host` or `rigctl_port` set there
  always wins (e.g. another rig server or port).
- `after-freedv` stops it.
- `env` runs FreeDV under X11 (`GDK_BACKEND=x11`): the panadapter finds the
  Reporter window (`snap_below_title`) with X11 tools, which can't see a
  native Wayland window. Needs freedv-rade-setup from 12 Oct 2026 or later
  (the start script reads `hooks/env`).

## Note

The panadapter's RX/SDR switch moves `FDV_RX_in` between the radio and
`FDV_PAN`. If you save the links in freedv-rade-setup, do it in **RX**
mode, or the saved list loses the radio -> `FDV_RX_in` link.
