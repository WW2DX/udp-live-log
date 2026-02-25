# 📡 UDP Live Log — N1MM to Club Log Bridge

**Version 1.4.1**

A self-contained Python bridge that connects [N1MM Logger+](https://n1mm.hamdocs.com/) to [Club Log Livestream](https://clublog.org/livestream.php), with a real-time web dashboard, comprehensive statistics, ADIF logging, and Raspberry Pi system monitoring — all in a single script with zero external dependencies.

Vibe Coded de [WW2DX](https://www.ww2dx.com)

---

## Features

### Core
- **Real-time N1MM database watcher** — monitors N1MM's SQLite database directly, no UDP configuration required
- **Club Log Livestream gateway** — auto-downloads the correct binary for your architecture (x86_64, ARM64, ARMv7), starts it, monitors it, and restarts on crash
- **QSO add / edit / delete** sync including tombstone tracking to prevent re-submission of deleted QSOs
- **ADIF logger** — writes every QSO to a monthly `CALLSIGN_YYYYMM.adi` file automatically
- **Full band coverage** including 6m, 2m, 70cm, 23cm, 13cm and all microwave bands — corrects N1MM's ×1000 frequency scale error above 1 GHz
- **Persistent state** — all QSOs survive bridge restarts and Pi reboots via `log_state.json`

### Live Dashboard
- Auto-refreshing stats: total QSOs, unique calls, rate/hr, first/last QSO times
- Band, mode, and operator breakdowns with animated bar charts
- 60-minute rate histogram in 10-minute buckets
- Recent QSO table with time, callsign, band, frequency, and mode
- Live Club Log Gateway and ADIF logger status indicators

### Detailed Statistics (9 Tabs)
- **Summary** — band × mode matrix, continent/zone counts, operating time summary
- **Rates** — best 1/10/30/60-min rates, hourly charts, per-band charts, UTC heatmap, sparkline
- **Bands** — band × mode matrix, band changes by hour, continents-by-band, time-per-band
- **Countries** — full DXCC table, first-worked chronology, DXCC-by-band, DXCC-by-mode (340-entry embedded prefix table — works offline)
- **Zones** — all 40 CQ zones and 90 ITU zones as worked/unworked pill displays
- **Map & Beams** — interactive Leaflet contact map + per-band SVG beam heading compass roses
- **Callsigns** — length distribution, top duplicates, unique prefix list
- **Time Analysis** — operating time, break list, band change log
- **QSO Log** — last 500 contacts with DXCC, continent, CQ zone, ITU zone enrichment

### Operations
- **Multi-account support** — store multiple callsign/password pairs, switch instantly from the web Admin page
- **Web-based Admin** — full config editor in the browser, no SSH needed during operations
- **ADIF import** — load existing log files via the Tools page, with duplicate detection
- **Log file browser** — list and download ADIF files from any browser on the local network
- **Log reset** — clear the in-memory log between sessions without restarting
- **Credential verification** — `--test-clublog` diagnoses your setup before going live

### Raspberry Pi
- **System health monitor** — live CPU, temperature, memory, swap, disk, load average, uptime, network interfaces, throttle/under-voltage warnings
- **Offline-first** — no CDN requests on page load, system font stack, Leaflet lazy-loaded only when needed
- **Threaded HTTP server** — concurrent requests, non-blocking CPU sampling
- **Zero dependencies** — Python 3 stdlib only, single script, just run and go

---

## Requirements

- Python 3.8 or later
- N1MM Logger+ running on a Windows PC on the same LAN
- Club Log account with an [App Password](https://clublog.org/appkeys.php) (not your login password)
- Internet access on first run only (to download the Club Log Gateway binary)

---

## Quick Start

**1. Download the script**
```bash
wget https://raw.githubusercontent.com/YOUR_USERNAME/udp-live-log/main/udp_live_log.py
```

**2. Generate a sample config file**
```bash
python3 udp_live_log.py --write-config
```

**3. Edit `config.ini`**
```ini
[clublog]
callsign = W1AW
password = YOUR_APP_PASSWORD_HERE

[web]
port = 8080

[adif]
directory = adif_logs
state_file = log_state.json
```

**4. Run**
```bash
python3 udp_live_log.py
```

**5. Open the dashboard**

Navigate to `http://[your-pi-ip]:8080` from any browser on the local network.

---

## Configuration

All settings can be managed via the **⚙ Admin** page in the web dashboard, or by editing `config.ini` directly.

### Full `config.ini` reference

```ini
[clublog]
# Active callsign (managed by Admin page)
callsign = W1AW
active   = W1AW
password = YOUR_APP_PASSWORD_HERE

# Multiple accounts — add one section per callsign
# [account.VP9/W1AW]
# callsign = VP9/W1AW
# password = YOUR_OTHER_APP_PASSWORD

[web]
port = 8080

[adif]
directory  = adif_logs
state_file = log_state.json
```

### Club Log App Password

Your App Password is a separate credential from your Club Log login password. Generate one at:
**https://clublog.org/appkeys.php**

It looks like: `407-Xl908-Rm690-Xx661-Wi881-Bg822-Hn`

---

## Command Line Options

```
python3 udp_live_log.py [options]

  --callsign CALL       Station callsign (overrides config.ini)
  --password PASS       Club Log App Password (overrides config.ini)
  --web-port PORT       Web dashboard port (default: 8080)
  --state-file FILE     Path to QSO state JSON file
  --adif-dir DIR        Directory for ADIF log files
  --config FILE         Config file path (default: config.ini)
  --write-config        Write a sample config.ini and exit
  --test-clublog        Verify Club Log credentials and exit
  --debug               Enable verbose debug logging
```

---

## N1MM Logger+ Setup

No special configuration is required in N1MM Logger+. The bridge watches N1MM's database file directly. Just ensure:

1. N1MM Logger+ is running on the same LAN as the bridge
2. The bridge can read N1MM's database file — if running on a different machine, the database must be on a shared/accessible path
3. N1MM is configured to log to Club Log (the gateway handles the actual upload)

> **Tip:** The easiest setup is to run the bridge on a Raspberry Pi on the same network as the N1MM PC, with N1MM's log directory accessible via a network share.

---

## Running as a Service (Raspberry Pi)

To have the bridge start automatically on boot:

**1. Create the service file**
```bash
sudo nano /etc/systemd/system/udp-live-log.service
```

```ini
[Unit]
Description=UDP Live Log — N1MM to Club Log Bridge
After=network.target

[Service]
Type=simple
User=pi
WorkingDirectory=/home/pi/udp-live-log
ExecStart=/usr/bin/python3 /home/pi/udp-live-log/udp_live_log.py
Restart=on-failure
RestartSec=5

[Install]
WantedBy=multi-user.target
```

**2. Enable and start**
```bash
sudo systemctl daemon-reload
sudo systemctl enable udp-live-log
sudo systemctl start udp-live-log
```

**3. Check status**
```bash
sudo systemctl status udp-live-log
journalctl -u udp-live-log -f
```

---

## Web Pages

| URL | Description |
|-----|-------------|
| `/` | Live dashboard |
| `/stats` | Detailed 9-tab statistics |
| `/logs` | ADIF log file browser & download |
| `/tools` | ADIF import, log reset |
| `/admin` | Account & config management |
| `/about` | Feature reference |

### API Endpoints

| Endpoint | Description |
|----------|-------------|
| `GET /api/stats` | Live QSO statistics |
| `GET /api/stats/detail` | Full statistics dataset (all 9 tabs) |
| `GET /api/system` | Raspberry Pi system vitals |
| `GET /api/uploader` | Club Log Gateway status |
| `GET /api/adif` | ADIF logger status |

---

## Changelog

| Version | Date | Notes |
|---------|------|-------|
| 1.4.1 | 2026-02-25 | Footer "Vibe Coded de WW2DX" on dashboard only |
| 1.4.0 | 2026-02-25 | Renamed to UDP Live Log, added footer credit |
| 1.3.0 | 2026-02-24 | Full 9-tab statistics, beam headings, contest log analysis |
| 1.2.0 | 2026-02-24 | DXCC tracking, zone analysis, interactive contact map |
| 1.1.0 | 2026-02-24 | Multi-account support, web-based Admin page |
| 1.0.0 | 2026-02-24 | Initial release — N1MM bridge, Club Log gateway, live dashboard |

---

## License

MIT License — free to use, modify, and distribute.

---

*Vibe Coded de [WW2DX](https://www.ww2dx.com)*
