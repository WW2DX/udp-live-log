#!/usr/bin/env python3
"""
N1MM Logger+ → Club Log Livestream Bridge & Web Dashboard
Runs on Raspberry Pi (or any Linux system)

Features:
  - Listens for N1MM UDP broadcasts on the LAN
  - Uploads QSOs to Club Log Livestream in real-time
  - Embedded web server with live statistics dashboard

Requirements:
  pip install flask requests

Usage:
  python3 n1mm_clublog_bridge.py --callsign YOURCALL --clublog-key YOUR_API_KEY

Configuration can also be done via config.ini (see bottom of file).
"""

VERSION = "1.4.1"  # 2026-02-25 — Footer "de WW2DX" on dashboard only

# ── Background CPU usage sampler (avoids sleep() blocking HTTP requests) ──
_cpu_pct_cache: dict = {"pct": None}

def _cpu_sampler_thread():
    """Continuously sample CPU usage in the background every 2 seconds."""
    import time as _t
    def _read():
        try:
            with open("/proc/stat") as f:
                v = list(map(int, f.readline().split()[1:8]))
            return v[3] + v[4], sum(v)
        except Exception:
            return None, None
    while True:
        try:
            i1, t1 = _read()
            _t.sleep(2)
            i2, t2 = _read()
            if t1 and t2 and (t2 - t1) > 0:
                _cpu_pct_cache["pct"] = round(100.0 * (1 - (i2 - i1) / (t2 - t1)), 1)
        except Exception:
            _t.sleep(2)

import threading as _threading
_cpu_thread = _threading.Thread(target=_cpu_sampler_thread, daemon=True, name="CPUSampler")
_cpu_thread.start()

import argparse
import re
import configparser
import hashlib
import json
import logging
import os
import socket
import threading
import time
import xml.etree.ElementTree as ET
from collections import defaultdict, deque
from datetime import datetime, timezone
from http.server import HTTPServer, BaseHTTPRequestHandler
import socketserver
from typing import Optional
from urllib import request as urllib_request, parse as urllib_parse
from urllib.error import URLError, HTTPError

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION
# ─────────────────────────────────────────────────────────────────────────────

DEFAULT_N1MM_UDP_PORT   = 12060   # N1MM primary broadcast port (used by Club Log Gateway)
DEFAULT_BRIDGE_UDP_PORT = 12061   # Our bridge listens here — add a second N1MM broadcast target
DEFAULT_WEB_PORT        = 8080
CLUBLOG_REALTIME_URL    = "https://clublog.org/realtime.php"
CLUBLOG_UPLOAD_URL      = "https://clublog.org/api/upload.php"

# How many minutes to look back for QSO-rate calculations
RATE_WINDOW_MINUTES = 60

# ─────────────────────────────────────────────────────────────────────────────
# BAND / MODE HELPERS
# ─────────────────────────────────────────────────────────────────────────────

def freq_to_band(freq_hz: int) -> str:
    """Convert frequency in Hz to amateur band string."""
    khz = freq_hz / 1000
    mhz = khz / 1000
    if   1800 <= khz <= 2000:   return "160m"
    elif 3500 <= khz <= 4000:   return "80m"
    elif 5330 <= khz <= 5410:   return "60m"
    elif 7000 <= khz <= 7300:   return "40m"
    elif 10100 <= khz <= 10150: return "30m"
    elif 14000 <= khz <= 14350: return "20m"
    elif 18068 <= khz <= 18168: return "17m"
    elif 21000 <= khz <= 21450: return "15m"
    elif 24890 <= khz <= 24990: return "12m"
    elif 28000 <= khz <= 29700: return "10m"
    elif 50 <= mhz <= 54:       return "6m"
    elif 144 <= mhz <= 148:     return "2m"
    elif 420 <= mhz <= 450:     return "70cm"
    elif 1240 <= mhz <= 1300:   return "23cm"
    else:                       return "OTH"

# ─────────────────────────────────────────────────────────────────────────────
# QSO DATA MODEL
# ─────────────────────────────────────────────────────────────────────────────

class QSO:
    __slots__ = ("id", "timestamp", "callsign", "band", "mode",
                 "freq_hz", "rst_sent", "rst_rcvd", "exchange",
                 "operator", "station_callsign", "raw_xml")

    def __init__(self):
        self.id              = ""
        self.timestamp       = datetime.now(timezone.utc)
        self.callsign        = ""
        self.band            = ""
        self.mode            = ""
        self.freq_hz         = 0
        self.rst_sent        = "599"
        self.rst_rcvd        = "599"
        self.exchange        = ""
        self.operator        = ""
        self.station_callsign = ""
        self.raw_xml         = ""

    def to_dict(self) -> dict:
        freq_mhz = f"{self.freq_hz / 1_000_000:.3f}" if self.freq_hz else (self.band.upper() if self.band else "")
        return {
            "id":               self.id,
            "timestamp":        self.timestamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "callsign":         self.callsign,
            "band":             self.band,
            "mode":             self.mode,
            "freq_hz":          self.freq_hz,
            "freq_mhz":         freq_mhz,
            "rst_sent":         self.rst_sent,
            "rst_rcvd":         self.rst_rcvd,
            "exchange":         self.exchange,
            "operator":         self.operator,
            "station_callsign": self.station_callsign,
        }

# ─────────────────────────────────────────────────────────────────────────────
# LOG DATABASE (in-memory)
# ─────────────────────────────────────────────────────────────────────────────

class LogDatabase:
    """In-memory QSO store with optional JSON persistence.

    State is saved to <state_file> (default: log_state.json) every time a QSO
    is added/updated/deleted, and reloaded automatically on startup so statistics
    survive restarts and reboots.
    """

    def __init__(self, state_file: str = "log_state.json", callsign: str = ""):
        self._lock        = threading.Lock()
        self._qsos: dict[str, QSO] = {}
        self._qso_times   = deque()
        self._deleted_ids: set = set()
        self._state_file  = state_file
        self.callsign     = callsign
        self._load_state()

    # ── Persistence ──────────────────────────────────────────────────────────

    def _qso_to_dict(self, qso: QSO) -> dict:
        return {
            "id":               qso.id,
            "timestamp":        qso.timestamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "callsign":         qso.callsign,
            "band":             qso.band,
            "mode":             qso.mode,
            "freq_hz":          qso.freq_hz,
            "rst_sent":         qso.rst_sent,
            "rst_rcvd":         qso.rst_rcvd,
            "exchange":         qso.exchange,
            "operator":         qso.operator,
            "station_callsign": qso.station_callsign,
        }

    # Band label normalisation map (handles N1MM cm-wavelength and bare-MHz values)
    _BAND_NORM = {
        # cm-wavelength integers N1MM sometimes uses
        "23": "23cm", "13": "13cm", "9": "9cm", "6": "6cm", "3": "3cm",
        # MHz integers
        "1": "160m", "3": "80m", "5": "60m", "7": "40m",
        "10": "30m", "14": "20m", "18": "17m", "21": "15m",
        "24": "12m", "28": "10m", "50": "6m", "70": "4m",
        "144": "2m", "222": "1.25m", "432": "70cm", "440": "70cm",
        "902": "33cm", "1240": "23cm", "1296": "23cm",
        "2304": "13cm", "2320": "13cm", "3400": "9cm",
        "5760": "6cm", "10368": "3cm",
    }
    _MICROWAVE_BANDS = {"23cm", "13cm", "9cm", "6cm", "3cm", "1.2cm"}

    @staticmethod
    def _normalise_band(band: str) -> str:
        """Normalise any N1MM band string to canonical form e.g. '23'→'23cm'."""
        if not band:
            return band
        b = band.strip().lower()
        # Already canonical (ends with 'm' or 'cm')
        if b.endswith("m"):
            return b
        # Look up in norm map (tries original case and stripped)
        return LogDatabase._BAND_NORM.get(band.strip(),
               LogDatabase._BAND_NORM.get(b, band.strip()))

    @staticmethod
    def _fix_freq(freq_hz: int, band: str) -> int:
        """Correct freq_hz that was stored with the ×1000 microwave scale error."""
        if freq_hz <= 0:
            return freq_hz
        mhz = freq_hz / 1_000_000
        if band in LogDatabase._MICROWAVE_BANDS and mhz < 100:
            return freq_hz * 1000   # was stored in 10kHz units, scale to Hz
        return freq_hz

    def _dict_to_qso(self, d: dict) -> QSO:
        qso = QSO()
        qso.id               = d.get("id", "")
        qso.callsign         = d.get("callsign", "")
        qso.band             = LogDatabase._normalise_band(d.get("band", ""))
        qso.mode             = d.get("mode", "")
        qso.freq_hz          = LogDatabase._fix_freq(d.get("freq_hz", 0), qso.band)
        qso.rst_sent         = d.get("rst_sent", "59")
        qso.rst_rcvd         = d.get("rst_rcvd", "59")
        qso.exchange         = d.get("exchange", "")
        qso.operator         = d.get("operator", "")
        qso.station_callsign = d.get("station_callsign", "")
        try:
            qso.timestamp = datetime.strptime(
                d.get("timestamp", ""), "%Y-%m-%dT%H:%M:%SZ"
            ).replace(tzinfo=timezone.utc)
        except ValueError:
            qso.timestamp = datetime.now(timezone.utc)
        return qso

    def _load_state(self):
        """Load persisted QSOs from JSON file on startup."""
        if not self._state_file or not os.path.exists(self._state_file):
            return
        try:
            with open(self._state_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            loaded = 0
            for d in data.get("qsos", []):
                qso = self._dict_to_qso(d)
                if qso.id and qso.callsign:
                    self._qsos[qso.id] = qso
                    self._qso_times.append((qso.timestamp, qso.id))
                    loaded += 1
            self._deleted_ids = set(data.get("deleted_ids", []))
            logging.info(f"Loaded {loaded} QSOs from state file: {self._state_file}")
        except (json.JSONDecodeError, OSError, KeyError) as e:
            logging.warning(f"Could not load state file ({self._state_file}): {e} — starting fresh")

    def _save_state(self):
        """Atomically write current QSOs to JSON state file."""
        if not self._state_file:
            return
        try:
            data = {
                "saved_at":   datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "qso_count":  len(self._qsos),
                "qsos":       [self._qso_to_dict(q) for q in self._qsos.values()],
                "deleted_ids": list(self._deleted_ids),
            }
            # Write to temp file then rename for atomicity (safe on Pi power loss)
            tmp = self._state_file + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, separators=(",", ":"))
            os.replace(tmp, self._state_file)
        except OSError as e:
            logging.warning(f"Could not save state file: {e}")

    def add_or_update(self, qso: QSO):
        # Normalise band and fix any microwave freq scale error before storing
        qso.band    = LogDatabase._normalise_band(qso.band)
        qso.freq_hz = LogDatabase._fix_freq(qso.freq_hz, qso.band)
        with self._lock:
            self._qsos[qso.id] = qso
            self._qso_times.append((qso.timestamp, qso.id))
            self._deleted_ids.discard(qso.id)
            self._save_state()

    def delete(self, qso_id: str):
        with self._lock:
            self._deleted_ids.add(qso_id)
            self._qsos.pop(qso_id, None)
            self._save_state()

    def is_deleted(self, qso_id: str) -> bool:
        with self._lock:
            return qso_id in self._deleted_ids

    def all_qsos(self) -> list[QSO]:
        with self._lock:
            return list(self._qsos.values())

    def reset_stats(self):
        """Clear all QSOs and wipe the state file. Irreversible."""
        with self._lock:
            self._qsos.clear()
            self._qso_times.clear()
            self._deleted_ids.clear()
            self._save_state()
        logging.info("Stats reset — all QSOs cleared from memory and state file")

    def import_adif(self, filepath: str) -> tuple[int, int, list]:
        """Import QSOs from an ADIF file into the live database.

        Returns (imported_count, skipped_duplicates, errors).
        """
        qsos, errors = parse_adif_file(filepath)
        imported = 0
        skipped  = 0
        with self._lock:
            for qso in qsos:
                if qso.id in self._qsos:
                    skipped += 1
                else:
                    self._qsos[qso.id] = qso
                    self._qso_times.append((qso.timestamp, qso.id))
                    imported += 1
            if imported:
                self._save_state()
        logging.info(f"ADIF import: {imported} imported, {skipped} duplicates skipped from {filepath}")
        return imported, skipped, errors

    def stats(self) -> dict:
        with self._lock:
            qsos = list(self._qsos.values())

        now = datetime.now(timezone.utc)
        total = len(qsos)

        # --- Per-band counts ---
        band_counts: dict[str, int] = defaultdict(int)
        for q in qsos:
            band_counts[q.band] += 1

        # --- Per-mode counts ---
        mode_counts: dict[str, int] = defaultdict(int)
        for q in qsos:
            mode_counts[q.mode.upper()] += 1

        # --- Per-operator ---
        op_counts: dict[str, int] = defaultdict(int)
        for q in qsos:
            op_counts[q.operator or "?"] += 1

        # --- Hourly QSO rate (last 60 minutes) ---
        cutoff_60 = now.timestamp() - 3600
        last_60 = sum(1 for q in qsos if q.timestamp.timestamp() >= cutoff_60)
        rate_per_hour = last_60  # already "in the last 60 min"

        # --- Rate by 10-minute buckets (last hour) ---
        buckets = [0] * 6  # 0-9, 10-19, 20-29, 30-39, 40-49, 50-59 min ago
        for q in qsos:
            age_min = (now.timestamp() - q.timestamp.timestamp()) / 60
            if 0 <= age_min < 60:
                bucket = min(5, int(age_min / 10))
                buckets[5 - bucket] += 1   # most-recent bucket on the right

        # --- Running totals by hour ---
        hourly: dict[str, int] = defaultdict(int)
        for q in qsos:
            hkey = q.timestamp.strftime("%Y-%m-%dT%H:00Z")
            hourly[hkey] += 1

        # --- Last 10 QSOs ---
        recent = sorted(qsos, key=lambda q: q.timestamp, reverse=True)[:10]

        # --- Unique callsigns ---
        unique_calls = len(set(q.callsign for q in qsos))

        # --- First/last QSO time ---
        times = [q.timestamp for q in qsos] if qsos else []
        first_qso = min(times).strftime("%Y-%m-%dT%H:%M:%SZ") if times else None
        last_qso  = max(times).strftime("%Y-%m-%dT%H:%M:%SZ") if times else None

        return {
            "total":           total,
            "unique_calls":    unique_calls,
            "rate_per_hour":   rate_per_hour,
            "rate_buckets":    buckets,
            "band_counts":     dict(sorted(band_counts.items())),
            "mode_counts":     dict(sorted(mode_counts.items())),
            "op_counts":       dict(op_counts),
            "hourly":          dict(sorted(hourly.items())),
            "recent":          [q.to_dict() for q in recent],
            "first_qso":       first_qso,
            "last_qso":        last_qso,
            "server_time":     now.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "callsign":        self.callsign,
        }


# ─────────────────────────────────────────────────────────────────────────────
# ADIF FILE IMPORTER
# ─────────────────────────────────────────────────────────────────────────────

def parse_adif_file(filepath: str) -> tuple[list, list]:
    """Parse an ADIF file and return (qsos, errors).

    Handles both field-per-line and compact single-line ADIF styles.
    Returns a list of QSO objects and a list of error strings.
    """
    qsos   = []
    errors = []

    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            raw = f.read()
    except OSError as e:
        return [], [f"Cannot open file: {e}"]

    # Strip header (everything before <EOH>)
    eoh = re.search(r'<EOH>', raw, re.IGNORECASE)
    body = raw[eoh.end():] if eoh else raw

    # Split into records on <EOR>
    records = re.split(r'<EOR>', body, flags=re.IGNORECASE)

    for rec_idx, record in enumerate(records):
        record = record.strip()
        if not record:
            continue

        # Extract all ADIF fields: <FIELDNAME:LEN>value or <FIELDNAME:LEN:TYPE>value
        fields: dict[str, str] = {}
        for m in re.finditer(r'<([A-Za-z_][A-Za-z0-9_]*)(?::\d+(?::[A-Za-z])?)?>([^<]*)', record):
            fname = m.group(1).upper()
            fval  = m.group(2).strip()
            fields[fname] = fval

        call = fields.get("CALL", "").upper()
        if not call:
            continue  # skip records without a callsign

        qso = QSO()

        # Generate a stable ID from call+date+time (reproducible across imports)
        date_raw = fields.get("QSO_DATE", "19700101")
        time_raw = fields.get("TIME_ON",  "000000")[:6].ljust(6, "0")
        qso.id   = hashlib.md5(f"{call}{date_raw}{time_raw}".encode()).hexdigest()

        qso.callsign         = call
        qso.operator         = fields.get("OPERATOR", "").upper()
        qso.station_callsign = fields.get("STATION_CALLSIGN", "").upper()
        qso.rst_sent         = fields.get("RST_SENT", "59")
        qso.rst_rcvd         = fields.get("RST_RCVD", "59")
        qso.exchange         = fields.get("COMMENT",  "") or fields.get("STX_STRING", "")
        qso.freq_hz          = 0

        # Mode — prefer SUBMODE for USB/LSB detail
        qso.mode = fields.get("SUBMODE", "") or fields.get("MODE", "")

        # Band
        band = fields.get("BAND", "")
        if band:
            qso.band = band.lower()
        else:
            try:
                freq_mhz = float(fields.get("FREQ", "0"))
                qso.freq_hz = int(freq_mhz * 1_000_000)
                qso.band = freq_to_band(qso.freq_hz)
            except ValueError:
                qso.band = "OTH"

        # Frequency
        if not qso.freq_hz:
            try:
                qso.freq_hz = int(float(fields.get("FREQ", "0")) * 1_000_000)
            except ValueError:
                qso.freq_hz = 0

        # Timestamp
        try:
            ts = datetime.strptime(f"{date_raw} {time_raw}", "%Y%m%d %H%M%S")
            qso.timestamp = ts.replace(tzinfo=timezone.utc)
        except ValueError:
            qso.timestamp = datetime.now(timezone.utc)

        qsos.append(qso)

    return qsos, errors

# ─────────────────────────────────────────────────────────────────────────────
# N1MM UDP LISTENER
# ─────────────────────────────────────────────────────────────────────────────

def parse_n1mm_contact(xml_str: str) -> Optional[QSO]:
    """Parse an N1MM ContactInfo XML packet into a QSO object.

    Actual N1MM field names (from live capture):
      <call>, <mycall>, <operator>, <StationName>
      <band>  — MHz as integer string, e.g. "14" for 20m
      <rxfreq>/<txfreq> — frequency in 10Hz units, e.g. 1420000 = 14.200 MHz
      <mode>  — USB, LSB, CW, FM, RTTY, etc.
      <snt>/<rcv> — RST sent/received
      <timestamp> — "YYYY-MM-DD HH:MM:SS"
      <ID>    — unique QSO identifier (hex string)
      <SentExchange>, <exchange1> — exchange fields
    """
    try:
        # Strip any leading BOM or whitespace before the XML declaration
        xml_str = xml_str.strip()
        if xml_str.startswith("\xef\xbb\xbf"):
            xml_str = xml_str[3:]

        # N1MM sometimes sends truncated packets without the closing tag.
        # Detect the root element name and append it if missing.
        m = re.search(r'<(?!\?)(\w+)', xml_str)
        if m:
            root_tag = m.group(1)
            close_tag = f'</{root_tag}>'
            if not xml_str.rstrip().endswith(close_tag):
                xml_str = xml_str.rstrip() + f'\n{close_tag}'

        root = ET.fromstring(xml_str)

        # The root element IS the contactinfo element
        ci = root

        def get(tag: str, default: str = "") -> str:
            """Case-insensitive child element search."""
            # Try exact match first
            el = ci.find(tag)
            if el is not None:
                return (el.text or "").strip()
            # Fall back to case-insensitive scan
            tag_lower = tag.lower()
            for child in ci:
                if child.tag.lower() == tag_lower:
                    return (child.text or "").strip()
            return default

        qso = QSO()
        qso.raw_xml = xml_str

        # ── Identity ──────────────────────────────────────────────────────
        qso.id               = get("ID") or str(time.time_ns())
        qso.callsign         = get("call").upper()
        qso.operator         = get("operator").upper() or get("mycall").upper()
        qso.station_callsign = get("StationName").upper() or get("mycall").upper()

        # ── RST ───────────────────────────────────────────────────────────
        # N1MM uses <snt>/<rcv> (not <Snt>/<Rcv>)
        qso.rst_sent = get("snt") or get("Snt") or "59"
        qso.rst_rcvd = get("rcv") or get("Rcv") or "59"

        # ── Mode ──────────────────────────────────────────────────────────
        qso.mode = get("mode").upper() or get("Mode").upper()

        # ── Exchange ──────────────────────────────────────────────────────
        qso.exchange = get("SentExchange") or get("exchange1") or get("Exchange") or ""

        # ── Timestamp ─────────────────────────────────────────────────────
        ts_str = get("timestamp") or get("Timestamp") or ""
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S"):
            try:
                qso.timestamp = datetime.strptime(ts_str.strip(), fmt).replace(tzinfo=timezone.utc)
                break
            except ValueError:
                continue
        else:
            qso.timestamp = datetime.now(timezone.utc)

        # ── Frequency → band ──────────────────────────────────────────────
        # txfreq / rxfreq are in 10 Hz units (e.g. 1420000 = 14.200 MHz)
        freq_raw = get("txfreq") or get("rxfreq") or get("Freq") or "0"
        try:
            freq_10hz = int(float(freq_raw))
            qso.freq_hz = freq_10hz * 10          # convert to Hz (10Hz units → Hz)
        except ValueError:
            qso.freq_hz = 0

        # ── Band field ─────────────────────────────────────────────────────────
        # N1MM sends <band> in several formats depending on version and band:
        #   HF:        "14", "7", "21" … (MHz as integer)
        #   VHF/UHF:   "144", "432", "1296" … (MHz as integer)  [some versions]
        #              "2m", "70cm", "23cm" … (band label)       [other versions]
        #   Microwave: "23", "13", "9" … (cm wavelength)         [some versions]
        band_field = (get("band") or get("Band") or "").strip()

        # Maps for both MHz-integer and cm-wavelength representations
        band_mhz_map = {
            "1": "160m", "3": "80m",  "5": "60m",  "7": "40m",
            "10": "30m", "14": "20m", "18": "17m",  "21": "15m",
            "24": "12m", "28": "10m", "50": "6m",   "70": "4m",
            "144": "2m", "222": "1.25m", "432": "70cm", "440": "70cm",
            "902": "33cm", "1240": "23cm", "1296": "23cm",
            "2304": "13cm", "2320": "13cm", "3400": "9cm",
            "5760": "6cm", "10368": "3cm", "24048": "1.2cm",
        }
        # cm-wavelength labels N1MM uses for microwave bands
        band_cm_map = {
            "23": "23cm", "13": "13cm", "9": "9cm",
            "6": "6cm",   "3": "3cm",  "1.2": "1.2cm",
        }
        # Canonical band-name aliases (already correct strings)
        band_label_set = {
            "160m","80m","60m","40m","30m","20m","17m","15m","12m","10m",
            "6m","4m","2m","1.25m","70cm","33cm","23cm","13cm","9cm","6cm","3cm",
        }

        if band_field.lower() in band_label_set:
            qso.band = band_field.lower()
        elif band_field in band_mhz_map:
            qso.band = band_mhz_map[band_field]
        elif band_field in band_cm_map:
            qso.band = band_cm_map[band_field]
        elif band_field and band_field.replace(".","",1).isdigit():
            # Unknown numeric — try freq_to_band fallback below
            qso.band = ""
        elif band_field:
            qso.band = band_field      # pass through unknown strings as-is
        else:
            qso.band = ""

        # ── Frequency ──────────────────────────────────────────────────────────
        # N1MM rxfreq/txfreq units:
        #   HF bands (< 30 MHz):  10 Hz units  e.g. 1420000 = 14.200 MHz
        #   VHF/UHF (50–900 MHz): 10 Hz units  e.g. 5007500 = 50.075 MHz
        #   Microwave (≥1 GHz):   N1MM sends in units of 10 kHz (×1000 off)
        #                         e.g. 129600 → should be 1296.000 MHz
        # Detect the ×1000 scale error: if freq_hz < 10 MHz but band says ≥1 GHz
        if qso.freq_hz > 0:
            freq_mhz = qso.freq_hz / 1_000_000
            band_is_microwave = qso.band in {
                "23cm","13cm","9cm","6cm","3cm","1.2cm"
            }
            if band_is_microwave and freq_mhz < 100:
                # Scale up by 1000 (N1MM sent in 10kHz units instead of 10Hz)
                qso.freq_hz *= 1000
            elif not qso.band and freq_mhz < 1:
                # Very small freq with no band — also likely microwave scale error
                qso.freq_hz *= 1000

        # Derive band from frequency if we still don't have one
        if not qso.band:
            qso.band = freq_to_band(qso.freq_hz)

        if not qso.callsign:
            logging.debug(f"Skipping packet — no callsign found. Tags: {[c.tag for c in ci]}")
            return None

        return qso

    except ET.ParseError as e:
        logging.error(f"XML parse error: {e}\nRaw (first 300 chars): {xml_str[:300]!r}")
        return None

class GatewayDBWatcher(threading.Thread):
    """Watches the Club Log Gateway's SQLite database for new/changed/deleted QSOs.

    The gateway writes every QSO it hears from N1MM into a local .db file
    (e.g. WW2DX.db).  We open that file read-only, poll it every few seconds,
    and feed any changes into our LogDatabase and ADIFLogger — no second UDP
    port needed, no changes to N1MM required.

    The gateway db schema (from G7VJR's source) has a 'qso' table with columns:
      id, callsign, timestamp, band, mode, freq, rst_sent, rst_rcvd,
      operator, mycall, deleted, updated_at  (and a few others we ignore)
    We use 'updated_at' as a high-water-mark to detect changes.
    """

    POLL_INTERVAL = 3   # seconds between polls

    def __init__(self, gateway_dir: str, callsign: str,
                 db: LogDatabase, adif_logger=None):
        super().__init__(daemon=True, name="GatewayDBWatcher")
        self.gateway_dir  = gateway_dir
        self.callsign     = callsign.upper()
        self.db           = db
        self.adif_logger  = adif_logger
        self._last_seen: dict[str, str] = {}   # id → updated_at (ISO string)
        self.qsos_seen    = 0
        self.last_error   = ""

    def _db_path(self) -> str:
        return os.path.join(self.gateway_dir, f"{self.callsign}.db")

    def run(self):
        db_path = self._db_path()
        logging.info(f"Watching gateway DB: {db_path}")

        # Wait up to 30 s for the gateway to create the db file
        waited = 0
        while not os.path.exists(db_path):
            if waited == 0:
                logging.info(f"Waiting for gateway to create {db_path}...")
            time.sleep(1)
            waited += 1
            if waited > 30:
                logging.error(f"Gateway DB not found after 30s: {db_path}")
                self.last_error = "DB file never appeared"
                return

        logging.info(f"Gateway DB found, starting to watch for QSOs")

        while True:
            try:
                self._poll(db_path)
            except Exception as e:
                msg = str(e)
                if msg != self.last_error:  # only log changes, not repeated identical errors
                    logging.debug(f"GatewayDBWatcher poll error: {msg}")
                self.last_error = msg
            time.sleep(self.POLL_INTERVAL)

    def _poll(self, db_path: str):
        import sqlite3 as _sql

        # Open read-only with URI to avoid locking the gateway's db
        uri = "file:" + db_path.replace("\\", "/") + "?mode=ro"
        try:
            con = _sql.connect(uri, uri=True, timeout=3,
                               check_same_thread=False)
        except _sql.OperationalError:
            # Fall back to regular open if URI mode not supported
            con = _sql.connect(db_path, timeout=3, check_same_thread=False)

        con.row_factory = _sql.Row
        try:
            # Discover all table names — the gateway may use "qso", "qsos",
            # "contact", "contacts", or a callsign-prefixed variant
            all_tables = {r[0].lower(): r[0] for r in
                          con.execute("SELECT name FROM sqlite_master "
                                      "WHERE type='table'").fetchall()}

            if not all_tables:
                logging.debug("Gateway DB has no tables yet — waiting for gateway to initialise")
                con.close()
                return

            # Pick the QSO table: prefer exact matches, then any table with
            # "qso" or "contact" in the name, then the first table found
            qso_table = None
            for candidate in ("qso", "qsos", "contact", "contacts", "log", "logs"):
                if candidate in all_tables:
                    qso_table = all_tables[candidate]
                    break
            if not qso_table:
                for name in all_tables:
                    if "qso" in name or "contact" in name or "log" in name:
                        qso_table = all_tables[name]
                        break
            if not qso_table:
                qso_table = next(iter(all_tables.values()))

            if not hasattr(self, "_table_logged"):
                logging.info(f"Gateway DB tables: {list(all_tables.keys())} — using '{qso_table}'")
                self._table_logged = True

            # Introspect available columns
            cols = {row["name"] for row in
                    con.execute(f"PRAGMA table_info({qso_table})").fetchall()}

            if not cols:
                logging.debug(f"Table '{qso_table}' has no columns yet")
                con.close()
                return

            # Normalise column names to lowercase for case-insensitive lookup.
            # The gateway uses mixed-case: "Call", "Band", "QSODate", etc.
            cols_lower = {c.lower(): c for c in cols}

            # Map our logical field names → actual column name in the table.
            # Supports both the gateway schema and hypothetical lowercase variants.
            def col(*candidates):
                """Return the first matching actual column name, or None."""
                for c in candidates:
                    if c.lower() in cols_lower:
                        return cols_lower[c.lower()]
                return None

            call_col = col("Call", "callsign", "call")
            id_col   = col("Checksum", "id", "rowid")

            if not call_col:
                logging.debug(f"Table '{qso_table}' missing required columns: {cols}")
                con.close()
                return

            # Select all available columns — we'll map them below
            rows = con.execute(f"SELECT * FROM {qso_table}").fetchall()

        except _sql.OperationalError as e:
            logging.debug(f"DB read error (gateway may be starting): {e}")
            con.close()
            return
        finally:
            con.close()

        def g(row, *candidates, default=""):
            """Get first matching field value from a Row, case-insensitive."""
            for c in candidates:
                try:
                    v = row[c]
                    if v is not None:
                        return str(v)
                except (IndexError, KeyError):
                    pass
                # Try the actual cased version via our cols_lower map
                actual = cols_lower.get(c.lower())
                if actual:
                    try:
                        v = row[actual]
                        if v is not None:
                            return str(v)
                    except (IndexError, KeyError):
                        pass
            return default

        # ── Classify all rows into live vs deleted ───────────────────────
        # _deleted_ids is a permanent tombstone set — once an ID is marked
        # deleted we never re-add it regardless of State changes.
        if not hasattr(self, "_deleted_ids"):
            self._deleted_ids: set = set()

        def row_id_of(row):
            rid = g(row, "Checksum", "checksum", "id")
            if not rid:
                try: rid = str(row["rowid"])
                except (IndexError, KeyError): pass
            return rid or None

        def is_row_deleted(row):
            action  = g(row, "Action", "action").upper()
            deleted = g(row, "deleted", "Deleted")
            return action == "DELETE" or deleted in ("1", "true", "True")

        live_ids    = set()
        deleted_now = set()
        for row in rows:
            rid = row_id_of(row)
            if not rid:
                continue
            action = g(row, "Action", "action").upper()
            deleted = g(row, "deleted", "Deleted")
            logging.debug(f"Poll row: id={rid} call={g(row,'Call','callsign')} action={action!r} deleted={deleted!r}")
            if is_row_deleted(row):
                deleted_now.add(rid)
            else:
                live_ids.add(rid)

        logging.debug(f"Poll summary: live={live_ids} deleted_now={deleted_now} last_seen={set(self._last_seen)} tombstone={self._deleted_ids}")

        # Anything marked deleted (soft) or disappeared (hard) gets removed
        to_delete = (deleted_now | (set(self._last_seen) - live_ids - deleted_now))
        logging.debug(f"to_delete={to_delete}")
        for gone_id in to_delete:
            if gone_id in self._last_seen or gone_id in deleted_now:
                logging.info(f"Gateway deleted QSO: id={gone_id}")
                self.db.delete(gone_id)
                self._last_seen.pop(gone_id, None)
                self._deleted_ids.add(gone_id)  # tombstone — never re-add

        # ── Process each live row ─────────────────────────────────────────
        for row in rows:
            row_id = row_id_of(row)
            if not row_id:
                continue

            # Never re-process a deleted row even if State changed
            if row_id in self._deleted_ids or is_row_deleted(row):
                continue

            # Change detection — use State as high-water mark
            updated_at = g(row, "State", "state", "updated_at", "updated", default=row_id)

            if self._last_seen.get(row_id) == updated_at:
                continue
            self._last_seen[row_id] = updated_at

            # ── Build QSO object ──────────────────────────────────────────
            qso = QSO()
            qso.id               = row_id
            qso.callsign         = g(row, "Call", "callsign", "call").upper()
            qso.station_callsign = self.callsign
            qso.operator         = g(row, "Operator", "operator").upper()
            qso.rst_sent         = g(row, "RSTSent", "rst_sent", "RST_sent", default="59")
            qso.rst_rcvd         = g(row, "RSTRcvd", "rst_rcvd", "RST_rcvd", default="59")
            qso.exchange         = g(row, "Exchange", "exchange", "Comment", "comment")

            if not qso.callsign:
                continue

            # Frequency — gateway "Freq" column is MHz (e.g. 14.225)
            qso.freq_hz = 0
            raw_freq = g(row, "Freq", "freq", "TxFreq", "txfreq")
            if raw_freq:
                try:
                    v = float(raw_freq)
                    if 0 < v < 1000:         # MHz  (e.g. 14.225)
                        qso.freq_hz = int(v * 1_000_000)
                    elif v < 1_000_000:      # kHz  (e.g. 14225)
                        qso.freq_hz = int(v * 1_000)
                    else:                    # Hz   (e.g. 14225000)
                        qso.freq_hz = int(v)
                except (ValueError, TypeError):
                    pass

            # Band — gateway stores "20", "20m", "14", "14.225" (MHz),
            #         "14225" (kHz), or "14225000" (Hz)
            raw_band = g(row, "Band", "band").strip()
            rl = raw_band.lower()

            # Map plain meter-band numbers to proper strings: "20"→"20m", "40"→"40m" etc.
            METER_BANDS = {"160","80","60","40","30","20","17","15","12","10","6","2"}
            CM_BANDS    = {"70cm","23cm","13cm"}

            if rl in CM_BANDS or rl.endswith("cm"):
                qso.band = rl
            elif rl.endswith("m"):
                qso.band = rl
            elif raw_band in METER_BANDS:
                qso.band = raw_band + "m"        # "20" → "20m"
            elif raw_band:
                try:
                    v = float(raw_band)
                    if v < 1000:            # MHz  (e.g. 14, 14.225)
                        hz = int(v * 1_000_000)
                    elif v < 1_000_000:     # kHz  (e.g. 14225)
                        hz = int(v * 1_000)
                    else:                   # Hz   (e.g. 14225000)
                        hz = int(v)
                    band = freq_to_band(hz)
                    qso.band = band if band != "OTH" else raw_band.lower()
                except ValueError:
                    qso.band = rl
            else:
                # Fall back to deriving band from the frequency column
                qso.band = freq_to_band(qso.freq_hz) if qso.freq_hz else ""

            # Mode
            qso.mode = g(row, "Mode", "mode").upper()

            # Timestamp — "QSODate" is "YYYY-MM-DD HH:MM:SS" or ISO variants
            ts_raw = g(row, "QSODate", "qso_date", "timestamp", "time")
            qso.timestamp = datetime.now(timezone.utc)
            for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%SZ",
                        "%Y-%m-%dT%H:%M:%S", "%Y%m%d %H%M%S", "%Y%m%d"):
                try:
                    qso.timestamp = datetime.strptime(ts_raw, fmt).replace(
                        tzinfo=timezone.utc)
                    break
                except (ValueError, TypeError):
                    continue

            # Skip if this exact QSO was deleted via gateway stdout signal
            if self.db.is_deleted(qso.id):
                logging.debug(f"Skipping tombstoned QSO: {qso.callsign} id={qso.id}")
                continue

            self.db.add_or_update(qso)
            if self.adif_logger:
                self.adif_logger.write(qso)
            self.qsos_seen += 1
            logging.info(f"QSO from gateway: {qso.callsign} {qso.band} {qso.mode}")

# Keep old name as alias so any leftover references don't break
N1MMListener = GatewayDBWatcher

# ─────────────────────────────────────────────────────────────────────────────
# CLUB LOG GATEWAY MANAGER
# ─────────────────────────────────────────────────────────────────────────────

# Download URLs for the official Club Log Gateway binary (G7VJR)
GATEWAY_URLS = {
    "linux_arm64":  "https://clublog.org/gateway-binaries/clublog-gateway-linux_arm64.gz",
    "linux_armv7":  "https://clublog.org/gateway-binaries/clublog-gateway-linux_armv7.gz",
    "linux_amd64":  "https://clublog.org/gateway-binaries/clublog-gateway-linux_amd64.gz",
}

def detect_gateway_arch() -> str:
    """Return the correct gateway architecture string for this machine."""
    import platform
    machine = platform.machine().lower()
    if machine in ("aarch64", "arm64"):
        return "linux_arm64"
    elif machine.startswith("arm"):
        return "linux_armv7"
    else:
        return "linux_amd64"

def download_gateway(dest_dir: str = ".") -> Optional[str]:
    """Download the Club Log Gateway binary for this platform.

    Returns the path to the executable, or None on failure.
    """
    arch    = detect_gateway_arch()
    url     = GATEWAY_URLS[arch]
    gz_path = os.path.join(dest_dir, f"clublog-gateway-{arch}.gz")
    bin_path= os.path.join(dest_dir, f"clublog-gateway-{arch}")

    if os.path.isfile(bin_path):
        logging.info(f"Gateway binary already present: {bin_path}")
        return bin_path

    logging.info(f"Downloading Club Log Gateway ({arch}) from {url} ...")
    try:
        req = urllib_request.Request(url, headers={"User-Agent": "N1MM-ClubLog-Bridge/1.0"})
        with urllib_request.urlopen(req, timeout=60) as resp:
            with open(gz_path, "wb") as f:
                f.write(resp.read())
        # Decompress
        import gzip
        with gzip.open(gz_path, "rb") as gz_in:
            with open(bin_path, "wb") as bin_out:
                bin_out.write(gz_in.read())
        os.chmod(bin_path, 0o755)
        os.unlink(gz_path)
        logging.info(f"Gateway downloaded and ready: {bin_path}")
        return bin_path
    except Exception as e:
        logging.error(f"Failed to download gateway: {e}")
        return None


class ClubLogGatewayManager(threading.Thread):
    """Manages the Club Log Gateway subprocess.

    The official Club Log Gateway binary (G7VJR) is the correct way to
    upload N1MM QSOs to Club Log in real-time.  It listens on the same
    UDP port as our bridge, so we run it alongside us.

    If the binary is not present it is downloaded automatically on first run.
    The gateway is restarted automatically if it crashes.
    """

    def __init__(self, callsign: str, password: str,
                 n1mm_port: int = 12060,
                 rate: int = 30,
                 gateway_dir: str = ".",
                 enabled: bool = True,
                 db=None):
        super().__init__(daemon=True, name="GatewayManager")
        self.callsign    = callsign.upper()
        self.password    = password
        self.n1mm_port   = n1mm_port
        self.rate        = rate
        self.gateway_dir = gateway_dir
        self.enabled     = enabled
        self.db          = db       # LogDatabase reference for processing deletes
        self.watcher     = None     # set by main() after watcher is created
        self._proc: Optional[object] = None
        self._bin_path   = ""
        self.status      = "stopped"
        self.restarts    = 0
        self.last_error  = ""
        # For stats reporting (mirrors old uploader interface)
        self.uploaded    = 0
        self.errors      = 0

    def enqueue(self, qso, action="add"):
        pass  # Gateway handles this itself by listening on UDP

    def enqueue_delete(self, qso_id):
        pass  # Gateway handles deletes via UDP contactdelete packets

    def run(self):
        if not self.enabled:
            logging.info("Club Log Gateway disabled (no credentials)")
            self.status = "disabled"
            return

        # Download binary if needed
        self._bin_path = download_gateway(self.gateway_dir)
        if not self._bin_path:
            self.status = "error"
            self.last_error = "Could not download gateway binary"
            self.errors += 1
            return

        logging.info(f"Starting Club Log Gateway for {self.callsign} "
                     f"(rate={self.rate}s, port={self.n1mm_port})")

        while True:
            self._run_process()
            if not self.enabled:
                break
            self.restarts += 1
            self.errors   += 1
            logging.warning(f"Gateway exited — restarting in 10s "
                            f"(restart #{self.restarts})")
            time.sleep(10)

    def _run_process(self):
        import subprocess
        cmd = [
            self._bin_path,
            f"-mode=listener",
            f"-callsign={self.callsign}",
            f"-password={self.password}",
            f"-n1mmport={self.n1mm_port}",
            f"-rate={self.rate}",
        ]
        logging.debug(f"Gateway command: {' '.join(cmd[:-1])} -password=***")
        self.status = "running"
        try:
            self._proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                cwd=self.gateway_dir,
            )
            # Stream gateway output to our logger
            for line in self._proc.stdout:
                line = line.rstrip()
                if not line:
                    continue
                line_lower = line.lower()
                if any(w in line_lower for w in ("error", "fail", "denied", "forbidden")):
                    logging.error(f"[Gateway] {line}")
                    self.last_error = line
                    self.errors += 1
                elif "n1mm delete qso:" in line_lower:
                    # Gateway tells us exactly which call was deleted — act on it immediately
                    logging.info(f"[Gateway] {line}")
                    if self.db:
                        self._handle_gateway_delete(line)
                elif any(w in line_lower for w in ("upload", "qso", "sent", "ok", "success")):
                    logging.info(f"[Gateway] {line}")
                    self.uploaded += 1
                else:
                    logging.debug(f"[Gateway] {line}")
            self._proc.wait()
            rc = self._proc.returncode
            if rc != 0:
                self.last_error = f"Exited with code {rc}"
                logging.warning(f"Gateway exited with code {rc}")
            else:
                logging.info("Gateway exited cleanly")
        except FileNotFoundError:
            self.last_error = f"Binary not found: {self._bin_path}"
            logging.error(self.last_error)
        except Exception as e:
            self.last_error = str(e)
            logging.error(f"Gateway error: {e}")
        finally:
            self.status = "stopped"

    def _handle_gateway_delete(self, line: str):
        """Parse 'n1mm delete QSO: CALL on ...' from gateway stdout and remove from our DB.

        The gateway line format is:
          HH:MM:SS n1mm delete QSO: CALL on BAND MODE at YYYY-MM-DD HH:MM:SS
        We match on callsign + QSO date/time (within 90s for clock skew).
        If no timestamp match, fall back to removing the most recent QSO for that call.
        """
        import re as _re
        m = _re.search(
            r"n1mm delete qso:\s+([A-Z0-9/]+)\s+on\s+\S+\s+\S+\s+at\s+([\d\-]+\s+[\d:]+)",
            line, _re.IGNORECASE)
        if not m:
            logging.warning(f"Could not parse gateway delete line: {repr(line)}")
            return

        callsign = m.group(1).upper()
        ts_str   = m.group(2).strip()
        logging.info(f"Gateway delete signal: {callsign} at {ts_str}")

        try:
            from datetime import datetime, timezone as _tz
            qso_time = datetime.strptime(ts_str, "%Y-%m-%d %H:%M:%S").replace(tzinfo=_tz.utc)
        except ValueError:
            qso_time = None

        # Collect all QSOs for this callsign
        candidates = [q for q in self.db.all_qsos() if q.callsign == callsign]
        if not candidates:
            logging.warning(f"Delete for {callsign}: not found in dashboard (already gone?)")
            return

        # Try to match by timestamp first (within 90s)
        matched = []
        if qso_time:
            matched = [q for q in candidates
                       if abs((q.timestamp - qso_time).total_seconds()) <= 90]

        # Fall back: if only one QSO for this call, just delete it
        # If multiple and no timestamp match, delete the closest one
        if not matched:
            if len(candidates) == 1:
                matched = candidates
            else:
                matched = [min(candidates,
                               key=lambda q: abs((q.timestamp - qso_time).total_seconds())
                               if qso_time else 0)]

        for qso in matched:
            logging.info(f"Deleting {qso.callsign} (id={qso.id} ts={qso.timestamp}) from dashboard")
            self.db.delete(qso.id)
            # Also tombstone the watcher so it doesn't re-add from the gateway DB
            if self.watcher is not None:
                self.watcher._deleted_ids.add(qso.id)
                self.watcher._last_seen.pop(qso.id, None)

    def stop(self):
        self.enabled = False
        if self._proc and self._proc.poll() is None:
            self._proc.terminate()
            try:
                self._proc.wait(timeout=5)
            except Exception:
                self._proc.kill()


# Keep a type alias so the rest of the code using 'uploader' still works
ClubLogUploader = ClubLogGatewayManager


# ─────────────────────────────────────────────────────────────────────────────
# LOCAL ADIF FILE LOGGER
# ─────────────────────────────────────────────────────────────────────────────

class ADIFLogger:
    """Appends every QSO to a local ADIF file in real-time.

    File name pattern:  <callsign>_<YYYYMMDD>.adi   (rotates at midnight)
    A standard ADIF file header is written once when the file is created.
    Duplicate QSO IDs are silently ignored (safe to restart the bridge).
    """

    def __init__(self, directory: str, callsign: str, enabled: bool = True):
        self.directory  = directory
        self.callsign   = callsign.upper() if callsign else "LOG"
        self.enabled    = enabled
        self._lock      = threading.Lock()
        self._seen_ids: set = set()
        self._current_path  = ""
        self._current_date  = ""
        self.written    = 0

        if enabled:
            os.makedirs(directory, exist_ok=True)
            logging.info(f"ADIF log directory: {os.path.abspath(directory)}")

    def write(self, qso: QSO):
        """Append a single QSO to today's ADIF file."""
        if not self.enabled:
            return
        with self._lock:
            if qso.id and qso.id in self._seen_ids:
                return                          # already written (e.g. after restart)
            self._rotate_if_needed()
            adif_record = self._to_adif(qso)
            try:
                with open(self._current_path, "a", encoding="utf-8") as f:
                    f.write(adif_record + "\n")
                self._seen_ids.add(qso.id)
                self.written += 1
                logging.debug(f"ADIF written: {qso.callsign} → {self._current_path}")
            except OSError as e:
                logging.error(f"ADIF write error: {e}")

    def _rotate_if_needed(self):
        """Switch to a new file if the month has changed."""
        today = datetime.now(timezone.utc).strftime("%Y%m")
        if today != self._current_date:
            self._current_date = today
            filename = f"{self.callsign}_{today}.adi"
            self._current_path = os.path.join(self.directory, filename)
            if not os.path.exists(self._current_path):
                self._write_header()
                logging.info(f"New ADIF log file: {self._current_path}")
            else:
                # File exists from a previous run — load seen IDs to avoid dupes
                self._load_seen_ids()
                logging.info(f"Appending to existing ADIF log: {self._current_path}")

    def _write_header(self):
        now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
        header = (
            f"UDP Live Log ADIF Log\n"
            f"Station: {self.callsign}\n"
            f"Created: {now} UTC\n"
            f"<ADIF_VER:5>3.1.4\n"
            f"<PROGRAMID:18>N1MM-ClubLog-Bridge\n"
            f"<PROGRAMVERSION:3>1.0\n"
            f"<EOH>\n\n"
        )
        with open(self._current_path, "w", encoding="utf-8") as f:
            f.write(header)

    def _load_seen_ids(self):
        """Scan existing file for QSO IDs to prevent duplicates on restart."""
        try:
            with open(self._current_path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
            # Extract APP_N1MM_ID fields if present, otherwise count EOR markers
            import re as _re
            ids = _re.findall(r'<APP_N1MM_ID:[^>]+>([^<\n]+)', text, _re.IGNORECASE)
            self._seen_ids.update(ids)
            logging.debug(f"Loaded {len(ids)} existing QSO IDs from {self._current_path}")
        except OSError:
            pass

    @staticmethod
    def _to_adif(qso: QSO) -> str:
        """Convert QSO to a complete ADIF record."""
        def f(name: str, value: str) -> str:
            if not value:
                return ""
            return f"<{name}:{len(value)}>{value} "

        freq_mhz = f"{qso.freq_hz / 1_000_000:.4f}" if qso.freq_hz else ""
        date_str = qso.timestamp.strftime("%Y%m%d")
        time_str = qso.timestamp.strftime("%H%M%S")

        mode_map = {
            "USB": "SSB", "LSB": "SSB", "CW": "CW", "FM": "FM", "AM": "AM",
            "RTTY": "RTTY", "RTTYR": "RTTY", "FT8": "FT8", "FT4": "FT4",
            "JS8": "JS8CALL", "PSK31": "PSK31", "PSK63": "PSK63", "DIGI": "DIGI",
        }
        adif_mode    = mode_map.get(qso.mode.upper(), qso.mode)
        adif_submode = qso.mode.upper() if qso.mode.upper() in ("USB","LSB","FT8","FT4","JS8","RTTY","PSK31","PSK63") else ""

        record = (
            f(  "CALL",         qso.callsign)       +
            f(  "BAND",         qso.band)            +
            f(  "MODE",         adif_mode)           +
            f(  "SUBMODE",      adif_submode)        +
            f(  "QSO_DATE",     date_str)            +
            f(  "TIME_ON",      time_str)            +
            f(  "RST_SENT",     qso.rst_sent)        +
            f(  "RST_RCVD",     qso.rst_rcvd)        +
            f(  "FREQ",         freq_mhz)            +
            f(  "OPERATOR",     qso.operator)        +
            f(  "STATION_CALLSIGN", qso.station_callsign) +
            f(  "COMMENT",      qso.exchange)        +
            f(  "APP_N1MM_ID",  qso.id)              +
            "<EOR>"
        )
        return record.strip()

# ─────────────────────────────────────────────────────────────────────────────
# WEB DASHBOARD
# ─────────────────────────────────────────────────────────────────────────────

HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>UDP Live Log Dashboard</title>
<style>
  :root{--bg:#0d1117;--card:#161b22;--border:#30363d;--text:#e6edf3;
    --muted:#8b949e;--green:#3fb950;--blue:#58a6ff;--orange:#d29922;
    --red:#f85149;--purple:#bc8cff;}
  *{box-sizing:border-box;margin:0;padding:0}
  body{background:var(--bg);color:var(--text);font-family:"Segoe UI",system-ui,sans-serif;padding:16px}
  h1{font-size:1.5rem;margin-bottom:4px;color:var(--blue)}
  .subtitle{color:var(--muted);font-size:.85rem;margin-bottom:20px}
  .grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px;margin-bottom:20px}
  .stat-card{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:16px;text-align:center}
  .stat-num{font-size:2.2rem;font-weight:700;color:var(--green)}
  .stat-label{font-size:.8rem;color:var(--muted);margin-top:4px;text-transform:uppercase;letter-spacing:.05em}
  .panels{display:grid;grid-template-columns:1fr 1fr 1fr;gap:12px;margin-bottom:20px}
  @media(max-width:900px){.panels{grid-template-columns:1fr 1fr}}
  @media(max-width:600px){.panels{grid-template-columns:1fr}}
  .panel{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:16px}
  .panel h2{font-size:.95rem;color:var(--muted);margin-bottom:12px;text-transform:uppercase;letter-spacing:.06em}
  .bar-row{display:flex;align-items:center;margin-bottom:6px;gap:8px;font-size:.85rem}
  .bar-label{width:60px;text-align:right;color:var(--text);flex-shrink:0}
  .bar-track{flex:1;background:#21262d;border-radius:4px;height:16px;overflow:hidden}
  .bar-fill{height:100%;border-radius:4px;background:var(--blue);transition:width .4s}
  .bar-count{width:40px;color:var(--muted);font-size:.8rem}
  table{width:100%;border-collapse:collapse;font-size:.82rem}
  th{color:var(--muted);text-align:left;padding:4px 8px;border-bottom:1px solid var(--border);font-weight:500}
  td{padding:5px 8px;border-bottom:1px solid #21262d;color:var(--text)}
  tr:last-child td{border-bottom:none}
  .badge{display:inline-block;padding:1px 6px;border-radius:4px;font-size:.75rem;font-weight:600}
  .badge-cw{background:#1f3547;color:var(--blue)}
  .badge-ssb{background:#1f3829;color:var(--green)}
  .badge-digi{background:#2d1f47;color:var(--purple)}
  .rate-bar{display:flex;gap:3px;align-items:flex-end;height:60px;margin-top:8px}
  .rate-bucket{flex:1;background:var(--blue);border-radius:3px 3px 0 0;min-height:2px;transition:height .4s}
  .rate-labels{display:flex;justify-content:space-between;font-size:.7rem;color:var(--muted);margin-top:2px}
  .upload-status{font-size:.8rem;padding:6px 10px;border-radius:6px;margin-bottom:16px;display:inline-block}
  .status-ok{background:#1f3829;color:var(--green)}
  .status-err{background:#3d1f1f;color:var(--red)}
  .status-off{background:#21262d;color:var(--muted)}
  /* ── Version bar ── */
  .version-bar{background:#0d1117;border-bottom:1px solid var(--border);
    padding:4px 16px;font-size:.72rem;color:var(--muted);
    display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px}
  .version-tag{font-family:'Consolas','Cascadia Code',monospace;color:var(--green);font-weight:600}
  .build-info{font-family:'Consolas','Cascadia Code',monospace;color:var(--muted)}
  /* ── System stats footer ── */
  .sys-footer{margin-top:24px;border-top:1px solid var(--border);padding-top:16px}
  .sys-footer h2{font-size:.85rem;color:var(--muted);text-transform:uppercase;
    letter-spacing:.07em;margin-bottom:12px}
  .sys-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:10px;margin-bottom:12px}
  .sys-card{background:var(--card);border:1px solid var(--border);border-radius:8px;
    padding:12px 14px;display:flex;flex-direction:column;gap:4px}
  .sys-card-label{font-size:.68rem;color:var(--muted);text-transform:uppercase;letter-spacing:.07em}
  .sys-card-value{font-family:'Consolas','Cascadia Code',monospace;font-size:1.15rem;
    font-weight:600;color:var(--text)}
  .sys-card-sub{font-size:.7rem;color:var(--muted)}
  .sys-bar-wrap{height:4px;background:#21262d;border-radius:2px;margin-top:4px;overflow:hidden}
  .sys-bar{height:100%;border-radius:2px;transition:width .6s}
  .bar-ok{background:var(--green)}
  .bar-warn{background:var(--orange)}
  .bar-crit{background:var(--red)}
  .sys-net{background:var(--card);border:1px solid var(--border);border-radius:8px;padding:12px 14px}
  .sys-net table{font-size:.78rem}
  .sys-net th{font-size:.68rem}
  .throttle-warn{background:#3d2a00;border:1px solid var(--orange);border-radius:6px;
    padding:6px 12px;font-size:.78rem;color:var(--orange);margin-bottom:10px;display:none}
  .pi-model-bar{font-size:.75rem;color:var(--muted);margin-bottom:10px;
    font-family:'Consolas','Cascadia Code',monospace}
  .sys-upd{font-size:.66rem;color:var(--muted);text-align:right;margin-top:6px}
  .val-green{color:var(--green)} .val-orange{color:var(--orange)} .val-red{color:var(--red)}
  .sys-os-row{display:flex;gap:16px;flex-wrap:wrap;margin-bottom:12px;font-size:.75rem;color:var(--muted)}
  .sys-os-row span{font-family:'Consolas','Cascadia Code',monospace;color:var(--text)}
  .nav-btn{display:inline-block;padding:5px 14px;background:var(--card);border:1px solid var(--border);border-radius:6px;text-decoration:none;font-size:.82rem;vertical-align:middle;white-space:nowrap}
  .nav-btn:hover{border-color:#58a6ff;background:#1c2128}
  #last-update{font-size:.75rem;color:var(--muted)}
  .vibe-footer{text-align:center;padding:14px;font-size:.75rem;color:var(--muted);
    border-top:1px solid var(--border);margin-top:28px}
  .vibe-footer a{color:var(--green);text-decoration:none;font-weight:600}
  .vibe-footer a:hover{text-decoration:underline}
</style>
</head>
<body>
<div class="version-bar">
  <div>
    <span class="build-info">UDP Live Log</span>
    &nbsp;
    <span class="version-tag" id="vbar-version">v—</span>
  </div>
  <div class="build-info" id="vbar-host">—</div>
</div>
<div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;margin-bottom:6px">
  <div style="display:flex;align-items:center;gap:16px">
    <h1 style="margin:0">📡 UDP Live Log</h1>
    <div id="station-callsign" style="font-size:2rem;font-weight:800;color:#3fb950;letter-spacing:.04em;line-height:1">—</div>
  </div>
  <div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap">
    <div id="upload-status" class="upload-status status-off">Club Log: connecting…</div>
    <div id="adif-status" class="upload-status status-off">ADIF: loading…</div>
    <a href="/logs"  class="nav-btn" style="color:#58a6ff">📁 Logs</a>
    <a href="/stats" class="nav-btn" style="color:#39d353">📊 Stats</a>
    <a href="/tools" class="nav-btn" style="color:#d29922">🛠 Tools</a>
    <a href="/admin" class="nav-btn" style="color:#bc8cff">⚙ Admin</a>
    <a href="/about" class="nav-btn" style="color:#39d4d4">ℹ About</a>
  </div>
</div>
<div class="subtitle" style="margin-bottom:16px">Real-time statistics • <span id="last-update" style="color:var(--muted)"></span></div>

<div class="grid" id="stat-grid">
  <div class="stat-card"><div class="stat-num" id="s-total">—</div><div class="stat-label">Total QSOs</div></div>
  <div class="stat-card"><div class="stat-num" id="s-rate">—</div><div class="stat-label">Rate/hr (last 60m)</div></div>
  <div class="stat-card"><div class="stat-num" id="s-unique">—</div><div class="stat-label">Unique Calls</div></div>
  <div class="stat-card"><div class="stat-num" id="s-first">—</div><div class="stat-label">First QSO</div></div>
  <div class="stat-card"><div class="stat-num" id="s-last">—</div><div class="stat-label">Last QSO</div></div>
</div>

<div class="panels">
  <div class="panel">
    <h2>By Band</h2>
    <div id="band-bars"></div>
  </div>
  <div class="panel">
    <h2>By Mode</h2>
    <div id="mode-bars"></div>
  </div>
  <div class="panel">
    <h2>By Operator</h2>
    <div id="op-bars"></div>
  </div>
</div>

<div class="panels">
  <div class="panel" style="grid-column:1/3">
    <h2>QSO Rate — Last 60 minutes (10-min buckets)</h2>
    <div class="rate-bar" id="rate-chart"></div>
    <div class="rate-labels"><span>-60m</span><span>-50m</span><span>-40m</span><span>-30m</span><span>-20m</span><span>-10m</span></div>
  </div>
  <div class="panel">
    <h2>Recent QSOs</h2>
    <table><thead><tr>
      <th>UTC</th><th>Call</th><th>Band</th><th>Freq</th><th>Mode</th>
    </tr></thead>
    <tbody id="recent-body"></tbody></table>
  </div>
</div>

<script>
const BADGE = {CW:"badge-cw",SSB:"badge-ssb",USB:"badge-ssb",LSB:"badge-ssb"};
function badgeClass(m){return BADGE[m]||"badge-digi";}

function bars(containerId, counts, colorVar){
  const el = document.getElementById(containerId);
  if(!el) return;
  const max = Math.max(...Object.values(counts),1);
  el.innerHTML = Object.entries(counts).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`
    <div class="bar-row">
      <span class="bar-label">${k}</span>
      <div class="bar-track"><div class="bar-fill" style="width:${Math.round(v/max*100)}%;background:var(${colorVar})"></div></div>
      <span class="bar-count">${v}</span>
    </div>`).join("");
}

function refresh(){
  fetch("/api/stats").then(r=>r.json()).then(d=>{
    if(d.callsign){document.getElementById("station-callsign").textContent=d.callsign;}
    document.getElementById("s-total").textContent  = d.total;
    document.getElementById("s-rate").textContent   = d.rate_per_hour;
    document.getElementById("s-unique").textContent = d.unique_calls;
    document.getElementById("s-first").textContent  = d.first_qso ? d.first_qso.slice(11,16)+"Z" : "—";
    document.getElementById("s-last").textContent   = d.last_qso  ? d.last_qso.slice(11,16)+"Z"  : "—";
    document.getElementById("last-update").textContent = "Updated: "+d.server_time;

    bars("band-bars", d.band_counts, "--blue");
    bars("mode-bars", d.mode_counts, "--green");
    bars("op-bars",   d.op_counts,   "--orange");

    // Rate chart
    const rc = document.getElementById("rate-chart");
    const bmax = Math.max(...d.rate_buckets, 1);
    rc.innerHTML = d.rate_buckets.map(v=>`
      <div class="rate-bucket" style="height:${Math.max(4,Math.round(v/bmax*56))}px" title="${v} QSOs"></div>
    `).join("");

    // Recent QSOs
    const tbody = document.getElementById("recent-body");
    tbody.innerHTML = d.recent.map(q=>`
      <tr>
        <td>${q.timestamp.slice(11,16)}Z</td>
        <td><strong>${q.callsign}</strong></td>
        <td>${q.band}</td>
        <td style="color:var(--muted);font-size:.82rem">${q.freq_mhz||""}</td>
        <td><span class="badge ${badgeClass(q.mode)}">${q.mode}</span></td>
      </tr>`).join("");
  }).catch(()=>{});

  fetch("/api/adif").then(r=>r.json()).then(d=>{
    const el = document.getElementById("adif-status");
    if(!d.enabled){
      el.className="upload-status status-off";
      el.textContent="ADIF: disabled";
    } else {
      el.className="upload-status status-ok";
      el.textContent=`ADIF: ✓ ${d.written} written → ${d.current_file}`;
    }
  }).catch(()=>{});

  fetch("/api/uploader").then(r=>r.json()).then(d=>{
    const el = document.getElementById("upload-status");
    if(!d.enabled){
      el.className="upload-status status-off";
      el.textContent="Club Log Gateway: disabled (set password in config)";
    } else if(d.status==="error"||d.last_error.toLowerCase().includes("forbidden")||d.last_error.toLowerCase().includes("auth")){
      el.className="upload-status status-err";
      el.textContent=`Club Log Gateway: error — ${d.last_error}`;
    } else if(d.status==="running"){
      el.className="upload-status status-ok";
      el.textContent=`Club Log Gateway: ✓ running (${d.uploaded} sent, ${d.restarts} restarts)`;
    } else {
      el.className="upload-status status-off";
      el.textContent=`Club Log Gateway: ${d.status||"starting…"}`;
    }
  }).catch(()=>{});
}

refresh();
setInterval(refresh, 5000);



// ── System stats ─────────────────────────────────────────────────────────
function barColor(pct){
  return pct < 70 ? "var(--green)" : pct < 85 ? "var(--orange)" : "var(--red)";
}
function tempColor(t){
  return t == null ? "var(--muted)" : t < 60 ? "var(--green)" : t < 75 ? "var(--orange)" : "var(--red)";
}
function setBar(id, pct, col){
  const el = document.getElementById(id);
  if(el){ el.style.width = Math.min(100, Math.max(0, pct)) + "%";
          el.style.background = col || barColor(pct); }
}
function refreshSys(){
  fetch("/api/system").then(r=>r.json()).then(s=>{
    // Version bar
    const vv = document.getElementById("vbar-version");
    if(vv) vv.textContent = "v" + (s.version || "—");
    const vh = document.getElementById("vbar-host");
    if(vh) vh.textContent = (s.hostname||"") + (s.pi_model ? " · "+s.pi_model : "");
    // Header meta
    const setText = (id,v) => { const e=document.getElementById(id); if(e) e.textContent=v||"—"; };
    setText("sys-hostname", s.hostname);
    setText("sys-model",    s.pi_model);
    setText("sys-os",       s.os_name);
    setText("sys-arch",     s.arch);
    setText("sys-uptime",   s.uptime);
    // Throttle
    const thr = document.getElementById("sys-throttle");
    if(thr) thr.style.display = s.throttled ? "block" : "none";
    // CPU
    if(s.cpu_pct != null){
      const e=document.getElementById("sys-cpu-pct");
      if(e){ e.textContent=s.cpu_pct;
        e.className = s.cpu_pct<70?"val-green":s.cpu_pct<85?"val-orange":"val-red"; }
      setBar("sys-cpu-bar", s.cpu_pct);
    }
    setText("sys-cpu-cores", s.cpu_count ? s.cpu_count+" cores" : "—");
    setText("sys-cpu-freq",  s.cpu_freq_mhz ? s.cpu_freq_mhz+" MHz" : "—");
    // Temperature
    const te=document.getElementById("sys-temp");
    if(s.cpu_temp != null){
      if(te){ te.textContent=s.cpu_temp; te.style.color=tempColor(s.cpu_temp); }
      const ts=document.getElementById("sys-temp-status");
      if(ts){ ts.textContent=s.cpu_temp<50?"Cool ✓":s.cpu_temp<70?"Normal":s.cpu_temp<80?"Warm ⚠":"HOT ⛔";
              ts.style.color=tempColor(s.cpu_temp); }
      setBar("sys-temp-bar", (s.cpu_temp/85)*100, tempColor(s.cpu_temp));
    } else {
      if(te) te.textContent="N/A";
      setText("sys-temp-status","Sensor unavailable");
    }
    // Memory
    if(s.mem_pct != null){
      const me=document.getElementById("sys-mem-pct");
      if(me){ me.textContent=s.mem_pct;
        me.className=s.mem_pct<70?"val-green":s.mem_pct<85?"val-orange":"val-red"; }
      setBar("sys-mem-bar", s.mem_pct);
    }
    setText("sys-mem-used",  s.mem_used_mb);
    setText("sys-mem-total", s.mem_total_mb);
    // Swap
    setText("sys-swap-used",  s.swap_used_mb  ?? "N/A");
    setText("sys-swap-total", s.swap_total_mb || "0");
    if(s.swap_total_mb>0) setBar("sys-swap-bar", Math.round(100*(s.swap_used_mb||0)/s.swap_total_mb));
    // Disk
    if(s.disk_pct != null){
      const de=document.getElementById("sys-disk-pct");
      if(de){ de.textContent=s.disk_pct;
        de.className=s.disk_pct<70?"val-green":s.disk_pct<85?"val-orange":"val-red"; }
      setBar("sys-disk-bar", s.disk_pct);
    }
    setText("sys-disk-used",  s.disk_used_gb);
    setText("sys-disk-total", s.disk_total_gb);
    // Load
    const loadEl=document.getElementById("sys-load1");
    if(loadEl){ loadEl.textContent=s.load_1??0;
      const cores=s.cpu_count||1;
      loadEl.className=s.load_1<cores?"val-green":s.load_1<cores*2?"val-orange":"val-red"; }
    setText("sys-load5",  s.load_5);
    setText("sys-load15", s.load_15);
    // Network
    const netTb=document.getElementById("sys-net-tbody");
    if(netTb){
      netTb.innerHTML = (s.network&&s.network.length)
        ? s.network.map(n=>`<tr>
            <td style="font-family:monospace;color:var(--blue)">${n.iface}</td>
            <td style="font-family:monospace">${n.ip||"—"}</td>
            <td style="color:var(--green)">${n.rx_mb} MB</td>
            <td style="color:var(--orange)">${n.tx_mb} MB</td>
          </tr>`).join("")
        : `<tr><td colspan="4" style="color:var(--muted)">No interfaces</td></tr>`;
    }
    const upd=document.getElementById("sys-upd-time");
    if(upd) upd.textContent="Last updated: "+new Date().toLocaleTimeString("en-GB",{hour12:false});
  }).catch(()=>{});
}
refreshSys();
setInterval(refreshSys, 10000);

</script>
<!-- ═══════════════════════ SYSTEM STATS FOOTER ══════════════════════════ -->
<div class="sys-footer">
  <h2>🖥 System — <span id="sys-hostname" style="color:var(--text)">—</span></h2>
  <div class="sys-os-row">
    <div>Model: <span id="sys-model">—</span></div>
    <div>OS: <span id="sys-os">—</span></div>
    <div>Arch: <span id="sys-arch">—</span></div>
    <div>Uptime: <span id="sys-uptime">—</span></div>
  </div>
  <div id="sys-throttle" class="throttle-warn">
    ⚠ Pi throttling detected — check power supply / temperature
  </div>
  <div class="sys-grid">
    <!-- CPU -->
    <div class="sys-card">
      <div class="sys-card-label">CPU Usage</div>
      <div class="sys-card-value"><span id="sys-cpu-pct">—</span><span style="font-size:.8rem;color:var(--muted)">%</span></div>
      <div class="sys-card-sub"><span id="sys-cpu-cores">—</span> cores · <span id="sys-cpu-freq">—</span></div>
      <div class="sys-bar-wrap"><div class="sys-bar" id="sys-cpu-bar" style="width:0%"></div></div>
    </div>
    <!-- CPU Temp -->
    <div class="sys-card">
      <div class="sys-card-label">CPU Temperature</div>
      <div class="sys-card-value"><span id="sys-temp">—</span><span style="font-size:.8rem;color:var(--muted)">°C</span></div>
      <div class="sys-card-sub" id="sys-temp-status">—</div>
      <div class="sys-bar-wrap"><div class="sys-bar" id="sys-temp-bar" style="width:0%"></div></div>
    </div>
    <!-- Memory -->
    <div class="sys-card">
      <div class="sys-card-label">Memory</div>
      <div class="sys-card-value"><span id="sys-mem-pct">—</span><span style="font-size:.8rem;color:var(--muted)">%</span></div>
      <div class="sys-card-sub"><span id="sys-mem-used">—</span> / <span id="sys-mem-total">—</span> MB</div>
      <div class="sys-bar-wrap"><div class="sys-bar" id="sys-mem-bar" style="width:0%"></div></div>
    </div>
    <!-- Swap -->
    <div class="sys-card">
      <div class="sys-card-label">Swap</div>
      <div class="sys-card-value"><span id="sys-swap-used">—</span> <span style="font-size:.8rem;color:var(--muted)">MB</span></div>
      <div class="sys-card-sub">of <span id="sys-swap-total">—</span> MB total</div>
      <div class="sys-bar-wrap"><div class="sys-bar" id="sys-swap-bar" style="width:0%"></div></div>
    </div>
    <!-- Disk -->
    <div class="sys-card">
      <div class="sys-card-label">Disk (/)</div>
      <div class="sys-card-value"><span id="sys-disk-pct">—</span><span style="font-size:.8rem;color:var(--muted)">%</span></div>
      <div class="sys-card-sub"><span id="sys-disk-used">—</span> / <span id="sys-disk-total">—</span> GB</div>
      <div class="sys-bar-wrap"><div class="sys-bar" id="sys-disk-bar" style="width:0%"></div></div>
    </div>
    <!-- Load -->
    <div class="sys-card">
      <div class="sys-card-label">Load Average</div>
      <div class="sys-card-value" id="sys-load1">—</div>
      <div class="sys-card-sub">5m: <span id="sys-load5">—</span> · 15m: <span id="sys-load15">—</span></div>
    </div>
  </div>
  <!-- Network -->
  <div class="sys-net">
    <table>
      <thead><tr>
        <th>Interface</th><th>IP Address</th>
        <th>RX</th><th>TX</th>
      </tr></thead>
      <tbody id="sys-net-tbody"></tbody>
    </table>
  </div>
  <div class="sys-upd">System stats refresh every 10s · <span id="sys-upd-time">—</span></div>
</div>
<div class="vibe-footer">Vibe Coded de <a href="https://www.ww2dx.com" target="_blank">WW2DX</a></div>
</body>
</html>

"""

class DashboardHandler(BaseHTTPRequestHandler):
    db: LogDatabase = None
    uploader: ClubLogUploader = None
    adif_logger: "ADIFLogger" = None

    def log_message(self, format, *args):
        pass  # suppress default access log

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self._send(200, "text/html", HTML_TEMPLATE.encode())
        elif self.path == "/api/stats":
            body = json.dumps(self.db.stats()).encode()
            self._send(200, "application/json", body)
        elif self.path == "/api/uploader":
            up = self.uploader
            info = {
                "enabled":    up.enabled,
                "uploaded":   up.uploaded,
                "errors":     up.errors,
                "last_error": up.last_error,
                "status":     getattr(up, "status", "unknown"),
                "restarts":   getattr(up, "restarts", 0),
            }
            self._send(200, "application/json", json.dumps(info).encode())
        elif self.path == "/api/adif":
            al = self.adif_logger
            info = {
                "enabled":      al.enabled if al else False,
                "written":      al.written if al else 0,
                "current_file": os.path.basename(al._current_path) if al and al._current_path else "",
                "directory":    os.path.abspath(al.directory) if al else "",
            }
            self._send(200, "application/json", json.dumps(info).encode())
        elif self.path == "/logs":
            self._send(200, "text/html", self._build_logs_page().encode())
        elif self.path.startswith("/logs/download/"):
            self._serve_adif_download()
        elif self.path == "/about":
            self._send(200, "text/html", self._build_about_page().encode())
        elif self.path == "/tools":
            self._send(200, "text/html", self._build_tools_page().encode())
        elif self.path == "/api/system":
            self._send(200, "application/json",
                       json.dumps(_get_system_stats()).encode())
        elif self.path == "/api/system":
            self._send(200, "application/json",
                       json.dumps(_get_system_stats()).encode())
        elif self.path == "/stats":
            self._send(200, "text/html", self._build_stats_page().encode())
        elif self.path == "/api/stats/detail":
            body = json.dumps(self._build_detailed_stats()).encode()
            self._send(200, "application/json", body)
        elif self.path == "/admin":
            self._send(200, "text/html", self._build_admin_page().encode())
        elif self.path == "/api/config":
            self._send(200, "application/json",
                       json.dumps(self._read_config_for_api()).encode())
        elif self.path == "/api/config":
            try:
                data = json.loads(rawbody.decode("utf-8"))
                result = self._save_config(data)
                self._send(200, "application/json", json.dumps(result).encode())
            except Exception as e:
                self._send(400, "application/json",
                           json.dumps({"ok": False, "message": str(e)}).encode())
        else:
            self._send(404, "text/plain", b"Not Found")

    def do_POST(self):
        length  = int(self.headers.get("Content-Length", 0))
        rawbody = self.rfile.read(length) if length else b""

        if self.path == "/api/reset":
            self.db.reset_stats()
            self._send(200, "application/json",
                       json.dumps({"ok": True, "message": "Stats reset successfully"}).encode())

        elif self.path == "/api/import":
            ct = self.headers.get("Content-Type", "")
            if "multipart/form-data" in ct:
                result = self._handle_multipart_import(ct, rawbody)
                self._send(200, "application/json", json.dumps(result).encode())
            elif "application/x-www-form-urlencoded" in ct:
                params   = urllib_parse.parse_qs(rawbody.decode("utf-8", errors="replace"))
                filepath = params.get("filepath", [""])[0].strip()
                if not filepath:
                    self._send(400, "application/json",
                               json.dumps({"ok": False, "message": "No filepath provided"}).encode())
                    return
                if not os.path.isfile(filepath):
                    self._send(404, "application/json",
                               json.dumps({"ok": False, "message": f"File not found: {filepath}"}).encode())
                    return
                imported, skipped, errors = self.db.import_adif(filepath)
                msg = f"Imported {imported} QSOs, {skipped} duplicates skipped"
                if errors:
                    msg += f" ({len(errors)} errors)"
                self._send(200, "application/json",
                           json.dumps({"ok": True, "message": msg,
                                       "imported": imported, "skipped": skipped}).encode())
            else:
                self._send(400, "application/json",
                           json.dumps({"ok": False, "message": "Unsupported content type"}).encode())

        elif self.path == "/api/config":
            try:
                data = json.loads(rawbody.decode("utf-8"))
                result = self._save_config(data)
                self._send(200, "application/json", json.dumps(result).encode())
            except Exception as e:
                self._send(400, "application/json",
                           json.dumps({"ok": False, "message": str(e)}).encode())

        else:
            self._send(404, "text/plain", b"Not Found")

    def _handle_multipart_import(self, content_type: str, body: bytes) -> dict:
        """Parse a multipart/form-data file upload and import the ADIF."""
        import tempfile as _tmp
        # Extract boundary
        bm = re.search(r'boundary=([^;\s]+)', content_type)
        if not bm:
            return {"ok": False, "message": "Missing multipart boundary"}
        bval = bm.group(1).strip()
        bval = bval.strip('"').strip("'")
        boundary = ("--" + bval).encode()

        # Split on boundary and find the file part
        parts = body.split(boundary)
        for part in parts:
            if b'Content-Disposition' not in part:
                continue
            # Split headers from body
            split = part.find(b'\r\n\r\n')
            if split == -1:
                split = part.find(b'\n\n')
                header_raw = part[:split].decode("utf-8", errors="replace")
                file_data  = part[split+2:].rstrip(b'\r\n--')
            else:
                header_raw = part[:split].decode("utf-8", errors="replace")
                file_data  = part[split+4:].rstrip(b'\r\n--')

            if 'filename=' not in header_raw:
                continue

            # Write to a temp file and import
            suffix = ".adi"
            fm = re.search(r'filename=["\']?([^"\'\r\n]+)', header_raw)
            if fm:
                suffix = os.path.splitext(fm.group(1))[1] or ".adi"
            try:
                with _tmp.NamedTemporaryFile(delete=False, suffix=suffix) as tf:
                    tf.write(file_data)
                    tmppath = tf.name
                imported, skipped, errors = self.db.import_adif(tmppath)
                os.unlink(tmppath)
                msg = f"Imported {imported} QSOs, {skipped} duplicates skipped"
                if errors:
                    msg += f" ({len(errors)} parse errors)"
                return {"ok": True, "message": msg,
                        "imported": imported, "skipped": skipped}
            except OSError as e:
                return {"ok": False, "message": f"File error: {e}"}

        return {"ok": False, "message": "No file found in upload"}

    def _list_adif_files(self):
        """Return list of dicts for every .adi file in the ADIF directory."""
        al = self.adif_logger
        if not al or not al.enabled or not al.directory:
            return []
        files = []
        try:
            for fname in sorted(os.listdir(al.directory), reverse=True):
                if fname.lower().endswith(".adi"):
                    fpath = os.path.join(al.directory, fname)
                    stat  = os.stat(fpath)
                    # Count QSOs by counting <EOR> markers
                    try:
                        with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                            qso_count = f.read().upper().count("<EOR>")
                    except OSError:
                        qso_count = 0
                    files.append({
                        "name":     fname,
                        "size":     stat.st_size,
                        "modified": datetime.fromtimestamp(stat.st_mtime, tz=timezone.utc)
                                           .strftime("%Y-%m-%d %H:%M UTC"),
                        "qsos":     qso_count,
                        "current":  fname == os.path.basename(al._current_path),
                    })
        except OSError:
            pass
        return files

    # ── Config path helper ───────────────────────────────────────────────────
    @property
    def _config_path(self):
        return getattr(DashboardHandler, "_cfg_path", "config.ini")

    # ── Multi-account config helpers ─────────────────────────────────────────

    def _load_accounts(self, cfg) -> list:
        """Return list of account dicts from [account.CALL] sections."""
        accounts = []
        for sec in cfg.sections():
            if sec.lower().startswith("account."):
                call = sec[len("account."):].upper()
                accounts.append({
                    "callsign": call,
                    "password": cfg.get(sec, "password", fallback=""),
                    "section":  sec,
                })
        if not accounts and cfg.has_section("clublog"):
            cs = cfg.get("clublog", "callsign", fallback="").upper()
            pw = cfg.get("clublog", "password", fallback="")
            if cs:
                accounts.append({"callsign": cs, "password": pw, "section": "clublog"})
        return accounts

    def _active_callsign(self, cfg) -> str:
        if cfg.has_section("clublog"):
            active = cfg.get("clublog", "active", fallback="").upper()
            if active:
                return active
            return cfg.get("clublog", "callsign", fallback="").upper()
        return ""

    def _read_config_for_api(self) -> dict:
        cfg = configparser.ConfigParser()
        cfg.read(self._config_path)
        def g(sec, key, fallback=""):
            return cfg.get(sec, key, fallback=fallback) if cfg.has_section(sec) else fallback
        accounts  = self._load_accounts(cfg)
        active_cs = self._active_callsign(cfg)
        return {
            "active":      active_cs,
            "accounts":    accounts,
            "web_port":    g("web",  "port",       fallback=str(DEFAULT_WEB_PORT)),
            "adif_dir":    g("adif", "directory",  fallback="adif_logs"),
            "state_file":  g("adif", "state_file", fallback="log_state.json"),
            "config_path": os.path.abspath(self._config_path),
        }

    def _save_config(self, data: dict) -> dict:
        cfg = configparser.ConfigParser()
        cfg.read(self._config_path)
        def ensure(sec):
            if not cfg.has_section(sec): cfg.add_section(sec)

        action = data.get("action", "")

        if action == "switch":
            new_cs = data.get("callsign", "").upper().strip()
            if not new_cs:
                return {"ok": False, "message": "No callsign provided"}
            ensure("clublog")
            cfg.set("clublog", "active",   new_cs)
            cfg.set("clublog", "callsign", new_cs)
            sec = f"account.{new_cs}"
            if cfg.has_section(sec):
                cfg.set("clublog", "password", cfg.get(sec, "password", fallback=""))
            with open(self._config_path, "w") as f:
                cfg.write(f)
            self.db.callsign = new_cs
            logging.info(f"Switched active account to {new_cs}")
            return {"ok": True, "message": f"Switched to {new_cs}. Restart the bridge to upload under this callsign."}

        if action in ("save_account", ""):
            cs = data.get("callsign", "").upper().strip()
            pw = data.get("password", "").strip()
            if not cs:
                return {"ok": False, "message": "Callsign is required"}
            sec = f"account.{cs}"
            ensure(sec)
            cfg.set(sec, "callsign", cs)
            cfg.set(sec, "password", pw)
            active = self._active_callsign(cfg)
            if not active or active == cs:
                ensure("clublog")
                cfg.set("clublog", "active",   cs)
                cfg.set("clublog", "callsign", cs)
                cfg.set("clublog", "password", pw)
                self.db.callsign = cs
            with open(self._config_path, "w") as f:
                cfg.write(f)
            logging.info(f"Saved account {cs}")
            return {"ok": True, "message": f"Account {cs} saved."}

        if action == "delete_account":
            cs = data.get("callsign", "").upper().strip()
            sec = f"account.{cs}"
            if cfg.has_section(sec):
                cfg.remove_section(sec)
            if self._active_callsign(cfg) == cs:
                accounts = self._load_accounts(cfg)
                ensure("clublog")
                if accounts:
                    cfg.set("clublog", "active",   accounts[0]["callsign"])
                    cfg.set("clublog", "callsign", accounts[0]["callsign"])
                    cfg.set("clublog", "password", accounts[0]["password"])
                else:
                    cfg.set("clublog", "active",   "")
                    cfg.set("clublog", "callsign", "")
            with open(self._config_path, "w") as f:
                cfg.write(f)
            logging.info(f"Deleted account {cs}")
            return {"ok": True, "message": f"Account {cs} deleted."}

        # save_settings action or fallthrough
        ensure("web")
        if "web_port"   in data: cfg.set("web",  "port",       str(int(data["web_port"])))
        ensure("adif")
        if "adif_dir"   in data: cfg.set("adif", "directory",  data["adif_dir"].strip())
        if "state_file" in data: cfg.set("adif", "state_file", data["state_file"].strip())
        with open(self._config_path, "w") as f:
            cfg.write(f)
        return {"ok": True, "message": "Settings saved. Restart the bridge to apply changes."}

    def _build_admin_page(self) -> str:
        d    = self._read_config_for_api()
        active   = d["active"]
        accounts = d["accounts"]
        port = d["web_port"]; adir = d["adif_dir"]
        sf   = d["state_file"]; cp  = d["config_path"]

        # Build account rows HTML
        if accounts:
            rows_html = ""
            for acc in accounts:
                cs  = acc["callsign"]
                is_active = (cs == active)
                active_badge = '<span style="background:#1f3829;color:#3fb950;padding:2px 8px;border-radius:4px;font-size:.72rem;font-weight:700;margin-left:6px">ACTIVE</span>' if is_active else ""
                switch_btn   = "" if is_active else f'''<button class="act-btn btn-switch" onclick="switchAccount(\'{cs}\')">▶ Use</button>'''
                rows_html += f"""
        <div class="acc-row" id="row-{cs}">
          <div class="acc-info">
            <span class="acc-call">{cs}</span>{active_badge}
          </div>
          <div class="acc-actions">
            {switch_btn}
            <button class="act-btn btn-edit"   onclick="editAccount('{cs}')">✏ Edit</button>
            <button class="act-btn btn-delete" onclick="deleteAccount('{cs}')"
              {"disabled" if is_active else ""}>✕</button>
          </div>
        </div>"""
        else:
            rows_html = '<p style="color:var(--muted);font-size:.85rem;padding:10px 0">No accounts yet — add one below.</p>'

        return f"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Admin — UDP Live Log</title>
<style>
:root{{--bg:#0d1117;--card:#161b22;--border:#30363d;--text:#e6edf3;
  --muted:#8b949e;--green:#3fb950;--blue:#58a6ff;--orange:#d29922;--red:#f85149;--purple:#bc8cff}}
*{{box-sizing:border-box;margin:0;padding:0}}
body{{background:var(--bg);color:var(--text);font-family:"Segoe UI",system-ui,sans-serif;
  padding:28px 24px;max-width:680px;margin:0 auto}}
h1{{font-size:1.4rem;color:var(--blue);margin-bottom:6px}}
h2{{font-size:.82rem;color:var(--muted);text-transform:uppercase;letter-spacing:.08em;
  margin-bottom:14px;padding-bottom:8px;border-bottom:1px solid var(--border)}}
.back{{display:inline-flex;align-items:center;gap:5px;margin-bottom:22px;color:var(--muted);
  text-decoration:none;font-size:.85rem;padding:5px 12px;border:1px solid var(--border);
  border-radius:6px;background:var(--card)}}
.back:hover{{color:var(--blue);border-color:var(--blue)}}
.note{{font-size:.78rem;color:var(--muted);margin-bottom:22px;line-height:1.5}}
.note code{{font-family:monospace;color:var(--orange);word-break:break-all}}
.section{{background:var(--card);border:1px solid var(--border);border-radius:10px;
  padding:20px;margin-bottom:14px}}
.field{{margin-bottom:14px}}
label{{display:block;font-size:.82rem;color:var(--muted);margin-bottom:5px;font-weight:500}}
input[type=text],input[type=password],input[type=number]{{
  width:100%;background:#0d1117;border:1px solid var(--border);border-radius:6px;
  color:var(--text);padding:9px 11px;font-size:.9rem;outline:none;transition:border .15s}}
input:focus{{border-color:var(--blue)}}
.hint{{font-size:.73rem;color:var(--muted);margin-top:4px;line-height:1.4}}
.warn{{font-size:.73rem;color:var(--orange);margin-top:4px}}
.btn{{padding:9px 20px;border-radius:7px;border:none;cursor:pointer;
  font-size:.88rem;font-weight:700}}
.btn-save{{background:#238636;color:#fff}}.btn-save:hover{{background:#2ea043}}
.btn-add{{background:#1c2128;color:var(--blue);border:1px solid var(--blue)}}
.btn-add:hover{{background:#1f3547}}
#msg{{margin-top:14px;padding:11px 15px;border-radius:7px;display:none;font-size:.85rem}}
.msg-ok{{background:#1f3829;color:var(--green);display:block!important}}
.msg-err{{background:#3d1f1f;color:var(--red);display:block!important}}
.pw-wrap{{position:relative}}.pw-wrap input{{padding-right:68px}}
.pw-toggle{{position:absolute;right:9px;top:50%;transform:translateY(-50%);
  background:none;border:none;color:var(--muted);cursor:pointer;font-size:.76rem;
  padding:3px 7px;border-radius:4px}}.pw-toggle:hover{{color:var(--blue);background:#21262d}}
/* Account list */
.acc-row{{display:flex;align-items:center;justify-content:space-between;
  padding:10px 12px;border:1px solid var(--border);border-radius:8px;margin-bottom:8px;
  background:#0d1117;gap:10px}}
.acc-call{{font-size:1rem;font-weight:700;letter-spacing:.04em}}
.acc-info{{display:flex;align-items:center;gap:4px;min-width:0;flex:1}}
.acc-actions{{display:flex;gap:6px;flex-shrink:0}}
.act-btn{{padding:4px 10px;border-radius:5px;border:1px solid var(--border);
  background:var(--card);color:var(--text);cursor:pointer;font-size:.78rem;white-space:nowrap}}
.act-btn:hover{{border-color:var(--blue);color:var(--blue)}}
.btn-switch{{border-color:var(--green);color:var(--green)}}
.btn-switch:hover{{background:#1f3829}}
.btn-edit{{border-color:var(--orange);color:var(--orange)}}
.btn-edit:hover{{background:#2d1f00}}
.btn-delete{{border-color:#444;color:var(--red)}}
.btn-delete:hover:not(:disabled){{background:#3d1f1f;border-color:var(--red)}}
.btn-delete:disabled{{opacity:.3;cursor:not-allowed}}
/* Form card */
.form-card{{background:#0d1117;border:1px solid var(--blue);border-radius:10px;
  padding:18px;margin-top:14px;display:none}}
.form-card.open{{display:block}}
.form-card h3{{font-size:.82rem;color:var(--blue);text-transform:uppercase;
  letter-spacing:.07em;margin-bottom:14px}}
.form-row{{display:flex;gap:10px;align-items:flex-end}}
.form-row .field{{flex:1;margin-bottom:0}}
  .vibe-footer{{text-align:center;padding:14px;font-size:.75rem;color:var(--muted);border-top:1px solid var(--border);margin-top:28px}}
  .vibe-footer a{{color:var(--green);text-decoration:none;font-weight:600}}
  .vibe-footer a:hover{{text-decoration:underline}}
</style></head><body>
<a href="/" class="back">← Dashboard</a>
<h1>⚙ Admin Settings</h1>
<p class="note">Config file: <code>{cp}</code></p>

<!-- ── Accounts ─────────────────────────────────────────────────── -->
<div class="section">
  <h2>Club Log Accounts</h2>
  <div id="acc-list">{rows_html}
  </div>
  <button class="btn btn-add" onclick="openForm(null)" style="margin-top:6px">＋ Add Account</button>

  <div class="form-card" id="acc-form">
    <h3 id="form-title">New Account</h3>
    <input type="hidden" id="f-orig-call">
    <div class="form-row">
      <div class="field">
        <label>Callsign</label>
        <input type="text" id="f-callsign" placeholder="WW2DX" autocomplete="off"
               oninput="this.value=this.value.toUpperCase()">
      </div>
      <div class="field" style="flex:2">
        <label>Club Log App Password</label>
        <div class="pw-wrap">
          <input type="password" id="f-password" placeholder="407-Xl908-Rm690-…" autocomplete="off">
          <button class="pw-toggle" onclick="togglePw(this)">Show</button>
        </div>
      </div>
    </div>
    <div class="hint" style="margin:8px 0 14px">
      App password from clublog.org → Settings → App Passwords
    </div>
    <div style="display:flex;gap:8px">
      <button class="btn btn-save" onclick="saveAccount()">💾 Save</button>
      <button class="btn" style="background:#21262d;color:var(--muted)" onclick="closeForm()">Cancel</button>
    </div>
  </div>
</div>

<!-- ── Web Dashboard ─────────────────────────────────────────────── -->
<div class="section">
  <h2>Web Dashboard</h2>
  <div class="field">
    <label>Dashboard Port</label>
    <input type="number" id="f-port" value="{port}" min="1024" max="65535" style="width:140px">
    <div class="warn">⚠ Requires bridge restart to take effect.</div>
  </div>
</div>

<!-- ── Storage ───────────────────────────────────────────────────── -->
<div class="section">
  <h2>Logging &amp; Storage</h2>
  <div class="field">
    <label>ADIF Log Directory</label>
    <input type="text" id="f-adif-dir" value="{adir}" placeholder="adif_logs">
    <div class="hint">Monthly <code style="color:var(--muted)">&lt;call&gt;_YYYYMM.adi</code> files are saved here.</div>
  </div>
  <div class="field">
    <label>State File</label>
    <input type="text" id="f-state-file" value="{sf}" placeholder="log_state.json">
    <div class="hint">Preserves QSO stats across reboots.</div>
  </div>
</div>

<button class="btn btn-save" onclick="saveSettings()">💾 Save Settings</button>
<div id="msg"></div>

<script>
function togglePw(btn){{
  const inp=document.getElementById("f-password");
  inp.type=inp.type==="password"?"text":"password";
  btn.textContent=inp.type==="password"?"Show":"Hide";
}}

function flash(txt, ok){{
  const m=document.getElementById("msg");
  m.textContent=txt; m.className=ok?"msg-ok":"msg-err";
  setTimeout(()=>{{m.className="";m.style.display="none";}},4000);
}}

function api(data, cb){{
  fetch("/api/config",{{method:"POST",headers:{{"Content-Type":"application/json"}},
    body:JSON.stringify(data)}})
    .then(r=>r.json()).then(cb)
    .catch(e=>flash("Network error: "+e, false));
}}

// ── Account form ──────────────────────────────────────────────────
function openForm(cs){{
  const form=document.getElementById("acc-form");
  document.getElementById("form-title").textContent = cs ? "Edit Account" : "New Account";
  document.getElementById("f-orig-call").value = cs||"";
  document.getElementById("f-callsign").value  = cs||"";
  document.getElementById("f-password").value  = "";
  form.classList.add("open");
  document.getElementById("f-callsign").focus();
  if(cs) loadPassword(cs);
}}

function loadPassword(cs){{
  fetch("/api/config").then(r=>r.json()).then(d=>{{
    const acc=d.accounts.find(a=>a.callsign===cs);
    if(acc) document.getElementById("f-password").value=acc.password;
  }});
}}

function closeForm(){{
  document.getElementById("acc-form").classList.remove("open");
}}

function editAccount(cs){{ openForm(cs); }}

function saveAccount(){{
  const cs=document.getElementById("f-callsign").value.trim().toUpperCase();
  const pw=document.getElementById("f-password").value.trim();
  if(!cs){{flash("Callsign is required",false);return;}}
  api({{action:"save_account",callsign:cs,password:pw}}, d=>{{
    flash(d.message,d.ok);
    if(d.ok){{closeForm();setTimeout(()=>location.reload(),800);}}
  }});
}}

function deleteAccount(cs){{
  if(!confirm("Delete account "+cs+"? This cannot be undone.")) return;
  api({{action:"delete_account",callsign:cs}}, d=>{{
    flash(d.message,d.ok);
    if(d.ok) setTimeout(()=>location.reload(),800);
  }});
}}

function switchAccount(cs){{
  if(!confirm("Switch active account to "+cs+"?\nThe dashboard will show stats for "+cs+" immediately.\nRestart the bridge to upload under this callsign.")) return;
  api({{action:"switch",callsign:cs}}, d=>{{
    flash(d.message,d.ok);
    if(d.ok) setTimeout(()=>location.reload(),1000);
  }});
}}

// ── General settings ──────────────────────────────────────────────
function saveSettings(){{
  api({{
    action:"save_settings",
    web_port:   document.getElementById("f-port").value.trim(),
    adif_dir:   document.getElementById("f-adif-dir").value.trim(),
    state_file: document.getElementById("f-state-file").value.trim(),
  }}, d=>flash(d.message,d.ok));
}}
</script>
</body></html>"""



    # ─────────────────────────────────────────────────────────────────────────
    # DETAILED STATS API + PAGE
    # ─────────────────────────────────────────────────────────────────────────

    # Compact DXCC prefix table: prefix -> (entity, continent, ITU, CQ, lat, lon)
    # ~340 most common prefixes — covers >99% of real QSOs
    _DXCC = {
        "AA":"United States,NA,7,5,38,-97","AB":"United States,NA,7,5,38,-97",
        "AC":"United States,NA,7,5,38,-97","AD":"United States,NA,7,5,38,-97",
        "AE":"United States,NA,7,5,38,-97","AF":"United States,NA,7,5,38,-97",
        "AG":"United States,NA,7,5,38,-97","AH":"United States,NA,7,5,38,-97",
        "AI":"United States,NA,7,5,38,-97","AJ":"United States,NA,7,5,38,-97",
        "AK":"United States,NA,7,5,38,-97","AL":"United States,NA,7,5,38,-97",
        "AM":"Spain,EU,14,14,40,-4","AN":"Spain,EU,14,14,40,-4",
        "AO":"Spain,EU,14,14,40,-4","AP":"Pakistan,AS,21,21,30,70",
        "C2":"Nauru,OC,65,31,-1,167","C3":"Andorra,EU,14,14,42.5,1.5",
        "C5":"The Gambia,AF,35,35,13,-15","C6":"Bahamas,NA,11,8,24,-76",
        "C9":"Mozambique,AF,53,37,-18,35","CA":"Chile,SA,14,12,-30,-71",
        "CB":"Chile,SA,14,12,-30,-71","CC":"Chile,SA,14,12,-30,-71",
        "CE":"Chile,SA,14,12,-30,-71","CM":"Cuba,NA,11,8,22,-79",
        "CO":"Cuba,NA,11,8,22,-79","CP":"Bolivia,SA,10,10,-17,-65",
        "CT":"Portugal,EU,14,14,39,-8","CT3":"Madeira,AF,33,33,32,-17",
        "CU":"Azores,EU,14,14,38,-27","CX":"Uruguay,SA,14,13,-33,-56",
        "CY0":"Sable Is.,NA,9,5,44,-60","CY9":"St Paul Is.,NA,9,5,47,-60",
        "D2":"Angola,AF,52,36,-12,18","D4":"Cape Verde,AF,35,35,16,-24",
        "D6":"Comoros,AF,53,39,-12,44","DA":"Germany,EU,14,14,51,10",
        "DB":"Germany,EU,14,14,51,10","DC":"Germany,EU,14,14,51,10",
        "DD":"Germany,EU,14,14,51,10","DE":"Germany,EU,14,14,51,10",
        "DF":"Germany,EU,14,14,51,10","DG":"Germany,EU,14,14,51,10",
        "DH":"Germany,EU,14,14,51,10","DI":"Germany,EU,14,14,51,10",
        "DJ":"Germany,EU,14,14,51,10","DK":"Germany,EU,14,14,51,10",
        "DL":"Germany,EU,14,14,51,10","DM":"Germany,EU,14,14,51,10",
        "DN":"Germany,EU,14,14,51,10","DO":"Germany,EU,14,14,51,10",
        "DP":"Germany,EU,14,14,51,10","DQ":"Germany,EU,14,14,51,10",
        "DR":"Germany,EU,14,14,51,10","DT":"South Korea,AS,25,25,37,127",
        "DU":"Philippines,OC,27,27,13,122","DX":"Philippines,OC,27,27,13,122",
        "E3":"Eritrea,AF,48,34,15,39","E4":"Palestine,AS,20,20,32,35",
        "E5":"N Cook Is.,OC,62,32,-10,-161","E6":"Niue,OC,62,32,-19,-170",
        "E7":"Bosnia-Herzegovina,EU,15,15,44,17","EA":"Spain,EU,14,14,40,-4",
        "EA6":"Balearic Is.,EU,14,14,39,3","EA8":"Canary Is.,AF,33,33,28,-15",
        "EA9":"Ceuta & Melilla,AF,33,33,35,-5","EI":"Ireland,EU,14,27,53,-8",
        "EK":"Armenia,AS,21,21,40,45","EL":"Liberia,AF,35,35,6,-9",
        "EP":"Iran,AS,21,21,32,53","ER":"Moldova,EU,16,16,47,29",
        "ES":"Estonia,EU,15,18,59,25","ET":"Ethiopia,AF,48,34,9,39",
        "EU":"Belarus,EU,16,16,54,28","EV":"Belarus,EU,16,16,54,28",
        "EW":"Belarus,EU,16,16,54,28","EX":"Kyrgyzstan,AS,17,17,42,74",
        "EY":"Tajikistan,AS,17,21,39,71","EZ":"Turkmenistan,AS,17,21,38,58",
        "F":"France,EU,14,14,46,2","FG":"Guadeloupe,NA,11,8,16,-61",
        "FH":"Mayotte,AF,53,39,-13,45","FK":"New Caledonia,OC,56,28,-21,165",
        "FM":"Martinique,NA,11,8,14,-61","FO":"French Polynesia,OC,63,31,-15,-140",
        "FP":"St Pierre & Miquelon,NA,9,5,47,-56","FR":"Reunion,AF,53,39,-21,55",
        "FT5W":"Crozet Is.,AF,68,38,-46,52","FT5X":"Kerguelen Is.,AF,68,29,-49,70",
        "FT5Z":"Amsterdam Is.,AF,68,29,-38,77","FW":"Wallis & Futuna,OC,62,32,-14,-177",
        "FY":"French Guiana,SA,12,9,4,-53","G":"England,EU,14,27,52,-2",
        "GB":"England,EU,14,27,52,-2","GD":"Isle of Man,EU,14,27,54,-4",
        "GI":"Northern Ireland,EU,14,27,55,-6","GJ":"Jersey,EU,14,27,49,-2",
        "GM":"Scotland,EU,14,27,57,-4","GU":"Guernsey,EU,14,27,49,-3",
        "GW":"Wales,EU,14,27,52,-4","H4":"Solomon Is.,OC,51,28,-9,160",
        "H40":"Temotu Prov.,OC,51,28,-11,166","HA":"Hungary,EU,15,15,47,19",
        "HB":"Switzerland,EU,14,14,47,8","HB0":"Liechtenstein,EU,14,14,47,9.5",
        "HC":"Ecuador,SA,10,10,-2,-78","HH":"Haiti,NA,11,8,19,-72",
        "HI":"Dominican Republic,NA,11,8,19,-70","HK":"Colombia,SA,9,9,4,-72",
        "HL":"South Korea,AS,25,25,37,127","HP":"Panama,NA,11,7,9,-79",
        "HR":"Honduras,NA,11,7,14,-87","HS":"Thailand,AS,26,26,15,101",
        "HV":"Vatican City,EU,15,33,42,12","HZ":"Saudi Arabia,AS,21,21,24,45",
        "I":"Italy,EU,15,33,42,13","IS":"Sardinia,EU,15,33,40,9",
        "J2":"Djibouti,AF,48,34,12,43","J3":"Grenada,NA,11,8,12,-62",
        "J5":"Guinea-Bissau,AF,35,35,12,-15","J6":"St Lucia,NA,11,8,14,-61",
        "J7":"Dominica,NA,11,8,15,-61","J8":"St Vincent,NA,11,8,13,-61",
        "JA":"Japan,AS,25,25,36,138","JD1":"Minami Torishima,OC,90,27,24,154",
        "JT":"Mongolia,AS,23,23,47,104","JW":"Svalbard,EU,18,40,78,15",
        "JX":"Jan Mayen,EU,18,40,71,-8","JY":"Jordan,AS,20,20,31,36",
        "K":"United States,NA,7,5,38,-97","KA":"United States,NA,7,5,38,-97",
        "KB":"United States,NA,7,5,38,-97","KC":"United States,NA,7,5,38,-97",
        "KD":"United States,NA,7,5,38,-97","KE":"United States,NA,7,5,38,-97",
        "KF":"United States,NA,7,5,38,-97","KG":"United States,NA,7,5,38,-97",
        "KH0":"Mariana Is.,OC,64,27,15,146","KH1":"Baker & Howland,OC,61,31,0,-176",
        "KH2":"Guam,OC,64,27,13,145","KH3":"Johnston Is.,OC,61,31,17,-169",
        "KH4":"Midway Is.,OC,61,31,28,-177","KH5":"Palmyra & Jarvis,OC,61,31,6,-162",
        "KH6":"Hawaii,OC,61,31,21,-157","KH7":"Kure Is.,OC,61,31,29,-178",
        "KH8":"American Samoa,OC,62,32,-14,-170","KH9":"Wake Is.,OC,65,31,19,167",
        "KI":"United States,NA,7,5,38,-97","KJ":"United States,NA,7,5,38,-97",
        "KK":"United States,NA,7,5,38,-97","KL":"Alaska,NA,1,1,64,-153",
        "KM":"United States,NA,7,5,38,-97","KN":"United States,NA,7,5,38,-97",
        "KP1":"Navassa Is.,NA,11,8,18,-75","KP2":"US Virgin Is.,NA,11,8,18,-65",
        "KP4":"Puerto Rico,NA,11,8,18,-67","KP5":"Desecheo Is.,NA,11,8,18,-67",
        "KQ":"United States,NA,7,5,38,-97","KR":"United States,NA,7,5,38,-97",
        "KS":"United States,NA,7,5,38,-97","KT":"United States,NA,7,5,38,-97",
        "KU":"United States,NA,7,5,38,-97","KV":"United States,NA,7,5,38,-97",
        "KW":"United States,NA,7,5,38,-97","KX":"United States,NA,7,5,38,-97",
        "KY":"United States,NA,7,5,38,-97","KZ":"United States,NA,7,5,38,-97",
        "LA":"Norway,EU,18,14,60,10","LU":"Argentina,SA,14,13,-34,-64",
        "LX":"Luxembourg,EU,14,14,49,6","LY":"Lithuania,EU,15,15,56,24",
        "LZ":"Bulgaria,EU,20,20,43,25","OA":"Peru,SA,10,10,-10,-76",
        "OD":"Lebanon,AS,20,20,34,36","OE":"Austria,EU,15,15,47,14",
        "OF":"Finland,EU,18,18,64,26","OG":"Finland,EU,18,18,64,26",
        "OH":"Finland,EU,18,18,64,26","OH0":"Aland Is.,EU,18,18,60,20",
        "OJ":"Finland,EU,18,18,64,26","OJ0":"Market Reef,EU,18,18,60,19",
        "OK":"Czech Republic,EU,15,15,50,15","OM":"Slovak Republic,EU,15,15,49,19",
        "ON":"Belgium,EU,14,14,51,4","OX":"Greenland,NA,5,40,72,-40",
        "OY":"Faroe Is.,EU,18,14,62,-7","OZ":"Denmark,EU,18,14,56,10",
        "P2":"Papua New Guinea,OC,51,28,-6,147","P29":"Papua New Guinea,OC,51,28,-6,147",
        "P4":"Aruba,SA,9,9,12,-70","PA":"Netherlands,EU,14,14,52,5",
        "PB":"Netherlands,EU,14,14,52,5","PC":"Netherlands,EU,14,14,52,5",
        "PD":"Netherlands,EU,14,14,52,5","PE":"Netherlands,EU,14,14,52,5",
        "PF":"Netherlands,EU,14,14,52,5","PG":"Netherlands,EU,14,14,52,5",
        "PH":"Netherlands,EU,14,14,52,5","PI":"Netherlands,EU,14,14,52,5",
        "PJ2":"Curacao,SA,9,9,12,-69","PJ4":"Bonaire,SA,9,9,12,-68",
        "PJ5":"Sint Eustatius,NA,11,8,17,-63","PJ7":"Sint Maarten,NA,11,8,18,-63",
        "PY":"Brazil,SA,11,11,-10,-53","PZ":"Suriname,SA,9,9,4,-56",
        "R":"Russia,EU,16,16,60,100","RA":"Russia,EU,16,16,60,100",
        "RK":"Russia,EU,16,16,60,100","RM":"Russia,EU,16,16,60,100",
        "RN":"Russia,EU,16,16,60,100","RO":"Russia,EU,16,16,60,100",
        "RQ":"Russia,EU,16,16,60,100","RT":"Russia,EU,16,16,60,100",
        "RU":"Russia,EU,16,16,60,100","RV":"Russia,EU,16,16,60,100",
        "RW":"Russia,EU,16,16,60,100","RX":"Russia,EU,16,16,60,100",
        "RY":"Russia,EU,16,16,60,100","RZ":"Russia,EU,16,16,60,100",
        "S0":"Western Sahara,AF,33,33,25,-13","S2":"Bangladesh,AS,26,26,24,90",
        "S5":"Slovenia,EU,15,15,46,15","S7":"Seychelles,AF,53,39,-5,56",
        "S9":"Sao Tome & Principe,AF,52,36,0,7","SM":"Sweden,EU,18,18,60,15",
        "SP":"Poland,EU,15,15,52,20","ST":"Sudan,AF,48,34,15,32",
        "SU":"Egypt,AF,34,33,26,28","SV":"Greece,EU,20,20,39,22",
        "SV5":"Dodecanese,EU,20,20,36,27","SV9":"Crete,EU,20,20,35,25",
        "SV/A":"Mount Athos,EU,20,20,40,24","T2":"Tuvalu,OC,65,31,-8,179",
        "T30":"W Kiribati,OC,65,31,1,173","T31":"C Kiribati,OC,61,31,-3,-172",
        "T32":"E Kiribati,OC,61,31,2,-157","T33":"Banaba Is.,OC,65,31,-1,170",
        "T5":"Somalia,AF,48,34,2,46","T7":"San Marino,EU,15,33,44,12",
        "T8":"Palau,OC,64,27,7,134","T9":"Bosnia-Herzegovina,EU,15,15,44,17",
        "TA":"Turkey,AS,20,20,39,35","TF":"Iceland,EU,17,40,65,-18",
        "TG":"Guatemala,NA,11,7,15,-91","TI":"Costa Rica,NA,11,7,10,-84",
        "TJ":"Cameroon,AF,47,36,4,12","TK":"Corsica,EU,15,15,42,9",
        "TL":"Central Africa,AF,47,36,7,21","TN":"Rep of Congo,AF,52,36,-1,15",
        "TR":"Gabon,AF,52,36,-1,12","TT":"Chad,AF,47,35,15,19",
        "TU":"Cote d'Ivoire,AF,35,35,6,-6","TY":"Benin,AF,35,35,9,2",
        "TZ":"Mali,AF,35,35,17,-4","UA":"Russia,EU,16,16,60,100",
        "UB":"Russia,EU,16,16,60,100","UC":"Russia,EU,16,16,60,100",
        "UD":"Russia,EU,16,16,60,100","UE":"Russia,EU,16,16,60,100",
        "UF":"Russia,EU,16,16,60,100","UG":"Russia,EU,16,16,60,100",
        "UH":"Russia,EU,16,16,60,100","UI":"Russia,EU,16,16,60,100",
        "UJ":"Uzbekistan,AS,17,21,41,64","UK":"Uzbekistan,AS,17,21,41,64",
        "UL":"Kazakhstan,AS,17,17,48,68","UM":"Uzbekistan,AS,17,21,41,64",
        "UN":"Kazakhstan,AS,17,17,48,68","UO":"Uzbekistan,AS,17,21,41,64",
        "UP":"Kazakhstan,AS,17,17,48,68","UR":"Ukraine,EU,16,16,49,32",
        "UX":"Ukraine,EU,16,16,49,32","UY":"Ukraine,EU,16,16,49,32",
        "UZ":"Ukraine,EU,16,16,49,32","V2":"Antigua & Barbuda,NA,11,8,17,-62",
        "V3":"Belize,NA,11,7,17,-89","V4":"St Kitts & Nevis,NA,11,8,17,-63",
        "V5":"Namibia,AF,57,38,-22,17","V6":"Micronesia,OC,65,27,7,151",
        "V7":"Marshall Is.,OC,65,31,7,171","V8":"Brunei,OC,54,28,5,115",
        "VE":"Canada,NA,4,5,56,-96","VA":"Canada,NA,4,5,56,-96",
        "VB":"Canada,NA,4,5,56,-96","VC":"Canada,NA,4,5,56,-96",
        "VD":"Canada,NA,4,5,56,-96","VF":"Canada,NA,4,5,56,-96",
        "VG":"Canada,NA,4,5,56,-96","VK":"Australia,OC,55,29,-27,134",
        "VO":"Canada,NA,4,5,56,-96","VP2E":"Anguilla,NA,11,8,18,-63",
        "VP2M":"Montserrat,NA,11,8,17,-62","VP2V":"Brit Virgin Is.,NA,11,8,18,-64",
        "VP5":"Turks & Caicos Is.,NA,11,8,22,-72","VP6":"Pitcairn Is.,OC,63,32,-25,-130",
        "VP8":"Falkland Is.,SA,16,13,-52,-59","VP9":"Bermuda,NA,11,5,32,-65",
        "VQ9":"Chagos Is.,AF,41,39,-7,72","VR":"Hong Kong,AS,24,24,22,114",
        "VS6":"Hong Kong,AS,24,24,22,114","VU":"India,AS,22,26,23,80",
        "VY1":"Yukon,NA,1,1,63,-136","VY2":"Prince Edward Is.,NA,5,9,46,-63",
        "W":"United States,NA,7,5,38,-97","WA":"United States,NA,7,5,38,-97",
        "WB":"United States,NA,7,5,38,-97","WC":"United States,NA,7,5,38,-97",
        "WD":"United States,NA,7,5,38,-97","WE":"United States,NA,7,5,38,-97",
        "WF":"United States,NA,7,5,38,-97","WG":"United States,NA,7,5,38,-97",
        "WH":"United States,NA,7,5,38,-97","WI":"United States,NA,7,5,38,-97",
        "WJ":"United States,NA,7,5,38,-97","WK":"United States,NA,7,5,38,-97",
        "WL":"United States,NA,7,5,38,-97","WM":"United States,NA,7,5,38,-97",
        "WN":"United States,NA,7,5,38,-97","WO":"United States,NA,7,5,38,-97",
        "WP3":"Puerto Rico,NA,11,8,18,-67","WP4":"Puerto Rico,NA,11,8,18,-67",
        "WQ":"United States,NA,7,5,38,-97","WR":"United States,NA,7,5,38,-97",
        "WS":"United States,NA,7,5,38,-97","WT":"United States,NA,7,5,38,-97",
        "WU":"United States,NA,7,5,38,-97","WV":"United States,NA,7,5,38,-97",
        "WW":"United States,NA,7,5,38,-97","WX":"United States,NA,7,5,38,-97",
        "WY":"United States,NA,7,5,38,-97","WZ":"United States,NA,7,5,38,-97",
        "XE":"Mexico,NA,11,6,24,-104","XF4":"Revillagigedo,NA,11,7,19,-111",
        "XT":"Burkina Faso,AF,35,35,12,-1","XU":"Cambodia,AS,26,26,12,105",
        "XV":"Vietnam,AS,26,26,16,108","XW":"Laos,AS,26,26,18,103",
        "XX9":"Macao,AS,24,24,22,113","XY":"Myanmar,AS,26,26,20,96",
        "XZ":"Myanmar,AS,26,26,20,96","YA":"Afghanistan,AS,21,21,34,66",
        "YB":"Indonesia,OC,54,28,-6,107","YI":"Iraq,AS,21,21,33,44",
        "YJ":"Vanuatu,OC,56,28,-16,167","YK":"Syria,AS,20,20,35,38",
        "YL":"Latvia,EU,15,15,57,25","YN":"Nicaragua,NA,11,7,13,-85",
        "YO":"Romania,EU,20,20,46,25","YS":"El Salvador,NA,11,7,14,-89",
        "YU":"Serbia,EU,15,15,44,21","YV":"Venezuela,SA,9,9,8,-66",
        "Z2":"Zimbabwe,AF,53,38,-20,30","Z3":"North Macedonia,EU,15,15,42,22",
        "Z6":"Kosovo,EU,15,15,42,21","Z8":"South Sudan,AF,48,34,7,30",
        "ZA":"Albania,EU,15,15,41,20","ZB":"Gibraltar,EU,14,14,36,-5",
        "ZC4":"UK Sov Base Areas,AS,20,20,35,33","ZD7":"St Helena,AF,66,36,-16,-6",
        "ZD8":"Ascension Is.,AF,66,36,-8,-14","ZD9":"Tristan da Cunha,AF,66,38,-37,-12",
        "ZF":"Cayman Is.,NA,11,8,19,-81","ZK3":"Tokelau,OC,62,31,-9,-172",
        "ZL":"New Zealand,OC,60,32,-41,174","ZL7":"Chatham Is.,OC,60,32,-44,-177",
        "ZL8":"Kermadec Is.,OC,60,32,-29,-178","ZL9":"Auckland & Campbell,OC,60,32,-52,169",
        "ZP":"Paraguay,SA,11,11,-23,-58","ZS":"South Africa,AF,57,38,-29,25",
        "ZS8":"Prince Edward & Marion,AF,57,38,-47,38",
    }

    def _lookup_dxcc(self, callsign: str) -> dict:
        """Look up DXCC entity for a callsign using prefix matching."""
        # Strip portable/mobile suffixes after last slash if they're short (e.g. /P /M /QRP)
        call = callsign.upper().strip()
        parts = call.split("/")
        # Use the longest part as the main call
        main = max(parts, key=len)

        # Try progressively shorter prefixes
        for length in range(min(len(main), 5), 0, -1):
            pfx = main[:length]
            if pfx in self._DXCC:
                fields = self._DXCC[pfx].split(",")
                return {
                    "entity": fields[0], "continent": fields[1],
                    "itu": int(fields[2]), "cq": int(fields[3]),
                    "lat": float(fields[4]), "lon": float(fields[5]),
                }
        return {"entity": "Unknown", "continent": "?", "itu": 0, "cq": 0, "lat": 0.0, "lon": 0.0}


    # ─────────────────────────────────────────────────────────────────────────
    # DETAILED STATS  (replaces _build_detailed_stats + _build_stats_page)
    # ─────────────────────────────────────────────────────────────────────────

    def _build_detailed_stats(self) -> dict:
        """Compute detailed contest statistics from in-memory QSOs."""
        import math
        from collections import defaultdict

        qsos = self.db.all_qsos()
        now  = datetime.now(timezone.utc)

        EMPTY = {
            "total":0,"unique_calls":0,"dupes":0,"dupe_list":[],
            "dxcc_count":0,"continent_count":0,"cq_zone_count":0,"itu_zone_count":0,
            "avg_rate":0,"best_1min":0,"best_10min":0,"best_30min":0,
            "best_60min":0,"best_60min_at":"","best_120min":0,
            "op_time_min":0,"break_time_min":0,"first_qso":"","last_qso":"",
            "max_streak":0,"call_length_dist":{},"prefix_count":0,
            "dxcc":[],"continents":{},"cont_by_band":{},"dxcc_by_band":{},
            "dxcc_by_mode":{},"dxcc_first_time":[],"cq_zones":{},"itu_zones":{},
            "band_mode":{},"band_time_min":{},"modes":{},"prefixes":[],
            "band_changes_total":0,"band_changes_by_hour":[],"band_seq":[],
            "breaks":[],"hourly":[],"hourly_by_band":{},"by_hour_of_day":[0]*24,
            "by_day":{},"top_calls":[],"map_points":[],"beam_headings":{},
            "qso_rate_by_min":[],"qsos":[],"callsign":self.db.callsign,
        }
        if not qsos:
            return EMPTY

        qsos_sorted = sorted(qsos, key=lambda q: q.timestamp)
        first_ts = qsos_sorted[0].timestamp
        last_ts  = qsos_sorted[-1].timestamp

        # ── Callsign / prefix / dupe analysis ────────────────────────────────
        seen_calls      = {}        # call -> first QSO index
        dupe_list       = []
        call_len_dist   = defaultdict(int)
        prefixes        = set()

        dxcc_map        = {}
        dxcc_by_band    = defaultdict(lambda: defaultdict(int))   # entity -> band -> n
        dxcc_by_mode    = defaultdict(lambda: defaultdict(int))   # entity -> mode -> n
        dxcc_first_seen = {}                                      # entity -> ts (first QSO)
        cont_map        = defaultdict(int)
        cont_by_band    = defaultdict(lambda: defaultdict(int))   # cont -> band -> n
        cq_map          = defaultdict(int)
        itu_map         = defaultdict(int)
        band_mode       = defaultdict(lambda: defaultdict(int))
        band_qso_times  = defaultdict(list)   # band -> list of timestamps
        modes_total     = defaultdict(int)
        by_hour_day     = [0]*24
        by_day          = defaultdict(int)
        map_points      = {}
        top_calls_c     = defaultdict(int)
        beam_hdg        = defaultdict(list)   # band -> list of (bearing, call)
        streak_days     = []
        # station lat/lon for beam heading (approx from callsign lookup of own call)
        OWN_LAT, OWN_LON = 38.0, -97.0   # default US; override from config if available

        for idx_q, q in enumerate(qsos_sorted):
            call = q.callsign.upper()
            band = q.band or "?"
            mode = (q.mode or "?").upper()

            # Dupes
            if call in seen_calls:
                dupe_list.append({"call": call, "band": band, "mode": mode,
                                  "ts": q.timestamp.strftime("%H:%M"),
                                  "date": q.timestamp.strftime("%Y-%m-%d")})
            else:
                seen_calls[call] = idx_q

            top_calls_c[call] += 1

            # Call length
            base = call.replace("/P","").replace("/M","").replace("/QRP","")
            base = base.split("/")[-1] if "/" in base else base
            call_len_dist[len(base)] += 1

            # Prefix (up to 3 chars before digit or all if no digit)
            import re as _re
            pm = _re.match(r"([A-Z]{1,3}\d)", base)
            if pm: prefixes.add(pm.group(1))

            # DXCC
            info = self._lookup_dxcc(call)
            entity = info["entity"]
            dxcc_map[entity] = dxcc_map.get(entity, 0) + 1
            dxcc_by_band[entity][band] += 1
            dxcc_by_mode[entity][mode] += 1
            if entity not in dxcc_first_seen:
                dxcc_first_seen[entity] = q.timestamp
            cont_map[info["continent"]] += 1
            cont_by_band[info["continent"]][band] += 1
            if info["cq"]:  cq_map[str(info["cq"])]  += 1
            if info["itu"]: itu_map[str(info["itu"])] += 1

            band_mode[band][mode] += 1
            band_qso_times[band].append(q.timestamp)
            modes_total[mode] += 1
            by_hour_day[q.timestamp.hour] += 1
            day_key = q.timestamp.strftime("%Y-%m-%d")
            by_day[day_key] += 1
            streak_days.append(day_key)

            # Map point
            if info["lat"] or info["lon"]:
                if entity not in map_points:
                    map_points[entity] = {"lat": info["lat"], "lon": info["lon"],
                                          "continent": info["continent"],
                                          "cq": info["cq"], "count": 0, "calls": []}
                map_points[entity]["count"] += 1
                if call not in map_points[entity]["calls"]:
                    map_points[entity]["calls"].append(call)

            # Beam heading (great-circle bearing from own station)
            if info["lat"] and info["lon"]:
                try:
                    lat1, lon1 = math.radians(OWN_LAT), math.radians(OWN_LON)
                    lat2, lon2 = math.radians(info["lat"]), math.radians(info["lon"])
                    dlon = lon2 - lon1
                    x = math.sin(dlon)*math.cos(lat2)
                    y = math.cos(lat1)*math.sin(lat2) - math.sin(lat1)*math.cos(lat2)*math.cos(dlon)
                    bearing = (math.degrees(math.atan2(x, y)) + 360) % 360
                    beam_hdg[band].append(int(bearing))
                except Exception:
                    pass

        # ── Operating time / break analysis ──────────────────────────────────
        GAP_THRESH = 30   # minutes gap = break
        op_time_min   = 0
        break_time_min = 0
        breaks = []
        for i in range(1, len(qsos_sorted)):
            gap = (qsos_sorted[i].timestamp - qsos_sorted[i-1].timestamp).total_seconds() / 60
            if gap >= GAP_THRESH:
                breaks.append({
                    "from": qsos_sorted[i-1].timestamp.strftime("%Y-%m-%d %H:%M"),
                    "to":   qsos_sorted[i].timestamp.strftime("%Y-%m-%d %H:%M"),
                    "duration_min": int(gap),
                })
                break_time_min += gap
            else:
                op_time_min += gap
        total_elapsed = (last_ts - first_ts).total_seconds() / 60
        op_time_min = max(1, total_elapsed - break_time_min)

        # ── Band changes ──────────────────────────────────────────────────────
        band_seq = []
        band_changes_total = 0
        band_changes_by_hour = [0]*24
        prev_band = None
        for q in qsos_sorted:
            b = q.band or "?"
            if prev_band is not None and b != prev_band:
                band_changes_total += 1
                band_changes_by_hour[q.timestamp.hour] += 1
                band_seq.append({"from": prev_band, "to": b,
                                 "ts": q.timestamp.strftime("%H:%M"),
                                 "date": q.timestamp.strftime("%Y-%m-%d")})
            prev_band = b

        # ── Rate analysis ─────────────────────────────────────────────────────
        ts_list = [q.timestamp.timestamp() for q in qsos_sorted]

        def best_rate(window_sec):
            best = 0
            best_at = ""
            for i, t0 in enumerate(ts_list):
                t1 = t0 + window_sec
                cnt = sum(1 for t in ts_list if t0 <= t < t1)
                if cnt > best:
                    best = cnt
                    best_at = qsos_sorted[i].timestamp.strftime("%H:%M")
            return best, best_at

        best_1, _    = best_rate(60)
        best_10, _   = best_rate(600)
        best_30, _   = best_rate(1800)
        best_60, b60at = best_rate(3600)
        best_120, _  = best_rate(7200)
        avg_rate     = round(len(qsos_sorted) / max(1, op_time_min / 60), 1)

        # QSO rate per minute (sliding 60s buckets for sparkline)
        qso_rate_by_min = []
        if qsos_sorted:
            t0 = int(first_ts.timestamp())
            t1 = int(last_ts.timestamp())
            for bucket in range(t0, t1+60, 60):
                c = sum(1 for t in ts_list if bucket <= t < bucket+60)
                qso_rate_by_min.append(c)

        # ── Hourly QSO count – all bands and per-band ──────────────────────
        hourly = []
        for h in range(23, -1, -1):
            t0c = now.timestamp() - (h+1)*3600
            t1c = now.timestamp() - h*3600
            cnt = sum(1 for q in qsos_sorted if t0c <= q.timestamp.timestamp() < t1c)
            label = (now - __import__("datetime").timedelta(hours=h)).strftime("%H:00")
            hourly.append({"label": label, "count": cnt})

        BAND_ORDER = ["160m","80m","60m","40m","30m","20m","17m","15m","12m","10m","6m","2m"]
        all_bands  = [b for b in BAND_ORDER if b in band_mode] + \
                     [b for b in band_mode if b not in BAND_ORDER and b != "?"]

        hourly_by_band = {}
        for band in all_bands:
            band_ts = [q.timestamp.timestamp() for q in qsos_sorted if q.band == band]
            hb = []
            for h in range(23, -1, -1):
                t0c = now.timestamp() - (h+1)*3600
                t1c = now.timestamp() - h*3600
                cnt = sum(1 for t in band_ts if t0c <= t < t1c)
                label = (now - __import__("datetime").timedelta(hours=h)).strftime("%H:00")
                hb.append({"label": label, "count": cnt})
            hourly_by_band[band] = hb

        # ── Band time (minutes spent on each band) ────────────────────────────
        band_time_min = {}
        for band, ts_b in band_qso_times.items():
            ts_b_s = sorted(t.timestamp() for t in ts_b)
            total_s = 0
            for i in range(1, len(ts_b_s)):
                gap = ts_b_s[i] - ts_b_s[i-1]
                if gap < GAP_THRESH*60:
                    total_s += gap
            band_time_min[band] = round(total_s / 60, 1)

        # ── Operating streak ──────────────────────────────────────────────────
        unique_days = sorted(set(streak_days))
        max_streak = cur_streak = 1
        for i in range(1, len(unique_days)):
            d0 = datetime.strptime(unique_days[i-1], "%Y-%m-%d")
            d1 = datetime.strptime(unique_days[i],   "%Y-%m-%d")
            if (d1 - d0).days == 1:
                cur_streak += 1
                max_streak = max(max_streak, cur_streak)
            else:
                cur_streak = 1

        # ── DXCC first-worked list ────────────────────────────────────────────
        dxcc_first_list = sorted(
            [{"entity": e, "ts": t.strftime("%Y-%m-%d %H:%M")}
             for e, t in dxcc_first_seen.items()],
            key=lambda x: x["ts"]
        )

        # ── Prefix list ───────────────────────────────────────────────────────
        prefix_list = sorted(list(prefixes))

        # ── Beam headings per band ────────────────────────────────────────────
        beam_by_band = {}
        for band, hdgs in beam_hdg.items():
            if hdgs:
                avg_hdg = int(sum(hdgs) / len(hdgs))
                dist_deg = [0]*36
                for h in hdgs:
                    dist_deg[min(35, int(h/10))] += 1
                beam_by_band[band] = {"avg": avg_hdg, "dist": dist_deg, "count": len(hdgs)}

        # ── Final QSO log (last 500) ──────────────────────────────────────────
        qso_rows = []
        for q in reversed(qsos_sorted[-500:]):
            info = self._lookup_dxcc(q.callsign)
            qso_rows.append({
                "call": q.callsign,
                "ts":   q.timestamp.strftime("%H:%M"),
                "date": q.timestamp.strftime("%Y-%m-%d"),
                "band": q.band, "mode": q.mode,
                "freq": f"{q.freq_hz/1e6:.3f}" if q.freq_hz else (q.band or ""),
                "entity": info["entity"], "cont": info["continent"],
                "cq": info["cq"], "itu": info["itu"],
            })

        return {
            "callsign":          self.db.callsign,
            "total":             len(qsos_sorted),
            "unique_calls":      len(seen_calls),
            "dupes":             len(dupe_list),
            "dupe_list":         dupe_list,
            "dxcc_count":        len(dxcc_map),
            "continent_count":   len(cont_map),
            "cq_zone_count":     len(cq_map),
            "itu_zone_count":    len(itu_map),
            "prefix_count":      len(prefix_list),
            "prefixes":          prefix_list,
            "call_length_dist":  dict(sorted(call_len_dist.items())),
            "avg_rate":          avg_rate,
            "best_1min":         best_1,
            "best_10min":        best_10,
            "best_30min":        best_30,
            "best_60min":        best_60,
            "best_60min_at":     b60at,
            "best_120min":       best_120,
            "op_time_min":       round(op_time_min),
            "break_time_min":    round(break_time_min),
            "first_qso":         first_ts.strftime("%Y-%m-%d %H:%M"),
            "last_qso":          last_ts.strftime("%Y-%m-%d %H:%M"),
            "max_streak":        max_streak,
            "dxcc":              sorted([{"entity":k,"count":v} for k,v in dxcc_map.items()],
                                        key=lambda x:-x["count"]),
            "dxcc_by_band":      {e: dict(v) for e, v in dxcc_by_band.items()},
            "dxcc_by_mode":      {e: dict(v) for e, v in dxcc_by_mode.items()},
            "dxcc_first_list":   dxcc_first_list,
            "continents":        dict(cont_map),
            "cont_by_band":      {c: dict(v) for c, v in cont_by_band.items()},
            "cq_zones":          {k: cq_map[k] for k in sorted(cq_map, key=int)},
            "itu_zones":         {k: itu_map[k] for k in sorted(itu_map, key=int)},
            "band_mode":         {b: dict(m) for b, m in band_mode.items()},
            "band_time_min":     band_time_min,
            "modes":             dict(modes_total),
            "band_changes_total":band_changes_total,
            "band_changes_by_hour": band_changes_by_hour,
            "band_seq":          band_seq[-100:],
            "breaks":            breaks,
            "hourly":            hourly,
            "hourly_by_band":    hourly_by_band,
            "by_hour_of_day":    by_hour_day,
            "by_day":            dict(sorted(by_day.items())),
            "top_calls":         sorted([{"call":k,"count":v} for k,v in top_calls_c.items()
                                         if v > 1], key=lambda x:-x["count"])[:30],
            "map_points":        list(map_points.values()),
            "beam_by_band":      beam_by_band,
            "qso_rate_by_min":   qso_rate_by_min[:1440],
            "all_bands":         all_bands,
            "qsos":              qso_rows,
        }

    def _build_stats_page(self) -> str:
        return r"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Statistics — UDP Live Log</title>
<style>
:root{
  --bg:#07090d;--surf:#0d1219;--card:#111928;--card2:#141e2e;
  --border:#1d2d3e;--border2:#243347;
  --text:#c9d8e8;--muted:#4e6880;--dim:#2a3f56;
  --green:#00e676;--green2:#00c853;--cyan:#00bcd4;--cyan2:#0097a7;
  --orange:#ff9800;--orange2:#e65100;--red:#ef5350;--red2:#b71c1c;
  --purple:#ce93d8;--yellow:#ffeb3b;--blue:#42a5f5;--blue2:#1565c0;
  --pink:#f48fb1;--teal:#80cbc4;
  --font-mono:'JetBrains Mono','Cascadia Code','Fira Code','Consolas',ui-monospace,monospace;
  --font-sans:'Inter',-apple-system,BlinkMacSystemFont,'Segoe UI',system-ui,sans-serif;
}
*{box-sizing:border-box;margin:0;padding:0}
html{scroll-behavior:smooth}
body{background:var(--bg);color:var(--text);font-family:var(--font-sans);min-height:100vh;font-size:14px}

/* ── Top nav ── */
.topnav{background:linear-gradient(90deg,#050a14 0%,#0a1628 50%,#050a14 100%);
  border-bottom:1px solid var(--border);
  display:flex;align-items:center;justify-content:space-between;
  padding:0 24px;height:54px;position:sticky;top:0;z-index:200;gap:16px}
.nav-logo{font-family:var(--font-mono);font-size:1.15rem;font-weight:700;
  color:var(--green);letter-spacing:.06em;white-space:nowrap;
  text-shadow:0 0 16px rgba(0,230,118,.25)}
.nav-tabs{display:flex;gap:2px;overflow-x:auto;-webkit-overflow-scrolling:touch}
.tab-btn{background:none;border:none;border-bottom:2px solid transparent;
  color:var(--muted);padding:18px 14px 16px;cursor:pointer;font-size:.78rem;
  font-family:var(--font-sans);font-weight:500;white-space:nowrap;letter-spacing:.03em;
  text-transform:uppercase;transition:.15s}
.tab-btn:hover{color:var(--text)}
.tab-btn.active{color:var(--cyan);border-bottom-color:var(--cyan)}
.nav-right{display:flex;align-items:center;gap:10px;flex-shrink:0}
.upd-time{font-family:var(--font-mono);font-size:.7rem;color:var(--muted)}
.back-btn{padding:6px 14px;border:1px solid var(--border);border-radius:6px;
  color:var(--muted);text-decoration:none;font-size:.75rem;background:var(--card);
  white-space:nowrap;transition:.15s}
.back-btn:hover{color:var(--cyan);border-color:var(--cyan)}

/* ── Sections (tab panels) ── */
.section{display:none;padding:20px 24px;max-width:1600px;margin:0 auto}
.section.active{display:block}

/* ── Loading ── */
#loading{position:fixed;inset:0;background:var(--bg);display:flex;flex-direction:column;
  align-items:center;justify-content:center;z-index:999;gap:14px}
.spin{width:32px;height:32px;border:3px solid var(--border);
  border-top-color:var(--cyan);border-radius:50%;animation:spin .8s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}

/* ── Hero cards ── */
.hero{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:10px;margin-bottom:18px}
.hcard{background:var(--card);border:1px solid var(--border);border-radius:10px;
  padding:16px 14px;position:relative;overflow:hidden;cursor:default}
.hcard::after{content:"";position:absolute;bottom:0;left:0;right:0;height:2px}
.hcard.g::after{background:linear-gradient(90deg,var(--green2),var(--green))}
.hcard.c::after{background:linear-gradient(90deg,var(--cyan2),var(--cyan))}
.hcard.o::after{background:linear-gradient(90deg,var(--orange2),var(--orange))}
.hcard.p::after{background:linear-gradient(90deg,#7b1fa2,var(--purple))}
.hcard.y::after{background:linear-gradient(90deg,#f57f17,var(--yellow))}
.hcard.r::after{background:linear-gradient(90deg,var(--red2),var(--red))}
.hcard.b::after{background:linear-gradient(90deg,var(--blue2),var(--blue))}
.hcard.t::after{background:linear-gradient(90deg,#00695c,var(--teal))}
.hnum{font-family:var(--font-mono);font-size:2rem;font-weight:700;line-height:1;margin-bottom:4px}
.hlbl{font-size:.68rem;color:var(--muted);text-transform:uppercase;letter-spacing:.07em}
.hsub{font-size:.68rem;color:var(--dim);margin-top:2px;font-family:var(--font-mono)}

/* ── Panels ── */
.grid{display:grid;gap:14px;margin-bottom:14px}
.g2{grid-template-columns:1fr 1fr}
.g3{grid-template-columns:1fr 1fr 1fr}
.g4{grid-template-columns:1fr 1fr 1fr 1fr}
@media(max-width:1200px){.g4{grid-template-columns:1fr 1fr 1fr}.g3{grid-template-columns:1fr 1fr}}
@media(max-width:800px){.g4,.g3,.g2{grid-template-columns:1fr}}
.panel{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:18px}
.panel-title{font-size:.72rem;font-family:var(--font-mono);color:var(--muted);
  text-transform:uppercase;letter-spacing:.09em;margin-bottom:14px;
  display:flex;align-items:center;gap:6px}
.panel-title span{color:var(--text)}

/* ── Bar rows ── */
.bar-row{display:flex;align-items:center;gap:7px;margin-bottom:4px}
.bar-lbl{width:130px;text-align:right;font-family:var(--font-mono);font-size:.72rem;
  color:var(--text);flex-shrink:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.bar-lbl.sm{width:55px}
.bar-lbl.med{width:90px}
.bar-track{flex:1;background:#080c12;border-radius:2px;height:13px;overflow:hidden}
.bar-fill{height:100%;border-radius:2px;transition:width .7s cubic-bezier(.4,0,.2,1)}
.bar-val{width:36px;text-align:right;font-family:var(--font-mono);font-size:.7rem;color:var(--muted)}

/* ── Tables ── */
.tbl{width:100%;border-collapse:collapse;font-size:.76rem}
.tbl th{color:var(--muted);text-align:left;padding:5px 8px;
  border-bottom:1px solid var(--border);font-family:var(--font-mono);font-weight:500;
  position:sticky;top:0;background:var(--card);z-index:1;white-space:nowrap}
.tbl td{padding:4px 8px;border-bottom:1px solid #0a1018;font-family:var(--font-mono)}
.tbl tr:hover td{background:#0d1826}
.scroll{max-height:340px;overflow-y:auto;border-radius:6px}
.scroll::-webkit-scrollbar{width:4px}
.scroll::-webkit-scrollbar-thumb{background:var(--border2);border-radius:2px}
.tbl td.num{text-align:right}
.tbl td.hi{color:var(--cyan)}
.tbl td.ok{color:var(--green)}
.tbl td.warn{color:var(--orange)}
.tbl td.dim{color:var(--muted)}

/* ── Matrix ── */
.matrix th,.matrix td{text-align:center!important;padding:5px 10px}
.matrix td.band-cell{text-align:left!important;font-weight:700;color:var(--text)}
.matrix td.val{color:var(--green)}
.matrix td.zero{color:var(--dim)}
.matrix td.total{color:var(--orange)}

/* ── Chart (SVG sparklines / bar charts) ── */
.chart-wrap{display:flex;gap:2px;align-items:flex-end;height:90px}
.chart-bar{flex:1;border-radius:2px 2px 0 0;min-height:2px;cursor:default;transition:opacity .15s}
.chart-bar:hover{opacity:.75}
.chart-labels{display:flex;justify-content:space-between;margin-top:3px;
  font-size:.6rem;color:var(--muted);font-family:var(--font-mono)}

/* ── Heatmap ── */
.heatmap{display:grid;grid-template-columns:repeat(24,1fr);gap:2px;margin-top:8px}
.hcell{height:26px;border-radius:2px;display:flex;align-items:center;
  justify-content:center;font-size:.58rem;color:rgba(255,255,255,.4);
  font-family:var(--font-mono);cursor:default}

/* ── Rose chart (beam headings) ── */
.rose-wrap{display:flex;gap:14px;flex-wrap:wrap}
.rose-box{text-align:center}
.rose-lbl{font-size:.7rem;color:var(--muted);margin-top:4px;font-family:var(--font-mono)}

/* ── Zone pills ── */
.pill-wrap{display:flex;flex-wrap:wrap;gap:4px;margin-top:4px}
.pill{background:#080c12;border:1px solid var(--border);border-radius:4px;
  padding:3px 8px;font-family:var(--font-mono);font-size:.7rem;
  display:flex;align-items:center;gap:4px}
.pill .pn{color:var(--cyan);font-weight:700}
.pill .pc{color:var(--muted)}

/* ── Continent colour tokens ── */
.c-NA{color:#42a5f5}.c-EU{color:#66bb6a}.c-AS{color:#ffa726}
.c-AF{color:#ef5350}.c-OC{color:#ce93d8}.c-SA{color:#ffeb3b}.c-AN{color:#80deea}

/* ── Break list ── */
.break-row{display:flex;align-items:center;gap:10px;padding:5px 0;
  border-bottom:1px solid var(--border);font-size:.76rem;font-family:var(--font-mono)}
.break-badge{background:#1a1e28;border:1px solid var(--border2);border-radius:4px;
  padding:2px 8px;color:var(--orange);font-weight:700;white-space:nowrap}
.break-range{color:var(--muted)}

/* ── Band-change list ── */
.bc-pill{display:inline-flex;align-items:center;gap:4px;padding:2px 8px;
  background:#0a1018;border:1px solid var(--border);border-radius:4px;
  font-family:var(--font-mono);font-size:.7rem;margin:2px}
.bc-arrow{color:var(--muted)}

/* ── Callsign length chart ── */
.clbar{display:flex;align-items:center;gap:8px;margin-bottom:3px;font-size:.76rem}
.cln{width:24px;text-align:right;color:var(--muted);font-family:var(--font-mono)}

/* ── Map ── */
#map{height:420px;border-radius:8px;border:1px solid var(--border)}

/* ── Rate sparkline ── */
#rate-spark{width:100%;height:60px;display:block}

/* ── Summary table ── */
.sum-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:6px}
.sum-row{display:flex;justify-content:space-between;align-items:center;
  padding:6px 10px;background:var(--card2);border-radius:6px;
  font-size:.78rem;border:1px solid var(--border)}
.sum-key{color:var(--muted)}
.sum-val{font-family:var(--font-mono);font-weight:600;color:var(--text)}
  .vibe-footer{{text-align:center;padding:14px;font-size:.75rem;color:var(--muted);border-top:1px solid var(--border);margin-top:28px}}
  .vibe-footer a{{color:var(--green);text-decoration:none;font-weight:600}}
  .vibe-footer a:hover{{text-decoration:underline}}
</style>
</head><body>
<div id="loading">
  <div class="spin"></div>
  <div style="font-family:var(--font-mono);color:var(--muted);font-size:.82rem">Computing statistics…</div>
</div>

<!-- ── Top nav ── -->
<nav class="topnav">
  <div class="nav-logo" id="nav-call">—</div>
  <div class="nav-tabs" id="nav-tabs">
    <button class="tab-btn active" data-tab="summary">Summary</button>
    <button class="tab-btn" data-tab="rates">Rates</button>
    <button class="tab-btn" data-tab="bands">Bands</button>
    <button class="tab-btn" data-tab="countries">Countries</button>
    <button class="tab-btn" data-tab="zones">Zones</button>
    <button class="tab-btn" data-tab="map">Map &amp; Beams</button>
    <button class="tab-btn" data-tab="calls">Callsigns</button>
    <button class="tab-btn" data-tab="time">Time Analysis</button>
    <button class="tab-btn" data-tab="log">QSO Log</button>
  </div>
  <div class="nav-right">
    <span class="upd-time" id="upd-time"></span>
    <a href="/" class="back-btn">← Dashboard</a>
  </div>
</nav>

<!-- ═══════════════════════════════════════════════════════ SUMMARY ═══ -->
<div class="section active" id="tab-summary">
  <div class="hero" id="hero-cards"></div>
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">📊 QSO Summary by Band &amp; Mode</div>
      <table class="tbl matrix" id="band-matrix"></table>
    </div>
    <div class="panel">
      <div class="panel-title">⏱ Operating Summary</div>
      <div class="sum-grid" id="op-summary"></div>
    </div>
  </div>
  <div class="grid g3">
    <div class="panel">
      <div class="panel-title">🌍 Continents</div>
      <div id="cont-bars"></div>
    </div>
    <div class="panel">
      <div class="panel-title">📡 Mode Breakdown</div>
      <div id="mode-bars"></div>
    </div>
    <div class="panel">
      <div class="panel-title">⏰ Time Spent per Band</div>
      <div id="bandtime-bars"></div>
    </div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ RATES ═════ -->
<div class="section" id="tab-rates">
  <div class="grid g4" style="margin-bottom:14px">
    <div class="panel"><div class="panel-title">Best 1 min</div>
      <div class="hnum" id="r1" style="font-family:var(--font-mono);font-size:2rem;color:var(--green)">—</div>
      <div class="hlbl">QSOs in 60 s</div></div>
    <div class="panel"><div class="panel-title">Best 10 min</div>
      <div class="hnum" id="r10" style="font-family:var(--font-mono);font-size:2rem;color:var(--cyan)">—</div>
      <div class="hlbl">→ <span id="r10h">—</span>/hr</div></div>
    <div class="panel"><div class="panel-title">Best 30 min</div>
      <div class="hnum" id="r30" style="font-family:var(--font-mono);font-size:2rem;color:var(--orange)">—</div>
      <div class="hlbl">→ <span id="r30h">—</span>/hr</div></div>
    <div class="panel"><div class="panel-title">Best 60 min</div>
      <div class="hnum" id="r60" style="font-family:var(--font-mono);font-size:2rem;color:var(--purple)">—</div>
      <div class="hlbl">at <span id="r60at" style="color:var(--muted)">—</span></div></div>
  </div>
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">📈 QSOs Last 24 Hours (all bands)</div>
      <div class="chart-wrap" id="hourly-chart"></div>
      <div class="chart-labels" id="hourly-labels"></div>
    </div>
    <div class="panel">
      <div class="panel-title">📈 QSOs per Hour — Per Band</div>
      <div id="hourly-band-select" style="margin-bottom:10px;display:flex;flex-wrap:wrap;gap:4px"></div>
      <div class="chart-wrap" id="hourly-band-chart"></div>
      <div class="chart-labels" id="hourly-band-labels"></div>
    </div>
  </div>
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">🕐 Activity by Hour of Day (UTC)</div>
      <div class="heatmap" id="hod-heatmap"></div>
      <div style="display:flex;justify-content:space-between;margin-top:3px;
        font-size:.58rem;color:var(--muted);font-family:var(--font-mono)">
        <span>00z</span><span>06z</span><span>12z</span><span>18z</span><span>23z</span>
      </div>
    </div>
    <div class="panel">
      <div class="panel-title">📅 Daily QSO Count</div>
      <div id="daily-bars"></div>
    </div>
  </div>
  <div class="panel" style="margin-bottom:14px">
    <div class="panel-title">⚡ QSO Rate per Minute (sparkline)</div>
    <svg id="rate-spark" viewBox="0 0 1200 60" preserveAspectRatio="none"></svg>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ BANDS ═════ -->
<div class="section" id="tab-bands">
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">📻 Band × Mode Matrix</div>
      <table class="tbl matrix" id="band-matrix2"></table>
    </div>
    <div class="panel">
      <div class="panel-title">🔄 Band Changes (<span id="bc-total">0</span> total)</div>
      <div style="margin-bottom:10px">
        <div class="chart-wrap" id="bc-chart" style="height:70px"></div>
        <div class="chart-labels" id="bc-chart-labels"></div>
      </div>
      <div id="bc-recent" class="scroll" style="max-height:200px"></div>
    </div>
  </div>
  <div class="panel" style="margin-bottom:14px">
    <div class="panel-title">🌍 Continents by Band</div>
    <table class="tbl" id="cont-band-tbl"></table>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ COUNTRIES ═ -->
<div class="section" id="tab-countries">
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">🌍 DXCC Entities Worked (<span id="dxcc-n">0</span>)</div>
      <div class="scroll">
        <table class="tbl" id="dxcc-tbl"></table>
      </div>
    </div>
    <div class="panel">
      <div class="panel-title">🕐 DXCC — First Worked Chronology</div>
      <div class="scroll">
        <table class="tbl" id="dxcc-first-tbl"></table>
      </div>
    </div>
  </div>
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">📻 DXCC by Band (top 20)</div>
      <div class="scroll">
        <table class="tbl" id="dxcc-band-tbl"></table>
      </div>
    </div>
    <div class="panel">
      <div class="panel-title">📡 DXCC by Mode (top 20)</div>
      <div class="scroll">
        <table class="tbl" id="dxcc-mode-tbl"></table>
      </div>
    </div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ ZONES ══════ -->
<div class="section" id="tab-zones">
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">🔢 CQ Zones Worked (<span id="cq-n">0</span> of 40)</div>
      <div class="pill-wrap" id="cq-pills"></div>
      <div style="margin-top:16px">
        <div class="panel-title" style="margin-bottom:8px">CQ Zones — Bar Chart</div>
        <div id="cq-bars"></div>
      </div>
    </div>
    <div class="panel">
      <div class="panel-title">📡 ITU Zones Worked (<span id="itu-n">0</span> of 90)</div>
      <div class="pill-wrap" id="itu-pills"></div>
      <div style="margin-top:16px">
        <div class="panel-title" style="margin-bottom:8px">ITU Zones — Bar Chart</div>
        <div id="itu-bars"></div>
      </div>
    </div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ MAP & BEAMS -->
<div class="section" id="tab-map">
  <div class="panel" style="margin-bottom:14px">
    <div class="panel-title">🗺 Contact Map</div>
    <div id="map"></div>
  </div>
  <div class="panel">
    <div class="panel-title">🧭 Beam Headings by Band</div>
    <div class="rose-wrap" id="rose-wrap"></div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ CALLSIGNS ═ -->
<div class="section" id="tab-calls">
  <div class="grid g3">
    <div class="panel">
      <div class="panel-title">📋 Callsign Length Distribution</div>
      <div id="calllen-bars"></div>
    </div>
    <div class="panel">
      <div class="panel-title">🔁 Duplicate Callers</div>
      <div id="dupe-bars"></div>
    </div>
    <div class="panel">
      <div class="panel-title">🏷 Unique Prefixes Worked (<span id="pfx-n">0</span>)</div>
      <div class="pill-wrap" id="pfx-pills"></div>
    </div>
  </div>
  <div class="panel">
    <div class="panel-title">🔴 Duplicate QSOs (<span id="dupe-n">0</span>)</div>
    <div class="scroll">
      <table class="tbl" id="dupe-tbl"></table>
    </div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ TIME ══════ -->
<div class="section" id="tab-time">
  <div class="grid g2">
    <div class="panel">
      <div class="panel-title">☕ Break Times (<span id="break-n">0</span> breaks)</div>
      <div id="break-list"></div>
    </div>
    <div class="panel">
      <div class="panel-title">🔄 Recent Band Changes</div>
      <div id="bc-list2" class="scroll"></div>
    </div>
  </div>
</div>

<!-- ═══════════════════════════════════════════════════════ QSO LOG ═══ -->
<div class="section" id="tab-log">
  <div class="panel">
    <div class="panel-title">📋 QSO Log — Last 500 contacts</div>
    <div class="scroll" style="max-height:600px">
      <table class="tbl">
        <thead><tr>
          <th>#</th><th>Time</th><th>Date</th><th>Callsign</th>
          <th>Band</th><th>Mode</th><th>Freq</th>
          <th>DXCC Entity</th><th>Cont</th><th>CQ</th><th>ITU</th>
        </tr></thead>
        <tbody id="log-tbody"></tbody>
      </table>
    </div>
  </div>
</div>

<script>
// ─── Tab router ───────────────────────────────────────────────────────────
document.querySelectorAll(".tab-btn").forEach(btn=>{
  btn.addEventListener("click",()=>{
    document.querySelectorAll(".tab-btn").forEach(b=>b.classList.remove("active"));
    document.querySelectorAll(".section").forEach(s=>s.classList.remove("active"));
    btn.classList.add("active");
    document.getElementById("tab-"+btn.dataset.tab).classList.add("active");
    if(btn.dataset.tab==="map" && !window._mapInit) initMap();
  });
});

// ─── Helpers ──────────────────────────────────────────────────────────────
function bars(parentId,data,color,labelW="130px",maxLabel=18){
  const el=document.getElementById(parentId); if(!el) return;
  el.innerHTML="";
  const max=Math.max(...Object.values(data),1);
  Object.entries(data).sort((a,b)=>b[1]-a[1]).forEach(([k,v])=>{
    const pct=(v/max*100).toFixed(1);
    el.innerHTML+=`<div class="bar-row">
      <div class="bar-lbl" style="width:${labelW}" title="${k}">${k.length>maxLabel?k.slice(0,maxLabel)+"…":k}</div>
      <div class="bar-track"><div class="bar-fill" style="width:${pct}%;background:${color}"></div></div>
      <div class="bar-val">${v}</div></div>`;
  });
}

function hbar(parentId,data,colorFn,labelW="130px"){
  const el=document.getElementById(parentId); if(!el) return;
  el.innerHTML="";
  const max=Math.max(...Object.values(data),1);
  Object.entries(data).sort((a,b)=>parseInt(a[0])-parseInt(b[0])).forEach(([k,v])=>{
    const pct=(v/max*100).toFixed(1);
    const col=typeof colorFn==="string"?colorFn:colorFn(k);
    el.innerHTML+=`<div class="bar-row">
      <div class="bar-lbl sm" style="width:${labelW}">${k}</div>
      <div class="bar-track"><div class="bar-fill" style="width:${pct}%;background:${col}"></div></div>
      <div class="bar-val">${v}</div></div>`;
  });
}

function fmt_min(m){
  if(m<60) return `${m}m`;
  const h=Math.floor(m/60),mm=m%60;
  return `${h}h ${mm}m`;
}

// ─── Main data load ────────────────────────────────────────────────────────
let D={}, _mapInst=null;
window._mapInit=false;

function render(d){
  D=d;
  document.getElementById("loading").style.display="none";
  document.getElementById("nav-call").textContent=d.callsign||"—";
  document.getElementById("upd-time").textContent="Updated "+new Date().toLocaleTimeString("en-GB",{hour12:false});

  buildSummary(d);
  buildRates(d);
  buildBands(d);
  buildCountries(d);
  buildZones(d);
  buildCalls(d);
  buildTime(d);
  buildLog(d);
}

// ═══════════════════════════════════════════════════════════ SUMMARY ═════
function buildSummary(d){
  // Hero cards
  const cards=[
    {n:d.total,         l:"Total QSOs",    s:"",                  cls:"g"},
    {n:d.unique_calls,  l:"Unique Calls",  s:`${d.dupes} dupes`,  cls:"c"},
    {n:d.dxcc_count,    l:"DXCC Entities", s:`${d.prefix_count} prefixes`, cls:"o"},
    {n:d.continent_count,l:"Continents",   s:"worked",            cls:"p"},
    {n:d.cq_zone_count, l:"CQ Zones",      s:"of 40",             cls:"y"},
    {n:d.itu_zone_count,l:"ITU Zones",     s:"of 90",             cls:"b"},
    {n:d.avg_rate,      l:"Avg QSOs/hr",   s:`Best 60min: ${d.best_60min}`, cls:"t"},
    {n:d.max_streak+"d",l:"Day Streak",    s:`${d.first_qso.slice(0,10)} →`,cls:"r"},
  ];
  document.getElementById("hero-cards").innerHTML=cards.map(c=>
    `<div class="hcard ${c.cls}">
      <div class="hnum">${c.n}</div>
      <div class="hlbl">${c.l}</div>
      <div class="hsub">${c.s}</div>
    </div>`).join("");

  // Band × mode matrix
  buildBandMatrix("band-matrix",d);

  // Op summary
  const opItems=[
    ["First QSO",d.first_qso],["Last QSO",d.last_qso],
    ["Operating Time",fmt_min(d.op_time_min)],
    ["Break Time",fmt_min(d.break_time_min)],
    ["Total QSOs",d.total],["Unique Calls",d.unique_calls],
    ["Dupes",d.dupes],["DXCC Entities",d.dxcc_count],
    ["CQ Zones",d.cq_zone_count],["ITU Zones",d.itu_zone_count],
    ["Unique Prefixes",d.prefix_count],
    ["Band Changes",d.band_changes_total],
    ["Best 1 min",d.best_1min+" Q"],
    ["Best 10 min",d.best_10min+" Q ("+(d.best_10min*6)+"/hr)"],
    ["Best 30 min",d.best_30min+" Q ("+(d.best_30min*2)+"/hr)"],
    ["Best 60 min",d.best_60min+" Q @ "+d.best_60min_at],
    ["Best 120 min",d.best_120min+" Q ("+(Math.round(d.best_120min/2))+"/hr)"],
    ["Avg Rate",d.avg_rate+" Q/hr"],
  ];
  document.getElementById("op-summary").innerHTML=opItems.map(([k,v])=>
    `<div class="sum-row"><span class="sum-key">${k}</span><span class="sum-val">${v}</span></div>`
  ).join("");

  bars("cont-bars",d.continents,"#42a5f5","80px",4);
  bars("mode-bars",d.modes,"#ce93d8","80px");
  bars("bandtime-bars",
    Object.fromEntries(Object.entries(d.band_time_min).filter(([,v])=>v>0)),
    "#ff9800","80px");
}

function buildBandMatrix(id,d){
  const allModes=[...new Set(Object.values(d.band_mode).flatMap(m=>Object.keys(m)))].sort();
  const BORDER=["160m","80m","60m","40m","30m","20m","17m","15m","12m","10m","6m","2m","70cm"];
  const bands=[...new Set([...BORDER.filter(b=>d.band_mode[b]),...d.all_bands])];
  let html=`<tr><th>Band</th>${allModes.map(m=>`<th>${m}</th>`).join("")}<th>Total</th><th>Time</th></tr>`;
  bands.forEach(b=>{
    const row=d.band_mode[b]||{};
    const tot=Object.values(row).reduce((a,c)=>a+c,0);
    const cells=allModes.map(m=>row[m]
      ?`<td class="val">${row[m]}</td>`
      :`<td class="zero">·</td>`).join("");
    const tm=d.band_time_min[b]?`${d.band_time_min[b]}m`:"";
    html+=`<tr><td class="band-cell">${b}</td>${cells}<td class="total">${tot}</td><td class="dim">${tm}</td></tr>`;
  });
  document.getElementById(id).innerHTML=html;
}

// ═══════════════════════════════════════════════════════════ RATES ════════
function buildRates(d){
  document.getElementById("r1").textContent=d.best_1min;
  document.getElementById("r10").textContent=d.best_10min;
  document.getElementById("r10h").textContent=d.best_10min*6;
  document.getElementById("r30").textContent=d.best_30min;
  document.getElementById("r30h").textContent=d.best_30min*2;
  document.getElementById("r60").textContent=d.best_60min;
  document.getElementById("r60at").textContent=d.best_60min_at;

  // Hourly (all bands)
  const hmax=Math.max(...d.hourly.map(h=>h.count),1);
  document.getElementById("hourly-chart").innerHTML=d.hourly.map((h,i)=>{
    const pct=(h.count/hmax*100).toFixed(1);
    return `<div class="chart-bar" style="height:${pct}%;background:var(--cyan);opacity:${h.count?".8":".15"}"
      title="${h.label}: ${h.count}"></div>`;
  }).join("");
  document.getElementById("hourly-labels").innerHTML=
    d.hourly.filter((_,i)=>i%6===0||i===d.hourly.length-1)
            .map(h=>`<span>${h.label}</span>`).join("");

  // Hourly per-band selector
  const sel=document.getElementById("hourly-band-select");
  sel.innerHTML=d.all_bands.map((b,i)=>
    `<button onclick="showBandHourly('${b}')" id="bhb-${b}"
      style="padding:3px 10px;border-radius:4px;border:1px solid var(--border);
      background:${i===0?'var(--cyan2)':'var(--card)'};color:${i===0?'#fff':'var(--muted)'};
      cursor:pointer;font-size:.7rem;font-family:var(--font-mono)">${b}</button>`
  ).join("");
  if(d.all_bands.length) showBandHourly(d.all_bands[0]);

  // HoD heatmap
  const hod=d.by_hour_of_day, hodMax=Math.max(...hod,1);
  document.getElementById("hod-heatmap").innerHTML=hod.map((v,i)=>{
    const intensity=v/hodMax;
    const bg=`rgba(0,188,212,${(0.05+intensity*.85).toFixed(2)})`;
    return `<div class="hcell" style="background:${bg}" title="${String(i).padStart(2,"0")}z: ${v}">${v||""}</div>`;
  }).join("");

  // Daily bars
  bars("daily-bars",d.by_day,"#ce93d8","120px",12);

  // Rate sparkline (SVG)
  const svg=document.getElementById("rate-spark");
  const rates=d.qso_rate_by_min;
  if(rates.length>1){
    const rmax=Math.max(...rates,1);
    const W=1200,H=60;
    const pts=rates.map((v,i)=>{
      const x=(i/(rates.length-1))*W;
      const y=H-(v/rmax)*(H-2)-1;
      return `${x.toFixed(1)},${y.toFixed(1)}`;
    }).join(" ");
    svg.innerHTML=`<polyline points="${pts}" fill="none" stroke="var(--cyan)" stroke-width="1.5" stroke-linejoin="round"/>
      <polyline points="0,${H} ${pts} ${W},${H}" fill="rgba(0,188,212,0.08)" stroke="none"/>`;
  }
}

function showBandHourly(band){
  document.querySelectorAll("[id^='bhb-']").forEach(b=>{
    b.style.background=b.id==="bhb-"+band?"var(--cyan2)":"var(--card)";
    b.style.color=b.id==="bhb-"+band?"#fff":"var(--muted)";
  });
  const hb=D.hourly_by_band[band]||[];
  const hmax=Math.max(...hb.map(h=>h.count),1);
  document.getElementById("hourly-band-chart").innerHTML=hb.map(h=>{
    const pct=(h.count/hmax*100).toFixed(1);
    return `<div class="chart-bar" style="height:${pct}%;background:var(--orange);opacity:${h.count?".8":".15"}"
      title="${h.label}: ${h.count}"></div>`;
  }).join("");
  document.getElementById("hourly-band-labels").innerHTML=
    hb.filter((_,i)=>i%6===0||i===hb.length-1).map(h=>`<span>${h.label}</span>`).join("");
}

// ═══════════════════════════════════════════════════════════ BANDS ════════
function buildBands(d){
  buildBandMatrix("band-matrix2",d);

  // Band changes
  document.getElementById("bc-total").textContent=d.band_changes_total;
  const bch=d.band_changes_by_hour, bcmax=Math.max(...bch,1);
  document.getElementById("bc-chart").innerHTML=bch.map((v,i)=>
    `<div class="chart-bar" style="height:${(v/bcmax*100).toFixed(1)}%;background:var(--orange);
      opacity:${v?".8":".15"}" title="${String(i).padStart(2,"0")}z: ${v} changes"></div>`
  ).join("");
  document.getElementById("bc-chart-labels").innerHTML=
    bch.filter((_,i)=>i%6===0||i===23).map((_,j,a)=>`<span>${String(j*6).padStart(2,"0")}z</span>`).join("");

  document.getElementById("bc-recent").innerHTML=d.band_seq.slice(-40).reverse().map(bc=>
    `<div class="bc-pill">${bc.date} ${bc.ts}
      <span style="color:var(--orange)">${bc.from}</span>
      <span class="bc-arrow">→</span>
      <span style="color:var(--cyan)">${bc.to}</span>
    </div>`).join("");

  // Continents by band
  const conts=[...new Set(Object.values(d.cont_by_band).flatMap(v=>Object.keys(v)))];
  const bnd=[...d.all_bands];
  let ctbHtml=`<tr><th>Continent</th>${bnd.map(b=>`<th>${b}</th>`).join("")}<th>Total</th></tr>`;
  conts.forEach(c=>{
    const row=d.cont_by_band[c]||{};
    const tot=Object.values(row).reduce((a,v)=>a+v,0);
    const col=CONT_COLS[c]||"var(--text)";
    ctbHtml+=`<tr><td style="color:${col};font-weight:600">${c}</td>
      ${bnd.map(b=>`<td class="${row[b]?'val':'zero'}">${row[b]||"·"}</td>`).join("")}
      <td class="total">${tot}</td></tr>`;
  });
  document.getElementById("cont-band-tbl").innerHTML=ctbHtml;
}

// ═══════════════════════════════════════════════════════════ COUNTRIES ════
function buildCountries(d){
  document.getElementById("dxcc-n").textContent=d.dxcc_count;

  // Full DXCC table
  let html=`<tr><th>#</th><th>Entity</th><th>Total</th>${d.all_bands.map(b=>`<th>${b}</th>`).join("")}</tr>`;
  d.dxcc.forEach((e,i)=>{
    const bbd=d.dxcc_by_band[e.entity]||{};
    html+=`<tr><td class="dim">${i+1}</td><td>${e.entity}</td>
      <td class="hi">${e.count}</td>
      ${d.all_bands.map(b=>`<td class="${bbd[b]?'ok':'zero'}">${bbd[b]||"·"}</td>`).join("")}
    </tr>`;
  });
  document.getElementById("dxcc-tbl").innerHTML=html;

  // First worked
  let fHtml=`<tr><th>#</th><th>Entity</th><th>First worked</th></tr>`;
  d.dxcc_first_list.forEach((e,i)=>{
    fHtml+=`<tr><td class="dim">${i+1}</td><td>${e.entity}</td><td class="dim">${e.ts}</td></tr>`;
  });
  document.getElementById("dxcc-first-tbl").innerHTML=fHtml;

  // DXCC by band (top 20)
  const top20=d.dxcc.slice(0,20);
  const bndList=d.all_bands;
  let bbHtml=`<tr><th>Entity</th>${bndList.map(b=>`<th>${b}</th>`).join("")}</tr>`;
  top20.forEach(e=>{
    const bbd=d.dxcc_by_band[e.entity]||{};
    bbHtml+=`<tr><td>${e.entity}</td>
      ${bndList.map(b=>`<td class="${bbd[b]?'ok':'zero'}">${bbd[b]||"·"}</td>`).join("")}
    </tr>`;
  });
  document.getElementById("dxcc-band-tbl").innerHTML=bbHtml;

  // DXCC by mode
  const allModes=[...new Set(Object.values(d.dxcc_by_mode).flatMap(v=>Object.keys(v)))].sort();
  let bmHtml=`<tr><th>Entity</th>${allModes.map(m=>`<th>${m}</th>`).join("")}</tr>`;
  top20.forEach(e=>{
    const bmd=d.dxcc_by_mode[e.entity]||{};
    bmHtml+=`<tr><td>${e.entity}</td>
      ${allModes.map(m=>`<td class="${bmd[m]?'ok':'zero'}">${bmd[m]||"·"}</td>`).join("")}
    </tr>`;
  });
  document.getElementById("dxcc-mode-tbl").innerHTML=bmHtml;
}

// ═══════════════════════════════════════════════════════════ ZONES ════════
function buildZones(d){
  document.getElementById("cq-n").textContent=d.cq_zone_count;
  document.getElementById("itu-n").textContent=d.itu_zone_count;

  // Fill all 40 CQ zones; highlight worked
  const cqAll={};
  for(let i=1;i<=40;i++) cqAll[i]=d.cq_zones[String(i)]||0;
  document.getElementById("cq-pills").innerHTML=Object.entries(cqAll).map(([z,c])=>{
    const worked=c>0;
    return `<div class="pill" style="${worked?'border-color:var(--cyan)':''}" title="Zone ${z}: ${c} QSOs">
      <span class="pn" style="${worked?'':'color:var(--dim)'}">${z}</span>
      <span class="pc">${worked?c:""}</span></div>`;
  }).join("");
  hbar("cq-bars",Object.fromEntries(Object.entries(d.cq_zones).filter(([,v])=>v>0)),
    "#00bcd4","35px");

  const ituAll={};
  for(let i=1;i<=90;i++) ituAll[i]=d.itu_zones[String(i)]||0;
  document.getElementById("itu-pills").innerHTML=Object.entries(ituAll).map(([z,c])=>{
    const worked=c>0;
    return `<div class="pill" style="${worked?'border-color:var(--purple)':''}" title="ITU ${z}: ${c} QSOs">
      <span class="pn" style="${worked?'color:var(--purple)':'color:var(--dim)'}">${z}</span>
      <span class="pc">${worked?c:""}</span></div>`;
  }).join("");
  hbar("itu-bars",Object.fromEntries(Object.entries(d.itu_zones).filter(([,v])=>v>0)),
    "#ce93d8","35px");
}

// ═══════════════════════════════════════════════════════════ MAP ══════════
function initMap(){
  window._mapInit=true;
  // Lazy-load Leaflet CSS+JS only when the Map tab is first opened
  if(!window.L){
    const css=document.createElement("link");
    css.rel="stylesheet";
    css.href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css";
    document.head.appendChild(css);
    const js=document.createElement("script");
    js.src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js";
    js.onload=()=>_initLeafletMap();
    js.onerror=()=>{
      document.getElementById("map").innerHTML=
        '<div style="display:flex;align-items:center;justify-content:center;height:100%;color:var(--muted);font-family:var(--font-mono);font-size:.85rem">Map unavailable offline — Leaflet CDN unreachable</div>';
    };
    document.head.appendChild(js);
    return;
  }
  _initLeafletMap();
}

function _initLeafletMap(){
  const map=L.map("map",{center:[20,0],zoom:2,preferCanvas:true,attributionControl:false});
  L.tileLayer("https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png",
    {subdomains:"abcd",maxZoom:19}).addTo(map);
  D.map_points.forEach(pt=>{
    const col=CONT_COLS[pt.continent]||"#aaa";
    const r=Math.min(20,5+Math.sqrt(pt.count)*2.5);
    L.circleMarker([pt.lat,pt.lon],{
      radius:r,color:col,fillColor:col,fillOpacity:.65,weight:1.5
    }).bindPopup(`<div style="font-family:monospace">
      <b style="color:${col}">${pt.calls.slice(0,6).join(", ")}${pt.calls.length>6?"…":""}</b><br>
      ${pt.count} QSO${pt.count>1?"s":""}
      &middot; CQ${pt.cq} &middot; ${pt.continent}</div>`)
     .addTo(map);
  });
  _mapInst=map;

  // Beam headings compass roses (SVG)
  const rw=document.getElementById("rose-wrap");
  rw.innerHTML="";
  Object.entries(D.beam_by_band).forEach(([band,info])=>{
    const size=140;
    const cx=size/2,cy=size/2,R=55;
    // Dist bars
    const distMax=Math.max(...info.dist,1);
    const bars36=info.dist.map((v,i)=>{
      const ang=(i*10-90)*Math.PI/180;
      const r=(v/distMax)*R;
      return r>2?`<line x1="${cx}" y1="${cy}"
        x2="${(cx+Math.cos(ang)*r).toFixed(1)}" y2="${(cy+Math.sin(ang)*r).toFixed(1)}"
        stroke="var(--cyan)" stroke-width="3" stroke-linecap="round" opacity=".7"/>`:""
    }).join("");
    // Avg bearing pointer
    const avgAng=(info.avg-90)*Math.PI/180;
    const px=(cx+Math.cos(avgAng)*R).toFixed(1);
    const py=(cy+Math.sin(avgAng)*R).toFixed(1);
    const svg=`<svg width="${size}" height="${size}" viewBox="0 0 ${size} ${size}">
      <circle cx="${cx}" cy="${cy}" r="${R}" fill="none" stroke="var(--border2)" stroke-width="1"/>
      <circle cx="${cx}" cy="${cy}" r="${R*0.5}" fill="none" stroke="var(--border)" stroke-width=".5" stroke-dasharray="3,3"/>
      ${bars36}
      <line x1="${cx}" y1="${cy}" x2="${px}" y2="${py}" stroke="var(--orange)" stroke-width="2" stroke-linecap="round"/>
      <circle cx="${px}" cy="${py}" r="3" fill="var(--orange)"/>
      <circle cx="${cx}" cy="${cy}" r="3" fill="var(--muted)"/>
      <text x="${cx}" y="10" text-anchor="middle" fill="var(--muted)" font-size="8" font-family="monospace">N</text>
      <text x="${cx}" y="${size-3}" text-anchor="middle" fill="var(--muted)" font-size="8" font-family="monospace">S</text>
      <text x="8" y="${cy+3}" text-anchor="middle" fill="var(--muted)" font-size="8" font-family="monospace">W</text>
      <text x="${size-8}" y="${cy+3}" text-anchor="middle" fill="var(--muted)" font-size="8" font-family="monospace">E</text>
    </svg>`;
    rw.innerHTML+=`<div class="rose-box">${svg}<div class="rose-lbl">${band}<br>avg ${info.avg}°<br>${info.count} Q</div></div>`;
  });
}

// ═══════════════════════════════════════════════════════════ CALLSIGNS ════
function buildCalls(d){
  // Call length distribution
  const clEl=document.getElementById("calllen-bars");
  const clMax=Math.max(...Object.values(d.call_length_dist),1);
  clEl.innerHTML=Object.entries(d.call_length_dist).sort((a,b)=>+a[0]-+b[0]).map(([len,cnt])=>{
    const pct=(cnt/clMax*100).toFixed(1);
    return `<div class="bar-row">
      <div class="bar-lbl sm">${len} chars</div>
      <div class="bar-track"><div class="bar-fill" style="width:${pct}%;background:var(--blue)"></div></div>
      <div class="bar-val">${cnt}</div></div>`;
  }).join("");

  // Dupe callers bar
  bars("dupe-bars",Object.fromEntries(d.top_calls.map(c=>[c.call,c.count])),"#ffeb3b","90px");

  // Prefixes
  document.getElementById("pfx-n").textContent=d.prefix_count;
  document.getElementById("pfx-pills").innerHTML=d.prefixes.map(p=>
    `<div class="pill"><span class="pn" style="color:var(--yellow)">${p}</span></div>`
  ).join("");

  // Dupe count badge + table
  document.getElementById("dupe-n").textContent=d.dupes;
  if(d.dupe_list.length){
    let html=`<tr><th>Callsign</th><th>Band</th><th>Mode</th><th>Date</th><th>Time</th></tr>`;
    d.dupe_list.forEach(r=>{
      html+=`<tr><td class="warn">${r.call}</td><td>${r.band}</td>
        <td>${r.mode}</td><td class="dim">${r.date}</td><td class="dim">${r.ts}</td></tr>`;
    });
    document.getElementById("dupe-tbl").innerHTML=html;
  } else {
    document.getElementById("dupe-tbl").innerHTML=
      `<tr><td colspan="5" style="color:var(--muted);padding:14px">No duplicates</td></tr>`;
  }
}

// ═══════════════════════════════════════════════════════════ TIME ═════════
function buildTime(d){
  document.getElementById("break-n").textContent=d.breaks.length;
  document.getElementById("break-list").innerHTML=d.breaks.length
    ? d.breaks.map(b=>
        `<div class="break-row">
          <span class="break-badge">${fmt_min(b.duration_min)}</span>
          <span class="break-range">${b.from} → ${b.to}</span>
        </div>`).join("")
    : `<p style="color:var(--muted);font-size:.8rem;padding:10px 0">No breaks detected (gaps &lt;30 min)</p>`;

  document.getElementById("bc-list2").innerHTML=d.band_seq.slice(-60).reverse().map(bc=>
    `<div class="bc-pill">${bc.date} ${bc.ts}
      <span style="color:var(--orange)">${bc.from}</span>
      <span class="bc-arrow">→</span>
      <span style="color:var(--cyan)">${bc.to}</span>
    </div>`).join("");
}

// ═══════════════════════════════════════════════════════════ QSO LOG ══════
function buildLog(d){
  document.getElementById("log-tbody").innerHTML=d.qsos.map((q,i)=>{
    const col=CONT_COLS[q.cont]||"var(--text)";
    return `<tr>
      <td class="dim">${d.qsos.length-i}</td>
      <td class="dim">${q.ts}</td>
      <td class="dim">${q.date}</td>
      <td class="hi" style="font-weight:700">${q.call}</td>
      <td style="color:var(--orange)">${q.band}</td>
      <td>${q.mode}</td>
      <td class="dim">${q.freq}</td>
      <td>${q.entity}</td>
      <td style="color:${col};font-weight:700">${q.cont}</td>
      <td class="dim">${q.cq||""}</td>
      <td class="dim">${q.itu||""}</td>
    </tr>`;
  }).join("");
}

// ─── Fetch & refresh ──────────────────────────────────────────────────────
const CONT_COLS={"NA":"#42a5f5","EU":"#66bb6a","AS":"#ffa726","AF":"#ef5350",
                 "OC":"#ce93d8","SA":"#ffeb3b","AN":"#80deea"};

function load(){
  fetch("/api/stats/detail")
    .then(r=>r.json())
    .then(d=>{ render(d); if(window._mapInit && _mapInst) { _mapInst.remove(); window._mapInit=false; } })
    .catch(e=>{ document.getElementById("loading").innerHTML=
      `<div style="color:var(--red);font-family:var(--font-mono)">Error: ${e}</div>`; });
}
load();
setInterval(load,30000);
</script>
</body></html>"""



    def _build_about_page(self) -> str:
        return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>About — UDP Live Log</title>
<style>
  :root{{--bg:#0d1117;--card:#161b22;--border:#30363d;--text:#e6edf3;
        --muted:#8b949e;--green:#3fb950;--blue:#58a6ff;--orange:#d29922;
        --red:#f85149;--purple:#bc8cff;--cyan:#39d4d4;}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);
        font-family:'Segoe UI',system-ui,sans-serif;min-height:100vh}}
  a{{color:var(--blue);text-decoration:none}}
  a:hover{{text-decoration:underline}}

  .topbar{{background:#0d1117;border-bottom:1px solid var(--border);
    padding:5px 20px;display:flex;align-items:center;
    justify-content:space-between;flex-wrap:wrap;gap:8px;
    position:sticky;top:0;z-index:10}}
  .topbar-left{{display:flex;align-items:center;gap:12px}}
  .site-title{{font-size:.9rem;color:var(--muted)}}
  .version-badge{{background:#1f3829;color:var(--green);border-radius:4px;
    padding:2px 8px;font-size:.72rem;font-family:monospace;font-weight:600}}
  .nav-btn{{display:inline-block;padding:5px 14px;background:var(--card);
    border:1px solid var(--border);border-radius:6px;text-decoration:none;
    font-size:.82rem;white-space:nowrap}}
  .nav-btn:hover{{border-color:var(--blue);background:#1c2128}}

  .hero{{background:linear-gradient(135deg,#0d1f12 0%,#0d1117 60%,#111827 100%);
    border-bottom:1px solid var(--border);padding:40px 40px 32px}}
  .hero h1{{font-size:1.8rem;font-weight:800;color:var(--text);margin-bottom:6px}}
  .hero p{{font-size:.9rem;color:var(--muted);max-width:680px;line-height:1.7}}
  .hero-meta{{display:flex;flex-wrap:wrap;gap:8px;margin-top:16px}}
  .meta-pill{{display:inline-flex;align-items:center;gap:5px;padding:4px 12px;
    border-radius:20px;font-size:.72rem;font-weight:600;border:1px solid}}
  .pill-green{{background:#1f3829;color:var(--green);border-color:#2d5a3a}}
  .pill-blue{{background:#1f2f47;color:var(--blue);border-color:#2d4a6e}}
  .pill-orange{{background:#2d2000;color:var(--orange);border-color:#4d3800}}
  .pill-purple{{background:#2a1f47;color:var(--purple);border-color:#3d2d66}}
  .pill-cyan{{background:#0d2a2a;color:var(--cyan);border-color:#1a4444}}

  .content{{max-width:1160px;margin:0 auto;padding:40px 32px 64px}}
  @media(max-width:700px){{.content{{padding:24px 16px 48px}}}}

  .section{{margin-bottom:48px}}
  .section-title{{font-size:.85rem;font-weight:700;color:var(--blue);
    text-transform:uppercase;letter-spacing:.1em;margin-bottom:20px;
    padding-bottom:8px;border-bottom:1px solid var(--border);
    display:flex;align-items:center;gap:8px}}

  /* ── feature cards ── */
  .feature-grid{{display:grid;
    grid-template-columns:repeat(auto-fill,minmax(320px,1fr));gap:14px}}
  .fc{{background:var(--card);border:1px solid var(--border);border-radius:10px;
    padding:18px 20px;transition:border-color .15s}}
  .fc:hover{{border-color:#444d56}}
  .fc-head{{display:flex;align-items:flex-start;gap:10px;margin-bottom:9px}}
  .fc-icon{{font-size:1.25rem;line-height:1;flex-shrink:0;margin-top:1px}}
  .fc-title{{font-size:.9rem;font-weight:600;color:var(--text);flex:1}}
  .fc-tag{{font-size:.63rem;padding:2px 8px;border-radius:10px;
    font-weight:600;white-space:nowrap;flex-shrink:0}}
  .tag-core{{background:#1f3829;color:var(--green)}}
  .tag-stats{{background:#1f2f47;color:var(--blue)}}
  .tag-ops{{background:#2d2000;color:var(--orange)}}
  .tag-pi{{background:#2a1f47;color:var(--purple)}}
  .fc p{{font-size:.8rem;color:var(--muted);line-height:1.65}}
  .fc ul{{font-size:.8rem;color:var(--muted);line-height:1.65;
    padding-left:1.1em;margin-top:6px}}
  .fc ul li{{margin-bottom:3px}}

  /* ── tech stack ── */
  .tech-grid{{display:flex;flex-wrap:wrap;gap:10px}}
  .tech-pill{{background:var(--card);border:1px solid var(--border);
    border-radius:6px;padding:7px 14px;font-size:.78rem;color:var(--muted);
    font-family:'Consolas','Cascadia Code',monospace}}
  .tech-pill strong{{color:var(--text)}}

  /* ── requirements ── */
  .req-grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:12px}}
  .req-card{{background:var(--card);border:1px solid var(--border);
    border-radius:8px;padding:14px 16px}}
  .req-card h3{{font-size:.78rem;text-transform:uppercase;letter-spacing:.07em;
    color:var(--muted);margin-bottom:8px}}
  .req-card p,.req-card li{{font-size:.82rem;color:var(--text);line-height:1.6}}
  .req-card ul{{padding-left:1.1em}}

  .page-footer{{border-top:1px solid var(--border);padding:18px 32px;
    font-size:.74rem;color:var(--muted);text-align:center;background:#0a0d13}}
  .page-footer strong{{color:var(--green)}}
  code{{font-family:'Consolas','Cascadia Code',monospace;
    background:#21262d;padding:1px 5px;border-radius:3px;font-size:.85em}}
</style>
</head>
<body>

<div class="topbar">
  <div class="topbar-left">
    <span class="site-title">📡 UDP Live Log</span>
    <span class="version-badge">v{VERSION}</span>
  </div>
  <div style="display:flex;gap:6px;flex-wrap:wrap">
    <a href="/"      class="nav-btn" style="color:var(--text)">🏠 Dashboard</a>
    <a href="/logs"  class="nav-btn" style="color:#58a6ff">📁 Logs</a>
    <a href="/stats" class="nav-btn" style="color:#39d353">📊 Stats</a>
    <a href="/tools" class="nav-btn" style="color:#d29922">🛠 Tools</a>
    <a href="/admin" class="nav-btn" style="color:#bc8cff">⚙ Admin</a>
    <a href="/about" class="nav-btn" style="color:#39d4d4;border-color:#39d4d4">ℹ About</a>
  </div>
</div>

<div class="hero">
  <h1>📡 UDP Live Log</h1>
  <p>A self-contained Python bridge that connects N1MM Logger+ to Club Log Livestream,
     with a real-time web dashboard, comprehensive statistics, ADIF logging, and
     Raspberry Pi system monitoring — all running offline with zero external dependencies.</p>
  <div class="hero-meta">
    <span class="meta-pill pill-green">✓ Python stdlib only — no pip installs</span>
    <span class="meta-pill pill-blue">✓ Offline-first — no internet required</span>
    <span class="meta-pill pill-orange">✓ Raspberry Pi native</span>
    <span class="meta-pill pill-purple">✓ All amateur bands inc. VHF/UHF/microwave</span>
    <span class="meta-pill pill-cyan">✓ Single script — just run and go</span>
  </div>
</div>

<div class="content">

  <!-- ══════════════════════════════════════════════════════════ CORE -->
  <div class="section">
    <div class="section-title">🔗 Core — N1MM Integration &amp; Club Log</div>
    <div class="feature-grid">

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">👁</span>
          <span class="fc-title">Real-time N1MM Database Watcher</span>
          <span class="fc-tag tag-core">Core</span>
        </div>
        <p>Polls N1MM Logger+'s SQLite database for changes and immediately reflects
           QSO adds, edits, and deletes in the bridge's own state. No UDP listener
           required — works with N1MM's native database directly.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📤</span>
          <span class="fc-title">Club Log Livestream Gateway</span>
          <span class="fc-tag tag-core">Core</span>
        </div>
        <p>Manages the official Club Log Gateway binary end-to-end:</p>
        <ul>
          <li>Auto-downloads the correct binary for your architecture (x86_64, ARM64, ARMv7)</li>
          <li>Starts, monitors, and restarts the gateway on crash</li>
          <li>Forwards QSO add / edit / delete events in real time</li>
          <li>Tombstone tracking prevents deleted QSOs from being re-submitted</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📋</span>
          <span class="fc-title">ADIF Logger</span>
          <span class="fc-tag tag-core">Core</span>
        </div>
        <p>Writes every QSO to a monthly ADIF file (<code>CALLSIGN_YYYYMM.adi</code>)
           automatically. Files are ready for direct import into logging software or
           upload to LoTW, eQSL, or any ADIF-compatible service.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📻</span>
          <span class="fc-title">Full Band Coverage incl. Microwave</span>
          <span class="fc-tag tag-core">Core</span>
        </div>
        <p>Correctly handles all amateur bands from 160m through microwave:</p>
        <ul>
          <li>Normalises N1MM's band field (MHz integer, cm-wavelength, label string)</li>
          <li>Corrects the ×1000 frequency scale error N1MM uses above 1 GHz</li>
          <li>Supports 6m, 2m, 70cm, 23cm, 13cm, 9cm, 6cm, 3cm and more</li>
          <li>Auto-corrects legacy bad values in the state file on load</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔄</span>
          <span class="fc-title">Persistent State &amp; Reboot Recovery</span>
          <span class="fc-tag tag-core">Core</span>
        </div>
        <p>All QSOs are persisted to <code>log_state.json</code> and survive bridge
           restarts and Pi reboots with full fidelity. Band and frequency data is
           normalised on every load to auto-correct any legacy format issues.</p>
      </div>

    </div>
  </div>

  <!-- ══════════════════════════════════════════════════════════ DASHBOARD -->
  <div class="section">
    <div class="section-title">📊 Live Dashboard</div>
    <div class="feature-grid">

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">⚡</span>
          <span class="fc-title">Real-time Statistics</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <p>Auto-refreshing dashboard (every 5 seconds) showing:</p>
        <ul>
          <li>Total QSOs, unique callsigns, first and last QSO times</li>
          <li>Current rate per hour (rolling 60-minute window)</li>
          <li>Band, mode, and operator breakdowns with animated bar charts</li>
          <li>60-minute rate histogram in 10-minute buckets</li>
          <li>Recent QSO table with time, callsign, band, frequency, and mode</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔴</span>
          <span class="fc-title">Live Status Indicators</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <p>Persistent status badges across the top of every page showing real-time
           health of the Club Log Gateway (connecting / running / error with last error
           message) and ADIF logger (disabled / active with QSO count and current
           filename).</p>
      </div>

    </div>
  </div>

  <!-- ══════════════════════════════════════════════════════════ STATISTICS -->
  <div class="section">
    <div class="section-title">📈 Detailed Statistics (9 Tabs)</div>
    <div class="feature-grid">

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📋</span>
          <span class="fc-title">Summary Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>8 hero stat cards: QSOs, unique calls, DXCC entities, continents, CQ zones, ITU zones, avg rate, day streak</li>
          <li>Full band × mode matrix with row totals and time-per-band</li>
          <li>18-field operating summary (first/last QSO, op time, break time, all best rates)</li>
          <li>Continent, mode, and band-time horizontal bar charts</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">⏱</span>
          <span class="fc-title">Rates Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Best 1 / 10 / 30 / 60-minute rates with timestamps and extrapolated hourly equivalents</li>
          <li>24-hour rolling bar chart (all bands combined)</li>
          <li>Per-band hourly chart with band selector buttons</li>
          <li>Hour-of-day UTC heatmap (24 buckets, intensity-shaded)</li>
          <li>Daily QSO count chart and per-minute sparkline for the full session</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📡</span>
          <span class="fc-title">Bands Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Band × mode matrix (detailed focus view)</li>
          <li>Band changes: total count, by-hour bar chart, recent transition list</li>
          <li>Continents-by-band cross-tab table, colour-coded by continent</li>
          <li>Time-per-band totals in minutes</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🌍</span>
          <span class="fc-title">Countries Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Full DXCC table: rank, entity, total QSOs, per-band breakdown</li>
          <li>First-worked chronology (entity #1, #2, #3… with timestamps)</li>
          <li>DXCC-by-band cross-tab (top 20 entities)</li>
          <li>DXCC-by-mode cross-tab (top 20 entities)</li>
          <li>340-entry embedded prefix table — works fully offline</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔢</span>
          <span class="fc-title">Zones Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>All 40 CQ zones as pills (worked = cyan, unworked = dim)</li>
          <li>All 90 ITU zones as pills (worked = purple, unworked = dim)</li>
          <li>Bar charts of worked CQ and ITU zones</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🗺</span>
          <span class="fc-title">Map &amp; Beams Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Interactive Leaflet contact map — circle markers per DXCC entity, sized by QSO count, coloured by continent</li>
          <li>Lazy-loaded map library (CDN only fetched on tab click — offline safe)</li>
          <li>Per-band SVG beam heading compass roses with 36-bucket (10°) radial distribution</li>
          <li>Average bearing pointer calculated via great-circle from configurable station coordinates</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔡</span>
          <span class="fc-title">Callsigns Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Callsign length distribution bar chart</li>
          <li>Top duplicate callers bar chart (top 30, worked more than once)</li>
          <li>Unique prefixes: count badge and full pill list</li>
          <li>Complete duplicate QSO table with call, band, mode, date, time</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🕐</span>
          <span class="fc-title">Time Analysis Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <ul>
          <li>Operating time vs break time (30-minute gap threshold)</li>
          <li>Full break list with from/to timestamps and duration badges</li>
          <li>Recent band change log with from→to transitions</li>
          <li>Maximum consecutive operating day streak</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📜</span>
          <span class="fc-title">QSO Log Tab</span>
          <span class="fc-tag tag-stats">Stats</span>
        </div>
        <p>Scrollable table of the last 500 contacts with full enriched data:</p>
        <ul>
          <li>UTC time, date, callsign, band, mode, frequency</li>
          <li>DXCC entity, continent (colour-coded), CQ zone, ITU zone</li>
          <li>Sticky header and hover row highlighting</li>
        </ul>
      </div>

    </div>
  </div>

  <!-- ══════════════════════════════════════════════════════════ OPERATIONS -->
  <div class="section">
    <div class="section-title">🛠 Operations</div>
    <div class="feature-grid">

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">👥</span>
          <span class="fc-title">Multi-Account Support</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>Store multiple Club Log callsign / App Password pairs in
           <code>config.ini</code>. Switch the active account instantly from the
           Admin page — the dashboard callsign updates live and the gateway reconnects
           on next restart. Useful when operating under multiple callsigns or event-specific designators.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">⚙</span>
          <span class="fc-title">Web-based Admin Page</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>Full configuration editor accessible from any browser on the local network.
           Add, edit, delete, and switch between callsign accounts with live updates —
           no SSH, no command line, no file editing required during operations.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📥</span>
          <span class="fc-title">ADIF Import</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>Import existing ADIF log files via the Tools page. Useful for pre-loading
           a prior session's log, merging logs from multiple operators, or recovering
           after a state reset. Duplicate detection prevents double-counting.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📁</span>
          <span class="fc-title">Log File Browser</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>The Logs page lists all ADIF files on disk with QSO counts and file sizes.
           Individual files can be downloaded directly from the browser — no file
           system access or SCP required to retrieve logs from the Pi.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔁</span>
          <span class="fc-title">Log Reset</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>Clear the in-memory QSO log and reset the state file from the Tools page,
           without restarting the bridge. Useful between contest sessions or when
           switching operations to a different callsign or event.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔐</span>
          <span class="fc-title">Credential Verification Tool</span>
          <span class="fc-tag tag-ops">Ops</span>
        </div>
        <p>Run <code>--test-clublog</code> from the command line to verify your Club Log
           App Password format, check that the gateway binary is present, and get a
           step-by-step diagnosis before going live — no QSOs needed to test the setup.</p>
      </div>

    </div>
  </div>

  <!-- ══════════════════════════════════════════════════════════ PI -->
  <div class="section">
    <div class="section-title">🍓 Raspberry Pi</div>
    <div class="feature-grid">

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🖥</span>
          <span class="fc-title">System Health Monitor</span>
          <span class="fc-tag tag-pi">Pi</span>
        </div>
        <p>Live Pi vitals at the bottom of every dashboard page, refreshed every 10 seconds:</p>
        <ul>
          <li>CPU usage % with colour-coded bar (green / amber / red)</li>
          <li>CPU temperature with Cool / Warm / HOT status label</li>
          <li>Memory and swap usage with bars</li>
          <li>Disk usage on <code>/</code></li>
          <li>Load averages (1 / 5 / 15 min), coloured relative to core count</li>
          <li>Uptime, hostname, Pi model, OS name, architecture</li>
          <li>Network interfaces with IP address, RX and TX totals</li>
          <li>Pi throttle / under-voltage warning banner</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">📶</span>
          <span class="fc-title">Offline-First Design</span>
          <span class="fc-tag tag-pi">Pi</span>
        </div>
        <ul>
          <li>Zero external HTTP requests on page load — no Google Fonts, no CDN blocking</li>
          <li>System font stack used throughout (no web fonts needed)</li>
          <li>Leaflet map library lazy-loaded only when the Map tab is clicked</li>
          <li>DXCC prefix table embedded in the script — no lookup services required</li>
          <li>Fully functional with no internet connection</li>
        </ul>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">⚡</span>
          <span class="fc-title">Threaded HTTP Server</span>
          <span class="fc-tag tag-pi">Pi</span>
        </div>
        <p>Multi-threaded HTTP server handles concurrent browser requests in parallel
           so a slow API call never blocks the dashboard from loading. CPU sampling
           runs in a dedicated background thread — the 250 ms measurement interval
           never delays any HTTP response.</p>
      </div>

      <div class="fc">
        <div class="fc-head">
          <span class="fc-icon">🔧</span>
          <span class="fc-title">Zero Dependencies</span>
          <span class="fc-tag tag-pi">Pi</span>
        </div>
        <p>The entire bridge is a single <code>.py</code> file using only Python's
           standard library — no <code>pip install</code>, no virtualenv, no package
           manager setup. Copy the script, write a <code>config.ini</code>, and run.
           Works on any Linux system with Python 3.8+.</p>
      </div>

    </div>
  </div>

  <!-- ══════════════════════════════════════════════════════════ TECH -->
  <div class="section">
    <div class="section-title">🔧 Technical Details</div>
    <div class="req-grid" style="margin-bottom:20px">
      <div class="req-card">
        <h3>Requirements</h3>
        <ul>
          <li>Python 3.8 or later</li>
          <li>N1MM Logger+ (Windows PC on same LAN)</li>
          <li>Club Log account with App Password</li>
          <li>Internet access on first run only (gateway auto-download)</li>
        </ul>
      </div>
      <div class="req-card">
        <h3>Configuration</h3>
        <ul>
          <li>Single <code>config.ini</code> file</li>
          <li>Web-based Admin page for live edits</li>
          <li>CLI flags for all key settings</li>
          <li><code>--write-config</code> generates a sample file</li>
        </ul>
      </div>
      <div class="req-card">
        <h3>Default Ports</h3>
        <ul>
          <li>Web dashboard: <code>:8080</code></li>
          <li>N1MM UDP listener: <code>:12060</code></li>
          <li>Club Log Gateway: internal</li>
        </ul>
      </div>
      <div class="req-card">
        <h3>API Endpoints</h3>
        <ul>
          <li><code>GET /api/stats</code> — live QSO stats</li>
          <li><code>GET /api/stats/detail</code> — full statistics dataset</li>
          <li><code>GET /api/system</code> — Pi system vitals</li>
          <li><code>GET /api/uploader</code> — gateway status</li>
          <li><code>GET /api/adif</code> — ADIF logger status</li>
        </ul>
      </div>
    </div>
    <div class="tech-grid">
      <div class="tech-pill"><strong>Python 3</strong> stdlib only</div>
      <div class="tech-pill"><strong>SQLite</strong> N1MM DB watcher</div>
      <div class="tech-pill"><strong>ThreadingMixIn</strong> HTTP server</div>
      <div class="tech-pill"><strong>JSON</strong> persistent state</div>
      <div class="tech-pill"><strong>Leaflet.js</strong> contact map</div>
      <div class="tech-pill"><strong>SVG</strong> compass roses</div>
      <div class="tech-pill"><strong>/proc</strong> system stats</div>
      <div class="tech-pill"><strong>Club Log Gateway</strong> binary</div>
      <div class="tech-pill"><strong>ADIF</strong> export format</div>
      <div class="tech-pill"><strong>Raspberry Pi 4</strong> target platform</div>
    </div>
  </div>

</div>

<div class="page-footer">
  <strong>UDP Live Log v{VERSION}</strong>
</div>
</body>
</html>"""


    def _build_tools_page(self) -> str:
        al      = self.adif_logger
        adif_dir = os.path.abspath(al.directory) if al else ""
        stats   = self.db.stats()

        # Build file options for the server-path import dropdown
        files = self._list_adif_files()
        file_opts = "".join(
            f'<option value="{os.path.join(al.directory, f["name"])}">{f["name"]} ({f["qsos"]} QSOs)</option>'
            for f in files
        ) if files else '<option value="">No ADIF files found</option>'

        return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Tools — UDP Live Log</title>
<style>
  :root{{--bg:#0d1117;--card:#161b22;--border:#30363d;--text:#e6edf3;
        --muted:#8b949e;--green:#3fb950;--blue:#58a6ff;--red:#f85149;--orange:#d29922}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);font-family:"Segoe UI",system-ui,sans-serif;padding:24px;max-width:860px}}
  a.back{{display:inline-flex;align-items:center;gap:6px;color:var(--blue);text-decoration:none;
          font-size:.88rem;margin-bottom:24px;padding:6px 12px;border:1px solid var(--border);
          border-radius:6px;background:var(--card)}}
  a.back:hover{{background:#21262d}}
  h1{{font-size:1.4rem;color:var(--blue);margin-bottom:6px}}
  .subtitle{{color:var(--muted);font-size:.85rem;margin-bottom:28px}}
  .panel{{background:var(--card);border:1px solid var(--border);border-radius:10px;
          padding:22px;margin-bottom:20px}}
  .panel h2{{font-size:1rem;margin-bottom:6px;display:flex;align-items:center;gap:8px}}
  .panel p{{color:var(--muted);font-size:.85rem;margin-bottom:16px;line-height:1.5}}
  label{{display:block;font-size:.85rem;color:var(--muted);margin-bottom:6px}}
  input[type=text],select{{width:100%;padding:8px 10px;background:#0d1117;border:1px solid var(--border);
    border-radius:6px;color:var(--text);font-size:.9rem;margin-bottom:12px}}
  input[type=file]{{width:100%;padding:8px 0;color:var(--text);font-size:.85rem;margin-bottom:12px}}
  .btn{{display:inline-block;padding:9px 20px;border-radius:6px;font-size:.88rem;
        font-weight:600;cursor:pointer;border:none;transition:opacity .15s}}
  .btn:hover{{opacity:.85}}
  .btn-blue{{background:#1f3a6e;color:var(--blue);border:1px solid var(--blue)}}
  .btn-red {{background:#3d1f1f;color:var(--red); border:1px solid var(--red)}}
  .btn-green{{background:#1f3829;color:var(--green);border:1px solid var(--green)}}
  .result{{display:none;margin-top:14px;padding:10px 14px;border-radius:6px;font-size:.85rem}}
  .result.ok  {{background:#1f3829;color:var(--green);border:1px solid #2ea043}}
  .result.err {{background:#3d1f1f;color:var(--red);  border:1px solid #f85149}}
  .warn-box{{background:#2d1f0a;border:1px solid var(--orange);border-radius:8px;
             padding:12px 16px;margin-bottom:16px;font-size:.83rem;color:var(--orange)}}
  .stat-row{{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:16px}}
  .stat-chip{{background:#21262d;border:1px solid var(--border);border-radius:6px;
              padding:8px 14px;font-size:.82rem;color:var(--muted)}}
  .stat-chip strong{{color:var(--text);font-size:1rem}}
  .tabs{{display:flex;gap:0;margin-bottom:16px;border-bottom:1px solid var(--border)}}
  .tab{{padding:8px 18px;cursor:pointer;font-size:.88rem;color:var(--muted);
         border-bottom:2px solid transparent;margin-bottom:-1px}}
  .tab.active{{color:var(--blue);border-bottom-color:var(--blue)}}
  .tab-panel{{display:none}}.tab-panel.active{{display:block}}
  #confirm-reset{{display:none;margin-top:12px;padding:14px;background:#1a0d0d;
                  border:1px solid var(--red);border-radius:8px}}
  #confirm-reset p{{color:var(--red);margin-bottom:12px;font-size:.88rem}}

  .vibe-footer{{text-align:center;padding:14px;font-size:.75rem;color:var(--muted);border-top:1px solid var(--border);margin-top:28px}}
  .vibe-footer a{{color:var(--green);text-decoration:none;font-weight:600}}
  .vibe-footer a:hover{{text-decoration:underline}}
</style>
</head>
<body>
<a class="back" href="/">← Back to Dashboard</a>
<h1>🛠 Tools</h1>
<div class="subtitle">Import ADIF logs into the statistics view, or reset all counters.</div>

<!-- Current stats summary -->
<div class="stat-row">
  <div class="stat-chip"><strong id="t-total">{stats["total"]}</strong><br>QSOs in memory</div>
  <div class="stat-chip"><strong id="t-unique">{stats["unique_calls"]}</strong><br>Unique calls</div>
  <div class="stat-chip"><strong id="t-first">{stats["first_qso"] or "—"}</strong><br>First QSO</div>
  <div class="stat-chip"><strong id="t-last">{stats["last_qso"] or "—"}</strong><br>Last QSO</div>
</div>

<!-- ── IMPORT PANEL ─────────────────────────────────────────────────────── -->
<div class="panel">
  <h2>📥 Import ADIF File</h2>
  <p>Load QSOs from an existing ADIF file into the live statistics.
     Duplicate QSOs (matched by callsign + date + time) are automatically skipped.</p>

  <div class="tabs">
    <div class="tab active" onclick="switchTab('upload')">Upload file</div>
    <div class="tab"        onclick="switchTab('server')">Server path</div>
  </div>

  <!-- Upload tab -->
  <div class="tab-panel active" id="tab-upload">
    <label>Select an ADIF file (.adi or .adif) from your computer:</label>
    <input type="file" id="upload-file" accept=".adi,.adif,.ADI,.ADIF">
    <button class="btn btn-blue" onclick="doUpload()">⬆ Upload &amp; Import</button>
    <div class="result" id="result-upload"></div>
  </div>

  <!-- Server path tab -->
  <div class="tab-panel" id="tab-server">
    <label>Select from ADIF files already on the Pi, or enter a custom path:</label>
    <select id="server-select" onchange="document.getElementById('server-path').value=this.value">
      <option value="">— choose a file —</option>
      {file_opts}
    </select>
    <label>Or enter a full path on the Pi:</label>
    <input type="text" id="server-path" placeholder="/home/pi/logs/mylog.adi">
    <button class="btn btn-blue" onclick="doServerImport()">📂 Import from Path</button>
    <div class="result" id="result-server"></div>
  </div>
</div>

<!-- ── RESET PANEL ─────────────────────────────────────────────────────── -->
<div class="panel">
  <h2>🗑 Reset Statistics</h2>
  <p>Clears all QSOs from the live statistics view and resets the state file.
     Your ADIF log files on disk are <strong>not</strong> affected.</p>
  <div class="warn-box">⚠ This cannot be undone. The state file will be erased.
    ADIF files in <code>{adif_dir}</code> are preserved.</div>
  <button class="btn btn-red" onclick="document.getElementById('confirm-reset').style.display='block'">
    🗑 Reset All Stats…
  </button>
  <div id="confirm-reset">
    <p>Are you sure? All {stats["total"]} QSOs will be removed from memory and the state file.</p>
    <button class="btn btn-red" onclick="doReset()" style="margin-right:10px">Yes, reset everything</button>
    <button class="btn btn-green" onclick="document.getElementById('confirm-reset').style.display='none'">Cancel</button>
  </div>
  <div class="result" id="result-reset"></div>
</div>

<script>
function switchTab(name){{
  document.querySelectorAll(".tab").forEach((t,i)=>{{
    t.classList.toggle("active", (i===0&&name==="upload")||(i===1&&name==="server"));
  }});
  document.getElementById("tab-upload").classList.toggle("active", name==="upload");
  document.getElementById("tab-server").classList.toggle("active", name==="server");
}}

function showResult(id, ok, msg){{
  const el=document.getElementById(id);
  el.style.display="block";
  el.className="result "+(ok?"ok":"err");
  el.textContent=(ok?"✓ ":"✗ ")+msg;
}}

function doUpload(){{
  const file = document.getElementById("upload-file").files[0];
  if(!file){{ showResult("result-upload",false,"Please select a file first."); return; }}
  const fd = new FormData();
  fd.append("adif", file, file.name);
  showResult("result-upload", true, "Uploading…");
  fetch("/api/import", {{method:"POST", body:fd}})
    .then(r=>r.json())
    .then(d=>{{ showResult("result-upload", d.ok, d.message); if(d.ok) refreshChips(); }})
    .catch(e=>showResult("result-upload", false, "Network error: "+e));
}}

function doServerImport(){{
  const path = document.getElementById("server-path").value.trim();
  if(!path){{ showResult("result-server",false,"Please enter or select a file path."); return; }}
  const body = new URLSearchParams({{filepath: path}});
  fetch("/api/import", {{method:"POST",
    headers:{{"Content-Type":"application/x-www-form-urlencoded"}},
    body: body.toString()}})
    .then(r=>r.json())
    .then(d=>{{ showResult("result-server", d.ok, d.message); if(d.ok) refreshChips(); }})
    .catch(e=>showResult("result-server", false, "Network error: "+e));
}}

function doReset(){{
  fetch("/api/reset", {{method:"POST"}})
    .then(r=>r.json())
    .then(d=>{{
      document.getElementById("confirm-reset").style.display="none";
      showResult("result-reset", d.ok, d.message);
      if(d.ok) refreshChips();
    }})
    .catch(e=>showResult("result-reset", false, "Network error: "+e));
}}

function refreshChips(){{
  fetch("/api/stats").then(r=>r.json()).then(d=>{{
    document.getElementById("t-total").textContent  = d.total;
    document.getElementById("t-unique").textContent = d.unique_calls;
    document.getElementById("t-first").textContent  = d.first_qso||"—";
    document.getElementById("t-last").textContent   = d.last_qso ||"—";
  }});
}}
</script>
</body>
</html>"""

    def _build_logs_page(self) -> str:
        files   = self._list_adif_files()
        al      = self.adif_logger
        adif_dir = os.path.abspath(al.directory) if al else "—"
        total_qsos = sum(f["qsos"] for f in files)

        rows = ""
        for f in files:
            badge = ' <span style="background:#1f3829;color:#3fb950;padding:1px 6px;border-radius:4px;font-size:.75rem;font-weight:600">active</span>' if f["current"] else ""
            size_kb = f"{f['size']/1024:.1f} KB"
            rows += f"""
            <tr>
              <td><a href="/logs/download/{f['name']}" style="color:#58a6ff;text-decoration:none;font-weight:600"
                  download="{f['name']}">📄 {f['name']}</a>{badge}</td>
              <td style="color:#8b949e">{f['modified']}</td>
              <td style="color:#8b949e">{size_kb}</td>
              <td style="color:#3fb950;font-weight:600">{f['qsos']}</td>
              <td><a href="/logs/download/{f['name']}" download="{f['name']}"
                  style="display:inline-block;padding:4px 12px;background:#21262d;border:1px solid #30363d;
                         border-radius:6px;color:#58a6ff;text-decoration:none;font-size:.82rem">⬇ Download</a></td>
            </tr>"""

        if not rows:
            rows = '<tr><td colspan="5" style="color:#8b949e;text-align:center;padding:24px">No ADIF files found yet — start logging QSOs!</td></tr>'

        return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>ADIF Log Files</title>
<style>
  :root{{--bg:#0d1117;--card:#161b22;--border:#30363d;--text:#e6edf3;--muted:#8b949e}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);font-family:"Segoe UI",system-ui,sans-serif;padding:24px}}
  a.back{{display:inline-flex;align-items:center;gap:6px;color:#58a6ff;text-decoration:none;
          font-size:.88rem;margin-bottom:20px;padding:6px 12px;border:1px solid #30363d;
          border-radius:6px;background:#161b22}}
  a.back:hover{{background:#21262d}}
  h1{{font-size:1.4rem;color:#58a6ff;margin-bottom:4px}}
  .meta{{color:var(--muted);font-size:.82rem;margin-bottom:20px}}
  .summary{{display:flex;gap:16px;margin-bottom:20px;flex-wrap:wrap}}
  .chip{{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:10px 18px;font-size:.85rem}}
  .chip strong{{display:block;font-size:1.3rem;color:#3fb950}}
  table{{width:100%;border-collapse:collapse;background:#161b22;border:1px solid #30363d;border-radius:10px;overflow:hidden}}
  th{{background:#21262d;color:var(--muted);text-align:left;padding:10px 14px;font-size:.8rem;
      text-transform:uppercase;letter-spacing:.06em;border-bottom:1px solid #30363d}}
  td{{padding:10px 14px;border-bottom:1px solid #21262d;font-size:.88rem}}
  tr:last-child td{{border-bottom:none}}
  tr:hover td{{background:#1c2128}}
  .refresh{{font-size:.75rem;color:var(--muted);margin-top:16px}}
</style>
</head>
<body>
<a class="back" href="/">← Back to Dashboard</a>
<h1>📁 ADIF Log Files</h1>
<div class="meta">Directory: <code style="background:#21262d;padding:2px 6px;border-radius:4px">{adif_dir}</code></div>

<div class="summary">
  <div class="chip"><strong>{len(files)}</strong>Log Files</div>
  <div class="chip"><strong>{total_qsos}</strong>Total QSOs</div>
</div>

<table>
  <thead><tr>
    <th>Filename</th><th>Last Modified</th><th>Size</th><th>QSOs</th><th>Download</th>
  </tr></thead>
  <tbody>{rows}</tbody>
</table>
<p class="refresh">Page does not auto-refresh — <a href="/logs" style="color:#58a6ff">reload</a> to see latest.</p>
</body>
</html>"""

    def _serve_adif_download(self):
        """Serve an ADIF file as a download."""
        al = self.adif_logger
        if not al:
            self._send(404, "text/plain", b"ADIF logging not enabled")
            return
        # Security: only allow simple filenames, no path traversal
        raw      = self.path[len("/logs/download/"):]
        filename = os.path.basename(raw)   # strips any ../ attempts
        if not filename.lower().endswith(".adi") or "/" in filename or "\\" in filename:
            self._send(400, "text/plain", b"Invalid filename")
            return
        filepath = os.path.join(al.directory, filename)
        if not os.path.isfile(filepath):
            self._send(404, "text/plain", b"File not found")
            return
        try:
            with open(filepath, "rb") as f:
                data = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "application/octet-stream")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.wfile.write(data)
        except OSError as e:
            self._send(500, "text/plain", f"Error reading file: {e}".encode())

    def _send(self, code: int, ct: str, body: bytes):
        self.send_response(code)
        self.send_header("Content-Type", ct)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        self.wfile.write(body)

def _get_system_stats() -> dict:
    """Collect Linux/Pi system stats using stdlib only (no psutil required)."""
    import shutil, platform, time as _time, os as _os

    out: dict = {
        "version": VERSION,
        "hostname": platform.node(),
        "pi_model": None,
        "os_name":  None,
        "arch":     platform.machine(),
        "cpu_pct":      None,
        "cpu_temp":     None,
        "cpu_freq_mhz": None,
        "cpu_count":    None,
        "mem_used_mb":  None,
        "mem_total_mb": None,
        "mem_pct":      None,
        "swap_used_mb": None,
        "swap_total_mb":None,
        "disk_used_gb": None,
        "disk_total_gb":None,
        "disk_pct":     None,
        "load_1": None, "load_5": None, "load_15": None,
        "uptime": None, "uptime_sec": None,
        "network": [],
        "throttled": None,   # Pi under-voltage / thermal flag
    }

    # ── CPU % from background-sampled cache (no sleep on request thread) ────
    try:
        out["cpu_pct"] = _cpu_pct_cache.get("pct")
    except Exception:
        pass

    # ── CPU core count ────────────────────────────────────────────────────────
    try:
        out["cpu_count"] = _os.cpu_count()
    except Exception:
        pass

    # ── CPU temperature ───────────────────────────────────────────────────────
    for tpath in ("/sys/class/thermal/thermal_zone0/temp",
                  "/sys/class/hwmon/hwmon0/temp1_input"):
        try:
            with open(tpath) as f:
                out["cpu_temp"] = round(int(f.read().strip()) / 1000.0, 1)
            break
        except Exception:
            pass

    # ── CPU frequency ─────────────────────────────────────────────────────────
    try:
        with open("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq") as f:
            out["cpu_freq_mhz"] = int(f.read().strip()) // 1000
    except Exception:
        pass

    # ── Memory (/proc/meminfo) ────────────────────────────────────────────────
    try:
        mem: dict = {}
        with open("/proc/meminfo") as f:
            for line in f:
                k, _, v = line.partition(":")
                mem[k.strip()] = int(v.strip().split()[0])
        total = mem.get("MemTotal", 0)
        avail = mem.get("MemAvailable", mem.get("MemFree", 0))
        used  = total - avail
        out["mem_total_mb"] = total // 1024
        out["mem_used_mb"]  = used  // 1024
        out["mem_pct"]      = round(100.0 * used / max(total, 1), 1)
        swap_total = mem.get("SwapTotal", 0)
        swap_free  = mem.get("SwapFree",  0)
        out["swap_total_mb"] = swap_total // 1024
        out["swap_used_mb"]  = (swap_total - swap_free) // 1024
    except Exception:
        pass

    # ── Disk ──────────────────────────────────────────────────────────────────
    try:
        d = shutil.disk_usage("/")
        out["disk_total_gb"] = round(d.total / 1024**3, 1)
        out["disk_used_gb"]  = round(d.used  / 1024**3, 1)
        out["disk_pct"]      = round(100.0 * d.used / max(d.total, 1), 1)
    except Exception:
        pass

    # ── Load averages ─────────────────────────────────────────────────────────
    try:
        la = _os.getloadavg()
        out["load_1"]  = round(la[0], 2)
        out["load_5"]  = round(la[1], 2)
        out["load_15"] = round(la[2], 2)
    except Exception:
        pass

    # ── Uptime ────────────────────────────────────────────────────────────────
    try:
        with open("/proc/uptime") as f:
            sec = float(f.read().split()[0])
        out["uptime_sec"] = int(sec)
        d2, r = divmod(int(sec), 86400)
        h,  r = divmod(r, 3600)
        m     = r // 60
        out["uptime"] = (f"{d2}d {h:02d}h {m:02d}m" if d2
                         else f"{h}h {m:02d}m" if h
                         else f"{m}m")
    except Exception:
        pass

    # ── Pi model ──────────────────────────────────────────────────────────────
    for mpath in ("/proc/device-tree/model", "/sys/firmware/devicetree/base/model"):
        try:
            with open(mpath, "rb") as f:
                out["pi_model"] = f.read().rstrip(b"\x00").decode("utf-8", errors="replace")
            break
        except Exception:
            pass
    if not out["pi_model"]:
        try:
            with open("/proc/cpuinfo") as f:
                for line in f:
                    if line.startswith("Model"):
                        out["pi_model"] = line.split(":", 1)[1].strip()
                        break
        except Exception:
            pass

    # ── OS name ───────────────────────────────────────────────────────────────
    try:
        with open("/etc/os-release") as f:
            for line in f:
                if line.startswith("PRETTY_NAME="):
                    out["os_name"] = line.split("=", 1)[1].strip().strip('"\'')
                    break
    except Exception:
        out["os_name"] = platform.system()

    # ── Pi throttling / under-voltage flag ───────────────────────────────────
    try:
        with open("/sys/devices/platform/soc/soc:firmware/raspberrypi-hwmon/hwmon/hwmon1/in0_lcrit_alarm") as f:
            out["throttled"] = f.read().strip() != "0"
    except Exception:
        try:
            import subprocess
            r = subprocess.check_output(["vcgencmd", "get_throttled"],
                                        timeout=1, stderr=subprocess.DEVNULL).decode()
            val = int(r.strip().split("=")[1], 16)
            out["throttled"] = val != 0
            out["throttle_flags"] = {
                "under_voltage":     bool(val & 0x1),
                "freq_capped":       bool(val & 0x2),
                "throttled_now":     bool(val & 0x4),
                "soft_temp_limit":   bool(val & 0x8),
                "under_voltage_ever":bool(val & 0x10000),
                "freq_capped_ever":  bool(val & 0x20000),
                "throttled_ever":    bool(val & 0x40000),
            }
        except Exception:
            pass

    # ── Network interfaces (/proc/net/dev) ────────────────────────────────────
    try:
        ifaces: dict = {}
        with open("/proc/net/dev") as f:
            for line in f.readlines()[2:]:
                parts = line.split()
                iface = parts[0].rstrip(":")
                if iface == "lo":
                    continue
                ifaces[iface] = {
                    "iface":   iface,
                    "rx_mb":   round(int(parts[1])  / 1024**2, 1),
                    "tx_mb":   round(int(parts[9])  / 1024**2, 1),
                    "rx_pkts": int(parts[2]),
                    "tx_pkts": int(parts[11]),
                    "ip":      None,
                }
        # IP addresses via /proc/net/fib_trie (no subprocess needed)
        try:
            import socket, struct
            with open("/proc/net/fib_trie") as f:
                trie = f.read()
            # Parse ip route via ip command if available
            import subprocess
            ip_out = subprocess.check_output(
                ["ip", "-4", "addr", "show"], timeout=2,
                stderr=subprocess.DEVNULL).decode()
            cur = None
            for line in ip_out.splitlines():
                line = line.strip()
                parts2 = line.split()
                if len(parts2) >= 2 and parts2[1].rstrip(":") in ifaces:
                    cur = parts2[1].rstrip(":")
                elif line.startswith("inet ") and cur:
                    ifaces[cur]["ip"] = line.split()[1].split("/")[0]
        except Exception:
            pass
        out["network"] = list(ifaces.values())
    except Exception:
        pass

    return out


class DashboardServer(threading.Thread):
    def __init__(self, port: int, db: LogDatabase, uploader: ClubLogUploader, adif_logger=None):
        super().__init__(daemon=True, name="DashboardServer")
        self.port   = port
        self.server = None
        # Inject references via class attributes (simple approach)
        DashboardHandler.db          = db
        DashboardHandler.uploader    = uploader
        DashboardHandler.adif_logger = adif_logger
        DashboardHandler._cfg_path   = "config.ini"  # overridden by main()

    def run(self):
        # Retry binding a few times in case the port is briefly in use
        for attempt in range(5):
            try:
                class _ThreadedHTTPServer(socketserver.ThreadingMixIn, HTTPServer):
                    daemon_threads = True
                self.server = _ThreadedHTTPServer(("0.0.0.0", self.port), DashboardHandler)
                logging.info(f"Web dashboard on http://0.0.0.0:{self.port}")
                self.server.serve_forever()
                return
            except OSError as e:
                if attempt < 4:
                    logging.warning(f"Dashboard port {self.port} not ready (attempt {attempt+1}/5): {e} — retrying in 2s")
                    time.sleep(2)
                else:
                    logging.error(f"Dashboard failed to start on port {self.port}: {e}")
                    logging.error("Try a different port with --web-port or check nothing else is using port 8080")

# ─────────────────────────────────────────────────────────────────────────────
# CONFIG FILE HELPER
# ─────────────────────────────────────────────────────────────────────────────

def load_config(path: str = "config.ini") -> configparser.ConfigParser:
    cfg = configparser.ConfigParser()
    cfg.read(path)
    return cfg

def write_sample_config(path: str = "config.ini"):
    sample = """[clublog]
# Active account callsign (managed by admin page — do not edit manually)
callsign = W1AW
active   = W1AW
password = YOUR_APP_PASSWORD_HERE

# ── Multiple accounts ──────────────────────────────────────────────────────
# Add one [account.CALLSIGN] section per station/expedition callsign.
# Use the Admin page (⚙ Admin) in the web dashboard to manage these.
#
# [account.W1AW]
# callsign = W1AW
# password = 407-Xl908-Rm690-Xx661-Wi881-Bg822-Hn
#
# [account.VP9/W1AW]
# callsign = VP9/W1AW
# password = 518-Ab123-Cd456-Ef789-Gh012-Ij345-Kl

[web]
# Port for the web dashboard
port = 8080

[adif]
# Directory where monthly ADIF log files are saved
# Files are named <callsign>_<YYYYMM>.adi
directory = adif_logs

# JSON file that persists QSO statistics across restarts/reboots
state_file = log_state.json
"""
    with open(path, "w") as f:
        f.write(sample)
    print(f"Sample config written to {path}")

# ─────────────────────────────────────────────────────────────────────────────
# MAIN
# ─────────────────────────────────────────────────────────────────────────────

def _test_clublog_credentials(args, cfg):
    """Check Club Log Gateway prerequisites and print a clear diagnosis."""

    def cfget(section, key, fallback=""):
        return cfg.get(section, key, fallback=fallback) if cfg.has_section(section) else fallback

    callsign = (getattr(args, "callsign", "") or cfget("clublog", "callsign")).upper()
    password =  getattr(args, "password", "") or cfget("clublog", "password")

    print()
    print("=" * 62)
    print("  Club Log Gateway — Credential & Setup Check")
    print("=" * 62)
    print(f"  Callsign   : {callsign or '(NOT SET)'}")
    print(f"  Password   : {'(set — ' + str(len(password)) + ' chars)' if password else '(NOT SET)'}")

    arch     = detect_gateway_arch()
    gateway_dir = os.path.dirname(os.path.abspath(__file__))
    bin_path = os.path.join(gateway_dir, f"clublog-gateway-{arch}")
    print(f"  Platform   : {arch}")
    print(f"  Binary     : {bin_path}")
    print(f"  Binary OK  : {'YES' if os.path.isfile(bin_path) else 'NOT DOWNLOADED YET (will auto-download on start)'}")
    print()

    missing = []
    if not callsign: missing.append("callsign")
    if not password or password in ("YOUR_APP_PASSWORD_HERE", "yourapppassword", "yourpassword"):
        missing.append("password (App Password)")

    if missing:
        print(f"  ✗ Missing: {', '.join(missing)}")
        print()
        print("  How to fix:")
        print("  1. Log in to https://clublog.org")
        print("  2. Go to Settings → App Passwords")
        print("  3. Create a new App Password — it looks like:")
        print("       407-Xl908-Rm690-Xx661-Wi881-Bg822-Hn")
        print("  4. Put it in config.ini:")
        print("       [clublog]")
        print("       callsign = WW2DX")
        print("       password = 407-Xl908-Rm690-Xx661-Wi881-Bg822-Hn")
        print()
        print("  NOTE: Do NOT use your main Club Log login password.")
        print("        The gateway ONLY accepts App Passwords.")
        print("=" * 62)
        return

    # Validate App Password format: looks like NNN-Xx... segments
    import re as _re
    if not _re.match(r'^\d{3}(-[A-Za-z0-9]{2,6})+$', password):
        print(f"  ⚠ Password format looks wrong.")
        print(f"    App Passwords look like: 407-Xl908-Rm690-Xx661-Wi881-Bg822-Hn")
        print(f"    Your password: {password[:8]}...")
        print(f"    → Get one at clublog.org → Settings → App Passwords")
        print()
    else:
        print(f"  ✓ Password format looks correct")

    print(f"  ✓ Callsign set: {callsign}")
    print()
    print("  The Club Log Gateway does not validate credentials until")
    print("  it actually connects and sends a QSO to Club Log.")
    print()
    print("  To test the full flow:")
    print(f"  1. Run the bridge normally: python3 {os.path.basename(__file__)}")
    print("  2. Log a test QSO in N1MM")
    print("  3. Watch the log for: [Gateway] ... uploaded/QSO/sent")
    print()
    print("  If the gateway prints auth errors, double-check your")
    print("  App Password at: clublog.org → Settings → App Passwords")
    print("=" * 62)
    print()


def main():
    parser = argparse.ArgumentParser(
        description="UDP Live Log — N1MM to Club Log Livestream Bridge + Web Dashboard"
    )
    parser.add_argument("--callsign",    default="", help="Station callsign")
    parser.add_argument("--password",    default="", help="Club Log password")
    parser.add_argument("--web-port",    type=int, default=0,
                        help=f"Web dashboard port (default {DEFAULT_WEB_PORT})")
    parser.add_argument("--state-file",   default="",
                        help="Path to JSON state file for persistence (default: log_state.json)")
    parser.add_argument("--adif-dir",    default="",
                        help="Directory to save ADIF log files (default: ./adif_logs)")
    parser.add_argument("--config",      default="config.ini",
                        help="Path to config.ini")
    parser.add_argument("--write-config", action="store_true",
                        help="Write a sample config.ini and exit")
    parser.add_argument("--test-clublog",  action="store_true",
                        help="Test Club Log credentials and exit")
    parser.add_argument("--debug",        action="store_true")
    args = parser.parse_args()

    if args.write_config:
        write_sample_config(args.config)
        return

    logging.basicConfig(
        level=logging.DEBUG if args.debug else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S"
    )

    if args.test_clublog:
        _test_clublog_credentials(args, load_config(args.config))
        return

    # Merge config file + CLI args (CLI wins)
    cfg = load_config(args.config)

    def cfget(section, key, fallback=""):
        return cfg.get(section, key, fallback=fallback) if cfg.has_section(section) else fallback

    callsign    = (args.callsign    or cfget("clublog", "callsign")).upper()
    password    = args.password     or cfget("clublog", "password")
    web_port    = args.web_port     or cfg.getint("web",  "port",    fallback=DEFAULT_WEB_PORT)
    adif_dir    = args.adif_dir     or cfget("adif", "directory") or "adif_logs"
    state_file  = args.state_file   or cfget("adif", "state_file") or "log_state.json"

    # Decide if upload is enabled
    # Gateway only needs callsign + App Password (no API key required)
    upload_enabled = bool(callsign and password and
                          password not in ("yourapppassword", "yourpassword", ""))
    if not upload_enabled:
        logging.warning(
            "Club Log Gateway disabled — set callsign + application password in "
            "config.ini or via --callsign / --password. "
            "Get an App Password: clublog.org → Settings → App Passwords")

    # Build components
    db          = LogDatabase(state_file=state_file, callsign=callsign)
    gateway_dir = os.path.dirname(os.path.abspath(__file__))
    uploader    = ClubLogGatewayManager(
        callsign=callsign, password=password,
        n1mm_port=DEFAULT_N1MM_UDP_PORT,   # Gateway always uses 12060
        rate=30,
        gateway_dir=gateway_dir, enabled=upload_enabled,
        db=db
    )
    adif_logger = ADIFLogger(adif_dir, callsign, enabled=True)
    listener    = GatewayDBWatcher(
        gateway_dir=gateway_dir,
        callsign=callsign,
        db=db,
        adif_logger=adif_logger
    )
    websvr      = DashboardServer(web_port, db, uploader, adif_logger)
    DashboardHandler._cfg_path = args.config    # so admin page can read/write it

    logging.info("=" * 60)
    logging.info(f"  Bridge version   : {VERSION}")
    logging.info(f"  Station callsign : {callsign or '(not set)'}")
    logging.info(f"  N1MM UDP port    : {DEFAULT_N1MM_UDP_PORT}  (Club Log Gateway listens here)")
    logging.info(f"  Web dashboard    : http://localhost:{web_port}")
    logging.info(f"  Club Log Gateway : {'ENABLED' if upload_enabled else 'DISABLED'}")
    if upload_enabled:
        logging.info(f"  Gateway callsign : {callsign}")
        logging.info(f"  Gateway dir      : {gateway_dir}")
    logging.info(f"  ADIF log dir     : {os.path.abspath(adif_dir)}")
    logging.info(f"  State file       : {os.path.abspath(state_file)}")
    logging.info("=" * 60)

    # Cross-wire uploader ↔ watcher so deletes propagate to the tombstone
    uploader.watcher = listener

    # Start threads
    uploader.start()
    listener.start()
    websvr.start()

    try:
        while True:
            time.sleep(60)
            stats = db.stats()
            logging.info(
                f"Stats: {stats['total']} QSOs | "
                f"{stats['rate_per_hour']}/hr | "
                f"Bands: {stats['band_counts']} | "
                f"Gateway uploads: {uploader.uploaded} | Errors: {uploader.errors} | Status: {uploader.status}"
            )
    except KeyboardInterrupt:
        logging.info("Shutting down.")


if __name__ == "__main__":
    main()
