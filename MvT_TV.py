#!/usr/bin/env python3
"""
MvT_TV.py
---------
SAT>IP television client for a Kathrein EXIP receiver.

The program:
  * reads channels from an M3U playlist,
  * controls the SAT>IP RTSP session itself,
  * receives RTP/MPEG-TS packets,
  * hands the stream to ffmpeg for a rolling HLS/DVR buffer,
  * displays the result in an embedded mpv window,
  * provides keyboard and Tk controls,
  * stores settings and the last volume in an app-named config file.

Required external programs:
  - mpv
  - ffmpeg
  - python3-tk
"""

from __future__ import annotations

import collections
import configparser
import base64
import functools
import itertools
import math
import os
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.request
import uuid
from datetime import datetime, timedelta, timezone
import tkinter as tk
import tkinter.font as tkfont
from pathlib import Path
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from tkinter import filedialog, messagebox, ttk
from urllib.parse import parse_qs, urljoin, urlsplit, urlunsplit


_SCRIPT_PATH = Path(__file__).absolute()
_INVOCATION_PATH = Path(sys.argv[0]).absolute()
_LINK_PATH = next(
    (path for path in (_INVOCATION_PATH, _SCRIPT_PATH) if path.is_symlink()),
    None,
)
_IS_LINK = _LINK_PATH is not None
_LINK_DIR = _LINK_PATH.parent if _LINK_PATH else _INVOCATION_PATH.parent
_TARGET_PATH = _LINK_PATH.resolve() if _LINK_PATH else _SCRIPT_PATH.resolve()
_TARGET_DIR = _TARGET_PATH.parent

# A symlink may carry its own configuration and assets. Check both the link
# name and the target program name, since links are often kept under a short
# alias while their configuration retains the program's original filename.
_LINK_CFG_NAME = next(
    (name for name in dict.fromkeys((
        _LINK_PATH.stem if _LINK_PATH else _INVOCATION_PATH.stem,
        _TARGET_PATH.stem,
    ))
     if (_LINK_DIR / f"{name}.cfg").is_file()),
    None,
)
if _IS_LINK and _LINK_CFG_NAME:
    APP_NAME = _LINK_CFG_NAME
    RESOURCE_DIR = _LINK_DIR
else:
    APP_NAME = _TARGET_PATH.stem or _SCRIPT_PATH.stem
    RESOURCE_DIR = _TARGET_DIR

CFG_FILE = RESOURCE_DIR / f"{APP_NAME}.cfg"
DEFAULT_M3U = RESOURCE_DIR / f"{APP_NAME}.m3u"
LOGO_DIR = RESOURCE_DIR / "logos"

# Console output is only produced when "Debug output on CLI" is enabled.
DEBUG_CLI = False


# Inputs: *args, **kwargs.
# Returns: None.
# Purpose: Print the supplied message when debug output is enabled.
def dprint(*args: object, **kwargs: object) -> None:
    if DEBUG_CLI:
        print(*args, **kwargs)


# Corner of the main window (and of the screen) that serves as the anchor point.
WINDOW_ANCHORS = {
    "top-left": "links oben",
    "top-right": "rechts oben",
    "bottom-left": "links unten",
    "bottom-right": "rechts unten",
}
GEOMETRY_RE = re.compile(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)")


# Inputs: geometry, anchor, screen_w, screen_h.
# Returns: the value produced, or None if this function produces no value.
# Purpose: (width, height, margin_x, margin_y): distance of the window corner `anchor` from the same corner of the screen.
def margins_from_geometry(geometry: str, anchor: str, screen_w: int, screen_h: int):
    """(width, height, margin_x, margin_y): distance of the window corner `anchor`
    from the same corner of the screen."""
    match = GEOMETRY_RE.fullmatch(geometry.strip())
    if not match:
        return None
    width, height, x, y = (int(value) for value in match.groups())
    margin_x = screen_w - (x + width) if anchor.endswith("right") else x
    margin_y = screen_h - (y + height) if anchor.startswith("bottom") else y
    return width, height, margin_x, margin_y


# Inputs: width, height, margin_x, margin_y, anchor, screen_w, screen_h.
# Returns: str.
# Purpose: Convert saved screen-corner distances into the window position and size.
def geometry_from_margins(width: int, height: int, margin_x: int, margin_y: int,
                          anchor: str, screen_w: int, screen_h: int) -> str:
    x = screen_w - margin_x - width if anchor.endswith("right") else margin_x
    y = screen_h - margin_y - height if anchor.startswith("bottom") else margin_y
    # Keep the title bar reachable if the screen is smaller than when saved.
    x = min(max(x, 100 - width), screen_w - 100)
    y = min(max(y, 0), screen_h - 60)
    return f"{width}x{height}+{x}+{y}"


# (label, mpv aspect override, VLC "vratio" value)
ASPECT_MODES = (
    ("Standard", "-1", "default"),
    ("1:1", "1", "1:1"),
    ("5:4", "1.25", "5:4"),
    ("4:3", "1.33333", "4:3"),
    ("16:10", "1.6", "16:10"),
    ("16:9", "1.77778", "16:9"),
    ("2.21:1", "2.21", "221:100"),
    ("2.35:1", "2.35", "235:100"),
    ("2.39:1", "2.39", "239:100"),
)

DEFAULTS = {
    "m3u_file": str(DEFAULT_M3U),
    "exip_ip": "192.168.0.36",
    "rtsp_port": "554",
    "source_mode": "direct",
    "tvh_ip": "127.0.0.1",
    "tvh_port": "9981",
    "tvh_playlist_path": "/playlist",
    "tvh_username": "",
    "tvh_password": "",
    "tvh_login_mode": "auto",
    "small_jump": "10",
    "big_jump": "60",
    "number_timeout_ms": "2000",
    "timeshift_directory": str(Path.home() / ".cache" / APP_NAME),
    "timeshift_ram": "false",
    "timeshift_size_gb": "16",
    "timeshift_ram_size_gb": "2",
    "player": "mpv",
    "vlc_path": "vlc",
    "recording_directory": str(Path.home() / "Videos" / APP_NAME),
    "key_start": "Return", "key_stop": "s", "key_pause": "space",
    "key_next": "n", "key_previous": "p", "key_small_back": "Left",
    "key_small_forward": "Right", "key_big_back": "Shift-Left",
    "key_big_forward": "Shift-Right", "key_volume_up": "Up",
    "key_volume_down": "Down", "key_record": "r", "key_fullscreen": "f",
    "key_record_pause": "Control-r", "key_info": "i", "key_live": "l",
    "key_aspect": "a", "key_channel_list": "Control-l",
    "list_width": "120", "list_font_size": "12", "list_autoclose": "true",
    "tooltip_s": "3", "title_update_s": "11",
    "view_start_mode": "1", "last_view_mode": "1",
    "debug_cli": "false", "aspect": "0",
    "logo_bg": "#A0A0A0",
    "ts_update_s": "13",
    "live_path": "direct",
    "mpv_path": "mpv",
    "live_delay_s": "2",
    "segment_s": "2",
    "probe_s": "2",
    "adaptive_speed": "true",
    "buffer_target_s": "2",
    "speed_min": "0.97",
    "speed_max": "1.03",
    "playlist_window_min": "0",
    "ffmpeg_path": "ffmpeg",
    "volume": "50",
    "now_next_timeout": "4",
    "last_channel": "1",
    "window_geometry": "1100x700+100+100",
    "window_anchor": "top-right",
    "window_size": "", "window_margin": "",
    "settings_size": "",
    "window_offset": "0,0",
}


class Config:
    """Configuration wrapper.

    The configuration is deliberately kept in a simple INI file so that it
    can also be edited manually. Values changed in the settings dialog are
    written back immediately when the user presses Save.
    """

    # Inputs: filename.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, filename: Path) -> None:
        self.filename = filename
        self.parser = configparser.ConfigParser()
        self.values = dict(DEFAULTS)
        self.load()

    # Read the configuration and fall back to defaults for missing values.
    # Inputs: none.
    # Returns: None.
    # Purpose: Read settings from the file and fill in any missing values with defaults.
    def load(self) -> None:
        self.parser.read(self.filename, encoding="utf-8")
        section = self.parser[APP_NAME] if APP_NAME in self.parser else {}
        for key, default in DEFAULTS.items():
            self.values[key] = str(section.get(key, default))
        # Migrate the earlier full TVHeadend URL setting to separate host/port fields.
        if "tvh_ip" not in section and section.get("tvh_url"):
            old_url = urlsplit(str(section.get("tvh_url")))
            if old_url.hostname:
                self.values["tvh_ip"] = old_url.hostname
                self.values["tvh_port"] = str(old_url.port or (443 if old_url.scheme == "https" else 9981))

    # Save the current configuration in a compact human-readable INI file.
    # Inputs: none.
    # Returns: None.
    # Purpose: Save the settings selected in the dialog.
    def save(self) -> None:
        self.parser[APP_NAME] = self.values
        with self.filename.open("w", encoding="utf-8") as f:
            self.parser.write(f)

    # Return one configuration value as a string.
    # Inputs: key.
    # Returns: str.
    # Purpose: Return the requested setting from the configuration.
    def get(self, key: str) -> str:
        return self.values.get(key, DEFAULTS[key])

    # Set one configuration value and keep it as a string for ConfigParser.
    # Inputs: key, value.
    # Returns: None.
    # Purpose: Save the supplied value in the configuration.
    def set(self, key: str, value: str) -> None:
        self.values[key] = value


# Inputs: url, username, password, login_mode, timeout.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Open a TVHeadend URL using anonymous, explicit, or fallback login.
def open_tvh_url(url: str, username: str, password: str, login_mode: str,
                 timeout: float = 10):
    """Open a TVHeadend URL using anonymous, explicit, or fallback login."""
    mode = login_mode.strip().lower()
    if mode not in ("auto", "on", "off"):
        mode = "auto"

    # Inputs: none.
    # Returns: the value produced, or None if this function produces no value.
    # Purpose: Open the TVHeadend address while sending the configured user name and password.
    def open_authenticated():
        request = urllib.request.Request(url)
        token = base64.b64encode(f"{username}:{password}".encode()).decode("ascii")
        request.add_header("Authorization", f"Basic {token}")
        return urllib.request.urlopen(request, timeout=timeout)

    if mode == "on":
        return open_authenticated()
    if mode == "off":
        return urllib.request.urlopen(url, timeout=timeout)

    try:
        return urllib.request.urlopen(url, timeout=timeout)
    except urllib.error.HTTPError as exc:
        if exc.code not in (401, 403) or not username:
            raise
        exc.close()
        return open_authenticated()


# Inputs: url.
# Returns: set[int].
# Purpose: PIDs requested in a SAT>IP URL (pids=... and addpids=...).
def parse_url_pids(url: str) -> set[int]:
    """PIDs requested in a SAT>IP URL (pids=... and addpids=...)."""
    found: set[int] = set()
    try:
        query = parse_qs(urlsplit(url).query)
    except ValueError:
        return found
    for key in ("pids", "addpids"):
        for value in query.get(key, []):
            for part in value.split(","):
                part = part.strip()
                if part.isdigit():
                    found.add(int(part))
    return found


class Channel:
    """One entry from the M3U playlist.

    The URL is retained unchanged wherever possible because SAT>IP URLs can
    contain receiver-specific parameters. The displayed name is taken from
    EXTINF when available.
    """

    # Inputs: name, url.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, name: str, url: str) -> None:
        self.name = name
        self.url = url
        self.service_id: int | None = None
        self.pids = parse_url_pids(url)


class SatIpClient:
    """Minimal SAT>IP RTSP client for an unicast RTP/MPEG-TS session.

    A new local UDP port pair is allocated for every tune operation.
    RTSP SETUP negotiates RTP/RTCP ports and PLAY starts the selected
    transponder/service. RTP payloads are forwarded to a local UDP socket
    consumed by ffmpeg.
    """

    # Inputs: exip_ip, rtsp_port, output_host, output_port, payload_callback.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, exip_ip: str, rtsp_port: int, output_host: str,
                 output_port: int,
                 payload_callback: callable | None = None) -> None:
        self.exip_ip = exip_ip
        self.rtsp_port = rtsp_port
        self.output_host = output_host
        self.output_port = output_port

        self.rtsp_sock: socket.socket | None = None
        self.rtsp_lock = threading.Lock()
        self.rtp_sock: socket.socket | None = None
        self.session: str | None = None
        self.cseq = 1
        self.stop_event = threading.Event()
        self.receive_thread: threading.Thread | None = None
        self.worker_thread: threading.Thread | None = None
        # Optional consumer for the raw MPEG-TS (live relay for the player).
        self.tap: callable | None = None
        self.keepalive_thread: threading.Thread | None = None
        self.forward_sock: socket.socket | None = None
        self.last_url = ""
        self.payload_callback = payload_callback
        self.rtp_packets = 0
        self.rtp_valid_packets = 0
        self.ts_payloads = 0
        self.bytes_forwarded = 0
        self.trace_last = 0.0
        self.last_rtp_sequence: int | None = None
        self.rtp_sequence_gaps = 0
        self.rtp_bad_packets = 0
        self.recording: Recording | None = None

    # Create the UDP sockets used for RTP reception and local forwarding.
    # Inputs: none.
    # Returns: int.
    # Purpose: Open a local UDP socket so the receiver can send RTP packets to this application.
    def _open_udp(self) -> int:
        self.rtp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.rtp_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        # A large kernel buffer absorbs short pauses of the Python threads.
        # Linux silently limits this to net.core.rmem_max.
        try:
            self.rtp_sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 8 * 1024 * 1024)
        except OSError:
            pass
        self.rtp_sock.bind(("0.0.0.0", 0))
        self.rtp_sock.settimeout(1.0)
        try:
            actual = self.rtp_sock.getsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF)
            dprint(f"[RTP] Empfangspuffer: {actual} Bytes", flush=True)
        except OSError:
            pass
        return self.rtp_sock.getsockname()[1]

    # Open the RTSP TCP connection and reset the RTSP sequence counter.
    # Inputs: none.
    # Returns: None.
    # Purpose: Connect to the receiver using RTSP, the protocol used to start and control the stream.
    def _open_rtsp(self) -> None:
        self.rtsp_sock = socket.create_connection(
            (self.exip_ip, self.rtsp_port), timeout=5.0
        )
        self.rtsp_sock.settimeout(5.0)
        self.cseq = 1

    # Send one RTSP request and return the complete response header/body.
    # Inputs: method, uri, headers.
    # Returns: str.
    # Purpose: Send one RTSP command and return the receiver response.
    def _request(self, method: str, uri: str, headers: dict[str, str] | None = None) -> str:
        with self.rtsp_lock:
            if self.rtsp_sock is None:
                raise RuntimeError("RTSP socket is not open")

            lines = [
                f"{method} {uri} RTSP/1.0",
                f"CSeq: {self.cseq}",
                f"User-Agent: {APP_NAME}/1.0",
            ]
            self.cseq += 1

            if headers:
                for key, value in headers.items():
                    lines.append(f"{key}: {value}")

            data = ("\r\n".join(lines) + "\r\n\r\n").encode("ascii")
            self.rtsp_sock.sendall(data)

            response = self._recv_rtsp_response()
        status = response.split("\r\n", 1)[0]
        if not re.search(r"RTSP/1\.[0-9]\s+2\d\d", status):
            raise RuntimeError(f"SAT>IP RTSP error: {status}")
        return response

    # Keep the Kathrein RTSP session alive while RTP is playing.
    # Inputs: session_header.
    # Returns: None.
    # Purpose: Periodically contact the receiver so it keeps the current stream session open.
    def _start_keepalive(self, session_header: str) -> None:
        timeout_match = re.search(r"(?i)(?:^|;)\s*timeout\s*=\s*(\d+)", session_header)
        session_timeout = int(timeout_match.group(1)) if timeout_match else 60
        interval = max(5, min(20, session_timeout // 2))

        # Inputs: none.
        # Returns: None.
        # Purpose: Keep the receiver session open while the stream is playing.
        def keepalive_loop() -> None:
            while not self.stop_event.wait(interval):
                if not self.rtsp_uri or not self.session:
                    return
                try:
                    self._request(
                        "OPTIONS", self.rtsp_uri,
                        {"Session": self.session},
                    )
                except Exception as exc:
                    if not self.stop_event.is_set():
                        dprint(f"[SAT>IP] RTSP-Keepalive fehlgeschlagen: {exc}", flush=True)
                    return

        self.keepalive_thread = threading.Thread(
            target=keepalive_loop, name="SATIP-Keepalive", daemon=True
        )
        self.keepalive_thread.start()

    # Read an RTSP response including its optional message body.
    # Inputs: none.
    # Returns: str.
    # Purpose: Read one complete RTSP response, including its body if present.
    def _recv_rtsp_response(self) -> str:
        assert self.rtsp_sock is not None
        data = b""
        while b"\r\n\r\n" not in data:
            chunk = self.rtsp_sock.recv(4096)
            if not chunk:
                raise ConnectionError("EXIP closed the RTSP connection")
            data += chunk

        header, rest = data.split(b"\r\n\r\n", 1)
        header_text = header.decode("latin1")
        match = re.search(r"(?im)^Content-Length:\s*(\d+)\s*$", header_text)
        content_length = int(match.group(1)) if match else 0

        while len(rest) < content_length:
            chunk = self.rtsp_sock.recv(4096)
            if not chunk:
                break
            rest += chunk

        return (header + b"\r\n\r\n" + rest[:content_length]).decode("latin1")

    # Extract a named RTSP header from a response.
    # Inputs: response, name.
    # Returns: str | None.
    # Purpose: Find and return a named header from an RTSP response.
    @staticmethod
    def _header(response: str, name: str) -> str | None:
        match = re.search(rf"(?im)^{re.escape(name)}:\s*(.+?)\s*$", response)
        return match.group(1).strip() if match else None

    # Extract the RTP client port negotiated by SETUP.
    # Inputs: response.
    # Returns: int | None.
    # Purpose: Read the receiver RTP port from its RTSP transport response.
    @staticmethod
    def _transport_server_port(response: str) -> int | None:
        transport = SatIpClient._header(response, "Transport") or ""
        match = re.search(r"server_port=(\d+)", transport)
        return int(match.group(1)) if match else None

    # Start an RTP receive thread which forwards only RTP payloads as UDP.
    # Inputs: destination_port.
    # Returns: None.
    # Purpose: Receive RTP packets, extract video data, and forward it to the player.
    def _start_receiver(self, destination_port: int) -> None:
        self.stop_event.clear()
        self.forward_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            self.forward_sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 4 * 1024 * 1024)
        except OSError:
            pass
        # Keep a private reference so stop() cannot turn the thread's socket into None.
        forward_sock = self.forward_sock

        # EPG parsing and recording run in their own thread. Otherwise a slow
        # DVB-SI parse or disk write delays the receive loop, the UDP buffer
        # overflows and the player sees a gap (visible as a stutter).
        work_queue: queue.Queue = queue.Queue(maxsize=256)

        # Inputs: none.
        # Returns: None.
        # Purpose: Write recordings and process guide data in a background thread.
        def worker_loop() -> None:
            while True:
                batch = work_queue.get()
                if batch is None:
                    return
                recording = self.recording
                if recording is not None:
                    try:
                        recording.write(batch)
                    except (OSError, ValueError) as exc:
                        dprint(f"[Aufnahme] Schreibfehler: {exc}", flush=True)
                # Channel is being switched: discard the backlog so old EPG
                # data cannot leak into the next channel's parser.
                if self.payload_callback is not None and not self.stop_event.is_set():
                    try:
                        self.payload_callback(batch)
                    except Exception:
                        pass

        worker = threading.Thread(target=worker_loop, name="SATIP-WORK", daemon=True)
        self.worker_thread = worker
        worker.start()

        # Inputs: none.
        # Returns: None.
        # Purpose: Receive video packets from the receiver and forward them to the player.
        def receive_loop() -> None:
            assert self.rtp_sock is not None
            epg_batch = bytearray()
            while not self.stop_event.is_set():
                try:
                    packet, _addr = self.rtp_sock.recvfrom(65536)
                except socket.timeout:
                    continue
                except OSError:
                    break

                self.rtp_packets += 1

                # Trace only the first packet and every 1000th packet so printing
                # cannot overload the receive loop and cause UDP packet loss.
                if self.rtp_packets == 1 or self.rtp_packets % 1000 == 0:
                    dprint(
                        f"[RTP] packet={self.rtp_packets} bytes={len(packet)} "
                        f"from={_addr}",
                        flush=True,
                    )

                # RTP header is normally 12 bytes. CSRC and extension fields
                # are handled so ffmpeg receives a clean MPEG-TS payload.
                if len(packet) < 12:
                    self.rtp_bad_packets += 1
                    continue
                if (packet[0] >> 6) != 2:
                    self.rtp_bad_packets += 1
                    continue

                # Check the RTP sequence number for dropped UDP/RTP packets.
                sequence = int.from_bytes(packet[2:4], "big")
                if self.last_rtp_sequence is not None:
                    expected = (self.last_rtp_sequence + 1) & 0xFFFF
                    if sequence != expected:
                        gap = (sequence - expected) & 0xFFFF
                        if 0 < gap < 0x8000:
                            self.rtp_sequence_gaps += gap
                            dprint(
                                f"[RTP] SEQUENCE GAP: expected={expected} "
                                f"received={sequence} missing={gap}",
                                flush=True,
                            )
                self.last_rtp_sequence = sequence

                cc = packet[0] & 0x0F
                has_extension = bool(packet[0] & 0x10)
                offset = 12 + cc * 4
                if len(packet) < offset:
                    continue

                if has_extension:
                    if len(packet) < offset + 4:
                        continue
                    extension_length = int.from_bytes(
                        packet[offset + 2:offset + 4], "big"
                    )
                    offset += 4 + extension_length * 4

                if packet[0] & 0x20:
                    if not packet:
                        continue
                    padding = packet[-1]
                    if padding:
                        packet = packet[:-padding]

                payload = packet[offset:]
                if not payload:
                    continue

                self.rtp_valid_packets += 1
                if len(payload) >= 188 and payload[0] == 0x47:
                    good_ts = all(payload[i] == 0x47 for i in range(0, min(len(payload), 188 * 7), 188))
                    if good_ts:
                        self.ts_payloads += 1

                # Hand data to the worker thread in larger blocks. If the worker
                # ever falls behind, drop the block instead of blocking the
                # time-critical receive loop.
                if self.payload_callback is not None or self.recording is not None:
                    epg_batch.extend(payload)
                    if len(epg_batch) >= 64 * 1316:
                        try:
                            work_queue.put_nowait(bytes(epg_batch))
                        except queue.Full:
                            pass
                        epg_batch.clear()

                tap = self.tap
                if tap is not None:
                    tap(payload)

                try:
                    forward_sock.sendto(
                        payload, (self.output_host, destination_port)
                    )
                    self.bytes_forwarded += len(payload)
                except OSError:
                    break

            if epg_batch:
                try:
                    work_queue.put_nowait(bytes(epg_batch))
                except queue.Full:
                    pass
            try:
                work_queue.put_nowait(None)
            except queue.Full:
                # Make room so the worker thread can terminate.
                try:
                    work_queue.get_nowait()
                    work_queue.put_nowait(None)
                except (queue.Empty, queue.Full):
                    pass

        self.receive_thread = threading.Thread(
            target=receive_loop, name="SATIP-RTP", daemon=True
        )
        self.receive_thread.start()

    # Tune the EXIP to one complete SAT>IP URL and start RTP delivery.
    # Inputs: url, local_udp_port.
    # Returns: None.
    # Purpose: Ask the SAT>IP receiver to start sending the selected channel.
    def tune(self, url: str, local_udp_port: int) -> None:
        self.stop()
        self.rtp_packets = 0
        self.rtp_valid_packets = 0
        self.ts_payloads = 0
        self.bytes_forwarded = 0
        self.last_rtp_sequence = None
        self.rtp_sequence_gaps = 0
        self.rtp_bad_packets = 0
        self.last_url = url

        parts = urlsplit(url)
        if parts.scheme.lower() not in ("rtsp", "http", "https"):
            raise ValueError(f"Nicht unterstütztes M3U-Format: {url}")

        # Kathrein playlists commonly contain an HTTP URL such as
        # http://192.168.0.36/?src=1&freq=... . The EXIP expects this query
        # as an RTSP request, so only the transport scheme/host are replaced.
        path = parts.path or "/"
        uri = urlunsplit(("rtsp", f"{self.exip_ip}:{self.rtsp_port}",
                          path, parts.query, ""))
        self.rtsp_uri = uri

        local_rtp_port = self._open_udp()
        self._open_rtsp()

        transport = (
            f"RTP/AVP;unicast;client_port={local_rtp_port}-"
            f"{local_rtp_port + 1}"
        )
        dprint("\n=== SAT>IP SETUP ===", flush=True)
        dprint(f"URL:       {url}", flush=True)
        dprint(f"RTSP URI:  {uri}", flush=True)
        dprint(f"Transport: {transport}", flush=True)

        response = self._request(
            "SETUP",
            uri,
            {"Transport": transport},
        )
        dprint("SETUP response:", response.replace("\r", "").strip(), flush=True)

        self.session = self._header(response, "Session")
        if self.session:
            self.session = self.session.split(";", 1)[0]

        dprint(f"Local RTP port: {local_rtp_port}", flush=True)
        dprint(f"Server port:    {self._transport_server_port(response)}", flush=True)
        dprint(f"Session:        {self.session}", flush=True)

        self._start_receiver(local_udp_port)

        headers = {}
        if self.session:
            headers["Session"] = self.session

        play_response = self._request("PLAY", uri, headers)
        dprint("PLAY response:", play_response.replace("\r", "").strip(), flush=True)
        if self.session:
            self._start_keepalive(self._header(response, "Session") or self.session)
        dprint("RTP receiver started; waiting for packets...", flush=True)

    # Print a compact receive summary for diagnosing SAT>IP/RTP problems.
    # Inputs: prefix.
    # Returns: None.
    # Purpose: Print counts that help diagnose missing or invalid stream packets.
    def print_trace(self, prefix: str = "SAT>IP") -> None:
        dprint(
            f"[{prefix}] RTP packets={self.rtp_packets}, "
            f"valid RTP={self.rtp_valid_packets}, TS payloads={self.ts_payloads}, "
            f"forwarded={self.bytes_forwarded} bytes",
            flush=True,
        )

    # Stop the current RTSP session and close all associated sockets.
    # Inputs: none.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self) -> None:
        self.stop_event.set()
        receive_thread = self.receive_thread

        if self.keepalive_thread is not None and self.keepalive_thread is not threading.current_thread():
            self.keepalive_thread.join(timeout=6)
        self.keepalive_thread = None

        if self.rtsp_sock is not None and self.session:
            try:
                self._request(
                    "TEARDOWN",
                    self.rtsp_uri or "*",
                    {"Session": self.session},
                )
            except Exception:
                pass

        for sock in (self.rtp_sock, self.forward_sock, self.rtsp_sock):
            if sock is not None:
                try:
                    sock.close()
                except OSError:
                    pass

        if receive_thread is not None and receive_thread is not threading.current_thread():
            receive_thread.join(timeout=2)
        worker_thread = self.worker_thread
        if worker_thread is not None and worker_thread is not threading.current_thread():
            worker_thread.join(timeout=2)
        self.worker_thread = None

        self.rtp_sock = None
        self.forward_sock = None
        self.rtsp_sock = None
        self.session = None
        self.rtsp_uri = None
        self.receive_thread = None


class Recording:
    """Write incoming MPEG-TS payloads to a recording file; pause skips data."""

    # Inputs: filename.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, filename: Path) -> None:
        self.filename = filename
        self.file = filename.open("wb")
        self.paused = False
        self.lock = threading.Lock()

    # Inputs: payload.
    # Returns: None.
    # Purpose: Write received video data to the recording file unless recording is paused.
    def write(self, payload: bytes) -> None:
        with self.lock:
            if not self.paused and not self.file.closed:
                self.file.write(payload)

    # Inputs: none.
    # Returns: bool.
    # Purpose: Pause or resume video playback.
    def toggle_pause(self) -> bool:
        with self.lock:
            self.paused = not self.paused
            return self.paused

    # Inputs: none.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self) -> None:
        with self.lock:
            if not self.file.closed:
                self.file.flush()
                self.file.close()


class _TvheadendProxyHandler(__import__("http.server").server.BaseHTTPRequestHandler):
    """Serve one authenticated TVHeadend MPEG-TS stream to the local player."""

    # Inputs: none.
    # Returns: None.
    # Purpose: Serve the requested stream to the player over a local web connection.
    def do_GET(self) -> None:
        if self.path != "/stream":
            self.send_error(404)
            return
        self.server.client.stream_to(self)

    # Inputs: _format, *_args.
    # Returns: None.
    # Purpose: Suppress routine web-server messages in the terminal.
    def log_message(self, _format: str, *_args: object) -> None:
        pass


class TvheadendClient:
    """Fetch a TVHeadend HTTP MPEG-TS stream and feed the local pipeline."""

    # Inputs: url, username, password, login_mode, output_host, output_port, payload_callback.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, url: str, username: str, password: str,
                 login_mode: str,
                 output_host: str | None, output_port: int | None,
                 payload_callback: callable | None = None) -> None:
        self.url = url
        self.username = username
        self.password = password
        self.login_mode = login_mode
        self.output = ((output_host, output_port)
                       if output_host is not None and output_port is not None else None)
        self.payload_callback = payload_callback
        self.response = None
        self.stop_event = threading.Event()
        self.thread: threading.Thread | None = None
        self.forward_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.error: Exception | None = None
        self.recording: Recording | None = None
        self.bytes_forwarded = 0
        self.ready_event = threading.Event()
        self.proxy_server = None
        self.tap: callable | None = None

    # Inputs: none.
    # Returns: str.
    # Purpose: Start a small local web server that lets the player read the TVHeadend stream.
    def start_proxy(self) -> str:
        """Expose the upstream HTTP stream locally without segmenting/remuxing it."""
        self.stop_event.clear()
        self.ready_event.clear()
        self.proxy_server = __import__("http.server").server.ThreadingHTTPServer(
            ("127.0.0.1", 0), _TvheadendProxyHandler
        )
        self.proxy_server.daemon_threads = True
        self.proxy_server.client = self
        threading.Thread(
            target=self.proxy_server.serve_forever,
            name="TVHeadend-Proxy",
            daemon=True,
        ).start()
        port = self.proxy_server.server_address[1]
        return f"http://127.0.0.1:{port}/stream"

    # Inputs: handler.
    # Returns: None.
    # Purpose: Copy stream data from TVHeadend to the connected player.
    def stream_to(self, handler: _TvheadendProxyHandler) -> None:
        """Relay source bytes to mpv and tap those same bytes for EPG/recording."""
        headers_sent = False
        try:
            response = open_tvh_url(
                self.url, self.username, self.password, self.login_mode, timeout=10
            )
            self.response = response
            if response.status != 200:
                raise RuntimeError(f"TVHeadend antwortet mit HTTP {response.status}")
            handler.send_response(200)
            handler.send_header("Content-Type", response.headers.get("Content-Type", "video/mp2t"))
            handler.send_header("Cache-Control", "no-store")
            handler.send_header("Connection", "close")
            handler.end_headers()
            headers_sent = True
            pending = bytearray()
            while not self.stop_event.is_set():
                # Batch roughly 45 ms of HD transport data per local write;
                # flushing each 1316-byte RTP-sized chunk would be needless overhead.
                block = response.read(64 * 1316)
                if not block:
                    break
                pending.extend(block)
                usable = len(pending) - (len(pending) % 1316)
                if usable == 0 and len(pending) < 1316:
                    continue
                if usable == 0:
                    usable = len(pending) - (len(pending) % 188)
                if usable:
                    payload = bytes(pending[:usable])
                    del pending[:usable]
                    self._consume_stream_payload(payload)
                    handler.wfile.write(payload)
                    handler.wfile.flush()
            if pending and not self.stop_event.is_set():
                usable = len(pending) - (len(pending) % 188)
                if usable:
                    payload = bytes(pending[:usable])
                    self._consume_stream_payload(payload)
                    handler.wfile.write(payload)
                    handler.wfile.flush()
        except (BrokenPipeError, ConnectionResetError, OSError) as exc:
            if not self.stop_event.is_set():
                self.error = exc
                if not headers_sent:
                    try:
                        handler.send_error(502, "TVHeadend-Stream konnte nicht geöffnet werden")
                    except OSError:
                        pass
        except Exception as exc:
            self.error = exc
            if not headers_sent:
                status = exc.code if isinstance(exc, urllib.error.HTTPError) else 502
                try:
                    handler.send_error(status, "TVHeadend-Stream konnte nicht geöffnet werden")
                except OSError:
                    pass
        finally:
            if self.response is not None:
                try:
                    self.response.close()
                except OSError:
                    pass
                self.response = None

    # Inputs: payload.
    # Returns: None.
    # Purpose: Write the received video data to a recording and pass it to the guide parser.
    def _consume_stream_payload(self, payload: bytes) -> None:
        self.ready_event.set()
        self.bytes_forwarded += len(payload)
        if self.payload_callback:
            try:
                self.payload_callback(payload)
            except Exception as exc:
                dprint(f"[TVHeadend] DVB-SI-Auswertung fehlgeschlagen: {exc}", flush=True)
        if self.recording:
            try:
                self.recording.write(payload)
            except OSError as exc:
                dprint(f"[TVHeadend] Aufnahme-Schreibfehler: {exc}", flush=True)

    # Inputs: none.
    # Returns: None.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self) -> None:
        self.response = open_tvh_url(
            self.url, self.username, self.password, self.login_mode, timeout=10
        )
        if self.response.status != 200:
            self.response.close()
            raise RuntimeError(f"TVHeadend antwortet mit HTTP {self.response.status}")

        # Inputs: none.
        # Returns: None.
        # Purpose: Read data from the TVHeadend stream and pass it into the local player pipeline.
        def receive() -> None:
            pending = bytearray()
            callback_error_reported = False
            recording_error_reported = False
            try:
                while not self.stop_event.is_set():
                    block = self.response.read(1316) if self.response else b""
                    if not block:
                        break
                    pending.extend(block)
                    # Preserve 188-byte MPEG-TS packet boundaries for UDP.
                    usable = len(pending) - (len(pending) % 1316)
                    if usable == 0 and len(pending) < 1316:
                        continue
                    if usable == 0:
                        usable = len(pending) - (len(pending) % 188)
                    if usable:
                        payload = bytes(pending[:usable])
                        del pending[:usable]
                        self.ready_event.set()
                        # Feed the player and ffmpeg first so EPG parsing or
                        # recording I/O cannot delay the live stream.
                        if self.tap is not None:
                            self.tap(payload)
                        if self.output is not None:
                            self.forward_sock.sendto(payload, self.output)
                        self.bytes_forwarded += len(payload) if self.output is not None else 0
                        if self.payload_callback:
                            try:
                                self.payload_callback(payload)
                            except Exception as exc:
                                if not callback_error_reported:
                                    dprint(f"[TVHeadend] DVB-SI-Auswertung fehlgeschlagen: {exc}", flush=True)
                                    callback_error_reported = True
                        if self.recording:
                            try:
                                self.recording.write(payload)
                            except OSError as exc:
                                if not recording_error_reported:
                                    dprint(f"[TVHeadend] Aufnahme-Schreibfehler: {exc}", flush=True)
                                    recording_error_reported = True
                if pending and not self.stop_event.is_set():
                    usable = len(pending) - (len(pending) % 188)
                    if usable:
                        payload = bytes(pending[:usable])
                        self.ready_event.set()
                        if self.tap is not None:
                            self.tap(payload)
                        if self.output is not None:
                            self.forward_sock.sendto(payload, self.output)
                            self.bytes_forwarded += len(payload)
                        if self.payload_callback:
                            try:
                                self.payload_callback(payload)
                            except Exception as exc:
                                if not callback_error_reported:
                                    dprint(f"[TVHeadend] DVB-SI-Auswertung fehlgeschlagen: {exc}", flush=True)
                                    callback_error_reported = True
                        if self.recording:
                            try:
                                self.recording.write(payload)
                            except OSError as exc:
                                if not recording_error_reported:
                                    dprint(f"[TVHeadend] Aufnahme-Schreibfehler: {exc}", flush=True)
                                    recording_error_reported = True
            except Exception as exc:
                if not self.stop_event.is_set():
                    self.error = exc

        self.thread = threading.Thread(target=receive, name="TVHeadend-HTTP", daemon=True)
        self.thread.start()

    # Inputs: timeout.
    # Returns: bool.
    # Purpose: Wait until stream data arrives or the wait time runs out.
    def wait_ready(self, timeout: float = 15.0) -> bool:
        return self.ready_event.wait(timeout)

    # Inputs: none.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self) -> None:
        self.stop_event.set()
        if self.response is not None:
            try:
                self.response.close()
            except OSError:
                pass
            self.response = None
        if self.thread is not None and self.thread is not threading.current_thread():
            self.thread.join(timeout=2)
        self.thread = None
        if self.proxy_server is not None:
            try:
                self.proxy_server.shutdown()
                self.proxy_server.server_close()
            except Exception:
                pass
            self.proxy_server = None
        try:
            self.forward_sock.close()
        except OSError:
            pass


class DvbSiParser:
    """Parse PAT/SDT/EIT data from MPEG-TS packets.

    The parser deliberately only inspects DVB-SI packets. Video and audio
    packets are never modified. SDT supplies the service name and service ID;
    EIT supplies current/next programme title and start/end times.
    """

    # Inputs: update_callback.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, update_callback: callable) -> None:
        self.update_callback = update_callback
        self.buffers: dict[int, bytearray] = {}
        self.service_names: dict[int, str] = {}
        self.events: dict[int, list[dict[str, object]]] = {}
        self.last_emit: float = 0.0
        # PAT: program (= service) number -> PMT PID.
        self.pat_programs: dict[int, int] = {}
        self.lock = threading.RLock()

    # Discard partial tables and cached service data before tuning another stream.
    # Inputs: none.
    # Returns: None.
    # Purpose: Clear programme-guide data before changing channels.
    def reset(self) -> None:
        with self.lock:
            self.buffers.clear()
            self.service_names.clear()
            self.events.clear()
            self.pat_programs.clear()
            self.last_emit = 0.0

    # Feed a block of MPEG-TS data and inspect only packets carrying DVB-SI.
    # Inputs: data.
    # Returns: None.
    # Purpose: Pass received video data to the programme-guide parser.
    def feed(self, data: bytes) -> None:
        with self.lock:
            self._feed(data)

    # Inputs: data.
    # Returns: None.
    # Purpose: Pass received video data to the programme-guide parser.
    def _feed(self, data: bytes) -> None:
        usable = len(data) - (len(data) % 188)
        for pos in range(0, usable, 188):
            packet = data[pos:pos + 188]
            if packet[0] != 0x47:
                continue
            pid = ((packet[1] & 0x1F) << 8) | packet[2]
            if pid not in (0x00, 0x11, 0x12):
                continue
            payload_start = bool(packet[1] & 0x40)
            adaptation = (packet[3] >> 4) & 0x03
            offset = 4
            if adaptation in (2, 3):
                if offset >= 188:
                    continue
                offset += 1 + packet[offset]
            if adaptation == 2 or offset >= 188:
                continue
            payload = packet[offset:]
            if not payload:
                continue
            buf = self.buffers.setdefault(pid, bytearray())
            if payload_start:
                pointer = payload[0]
                payload = payload[1:]
                if pointer <= len(payload):
                    if pointer and buf:
                        buf.extend(payload[:pointer])
                        self._consume_sections(pid, buf)
                        del buf[:]
                    payload = payload[pointer:]
                else:
                    buf.clear()
            buf.extend(payload)
            self._consume_sections(pid, buf)

    # Extract complete PSI/SI sections from a per-PID byte buffer.
    # Inputs: pid, buf.
    # Returns: None.
    # Purpose: Read complete programme-guide messages and update the channel information.
    def _consume_sections(self, pid: int, buf: bytearray) -> None:
        while len(buf) >= 3:
            if buf[0] == 0xFF:
                del buf[:1]
                continue
            length = ((buf[1] & 0x0F) << 8) | buf[2]
            total = 3 + length
            if length < 4 or total > 4096:
                del buf[:1]
                continue
            if len(buf) < total:
                return
            section = bytes(buf[:total])
            del buf[:total]
            if pid == 0x00:
                self._parse_pat(section)
            elif pid == 0x11:
                self._parse_sdt(section)
            elif pid == 0x12:
                self._parse_eit(section)

    # PAT: which PMT PID belongs to which service number.
    # Inputs: sec.
    # Returns: None.
    # Purpose: Read service identifiers from the programme association table.
    def _parse_pat(self, sec: bytes) -> None:
        if len(sec) < 12 or sec[0] != 0x00:
            return
        for pos in range(8, len(sec) - 4 - 3, 4):
            program = (sec[pos] << 8) | sec[pos + 1]
            pmt_pid = ((sec[pos + 2] & 0x1F) << 8) | sec[pos + 3]
            if program != 0:
                self.pat_programs[program] = pmt_pid

    # Decode DVB SDT service descriptors and map service IDs to names.
    # Inputs: sec.
    # Returns: None.
    # Purpose: Read channel names from the service description table.
    def _parse_sdt(self, sec: bytes) -> None:
        if len(sec) < 12 or sec[0] not in (0x42, 0x46):
            return
        loop_end = len(sec) - 4
        pos = 11
        while pos + 5 <= loop_end:
            service_id = (sec[pos] << 8) | sec[pos + 1]
            descriptors_len = ((sec[pos + 3] & 0x0F) << 8) | sec[pos + 4]
            dpos = pos + 5
            dend = min(loop_end, dpos + descriptors_len)
            while dpos + 2 <= dend:
                tag = sec[dpos]
                length = sec[dpos + 1]
                body = sec[dpos + 2:dpos + 2 + length]
                if tag == 0x48 and len(body) >= 2:
                    provider_len = body[1]
                    name_pos = 2 + provider_len
                    if name_pos < len(body):
                        name_len = body[name_pos]
                        raw = body[name_pos + 1:name_pos + 1 + name_len]
                        self.service_names[service_id] = self._decode_dvb_text(raw)
                dpos += 2 + length
            pos = dend
            if service_id in self.events:
                self._emit(service_id)

    # Decode EIT present/following events and update the application callback.
    # Inputs: sec.
    # Returns: None.
    # Purpose: Read current and upcoming programme details from the stream.
    def _parse_eit(self, sec: bytes) -> None:
        if len(sec) < 18 or sec[0] not in (0x4E, 0x4F):
            return
        service_id = (sec[3] << 8) | sec[4]
        version = (sec[5] >> 1) & 0x1F
        pos = 14
        end = len(sec) - 4
        events: list[dict[str, object]] = []
        while pos + 12 <= end:
            event_id = (sec[pos] << 8) | sec[pos + 1]
            start = self._decode_dvb_datetime(sec[pos + 2:pos + 7])
            duration = self._decode_duration(sec[pos + 7:pos + 10])
            descriptors_len = ((sec[pos + 10] & 0x0F) << 8) | sec[pos + 11]
            dpos = pos + 12
            dend = min(end, dpos + descriptors_len)
            title = ""
            short_description = ""
            extended_descriptions: dict[int, str] = {}
            while dpos + 2 <= dend:
                tag = sec[dpos]
                length = sec[dpos + 1]
                body = sec[dpos + 2:dpos + 2 + length]
                if tag == 0x4D and len(body) >= 5:
                    name_len = body[3]
                    name_end = min(len(body), 4 + name_len)
                    title = self._decode_dvb_text(body[4:name_end])
                    text_len_pos = name_end
                    if text_len_pos < len(body):
                        text_len = body[text_len_pos]
                        short_description = self._decode_dvb_text(
                            body[text_len_pos + 1:text_len_pos + 1 + text_len]
                        )
                elif tag == 0x4E and len(body) >= 6:
                    descriptor_number = body[0] >> 4
                    items_length = body[4]
                    text_length_pos = 5 + items_length
                    if text_length_pos < len(body):
                        text_length = body[text_length_pos]
                        description = self._decode_dvb_text(
                            body[text_length_pos + 1:text_length_pos + 1 + text_length]
                        )
                        items: list[str] = []
                        item_pos = 5
                        items_end = min(len(body), text_length_pos)
                        while item_pos < items_end:
                            item_description_length = body[item_pos]
                            item_pos += 1
                            item_description = self._decode_dvb_text(
                                body[item_pos:item_pos + item_description_length]
                            )
                            item_pos += item_description_length
                            if item_pos >= items_end:
                                break
                            item_length = body[item_pos]
                            item_pos += 1
                            item_value = self._decode_dvb_text(body[item_pos:item_pos + item_length])
                            item_pos += item_length
                            if item_description and item_value:
                                items.append(f"{item_description}: {item_value}")
                        parts = items + ([description] if description else [])
                        if parts:
                            extended_descriptions[descriptor_number] = "\n".join(parts)
                dpos += 2 + length
            if start is not None:
                description_parts = [short_description] + [
                    extended_descriptions[number]
                    for number in sorted(extended_descriptions)
                ]
                events.append({
                    "id": event_id,
                    "start": start,
                    "end": start + duration,
                    "title": title or "(ohne Titel)",
                    "description": "\n\n".join(part for part in description_parts if part),
                    "version": version,
                })
            pos = dend
        if events:
            # EIT present/following can arrive as separate table sections.
            # Merge by event ID so an update containing only "Now" does not
            # erase the previously received "Next" event (or vice versa).
            merged = {event["id"]: event for event in self.events.get(service_id, [])}
            merged.update({event["id"]: event for event in events})
            cutoff = datetime.now().astimezone() - timedelta(hours=1)
            self.events[service_id] = sorted(
                (event for event in merged.values() if event["end"] >= cutoff),
                key=lambda event: event["start"],
            )
            self._emit(service_id)

    # Notify the UI when a current/next pair can be determined.
    # Inputs: service_id.
    # Returns: None.
    # Purpose: Send the current and next programme details to the user interface.
    def _emit(self, service_id: int) -> None:
        now = datetime.now().astimezone()
        candidates = sorted(self.events.get(service_id, []), key=lambda e: e["start"])
        current = None
        following = None
        for event in candidates:
            start = event["start"]
            end = event["end"]
            if start <= now < end:
                current = event
            elif start > now and following is None:
                following = event
        if current or following:
            self.update_callback(service_id, self.service_names.get(service_id, ""), current, following)

    # Decode a DVB character field with common German DVB encodings.
    # Inputs: data.
    # Returns: str.
    # Purpose: Convert DVB encoded text into readable text.
    @staticmethod
    def _decode_dvb_text(data: bytes) -> str:
        if not data:
            return ""
        try:
            selectors = {
                0x01: "iso8859_5", 0x02: "iso8859_6", 0x03: "iso8859_7",
                0x04: "iso8859_8", 0x05: "iso8859_9", 0x06: "iso8859_10",
                0x07: "iso8859_11", 0x09: "iso8859_13", 0x0A: "iso8859_14",
                0x0B: "iso8859_15",
            }
            selector = data[0]
            if selector in selectors:
                text = data[1:].decode(selectors[selector], errors="replace")
            elif selector == 0x10 and len(data) >= 3 and data[1] == 0:
                table = data[2]
                codec = {
                    1: "iso8859_1", 2: "iso8859_2", 3: "iso8859_3",
                    4: "iso8859_4", 5: "iso8859_5", 6: "iso8859_6",
                    7: "iso8859_7", 8: "iso8859_8", 9: "iso8859_9",
                    10: "iso8859_10", 11: "iso8859_11", 13: "iso8859_13",
                    14: "iso8859_14", 15: "iso8859_15",
                }.get(table, "latin-1")
                text = data[3:].decode(codec, errors="replace")
            elif selector == 0x11:
                text = data[1:].decode("utf-16-be", errors="replace")
            elif selector == 0x12:
                text = data[1:].decode("euc-kr", errors="replace")
            elif selector == 0x13:
                text = data[1:].decode("gb2312", errors="replace")
            elif selector == 0x14:
                text = data[1:].decode("big5", errors="replace")
            elif selector == 0x15:
                text = data[1:].decode("utf-8", errors="replace")
            else:
                text = data.decode("latin-1", errors="replace")
            return re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text).strip()
        except Exception:
            return data.decode("latin-1", errors="replace").strip()

    # Decode the five-byte DVB UTC/MJD date-time representation.
    # Inputs: data.
    # Returns: datetime | None.
    # Purpose: Convert a DVB date and time value into the computer local time.
    @staticmethod
    def _decode_dvb_datetime(data: bytes) -> datetime | None:
        if len(data) != 5 or data == b"\xff\xff\xff\xff\xff":
            return None
        mjd = (data[0] << 8) | data[1]
        y = int((mjd - 15078.2) / 365.25)
        m = int((mjd - 14956.1 - int(y * 365.25)) / 30.6001)
        d = mjd - 14956 - int(y * 365.25) - int(m * 30.6001)
        k = 1 if m in (14, 15) else 0
        year = y + k + 1900
        month = m - 1 - k * 12
        try:
            hour = int(f"{data[2] >> 4}{data[2] & 0x0F}")
            minute = int(f"{data[3] >> 4}{data[3] & 0x0F}")
            second = int(f"{data[4] >> 4}{data[4] & 0x0F}")
            return datetime(year, month, d, hour, minute, second, tzinfo=timezone.utc).astimezone()
        except (ValueError, OverflowError):
            return None

    # Decode a DVB three-byte BCD duration into a timedelta.
    # Inputs: data.
    # Returns: timedelta.
    # Purpose: Convert a DVB duration value into a time interval.
    @staticmethod
    def _decode_duration(data: bytes) -> timedelta:
        if len(data) != 3:
            return timedelta(0)
        try:
            h = int(f"{data[0] >> 4}{data[0] & 0x0F}")
            m = int(f"{data[1] >> 4}{data[1] & 0x0F}")
            s = int(f"{data[2] >> 4}{data[2] & 0x0F}")
            return timedelta(hours=h, minutes=m, seconds=s)
        except ValueError:
            return timedelta(0)


class LiveRelay:
    """Serve the received MPEG-TS to the local player over HTTP.

    The player gets the live stream directly, without ffmpeg and HLS segments
    in between. A short ring buffer keeps the data since the tune, so a player
    that connects slightly later still receives PAT/PMT and the first
    keyframe and starts as early as possible.
    """

    # Inputs: ring_bytes.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, ring_bytes: int = 8 * 1024 * 1024) -> None:
        self.ring_bytes = ring_bytes
        self.cond = threading.Condition()
        self.chunks: collections.deque[bytes] = collections.deque()
        self.first_index = 0
        self.size = 0
        self.total_bytes = 0
        self.closed = False
        self.server: ThreadingHTTPServer | None = None
        self.thread: threading.Thread | None = None
        self.port = 0

    # Inputs: none.
    # Returns: int.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self) -> int:
        relay = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            # Inputs: none.
            # Returns: None.
            # Purpose: Serve the requested stream to the player over a local web connection.
            def do_GET(self) -> None:
                relay._serve(self)

            # Inputs: _format, *_args.
            # Returns: None.
            # Purpose: Suppress routine web-server messages in the terminal.
            def log_message(self, _format: str, *_args: object) -> None:
                pass

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.port = self.server.server_address[1]
        self.thread = threading.Thread(
            target=self.server.serve_forever, kwargs={"poll_interval": 0.2},
            name="MvT-TV-live", daemon=True,
        )
        self.thread.start()
        return self.port

    # URL for the player. back_bytes limits how much history a new client gets
    # (None = everything since the tune).
    # Inputs: back_bytes.
    # Returns: str.
    # Purpose: Build the local web address that the player uses to read the live stream.
    def url(self, back_bytes: int | None = None) -> str:
        suffix = f"?back={back_bytes}" if back_bytes is not None else ""
        return f"http://127.0.0.1:{self.port}/live.ts{suffix}"

    # Inputs: data.
    # Returns: None.
    # Purpose: Add new video data to the live buffer and wake waiting players.
    def push(self, data: bytes) -> None:
        with self.cond:
            self.chunks.append(data)
            self.size += len(data)
            self.total_bytes += len(data)
            while self.size > self.ring_bytes and len(self.chunks) > 1:
                self.size -= len(self.chunks.popleft())
                self.first_index += 1
            self.cond.notify_all()

    # Caller must hold self.cond.
    # Inputs: back_bytes.
    # Returns: int.
    # Purpose: Choose where a new player should begin reading from the live buffer.
    def _start_index(self, back_bytes: int | None) -> int:
        if back_bytes is None:
            return self.first_index
        index = self.first_index + len(self.chunks)
        total = 0
        for chunk in reversed(self.chunks):
            if total >= back_bytes:
                break
            total += len(chunk)
            index -= 1
        return max(index, self.first_index)

    # Inputs: handler.
    # Returns: None.
    # Purpose: Send buffered stream data to a player over a local web connection.
    def _serve(self, handler: BaseHTTPRequestHandler) -> None:
        back = None
        try:
            back = int(parse_qs(urlsplit(handler.path).query)["back"][0])
        except (KeyError, IndexError, ValueError):
            pass
        try:
            handler.send_response(200)
            handler.send_header("Content-Type", "video/mp2t")
            handler.send_header("Cache-Control", "no-cache")
            handler.end_headers()
            with self.cond:
                position = self._start_index(back)
            while True:
                with self.cond:
                    while not self.closed and position >= self.first_index + len(self.chunks):
                        self.cond.wait(1.0)
                    if self.closed:
                        return
                    if position < self.first_index:
                        # The client was too slow: skip ahead (live stream).
                        position = self.first_index
                    offset = position - self.first_index
                    count = min(16, len(self.chunks) - offset)
                    data = b"".join(itertools.islice(self.chunks, offset, offset + count))
                    position += count
                handler.wfile.write(data)
        except (OSError, ValueError):
            return

    # Inputs: none.
    # Returns: None.
    # Purpose: Close the related window or service and release its resources.
    def close(self) -> None:
        with self.cond:
            self.closed = True
            self.cond.notify_all()
        if self.server is not None:
            try:
                self.server.shutdown()
                self.server.server_close()
            except Exception:
                pass
            self.server = None


class Timeshift:
    """Create and maintain a byte-limited rolling MPEG-TS segment buffer.

    ffmpeg cuts the incoming MPEG-TS into short files. Python maintains the
    actual byte limit and generates a live HLS playlist from the files that
    still belong to the ring. A tiny local HTTP server presents that playlist
    and its segments to mpv, which gives mpv a normal seekable HLS source.
    """

    # Inputs: ffmpeg_path, directory, size_gb, segment_seconds, archive_directory, ram_size_gb, playlist_window_min, probe_s.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, ffmpeg_path: str, directory: Path,
                 size_gb: float, segment_seconds: int = 2,
                 archive_directory: Path | None = None,
                 ram_size_gb: float = 0.0,
                 playlist_window_min: float = 0.0,
                 probe_s: float = 2.0) -> None:
        self.ffmpeg_path = ffmpeg_path
        # (sequence, relative path, duration, wall-clock start) of the
        # completed segments in the current playlist.
        self.playlist_entries: list[tuple[int, str, float, float]] = []
        self.ts_start_sequence: int | None = None
        # Space currently used by the combined ring (RAM + disk), in bytes.
        self.used_bytes = 0
        self.ts_snapshot_counter = 0
        self.ts_lock = threading.Lock()
        self.probe_s = max(0.5, float(probe_s))
        self.playlist_window_min = max(0.0, float(playlist_window_min))
        self.directory = directory
        self.archive_directory = archive_directory
        self.ram_size_bytes = max(0, int(ram_size_gb * 1024 ** 3))
        self.ram_spill_bytes = int(self.ram_size_bytes * 0.25)
        self.ram_threshold_bytes = int(self.ram_size_bytes * 0.75)
        self.disk_size_bytes = max(1, int(size_gb * 1024 ** 3))
        self.disk_chunk_bytes = min(1024 ** 3, self.disk_size_bytes)
        self.segment_paths: dict[int, Path] = {}
        self.segment_mtimes: dict[int, float] = {}
        self.segment_revision = 0
        self.playlist_revision = -1
        self.chunk_sizes: dict[Path, int] = {}
        self.disk_bytes = 0
        self.segment_seconds = max(1, segment_seconds)
        self.process: subprocess.Popen[bytes] | None = None
        self.ffmpeg_errors: list[str] = []
        self.input_port = self._find_free_udp_port()
        self.http_port = self._find_free_tcp_port()
        self.http_server: _TimeshiftHTTPServer | None = None
        self.manager_thread: threading.Thread | None = None
        self.stop_event = threading.Event()
        self.lock = threading.Lock()

    # Find an unused local UDP port for ffmpeg's MPEG-TS input.
    # Inputs: none.
    # Returns: int.
    # Purpose: Ask the operating system for an unused local UDP port.
    @staticmethod
    def _find_free_udp_port() -> int:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
        sock.close()
        return port

    # Find an unused local TCP port for the private HLS HTTP server.
    # Inputs: none.
    # Returns: int.
    # Purpose: Ask the operating system for an unused local TCP port.
    @staticmethod
    def _find_free_tcp_port() -> int:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
        sock.close()
        return port

    # Remove old files from an earlier session of this app.
    # Inputs: wait_for_delete.
    # Returns: None.
    # Purpose: Remove old timeshift files and reset the list of saved segments.
    def clear(self, wait_for_delete: bool = False) -> None:
        directories = [self.directory]
        if self.archive_directory is not None and self.archive_directory != self.directory:
            directories.append(self.archive_directory)
        cleanup_threads: list[threading.Thread] = []
        for directory in directories:
            directory.mkdir(parents=True, exist_ok=True)
            cleanup = directory / f".mvt_cleanup_{uuid.uuid4().hex}"
            moved_any = False
            for path in directory.glob("seg*.ts"):
                try:
                    cleanup.mkdir(exist_ok=True)
                    path.rename(cleanup / path.name)
                    moved_any = True
                except OSError:
                    pass
            for chunk in directory.glob("chunk[0-9]*"):
                if chunk.is_dir():
                    try:
                        cleanup.mkdir(exist_ok=True)
                        chunk.rename(cleanup / chunk.name)
                        moved_any = True
                    except OSError:
                        pass
            # Old cleanup folders can be left behind if the application was
            # terminated while removing a large buffer.
            for stale in directory.glob(".mvt_cleanup_*"):
                if stale != cleanup and stale.is_dir():
                    thread = threading.Thread(
                        target=shutil.rmtree,
                        args=(stale,),
                        kwargs={"ignore_errors": True},
                        name="MvT-TV-Cleanup",
                        daemon=not wait_for_delete,
                    )
                    thread.start()
                    cleanup_threads.append(thread)
            if moved_any:
                thread = threading.Thread(
                    target=shutil.rmtree,
                    args=(cleanup,),
                    kwargs={"ignore_errors": True},
                    name="MvT-TV-Cleanup",
                    daemon=not wait_for_delete,
                )
                thread.start()
                cleanup_threads.append(thread)
        if wait_for_delete:
            for thread in cleanup_threads:
                thread.join()
        # Remove the old playlist as well. Otherwise mpv can open a stale
        # playlist before the first segment of the new channel exists.
        for directory in directories:
            for name in ("live.m3u8", "live.m3u8.tmp"):
                path = directory / name
                try:
                    path.unlink()
                except OSError:
                    pass
        self.segment_paths.clear()
        self.segment_mtimes.clear()
        self.chunk_sizes.clear()
        self.disk_bytes = 0
        self.segment_revision += 1
        self.playlist_revision = -1

    # Return the current segment files in sequence-number order.
    # Inputs: none.
    # Returns: list[Path].
    # Purpose: Find completed video segments and return them in playback order.
    def _segments(self) -> list[Path]:
        # Only scan the shallow, actively written directory. Completed chunks
        # are tracked in memory instead of recursively listing the whole ring.
        roots = [self.directory]
        if self.archive_directory is not None and self.archive_directory != self.directory:
            roots.append(self.archive_directory)
        for root in roots:
            for path in root.glob("seg*.ts"):
                match = re.search(r"(\d+)$", path.stem)
                if match:
                    sequence = int(match.group(1))
                    if self.segment_paths.get(sequence) != path:
                        self.segment_paths[sequence] = path
                        self.segment_revision += 1
        return [self.segment_paths[sequence] for sequence in sorted(self.segment_paths)]

    # Select a roughly 1 GB disk group, creating the next group when needed.
    # Inputs: disk_root, next_size.
    # Returns: Path.
    # Purpose: Choose a disk folder with enough space for the next video segment.
    def _disk_chunk(self, disk_root: Path, next_size: int) -> Path:
        chunks = sorted(self.chunk_sizes, key=lambda p: p.name)
        if chunks:
            latest = chunks[-1]
            chunk_size = self.chunk_sizes[latest]
            if chunk_size + next_size <= self.disk_chunk_bytes:
                return latest
            next_number = int(latest.name.removeprefix("chunk")) + 1
        else:
            next_number = 1
        chunk = disk_root / f"chunk{next_number:08d}"
        chunk.mkdir(parents=True, exist_ok=True)
        self.chunk_sizes[chunk] = 0
        return chunk

    # Move a completed transport segment into the current disk group.
    # Inputs: path, disk_root.
    # Returns: int.
    # Purpose: Move a completed video segment into its storage folder.
    def _move_to_disk_chunk(self, path: Path, disk_root: Path) -> int:
        try:
            size = path.stat().st_size
            chunk = self._disk_chunk(disk_root, size)
            destination = chunk / path.name
            shutil.move(str(path), str(destination))
            sequence_match = re.search(r"(\d+)$", path.stem)
            if sequence_match:
                sequence = int(sequence_match.group(1))
                self.segment_paths[sequence] = destination
                self.segment_revision += 1
            self.chunk_sizes[chunk] = self.chunk_sizes.get(chunk, 0) + size
            self.disk_bytes += size
            return size
        except OSError:
            return 0

    # Group completed disk segments even when no RAM tier is configured.
    # Inputs: none.
    # Returns: None.
    # Purpose: Sort completed segments into the configured storage locations.
    def _organize_disk_segments(self) -> None:
        disk_root = self.archive_directory or self.directory
        root_files = sorted(disk_root.glob("seg*.ts"), key=lambda p: p.name)
        # The final file is currently being written by ffmpeg in disk-only mode.
        completed = root_files if self.archive_directory else root_files[:-1]
        for path in completed:
            self._move_to_disk_chunk(path, disk_root)

    # The newest file is still open in ffmpeg; players only get closed segments.
    # Inputs: none.
    # Returns: list[Path].
    # Purpose: Return the segments that are ready for playback.
    def _completed_segments(self) -> list[Path]:
        files = self._segments()
        return files[:-1] if len(files) > 1 else []

    # Move the oldest completed RAM segments to disk when RAM reaches 75%.
    # Inputs: none.
    # Returns: None.
    # Purpose: Move older video segments from memory to disk to free memory.
    def _spill_ram(self) -> None:
        if self.archive_directory is None or self.ram_size_bytes <= 0:
            return
        self.archive_directory.mkdir(parents=True, exist_ok=True)
        ram_files = sorted(self.directory.glob("seg*.ts"), key=lambda p: p.name)
        sizes: list[tuple[Path, int]] = []
        for path in ram_files:
            try:
                sizes.append((path, path.stat().st_size))
            except OSError:
                continue
        if sum(size for _path, size in sizes) < self.ram_threshold_bytes:
            return

        moved = 0
        # ffmpeg is still writing the newest file, so leave it in RAM.
        for path, size in sizes[:-1]:
            actual_size = self._move_to_disk_chunk(path, self.archive_directory)
            if actual_size == 0:
                break
            moved += actual_size
            if moved >= self.ram_spill_bytes:
                break

    # Evict whole oldest disk groups when their configured storage limit is reached.
    # Inputs: none.
    # Returns: list[Path].
    # Purpose: Delete old video segments when the buffer reaches its size limit.
    def _prune(self) -> list[Path]:
        disk_root = self.archive_directory or self.directory
        active_disk_bytes = sum(
            path.stat().st_size for path in disk_root.glob("seg*.ts") if path.exists()
        )
        disk_total = self.disk_bytes + active_disk_bytes
        # Segments that still live in RAM (only when RAM and disk are combined).
        ram_bytes = 0
        if self.archive_directory is not None and self.archive_directory != self.directory:
            for path in self.directory.glob("seg*.ts"):
                try:
                    ram_bytes += path.stat().st_size
                except OSError:
                    pass
        chunks = sorted(self.chunk_sizes, key=lambda p: p.name)
        # Delete whole oldest groups, leaving room for the next group to grow.
        for chunk in chunks:
            if disk_total <= self.disk_size_bytes:
                break
            chunk_size = self.chunk_sizes.pop(chunk, 0)
            shutil.rmtree(chunk, ignore_errors=True)
            self.disk_bytes -= chunk_size
            disk_total -= chunk_size
            for sequence, path in list(self.segment_paths.items()):
                if path.parent == chunk:
                    del self.segment_paths[sequence]
                    self.segment_mtimes.pop(sequence, None)
                    self.segment_revision += 1

        self.used_bytes = max(0, disk_total) + ram_bytes
        return self._segments()

    # Generate a current HLS playlist from the segments still in the ring.
    # Inputs: files.
    # Returns: None.
    # Purpose: Create the playlist that tells the player which video segments to read.
    def _write_playlist(self, files: list[Path]) -> None:
        if self.playlist_revision == self.segment_revision:
            return
        # Exclude the segment that ffmpeg is currently writing to avoid reads
        # from a growing file. This keeps a short, stable buffer behind live.
        if len(files) > 1:
            files = files[:-1]
        else:
            files = []
        if not files:
            return
        # Optionally limit the playlist length. Very long live playlists make
        # every playlist reload expensive for the player (especially VLC).
        if self.playlist_window_min > 0:
            max_entries = max(10, int(self.playlist_window_min * 60 / self.segment_seconds))
            files = files[-max_entries:]

        media_sequence = int(re.search(r"(\d+)$", files[0].stem).group(1))
        durations: list[float] = []
        mtimes: list[float] = []
        previous_mtime: float | None = None
        for path in files:
            sequence = int(re.search(r"(\d+)$", path.stem).group(1))
            mtime = self.segment_mtimes.get(sequence)
            try:
                if mtime is None:
                    mtime = path.stat().st_mtime
                    self.segment_mtimes[sequence] = mtime
            except OSError:
                mtime = previous_mtime
            if previous_mtime is None or mtime is None:
                duration = float(self.segment_seconds)
            else:
                duration = max(0.1, mtime - previous_mtime)
            durations.append(duration)
            mtimes.append(mtime if mtime is not None else 0.0)
            previous_mtime = mtime
        target_duration = max(
            self.segment_seconds,
            max(int(duration + 0.999) for duration in durations),
        )
        lines = [
            "#EXTM3U",
            "#EXT-X-VERSION:3",
            f"#EXT-X-TARGETDURATION:{target_duration}",
            f"#EXT-X-MEDIA-SEQUENCE:{media_sequence}",
        ]

        entries: list[tuple[int, str, float, float]] = []
        for path, duration, mtime in zip(files, durations, mtimes):
            lines.append(f"#EXTINF:{duration:.3f},")
            if self.archive_directory and path.is_relative_to(self.archive_directory):
                relative = path.relative_to(self.archive_directory).as_posix()
            else:
                relative = path.relative_to(self.directory).as_posix()
            lines.append(relative)
            sequence = int(re.search(r"(\d+)$", path.stem).group(1))
            entries.append((sequence, relative, duration, mtime - duration))

        playlist = self.directory / "live.m3u8"
        tmp = self.directory / "live.m3u8.tmp"
        tmp.write_text("\n".join(lines) + "\n", encoding="utf-8")
        tmp.replace(playlist)
        self.playlist_entries = entries
        if self.ts_start_sequence is not None:
            self._write_ts_playlist(entries, "tsplay.m3u8", False, self.ts_start_sequence)
        self.playlist_revision = self.segment_revision

    # Write a playlist that begins at a chosen segment. A growing one
    # (finite=False) follows the live edge, a finite one ends with ENDLIST.
    # Inputs: entries, name, finite, start_sequence.
    # Returns: bool.
    # Purpose: Create the playlist used to play or seek through saved video segments.
    def _write_ts_playlist(self, entries: list[tuple[int, str, float, float]],
                           name: str, finite: bool, start_sequence: int) -> bool:
        selected = [entry for entry in entries if entry[0] >= start_sequence]
        if not selected:
            return False
        target = max(self.segment_seconds,
                     max(int(entry[2] + 0.999) for entry in selected))
        lines = [
            "#EXTM3U",
            "#EXT-X-VERSION:3",
            *([] if finite else ["#EXT-X-PLAYLIST-TYPE:EVENT"]),
            f"#EXT-X-TARGETDURATION:{target}",
            f"#EXT-X-MEDIA-SEQUENCE:{selected[0][0]}",
        ]
        for _sequence, relative, duration, _start in selected:
            lines.append(f"#EXTINF:{duration:.3f},")
            lines.append(relative)
        if finite:
            lines.append("#EXT-X-ENDLIST")
        with self.ts_lock:
            tmp = self.directory / (name + ".tmp")
            tmp.write_text("\n".join(lines) + "\n", encoding="utf-8")
            tmp.replace(self.directory / name)
        return True

    # Prepare a playlist that starts at the segment containing the wall-clock
    # time `wall`. Returns (URL, wall-clock start of the first segment), or
    # None if the ring does not contain that time yet.
    # Inputs: wall, finite.
    # Returns: tuple[str, float] | None.
    # Purpose: Build a playback playlist beginning at the requested time.
    def prepare_from(self, wall: float, finite: bool) -> tuple[str, float, float] | None:
        entries = list(self.playlist_entries)
        chosen = None
        for entry in entries:
            if entry[3] + entry[2] >= wall:
                chosen = entry
                break
        if chosen is None:
            return None
        sequence, _relative, _duration, start_wall = chosen
        selected = [entry for entry in entries if entry[0] >= sequence]
        end_wall = selected[-1][3] + selected[-1][2]
        try:
            if finite:
                self.ts_snapshot_counter += 1
                name = f"tssnap{self.ts_snapshot_counter}.m3u8"
                written = self._write_ts_playlist(entries, name, True, sequence)
            else:
                name = "tsplay.m3u8"
                written = self._write_ts_playlist(entries, name, False, sequence)
                if written:
                    self.ts_start_sequence = sequence
        except OSError:
            return None
        if not written:
            return None
        return f"http://127.0.0.1:{self.http_port}/{name}", start_wall, end_wall

    # Maintain the byte-limited ring and its live HLS playlist.
    # Inputs: none.
    # Returns: None.
    # Purpose: Watch the video buffer and keep its size within the configured limits.
    def _manager(self) -> None:
        while not self.stop_event.wait(0.25):
            try:
                self._spill_ram()
                self._organize_disk_segments()
                files = self._prune()
                self._write_playlist(files)
            except OSError:
                pass

    # Start ffmpeg, the ring manager and the local HLS HTTP server.
    # Inputs: none.
    # Returns: None.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self) -> None:
        self.stop(clear_files=False)
        self.clear()
        self.used_bytes = 0
        self.stop_event.clear()

        cmd = [
            self.ffmpeg_path,
            "-hide_banner",
            "-loglevel", "error",
            "-fflags", "+genpts",
            # DVB streams contain data/teletext streams that never deliver
            # codec parameters, so ffmpeg would otherwise probe for the full
            # analysis time before it writes the first segment.
            "-analyzeduration", str(int(self.probe_s * 1_000_000)),
            "-probesize", str(int(self.probe_s * 3_000_000)),
            "-i", f"udp://127.0.0.1:{self.input_port}"
                   f"?fifo_size=5000000&overrun_nonfatal=1&buffer_size=8388608",
            # Do not use an explicit -map here. The UDP input is initially
            # empty when ffmpeg starts, so an explicit stream map can fail
            # before the first MPEG-TS packets arrive. ffmpeg's normal output
            # stream selection chooses the usable video/audio streams and
            # leaves DVB/unknown descriptor streams out of the output.
            "-c", "copy",
            "-f", "segment",
            "-segment_time", str(self.segment_seconds),
            "-segment_format", "mpegts",
            str(self.directory / "seg%08d.ts"),
        ]

        dprint("\n=== FFMPEG START ===", flush=True)
        dprint(" ".join(cmd), flush=True)
        self.process = subprocess.Popen(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )

        # Inputs: none.
        # Returns: None.
        # Purpose: Read ffmpeg messages and report stream or segment errors.
        def ffmpeg_trace() -> None:
            if self.process is None or self.process.stderr is None:
                return
            for raw in iter(self.process.stderr.readline, b""):
                line = raw.decode("utf-8", errors="replace").rstrip()
                if line:
                    if "Last message repeated" in line:
                        continue
                    if re.search(
                        r"\[(?:h264|hevc) @ .*\] (?:non-existing (?:SPS|PPS)|no frame!|mmco:)",
                        line,
                        re.IGNORECASE,
                    ):
                        continue
                    dprint(f"[ffmpeg] {line}", flush=True)
                    if re.search(r"(?i)(error|invalid|does not contain any stream)", line):
                        self.ffmpeg_errors.append(line)
                        del self.ffmpeg_errors[:-10]

        threading.Thread(target=ffmpeg_trace, name="MvT-TV-ffmpeg", daemon=True).start()

        self.http_server = _TimeshiftHTTPServer(
            ("127.0.0.1", self.http_port),
            _TimeshiftHandler,
            self.directory,
            self.archive_directory,
        )
        threading.Thread(
            target=self.http_server.serve_forever,
            name="MvT-TV-HTTP",
            daemon=True,
        ).start()

        self.manager_thread = threading.Thread(
            target=self._manager,
            name="MvT-TV-Ring",
            daemon=True,
        )
        self.manager_thread.start()

    # Stop ffmpeg, the ring manager and the local HTTP server.
    # Inputs: clear_files, wait_for_delete.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self, clear_files: bool = True, wait_for_delete: bool = True) -> None:
        self.stop_event.set()

        if self.http_server is not None:
            try:
                self.http_server.shutdown()
                self.http_server.server_close()
            except Exception:
                pass
            self.http_server = None

        if self.manager_thread is not None:
            self.manager_thread.join(timeout=1)
            self.manager_thread = None

        if self.process is not None:
            try:
                self.process.terminate()
                self.process.wait(timeout=2)
            except Exception:
                try:
                    self.process.kill()
                except Exception:
                    pass
            self.process = None

        if clear_files:
            self.clear(wait_for_delete=wait_for_delete)

    # Wait until ffmpeg has created at least one non-empty MPEG-TS segment.
    # Inputs: timeout.
    # Returns: bool.
    # Purpose: Wait until stream data arrives or the wait time runs out.
    def wait_ready(self, timeout: float = 15.0) -> bool:
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if self.process is not None and self.process.poll() is not None:
                return False
            files = self._completed_segments()
            has_completed_segment = False
            for path in files:
                try:
                    if path.stat().st_size > 188:
                        has_completed_segment = True
                        break
                except OSError:
                    pass
            if has_completed_segment:
                playlist = self.directory / "live.m3u8"
                try:
                    entries = [
                        line.strip() for line in playlist.read_text(encoding="utf-8").splitlines()
                        if line.strip() and not line.startswith("#")
                    ]
                except OSError:
                    entries = []
                for entry in entries:
                    relative_path = Path(entry)
                    candidates = [self.directory / relative_path]
                    if self.archive_directory is not None:
                        candidates.append(self.archive_directory / relative_path)
                    for path in candidates:
                        try:
                            if path.stat().st_size > 188:
                                return True
                        except OSError:
                            pass
            time.sleep(0.1)
        return False

    # Wait until the playlist holds at least `seconds` of completed video.
    # Players start close to the live edge of an HLS playlist. If the playlist
    # is still very short, the player runs out of data as soon as the next
    # segment is late, which causes the short freezes.
    # Inputs: seconds, timeout.
    # Returns: bool.
    # Purpose: Wait until enough video is buffered for playback or the timeout expires.
    def wait_buffered(self, seconds: float, timeout: float = 30.0) -> bool:
        if seconds <= 0:
            return True
        playlist = self.directory / "live.m3u8"
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if self.process is not None and self.process.poll() is not None:
                return False
            try:
                lines = playlist.read_text(encoding="utf-8").splitlines()
            except OSError:
                lines = []
            total = 0.0
            for line in lines:
                if line.startswith("#EXTINF:"):
                    try:
                        total += float(line[8:].split(",", 1)[0])
                    except ValueError:
                        pass
            if total >= seconds:
                return True
            time.sleep(0.1)
        return False

    # Return the local HTTP URL used by mpv for the rolling HLS source.
    # Inputs: none.
    # Returns: str.
    # Purpose: Build the local web address for the timeshift playlist.
    def playlist_url(self) -> str:
        return f"http://127.0.0.1:{self.http_port}/live.m3u8"


class _TimeshiftHandler(__import__("http.server").server.SimpleHTTPRequestHandler):
    """HTTP handler serving only the private app timeshift directory."""

    directory: str | None = None
    archive_directory: str | None = None
    # Keep-alive avoids a new TCP connection for every playlist reload/segment.
    protocol_version = "HTTP/1.1"

    # Inputs: directory, archive_directory, *args, **kwargs.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, *args, directory: str | None = None,
                 archive_directory: str | None = None, **kwargs) -> None:
        self.archive_directory = archive_directory
        super().__init__(*args, directory=directory, **kwargs)

    # Inputs: format, *args.
    # Returns: None.
    # Purpose: Suppress routine web-server messages in the terminal.
    def log_message(self, format: str, *args: object) -> None:
        """Suppress HTTP request logging in the terminal."""
        return

    # Inputs: none.
    # Returns: None.
    # Purpose: Finish sending the HTTP response headers to the player.
    def end_headers(self) -> None:
        # VLC can otherwise reuse a cached HLS manifest after it has changed.
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()

    # Inputs: none.
    # Returns: the value produced, or None if this function produces no value.
    # Purpose: Find the requested video file and prepare its HTTP response.
    def send_head(self):
        # Always return the current live playlist, even if a client sends a
        # conditional request based on the previous playlist's timestamp.
        if urlsplit(self.path).path.endswith("/live.m3u8"):
            if "If-Modified-Since" in self.headers:
                del self.headers["If-Modified-Since"]
        return super().send_head()

    # Inputs: path.
    # Returns: str.
    # Purpose: Map a web address to a file in the timeshift folders.
    def translate_path(self, path: str) -> str:
        """Map URL paths into the configured timeshift directory."""
        clean = path.split("?", 1)[0].lstrip("/")
        roots = [Path(self.directory or ".").resolve()]
        if self.archive_directory:
            roots.append(Path(self.archive_directory).resolve())
        for root in roots:
            candidate = (root / clean).resolve()
            if candidate.exists():
                return str(candidate)
        return str(roots[0] / clean)


class _TimeshiftHTTPServer(__import__("http.server").server.ThreadingHTTPServer):
    """Threading HTTP server exposing the current HLS ring locally."""

    # Inputs: server_address, handler, directory, archive_directory.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, server_address: tuple[str, int], handler: type,
                 directory: Path, archive_directory: Path | None = None) -> None:
        bound_handler = functools.partial(
            handler,
            directory=str(directory),
            archive_directory=str(archive_directory) if archive_directory else None,
        )
        super().__init__(server_address, bound_handler)


class MpvPlayer:
    """Control an embedded mpv process through its JSON IPC interface."""

    # Inputs: mpv_path, volume.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, mpv_path: str, volume: int) -> None:
        self.mpv_path = mpv_path
        self.volume = max(0, min(100, volume))
        self.process: subprocess.Popen[bytes] | None = None
        self.ipc_path = Path(f"/tmp/{APP_NAME}_mpv_{os.getpid()}.sock")
        self.lock = threading.Lock()
        self.cache_monitor: threading.Thread | None = None
        self.cache_stop_event = threading.Event()
        self.cache_directory: Path | None = None
        self.disk_cache_limit = 0
        self.request_id = 0
        # Adaptive playback speed (buffer level controller).
        self.adaptive: dict[str, float] | None = None
        self.speed_thread: threading.Thread | None = None
        self.speed_stop_event = threading.Event()
        self.current_speed = 1.0
        self.buffer_ahead: float | None = None
        self.timeshifted = False
        self.is_paused = False
        # True while mpv shows the direct live stream (or a timeshift playlist
        # chosen by the application) instead of the legacy live HLS playlist.
        self.direct_live = False
        self.last_position: float | None = None
        self.ctl_reset = threading.Event()

    # Start mpv embedded in the supplied Tk window.
    # Inputs: parent_window_id, playlist, direct_stream, cache_directory, ram_size_gb, disk_size_gb, adaptive, direct_live, probe_s.
    # Returns: None.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self, parent_window_id: int, playlist: Path | str | None,
              direct_stream: bool = False,
              cache_directory: Path | None = None,
              ram_size_gb: float = 0.0, disk_size_gb: float = 0.0,
              adaptive: dict[str, float] | None = None,
              direct_live: bool = False, probe_s: float = 2.0) -> None:
        self.stop()
        self.direct_live = direct_live
        self.last_position = None
        self.adaptive = adaptive if (adaptive and not direct_stream) else None
        self.current_speed = self.adaptive["min"] if self.adaptive else 1.0
        self.buffer_ahead = None
        self.timeshifted = False
        self.is_paused = False
        try:
            self.ipc_path.unlink()
        except FileNotFoundError:
            pass
        cmd = [
            self.mpv_path,
            "--no-terminal",
            "--vo=gpu",
            "--gpu-context=x11egl",
            "--idle=yes",
            "--keep-open=yes",
            "--osd-level=1",
            # mpv must never react to keyboard or mouse; this app handles all input.
            "--no-input-default-bindings",
            "--input-vo-keyboard=no",
            "--no-input-cursor",
            "--no-osc",
            "--volume=" + str(self.volume),
            "--input-ipc-server=" + str(self.ipc_path),
            f"--wid={parent_window_id}",
        ]
        if direct_stream:
            if cache_directory is None:
                raise ValueError("Für den direkten Stream fehlt das Timeshift-Verzeichnis")
            shutil.rmtree(cache_directory, ignore_errors=True)
            cache_directory.mkdir(parents=True, exist_ok=True)
            ram_bytes = max(64 * 1024 ** 2, int(ram_size_gb * 1024 ** 3))
            disk_bytes = max(1, int(disk_size_gb * 1024 ** 3))
            cmd.extend([
                "--hwdec=auto-safe",
                "--cache=yes",
                "--cache-on-disk=yes",
                "--demuxer-cache-dir=" + str(cache_directory),
                "--demuxer-max-bytes=" + str(int(ram_bytes * 0.75)),
                "--demuxer-max-back-bytes=" + str(int(ram_bytes * 0.25)),
            ])
            self.cache_directory = cache_directory
            self.disk_cache_limit = disk_bytes
        else:
            readahead = self.adaptive["cap"] if self.adaptive else 10.0
            cmd.append(f"--demuxer-readahead-secs={readahead:.0f}")
            cmd.append("--cache=yes")
            if self.adaptive:
                # Start slightly slowed down so the buffer fills while playing.
                cmd.append(f"--speed={self.current_speed:.2f}")
            if direct_live:
                # Short stream analysis (the DVB data streams would otherwise
                # make it run for the full default time), and timeshift
                # playlists start at their first entry instead of the live edge.
                cmd.append(f"--demuxer-lavf-analyzeduration={probe_s:g}")
                cmd.append(f"--demuxer-lavf-probesize={int(probe_s * 3_000_000)}")
                cmd.append("--demuxer-lavf-o=live_start_index=0")
            if playlist:
                cmd.append(str(playlist))

        self.process = subprocess.Popen(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

        for _ in range(100):
            if self.ipc_path.exists():
                break
            time.sleep(0.05)
        if direct_stream:
            self.commands(["loadfile", str(playlist), "replace"])
            self.cache_stop_event.clear()
            self.cache_monitor = threading.Thread(
                target=self._monitor_disk_cache,
                name="MvT-TV-mpv-cache",
                daemon=True,
            )
            self.cache_monitor.start()
        else:
            self._ensure_controller()

    # Inputs: none.
    # Returns: None.
    # Purpose: Start the helper process that controls the embedded video player.
    def _ensure_controller(self) -> None:
        if self.speed_thread is not None and self.speed_thread.is_alive():
            return
        self.speed_stop_event.clear()
        self.speed_thread = threading.Thread(
            target=self._speed_controller,
            name="MvT-TV-speed",
            daemon=True,
        )
        self.speed_thread.start()

    # Inputs: none.
    # Returns: bool.
    # Purpose: Check whether the video player process is still running.
    def alive(self) -> bool:
        return self.process is not None and self.process.poll() is None

    # Show the live stream. The player process keeps running between channels,
    # so a channel change does not pay for starting mpv again.
    # Inputs: url, adaptive.
    # Returns: None.
    # Purpose: Tell the video player to play the live stream address.
    def play_live(self, url: str, adaptive: dict[str, float] | None) -> None:
        self.adaptive = adaptive
        self.direct_live = True
        self.timeshifted = False
        self.is_paused = False
        self.buffer_ahead = None
        self.last_position = None
        self.current_speed = adaptive["min"] if adaptive else 1.0
        self.ctl_reset.set()
        self.commands(
            ["set_property", "pause", False],
            ["set_property", "speed", self.current_speed],
            ["loadfile", url, "replace"],
        )
        self._ensure_controller()

    # Play a timeshift playlist. Returns the first playback position (used by
    # the caller to map positions to wall-clock time) or None.
    # Inputs: url, paused.
    # Returns: float | None.
    # Purpose: Tell the video player to play the timeshift playlist.
    def play_timeshift(self, url: str, paused: bool,
                       start_offset: float = 0.0) -> float | None:
        self.direct_live = True
        self.timeshifted = True
        self.is_paused = bool(paused)
        self.buffer_ahead = None
        self.last_position = None
        self.current_speed = 1.0
        self.commands(
            ["set_property", "speed", 1.0],
            ["loadfile", url, "replace"],
            ["set_property", "pause", bool(paused)],
        )
        time.sleep(0.1)
        deadline = time.monotonic() + 4.0
        while time.monotonic() < deadline:
            position = self._get_property("time-pos")
            if isinstance(position, (int, float)):
                if start_offset > 0.05:
                    # The HLS playlist starts at the beginning of the segment
                    # containing the requested wall-clock time. Continue to
                    # the exact point within that segment after mpv has loaded.
                    self.command("seek", start_offset, "absolute+exact")
                    seek_deadline = time.monotonic() + 1.0
                    while time.monotonic() < seek_deadline:
                        position = self._get_property("time-pos")
                        if isinstance(position, (int, float)) and position >= start_offset - 0.5:
                            break
                        time.sleep(0.05)
                self.last_position = float(position)
                return self.last_position
            time.sleep(0.05)
        return None

    # Inputs: none.
    # Returns: float | None.
    # Purpose: Read the current playback position from the video player.
    def get_position(self) -> float | None:
        return self.last_position

    # Inputs: mode.
    # Returns: None.
    # Purpose: Set the video shape used by the player.
    def set_aspect(self, mode: tuple) -> None:
        self.command("set_property", "video-aspect-override", mode[1])

    # Seconds of data buffered ahead of the playback position, or None.
    # Inputs: position.
    # Returns: float | None.
    # Purpose: Estimate how much video is ready ahead of the current playback point.
    def _buffer_ahead(self, position: object = None) -> float | None:
        if position is None:
            position = self._get_property("time-pos")
        end = self._get_property("demuxer-cache-time")
        if isinstance(position, (int, float)) and isinstance(end, (int, float)):
            return max(0.0, float(end) - float(position))
        state = self._get_property("demuxer-cache-state")
        if isinstance(state, dict):
            duration = state.get("cache-duration")
            if isinstance(duration, (int, float)):
                return max(0.0, float(duration))
        return None

    # Keep the buffer reserve near the target by varying the playback speed.
    # Too little reserve: play slower so the buffer grows. Too much: play
    # slightly faster. Changes are smoothed and rate limited so that neither
    # picture nor (pitch-corrected) sound shows abrupt jumps.
    # Inputs: none.
    # Returns: None.
    # Purpose: Make small playback speed changes to keep playback near the live edge.
    def _speed_controller(self) -> None:
        step = 0.01                 # max speed change per tick (0.5 s)
        # Reserve as a fraction of the target. Stage -3 = slowest speed,
        # 0 = normal speed, +3 = fastest speed (one stage = 1/3 of the range):
        #   <1/2 | 1/2 | 3/4 | 1/1 | 5/4 | 3/2 | >=2/1
        thresholds = (0.5, 0.75, 1.0, 1.25, 1.5, 2.0)
        hysteresis = 0.04           # avoids flapping at a threshold
        stage = -3
        smoothed: float | None = None
        while not self.speed_stop_event.wait(0.5):
            if self.process is None or self.process.poll() is not None:
                return
            if self.ctl_reset.is_set():
                self.ctl_reset.clear()
                stage = -3
                smoothed = None
            if self.is_paused:
                continue
            position = self._get_property("time-pos")
            if isinstance(position, (int, float)):
                self.last_position = float(position)
            cfg = self.adaptive
            if not cfg:
                continue
            target = cfg.get("target", 2.0)
            speed_min = cfg.get("min", 0.97)
            speed_max = cfg.get("max", 1.03)
            cap = cfg.get("cap", 10.0)  # equals the demuxer read-ahead
            ahead = self._buffer_ahead(position)
            if ahead is None:
                continue
            smoothed = ahead if smoothed is None else smoothed + 0.25 * (ahead - smoothed)
            self.buffer_ahead = smoothed

            # After a pause or a jump backwards the user is deliberately behind
            # live and the cache is simply full: leave the speed alone. When
            # the reserve drops below the cache limit again, we are at live.
            if self.timeshifted and not self.direct_live and smoothed < cap - 2.0:
                self.timeshifted = False

            if self.timeshifted:
                desired = 1.0
            else:
                ratio = smoothed / target
                while stage < 3 and ratio >= thresholds[stage + 3] + hysteresis:
                    stage += 1
                while stage > -3 and ratio < thresholds[stage + 2] - hysteresis:
                    stage -= 1
                if stage < 0:
                    desired = 1.0 - (1.0 - speed_min) * (-stage) / 3.0
                else:
                    desired = 1.0 + (speed_max - 1.0) * stage / 3.0

            new_speed = self.current_speed
            if desired > new_speed + step:
                new_speed += step
            elif desired < new_speed - step:
                new_speed -= step
            else:
                new_speed = desired
            new_speed = round(new_speed, 3)
            if new_speed != self.current_speed:
                self.current_speed = new_speed
                self.command("set_property", "speed", new_speed)

    # Inputs: *commands.
    # Returns: None.
    # Purpose: Send several related control commands to the video player.
    def commands(self, *commands: list[object]) -> None:
        """Send ordered mpv IPC commands over one socket connection."""
        import json

        if not self.ipc_path.exists():
            return
        message = "".join(json.dumps({"command": command}) + "\n" for command in commands)
        try:
            with self.lock, socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
                sock.connect(str(self.ipc_path))
                sock.sendall(message.encode("utf-8"))
        except OSError:
            pass

    # Inputs: name.
    # Returns: the value produced, or None if this function produces no value.
    # Purpose: Ask the player for the current value of a named setting.
    def _get_property(self, name: str):
        import json

        self.request_id += 1
        request_id = self.request_id
        request = json.dumps({
            "command": ["get_property", name],
            "request_id": request_id,
        }) + "\n"
        try:
            with self.lock, socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
                sock.settimeout(0.4)
                sock.connect(str(self.ipc_path))
                sock.sendall(request.encode("utf-8"))
                pending = b""
                while True:
                    chunk = sock.recv(8192)
                    if not chunk:
                        return None
                    pending += chunk
                    while b"\n" in pending:
                        line, pending = pending.split(b"\n", 1)
                        try:
                            response = json.loads(line)
                        except (UnicodeDecodeError, json.JSONDecodeError):
                            continue
                        if response.get("request_id") == request_id:
                            return response.get("data")
        except (OSError, TimeoutError):
            return None

    # Inputs: none.
    # Returns: None.
    # Purpose: Watch the player disk cache and stop writing when it reaches its limit.
    def _monitor_disk_cache(self) -> None:
        while not self.cache_stop_event.wait(0.5):
            if self.process is None or self.process.poll() is not None:
                return
            state = self._get_property("demuxer-cache-state")
            if not isinstance(state, dict):
                continue
            if int(state.get("file-cache-bytes", 0)) >= self.disk_cache_limit:
                self.command("set_property", "cache-on-disk", False)
                self.disk_cache_limit = 0
                dprint("[mpv] Disk-Timeshiftlimit erreicht; weitere Daten bleiben im RAM-Puffer.", flush=True)
                return

    # Send one JSON IPC command to mpv.
    # Inputs: *args.
    # Returns: None.
    # Purpose: Send a control command to the selected video player.
    def command(self, *args: object) -> None:
        import json

        if not self.ipc_path.exists():
            return

        message = json.dumps({"command": list(args)}) + "\n"
        try:
            with self.lock:
                sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                sock.connect(str(self.ipc_path))
                sock.sendall(message.encode("utf-8"))
                sock.close()
        except OSError:
            pass

    # Change the mpv volume by a relative percentage.
    # Inputs: amount.
    # Returns: None.
    # Purpose: Increase or decrease the player volume by the requested amount.
    def add_volume(self, amount: int) -> None:
        self.command("add", "volume", amount)
        self.volume = max(0, min(100, self.volume + amount))

    # Inputs: none.
    # Returns: None.
    # Purpose: Pause or resume video playback.
    def toggle_pause(self) -> None:
        self.is_paused = not self.is_paused
        if self.is_paused and not self.direct_live:
            self.timeshifted = True
        self.command("cycle", "pause")

    # Inputs: seconds.
    # Returns: None.
    # Purpose: Move playback forward or backward by the requested number of seconds.
    def seek_by(self, seconds: int) -> None:
        if seconds < 0 and not self.direct_live:
            self.timeshifted = True
        self.command("seek", seconds, "relative")

    # Query mpv for the current volume and store it locally.
    # Inputs: none.
    # Returns: int.
    # Purpose: Return the volume currently tracked by the application.
    def read_volume(self) -> int:
        # A full JSON reply reader is unnecessary for normal operation;
        # volume is tracked locally whenever our controls change it.
        return self.volume

    # Stop mpv and remove its private IPC socket.
    # Inputs: none.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self) -> None:
        self.speed_stop_event.set()
        self.speed_thread = None
        self.cache_stop_event.set()
        if self.cache_monitor is not None:
            self.cache_monitor.join(timeout=1)
            self.cache_monitor = None
        if self.process is not None:
            try:
                self.command("quit")
            except Exception:
                pass
            try:
                self.process.wait(timeout=2)
            except Exception:
                try:
                    self.process.kill()
                except Exception:
                    pass
            self.process = None

        try:
            self.ipc_path.unlink()
        except FileNotFoundError:
            pass
        if self.cache_directory is not None:
            shutil.rmtree(self.cache_directory, ignore_errors=True)
            self.cache_directory = None
        self.disk_cache_limit = 0


class VlcPlayer:
    """Control VLC's remote-control interface and embed its video in Tk."""

    # Inputs: vlc_path, volume.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, vlc_path: str, volume: int) -> None:
        self.vlc_path = vlc_path
        self.volume = max(0, min(100, volume))
        self.process: subprocess.Popen[bytes] | None = None
        self.port = 42120 + (os.getpid() % 10000)

    # Inputs: parent_window_id, playlist.
    # Returns: None.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self, parent_window_id: int, playlist: Path | str | None = None) -> None:
        self.stop()
        cmd = [self.vlc_path, "--intf=dummy", "--extraintf=rc",
               f"--rc-host=127.0.0.1:{self.port}",
               f"--drawable-xid={parent_window_id}", "--no-video-title-show",
               "--no-keyboard-events", "--no-mouse-events",
               "--network-caching=2000", "--live-caching=2000",
               "--file-caching=2000",
               f"--volume={round(self.volume * 5.12)}"]
        if playlist:
            cmd.append(str(playlist))
        self.process = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                                        stdout=subprocess.DEVNULL,
                                        stderr=subprocess.DEVNULL)
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            if self.process.poll() is not None:
                return_code = self.process.returncode
                self.process = None
                raise RuntimeError(f"VLC wurde beim Start beendet (Status {return_code}).")
            try:
                with socket.create_connection(("127.0.0.1", self.port), timeout=0.2):
                    return
            except OSError:
                time.sleep(0.05)
        self.stop()
        raise RuntimeError("VLC hat seine Remote-Control-Schnittstelle nicht gestartet.")

    # Inputs: none.
    # Returns: bool.
    # Purpose: Check whether the video player process is still running.
    def alive(self) -> bool:
        return self.process is not None and self.process.poll() is None

    # Show the live stream; the VLC process keeps running between channels.
    # Inputs: url, adaptive.
    # Returns: None.
    # Purpose: Tell the video player to play the live stream address.
    def play_live(self, url: str, adaptive: object = None) -> None:
        self.command("clear")
        self.command("add", url)

    # Play the growing timeshift playlist (VLC starts at its first entry).
    # Inputs: url, paused.
    # Returns: float | None.
    # Purpose: Tell the video player to play the timeshift playlist.
    def play_timeshift(self, url: str, paused: bool,
                       start_offset: float = 0.0) -> float | None:
        self.command("clear")
        self.command("add", url)
        if start_offset > 0.05:
            # VLC's RC interface accepts a seek only after the new playlist
            # item has started. Give HLS time to open it before seeking.
            def seek_after_load() -> None:
                time.sleep(1.0)
                if self.alive():
                    self.command("seek", f"{start_offset:.3f}")

            threading.Thread(
                target=seek_after_load,
                name="MvT-TV-vlc-timeshift-seek",
                daemon=True,
            ).start()
        return None

    # Inputs: none.
    # Returns: float | None.
    # Purpose: Read the current playback position from the video player.
    def get_position(self) -> float | None:
        return None

    # Inputs: mode.
    # Returns: None.
    # Purpose: Set the video shape used by the player.
    def set_aspect(self, mode: tuple) -> None:
        self.command("vratio", mode[2])

    # Inputs: *args.
    # Returns: None.
    # Purpose: Send a control command to the selected video player.
    def command(self, *args: object) -> None:
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=0.2) as sock:
                sock.sendall((" ".join(map(str, args)) + "\n").encode())
        except OSError:
            pass

    # Inputs: amount.
    # Returns: None.
    # Purpose: Increase or decrease the player volume by the requested amount.
    def add_volume(self, amount: int) -> None:
        self.volume = max(0, min(100, self.volume + amount))
        self.command("volume", str(round(self.volume * 5.12)))

    # Inputs: none.
    # Returns: None.
    # Purpose: Pause or resume video playback.
    def toggle_pause(self) -> None:
        self.command("pause")

    # Inputs: seconds.
    # Returns: None.
    # Purpose: Move playback forward or backward by the requested number of seconds.
    def seek_by(self, seconds: int) -> None:
        self.command("seek", f"{seconds:+d}")

    # Inputs: none.
    # Returns: int.
    # Purpose: Return the volume currently tracked by the application.
    def read_volume(self) -> int:
        return self.volume

    # Inputs: none.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self) -> None:
        if self.process is not None:
            self.command("quit")
            try:
                self.process.wait(timeout=2)
            except Exception:
                try:
                    self.process.terminate()
                    self.process.wait(timeout=2)
                except Exception:
                    try:
                        self.process.kill()
                        self.process.wait(timeout=2)
                    except Exception:
                        pass
            self.process = None


class SettingsDialog(tk.Toplevel):
    """Tk settings dialog for all user-adjustable app parameters."""

    # Inputs: parent, config.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, parent: tk.Misc, config: Config) -> None:
        super().__init__(parent)
        self.title(f"{APP_NAME} Einstellungen")
        # Remember the size the user gave the dialog; never smaller than 200x200.
        self.min_size = 200
        saved = re.fullmatch(r"(\d+)x(\d+)", config.get("settings_size").strip())
        width, height = ((max(self.min_size, int(saved.group(1))), max(self.min_size, int(saved.group(2))))
                         if saved else (780, 680))
        self.initial_size = (width, height)
        self.geometry(f"{width}x{height}")
        self.minsize(self.min_size, self.min_size)
        self.resizable(True, True)
        self.result = False
        self.config = config

        fields = [
            ("M3U-Datei", "m3u_file"),
            ("Kathrein EXIP IP-Adresse", "exip_ip"),
            ("RTSP-Port", "rtsp_port"),
            ("TVHeadend IP-Adresse", "tvh_ip"),
            ("TVHeadend HTTP-Port", "tvh_port"),
            ("TVHeadend-Playlist-Pfad", "tvh_playlist_path"),
            ("TVHeadend-Benutzer", "tvh_username"),
            ("TVHeadend-Passwort", "tvh_password"),
            ("TVHeadend Login", "tvh_login_mode"),
            ("Small Jump (s)", "small_jump"),
            ("Big Jump (s)", "big_jump"),
            ("Zahleneingabe Timeout (ms)", "number_timeout_ms"),
            ("Timeshift-Verzeichnis", "timeshift_directory"),
            ("Ringbuffer-Größe (GB)", "timeshift_size_gb"),
            ("RAM-Puffer (GB)", "timeshift_ram_size_gb"),
            ("Aufnahme-Verzeichnis", "recording_directory"),
            ("mpv-Pfad", "mpv_path"),
            ("VLC-Pfad", "vlc_path"),
            ("ffmpeg-Pfad", "ffmpeg_path"),
            ("Startpuffer im HLS-Modus (s)", "live_delay_s"),
            ("Playlist-Fenster (min, 0 = alles)", "playlist_window_min"),
            ("Segmentlänge (s, 1–4)", "segment_s"),
            ("ffmpeg-Analysezeit (s, 0.5–5)", "probe_s"),
            ("Puffer nach Umschalten (s, 1–9)", "buffer_target_s"),
            ("Min. Tempo (z. B. 0.97)", "speed_min"),
            ("Max. Tempo (z. B. 1.03)", "speed_max"),
            ("Now & Next Anzeige (s)", "now_next_timeout"),
            ("Now & Next Logo-Hintergrund (Hex, z. B. A0A0A0)", "logo_bg"),
            ("Senderliste: Breite (px)", "list_width"),
            ("Senderliste: Schriftgröße", "list_font_size"),
            ("Tooltip-Anzeigedauer (s)", "tooltip_s"),
            ("Titelzeile aktualisieren alle (s, 0 = aus)", "title_update_s"),
            ("Timeshift-Anzeige aktualisieren (s, 3–600)", "ts_update_s"),
        ]

        self.vars: dict[str, tk.StringVar] = {}

        container = ttk.Frame(self)
        container.pack(fill="both", expand=True)
        canvas = tk.Canvas(container, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        frame = ttk.Frame(canvas, padding=12)
        content_window = canvas.create_window((0, 0), window=frame, anchor="nw")
        frame.bind(
            "<Configure>",
            lambda _event: canvas.configure(scrollregion=canvas.bbox("all")),
        )
        canvas.bind(
            "<Configure>",
            lambda event: canvas.itemconfigure(content_window, width=event.width),
        )
        canvas.bind("<Enter>", lambda _event: self._bind_mousewheel(canvas))
        canvas.bind("<Leave>", lambda _event: self._unbind_mousewheel())
        canvas.bind("<Destroy>", lambda _event: self._unbind_mousewheel())

        for row, (label, key) in enumerate(fields):
            ttk.Label(frame, text=label).grid(
                row=row, column=0, sticky="w", padx=(0, 8), pady=4
            )
            var = tk.StringVar(value=config.get(key))
            self.vars[key] = var
            if key == "tvh_login_mode":
                entry = ttk.Combobox(frame, textvariable=var,
                                     values=("auto", "on", "off"),
                                     state="readonly", width=39)
            else:
                entry = ttk.Entry(frame, textvariable=var, width=42,
                                  show="*" if key == "tvh_password" else "")
            entry.grid(
                row=row, column=1, sticky="ew", pady=4
            )

            if key in ("m3u_file", "timeshift_directory", "recording_directory"):
                if key == "m3u_file":
                    ttk.Button(
                        frame, text="...", width=3,
                        command=self.choose_m3u
                    ).grid(row=row, column=2, padx=(5, 0))
                else:
                    ttk.Button(
                        frame, text="...", width=3,
                        command=lambda k=key: self.choose_directory(k)
                    ).grid(row=row, column=2, padx=(5, 0))

        row = len(fields)
        ttk.Label(frame, text="Abspieler").grid(row=row, column=0, sticky="w", pady=4)
        self.player_var = tk.StringVar(value=self.config.get("player"))
        ttk.Combobox(frame, textvariable=self.player_var, values=("mpv", "vlc"),
                     state="readonly", width=39).grid(row=row, column=1, sticky="ew", pady=4)
        row += 1
        ttk.Label(frame, text="Quelle").grid(row=row, column=0, sticky="w", pady=4)
        self.source_var = tk.StringVar(value=self.config.get("source_mode"))
        source_frame = ttk.Frame(frame)
        source_frame.grid(row=row, column=1, sticky="w", pady=4)
        ttk.Radiobutton(source_frame, text="direkt", value="direct",
                        variable=self.source_var).pack(side="left")
        ttk.Radiobutton(source_frame, text="TVHeadend", value="tvheadend",
                        variable=self.source_var).pack(side="left", padx=(12, 0))
        row += 1
        ttk.Label(frame, text="Fenster-Ankerecke").grid(row=row, column=0, sticky="w", pady=4)
        self.anchor_var = tk.StringVar(
            value=WINDOW_ANCHORS.get(self.config.get("window_anchor"), WINDOW_ANCHORS["top-right"]))
        ttk.Combobox(frame, textvariable=self.anchor_var, values=tuple(WINDOW_ANCHORS.values()),
                     state="readonly", width=39).grid(row=row, column=1, sticky="ew", pady=4)
        row += 1
        ttk.Label(frame, text="Start-Ansicht").grid(row=row, column=0, sticky="w", pady=4)
        self.view_modes = {
            "0": "0 – wie beim letzten Beenden",
            "1": "1 – Normales Fenster",
            "2": "2 – Vollbild mit Fensterelementen",
            "3": "3 – Echtes Vollbild (nur Video)",
        }
        self.view_mode_var = tk.StringVar(
            value=self.view_modes.get(self.config.get("view_start_mode"), self.view_modes["1"]))
        ttk.Combobox(frame, textvariable=self.view_mode_var,
                     values=tuple(self.view_modes.values()),
                     state="readonly", width=39).grid(row=row, column=1, sticky="ew", pady=4)
        row += 1

        self.ram_var = tk.BooleanVar(value=self.config.get("timeshift_ram").lower() == "true")
        self.adaptive_var = tk.BooleanVar(value=self.config.get("adaptive_speed").lower() == "true")
        self.live_direct_var = tk.BooleanVar(value=self.config.get("live_path").lower() != "hls")
        self.list_autoclose_var = tk.BooleanVar(value=self.config.get("list_autoclose").lower() == "true")
        self.debug_var = tk.BooleanVar(value=self.config.get("debug_cli").lower() == "true")
        for text, variable in (
            ("Timeshift im RAM verwenden (/dev/shm)", self.ram_var),
            ("Tempo dynamisch an Pufferstand anpassen (nur mpv)", self.adaptive_var),
            ("Live-Bild direkt (schnell); Timeshift erst bei Pause/Zurückspringen",
             self.live_direct_var),
            ("Senderliste nach der Senderwahl automatisch schließen", self.list_autoclose_var),
            ("Debug output on CLI", self.debug_var),
        ):
            ttk.Checkbutton(frame, text=text, variable=variable).grid(
                row=row, column=0, columnspan=3, sticky="w", pady=(0, 4))
            row += 1

        self.key_vars: dict[str, tk.StringVar] = {}
        key_labels = {"start": "Start", "stop": "Stop", "pause": "Pause/Start",
                      "next": "Nächstes Programm", "previous": "Vorheriges Programm",
                      "small_back": "10s zurück", "small_forward": "10s vor",
                      "big_back": "Großer Sprung zurück", "big_forward": "Großer Sprung vor",
                      "volume_up": "Lautstärke +", "volume_down": "Lautstärke -",
                      "record": "Aufnahme", "record_pause": "Aufnahme Pause/Weiter",
                      "fullscreen": "Vollbild", "info": "Programminformationen",
                      "live": "Zurück zu Live", "aspect": "Seitenverhältnis",
                      "channel_list": "Senderliste"}
        key_frame = ttk.LabelFrame(frame, text="Tastenkürzel (Tkinter-Schreibweise, z. B. Shift-Left)")
        key_frame.grid(row=row, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        row += 1
        for i, (action, label) in enumerate(key_labels.items()):
            key_row, col = divmod(i, 2)
            ttk.Label(key_frame, text=label).grid(row=key_row, column=col * 2, sticky="w", padx=5, pady=2)
            var = tk.StringVar(value=self.config.get("key_" + action))
            self.key_vars[action] = var
            ttk.Entry(key_frame, textvariable=var, width=16).grid(row=key_row, column=col * 2 + 1, padx=5, pady=2)

        button_frame = ttk.Frame(frame)
        button_frame.grid(
            row=row, column=0, columnspan=3, pady=(12, 0), sticky="w"
        )
        ttk.Button(
            button_frame, text="Abbrechen", command=self.destroy
        ).pack(side="left", padx=(0, 4))
        ttk.Button(
            button_frame, text="Speichern", command=self.save
        ).pack(side="left", padx=4)
        # ESC closes the dialog without saving.
        self.bind("<Escape>", lambda _event: self.destroy())

        self.transient(parent)
        self.grab_set()

    # Store the dialog size if the user changed it (also when cancelled or closed with ESC).
    # Inputs: none.
    # Returns: None.
    # Purpose: Save the current size of the settings window.
    def _remember_size(self) -> None:
        try:
            width, height = self.winfo_width(), self.winfo_height()
        except tk.TclError:
            return
        if not isinstance(width, int) or not isinstance(height, int) or width <= 1 or height <= 1:
            return
        size = (max(self.min_size, width), max(self.min_size, height))
        if size != self.initial_size:
            self.config.set("settings_size", f"{size[0]}x{size[1]}")
            self.config.save()
            self.initial_size = size

    # Inputs: none.
    # Returns: None.
    # Purpose: Save the settings window size and close the window.
    def destroy(self) -> None:
        self._remember_size()
        super().destroy()

    # Bind wheel events only while the pointer is over the scrollable dialog.
    # Inputs: canvas.
    # Returns: None.
    # Purpose: Connect mouse-wheel events so the settings panel can scroll.
    def _bind_mousewheel(self, canvas: tk.Canvas) -> None:
        self.bind_all("<MouseWheel>", lambda event: self._on_mousewheel(canvas, event))
        self.bind_all("<Button-4>", lambda _event: canvas.yview_scroll(-1, "units"))
        self.bind_all("<Button-5>", lambda _event: canvas.yview_scroll(1, "units"))

    # Support both Windows wheel deltas and smaller macOS wheel deltas.
    # Inputs: canvas, event.
    # Returns: None.
    # Purpose: Scroll the settings panel in response to a mouse-wheel event.
    @staticmethod
    def _on_mousewheel(canvas: tk.Canvas, event: tk.Event) -> None:
        delta = int(event.delta)
        steps = int(delta / 120) if abs(delta) >= 120 else (1 if delta > 0 else -1)
        canvas.yview_scroll(-steps, "units")

    # Remove global wheel bindings when the pointer leaves the dialog canvas.
    # Inputs: none.
    # Returns: None.
    # Purpose: Disconnect mouse-wheel events from the settings panel.
    def _unbind_mousewheel(self) -> None:
        self.unbind_all("<MouseWheel>")
        self.unbind_all("<Button-4>")
        self.unbind_all("<Button-5>")

    # Open a file chooser for selecting the M3U playlist.
    # Inputs: none.
    # Returns: None.
    # Purpose: Ask the user to select a channel playlist file.
    def choose_m3u(self) -> None:
        filename = filedialog.askopenfilename(
            parent=self,
            title="M3U-Datei auswählen",
            filetypes=[("M3U", "*.m3u *.m3u8"), ("Alle Dateien", "*.*")],
        )
        if filename:
            self.vars["m3u_file"].set(filename)

    # Open a directory chooser for the timeshift ringbuffer.
    # Inputs: key.
    # Returns: None.
    # Purpose: Ask the user to select a folder for recordings or timeshift data.
    def choose_directory(self, key: str = "timeshift_directory") -> None:
        directory = filedialog.askdirectory(
            parent=self,
            title="Timeshift-Verzeichnis auswählen",
        )
        if directory:
            self.vars[key].set(directory)

    # Validate and save all settings entered in the dialog.
    # Inputs: none.
    # Returns: None.
    # Purpose: Save the settings selected in the dialog.
    def save(self) -> None:
        try:
            int(self.vars["rtsp_port"].get())
            int(self.vars["tvh_port"].get())
            int(self.vars["small_jump"].get())
            int(self.vars["big_jump"].get())
            int(self.vars["number_timeout_ms"].get())
            float(self.vars["timeshift_size_gb"].get())
            float(self.vars["timeshift_ram_size_gb"].get())
            int(self.vars["now_next_timeout"].get())
            float(self.vars["live_delay_s"].get())
            float(self.vars["playlist_window_min"].get())
            target_s = float(self.vars["buffer_target_s"].get().replace(",", "."))
            if not (1.0 <= target_s <= 9.0):
                raise ValueError("target")
            if not (1 <= int(self.vars["segment_s"].get()) <= 4):
                raise ValueError("segment")
            if not (0.5 <= float(self.vars["probe_s"].get().replace(",", ".")) <= 5.0):
                raise ValueError("probe")
            if not re.fullmatch(r"#?[0-9a-fA-F]{6}", self.vars["logo_bg"].get().strip()):
                raise ValueError("logo_bg")
            if not (50 <= int(self.vars["list_width"].get()) <= 2000):
                raise ValueError("list_width")
            if not (6 <= int(self.vars["list_font_size"].get()) <= 72):
                raise ValueError("list_font_size")
            if not (0.5 <= float(self.vars["tooltip_s"].get().replace(",", ".")) <= 60):
                raise ValueError("tooltip")
            if not (0 <= int(self.vars["title_update_s"].get()) <= 3600):
                raise ValueError("title")
            if not (3 <= int(self.vars["ts_update_s"].get()) <= 600):
                raise ValueError("ts_update")
            speed_min = float(self.vars["speed_min"].get().replace(",", "."))
            speed_max = float(self.vars["speed_max"].get().replace(",", "."))
            if not (0.5 <= speed_min <= 1.0 and 1.0 <= speed_max <= 1.5):
                raise ValueError("speed")
        except ValueError:
            messagebox.showerror(
                "Ungültige Einstellung",
                "Port, Sprungweiten, Timeout und Tempo müssen Zahlen sein "
                "(Puffer 1–9 s, Segmentlänge 1–4, Analysezeit 0.5–5 s, "
                "Min. Tempo 0.5–1.0, Max. Tempo 1.0–1.5, Senderliste 50–2000 px, "
                "Schriftgröße 6–72, Tooltip 0.5–60 s, Titelzeile 0–3600 s, "
                "Timeshift-Anzeige 3–600 s, Logo-Hintergrund als 6-stelliger Hex-Wert).",
                parent=self,
            )
            return

        for key, var in self.vars.items():
            self.config.set(key, var.get().strip())
        self.config.set("player", self.player_var.get())
        for action, var in self.key_vars.items():
            self.config.set("key_" + action, var.get().strip())
        self.config.set("timeshift_ram", "true" if self.ram_var.get() else "false")
        self.config.set("adaptive_speed", "true" if self.adaptive_var.get() else "false")
        self.config.set("live_path", "direct" if self.live_direct_var.get() else "hls")
        self.config.set("source_mode", self.source_var.get())
        reverse_anchors = {label: key for key, label in WINDOW_ANCHORS.items()}
        self.config.set("window_anchor", reverse_anchors.get(self.anchor_var.get(), "top-right"))
        reverse_modes = {label: key for key, label in self.view_modes.items()}
        self.config.set("view_start_mode", reverse_modes.get(self.view_mode_var.get(), "1"))
        self.config.set("list_autoclose", "true" if self.list_autoclose_var.get() else "false")
        self.config.set("debug_cli", "true" if self.debug_var.get() else "false")

        self.config.save()
        self.result = True
        self.destroy()


class ToolTip:
    """Tooltip that appears when the pointer rests on a widget for a while."""

    # Inputs: widget, text_provider, duration_provider, delay_ms.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, widget: tk.Misc, text_provider: callable,
                 duration_provider: callable, delay_ms: int = 2000) -> None:
        self.widget = widget
        self.text_provider = text_provider
        self.duration_provider = duration_provider
        self.delay_ms = delay_ms
        self.window: tk.Toplevel | None = None
        self.show_id: str | None = None
        self.hide_id: str | None = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._cancel, add="+")
        widget.bind("<ButtonPress>", self._cancel, add="+")
        widget.bind("<Destroy>", self._cancel, add="+")

    # Inputs: _event.
    # Returns: None.
    # Purpose: Schedule a help tooltip to appear after a short delay.
    def _schedule(self, _event: object = None) -> None:
        self._cancel()
        self.show_id = self.widget.after(self.delay_ms, self._show)

    # Inputs: none.
    # Returns: None.
    # Purpose: Display the help tooltip beside its widget.
    def _show(self) -> None:
        self.show_id = None
        text = self.text_provider()
        if not text:
            return
        window = tk.Toplevel(self.widget)
        window.wm_overrideredirect(True)
        try:
            window.wm_attributes("-topmost", True)
        except tk.TclError:
            pass
        tk.Label(window, text=text, background="#ffffe0", foreground="#000000",
                 relief="solid", borderwidth=1, padx=6, pady=2).pack()
        window.update_idletasks()
        x = self.widget.winfo_rootx() + (self.widget.winfo_width() - window.winfo_reqwidth()) // 2
        y = self.widget.winfo_rooty() - window.winfo_reqheight() - 4
        window.geometry(f"+{max(0, x)}+{max(0, y)}")
        self.window = window
        try:
            seconds = float(self.duration_provider())
        except (TypeError, ValueError):
            seconds = 3.0
        self.hide_id = self.widget.after(max(200, int(seconds * 1000)), self._cancel)

    # Inputs: _event.
    # Returns: None.
    # Purpose: Cancel a pending tooltip and hide it if it is visible.
    def _cancel(self, _event: object = None) -> None:
        for attribute in ("show_id", "hide_id"):
            after_id = getattr(self, attribute)
            if after_id is not None:
                try:
                    self.widget.after_cancel(after_id)
                except tk.TclError:
                    pass
                setattr(self, attribute, None)
        if self.window is not None:
            try:
                self.window.destroy()
            except tk.TclError:
                pass
            self.window = None


class MvTTV:
    """Main application coordinating playlist, SAT>IP, ffmpeg and mpv."""

    # Inputs: root.
    # Returns: None.
    # Purpose: Create the object and set up the values and resources it needs.
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(APP_NAME)

        self.config = Config(CFG_FILE)
        global DEBUG_CLI
        DEBUG_CLI = self.config.get("debug_cli").lower() == "true"
        initial_geometry = self.initial_geometry()
        # Some window managers place the window including the title bar but report
        # the position without it, so the window would sink by one title bar height
        # with every restart. The measured difference is stored and compensated.
        self.window_offset = self.load_window_offset()
        self.intended_geometry = initial_geometry
        self.root.geometry(self.shifted_geometry(initial_geometry, self.window_offset))
        self.channels: list[Channel] = []
        try:
            self.channel_index = max(0, int(self.config.get("last_channel")) - 1)
        except ValueError:
            self.channel_index = 0

        self.satip: SatIpClient | None = None
        self.tvheadend: TvheadendClient | None = None
        self.timeshift: Timeshift | None = None
        self.mpv: MpvPlayer | None = None
        self.recording: Recording | None = None
        self.epg_updates: queue.Queue = queue.Queue()
        self.dvb = DvbSiParser(self.on_now_next)
        self.now_next_window: tk.Toplevel | None = None
        self.now_next_after_id: str | None = None
        self.now_next_signature: tuple | None = None
        self.now_next_shown_at: float | None = None
        self.info_window: tk.Toplevel | None = None
        self.now_next_pending = False

        self.number_buffer = ""
        self.number_after_id: str | None = None
        self.key_overlay_after_id: str | None = None
        self.running = False
        self.paused = False
        self.live_status_text = "Live"
        self.buffer_status_after_id: str | None = None
        # Direct live view with timeshift only on demand.
        self.relay: LiveRelay | None = None
        self.live_direct_active = False
        self.view_mode = "live"          # "live" or "timeshift"
        self.adaptive_cfg: dict[str, float] | None = None
        self.pause_started = 0.0
        self.pause_wall = 0.0
        self.ts_anchor_wall = 0.0
        self.ts_anchor_pos = 0.0
        self.ts_snapshot_duration = 0.0
        self.ts_snapshot_started = 0.0
        self.watch_after_id: str | None = None
        self.no_data_after_id: str | None = None

        # Channel list panel, window mode, aspect ratio, title.
        self.list_frame: tk.Frame | None = None
        self.channel_listbox: tk.Listbox | None = None
        self.window_mode = 1             # 1 window, 2 maximized, 3 true fullscreen
        self.normal_geometry = initial_geometry
        self.title_after_id: str | None = None
        self._overlay_bound = False
        try:
            self.aspect_index = max(0, min(len(ASPECT_MODES) - 1, int(self.config.get("aspect"))))
        except ValueError:
            self.aspect_index = 0

        self.status_var = tk.StringVar(value="Bereit")
        self.channel_var = tk.StringVar(value="Kein Sender")
        self.aspect_var = tk.StringVar(value=ASPECT_MODES[self.aspect_index][0])
        self.ts_var = tk.StringVar(value="")
        self.ts_after_id: str | None = None
        self.source_mode_var = tk.StringVar(value=self.config.get("source_mode"))

        self.build_ui()
        self.bind_keys()
        self.load_playlist()
        self.root.after(250, self.process_epg_updates)
        self.restart_title_timer()
        self.restart_ts_timer()
        start_mode = self.config.get("view_start_mode")
        try:
            mode = int(self.config.get("last_view_mode")) if start_mode == "0" else int(start_mode)
        except ValueError:
            mode = 1
        if mode in (2, 3):
            self.root.after(150, lambda: self.set_window_mode(mode))
        else:
            self.root.after(500, self.calibrate_window_position)

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        # Start the last selected channel automatically after the Tk window
        # has been realized, so mpv has a valid embedding window ID.
        if self.channels:
            self.root.after(200, self.start)

    # Build the main Tkinter window and its controls.
    # Inputs: none.
    # Returns: None.
    # Purpose: Create the main window and its playback controls.
    def build_ui(self) -> None:
        # The middle area holds the video and, on request, the channel list.
        self.middle = tk.Frame(self.root)
        self.middle.pack(fill="both", expand=True, padx=5, pady=5)
        self.video_frame = tk.Frame(
            self.middle, background="black", width=1000, height=560
        )
        self.video_frame.pack(side="left", fill="both", expand=True)
        self.video_frame.pack_propagate(False)

        controls = ttk.Frame(self.root, padding=(5, 5))
        controls.pack(fill="x")
        self.controls = controls

        default_font = tkfont.nametofont("TkDefaultFont")
        default_size = abs(int(default_font.actual("size")))
        icon_font = (
            default_font.actual("family"),
            max(1, round(default_size * 1.5)),
            default_font.actual("weight"),
        )
        button_style = ttk.Style(self.root)
        self.style_scrollbars(button_style)
        button_style.configure("Icon.TButton", font=icon_font)
        button_style.configure("Record.Icon.TButton", font=icon_font, foreground="#c62828")
        button_style.configure("Stop.Icon.TButton", font=icon_font, foreground="#000000")
        # Draw the volume ramps as small images so their size does not depend
        # on font glyph metrics or get clipped by the narrow buttons.
        self.volume_down_icon = tk.PhotoImage(width=20, height=20)
        self.volume_up_icon = tk.PhotoImage(width=20, height=20)
        for image, heights in (
            (self.volume_down_icon, (16, 12, 8, 4)),
            (self.volume_up_icon, (4, 8, 12, 16)),
        ):
            for i, height in enumerate(heights):
                left = 1 + i * 5
                image.put("#222222", to=(left, 18 - height, left + 3, 18))
        buttons = [
            ("▶", self.start, "Icon.TButton"),
            ("●", self.toggle_recording, "Record.Icon.TButton"),
            ("■", self.stop_key, "Stop.Icon.TButton"),
            ("Ⅱ", self.pause, "Icon.TButton"),
            ("P+", self.next_channel, "Icon.TButton"),
            ("P-", self.previous_channel, "Icon.TButton"),
            ("<<", lambda: self.seek(-self.big_jump()), "Icon.TButton"),
            ("<", lambda: self.seek(-self.small_jump()), "Icon.TButton"),
            (">", lambda: self.seek(self.small_jump()), "Icon.TButton"),
            (">>", lambda: self.seek(self.big_jump()), "Icon.TButton"),
            ("█▆▃▁", lambda: self.change_volume(-5), "Icon.TButton"),
            ("▁▃▆█", lambda: self.change_volume(5), "Icon.TButton"),
            ("☰", self.toggle_channel_list, "Icon.TButton"),
            ("⚙", self.open_settings, "Icon.TButton"),
        ]

        for symbol, command, style_name in buttons:
            if symbol in ("█▆▃▁", "▁▃▆█"):
                image = self.volume_down_icon if symbol == "█▆▃▁" else self.volume_up_icon
                button = ttk.Button(
                    controls, image=image, command=command,
                    style=style_name, width=3,
                )
                button.pack(side="left", padx=2)
                self._add_button_tooltip(button, symbol)
                continue
            button = ttk.Button(controls, text=symbol, command=command,
                                style=style_name, width=3)
            button.pack(side="left", padx=2)
            self._add_button_tooltip(button, symbol)
        # Right part of the button row: key display (far right), aspect ratio,
        # and the right-aligned status text next to the buttons.
        self.key_overlay = tk.Label(
            controls, text="", foreground="white", background="#222222",
            font=("TkDefaultFont", 10, "bold"), padx=8, pady=4,
        )
        self.key_overlay.pack(side="right", padx=(8, 4))
        # Plain dark green text without a frame, same font size as the status text.
        self.aspect_label = ttk.Label(
            controls, textvariable=self.aspect_var, foreground="#006400",
            anchor="center",
        )
        self.aspect_label.pack(side="right", padx=(8, 0))
        ToolTip(self.aspect_label,
                lambda: self.format_keys(("aspect",)), self._tooltip_seconds)
        # Two-line info area: status text on top, timeshift figures below.
        info_area = ttk.Frame(controls)
        info_area.pack(side="right", fill="x", expand=True, padx=(8, 0))
        ttk.Label(info_area, textvariable=self.status_var, anchor="e").pack(fill="x")
        ttk.Label(info_area, textvariable=self.ts_var, anchor="e").pack(fill="x")

    # Make the background (trough) of all scrollbars somewhat darker; the
    # slider keeps its colour.
    # Inputs: style.
    # Returns: None.
    # Purpose: Set the appearance of the application scrollbars.
    def style_scrollbars(self, style: ttk.Style) -> None:
        trough = ""
        for name in ("Vertical.TScrollbar", "TScrollbar"):
            trough = style.lookup(name, "troughcolor") or trough
        try:
            red, green, blue = (value / 65535 for value in self.root.winfo_rgb(trough or "#c3c3c3"))
            dark = "#%02x%02x%02x" % tuple(round(255 * c * 0.82) for c in (red, green, blue))
        except (tk.TclError, TypeError, ValueError):
            dark = "#a0a0a0"
        for name in ("Vertical.TScrollbar", "Horizontal.TScrollbar"):
            style.configure(name, troughcolor=dark)

    # ----- tooltips -----------------------------------------------------
    _BUTTON_ACTIONS = {
        "▶": ("start",), "●": ("record",), "■": ("stop",), "Ⅱ": ("pause",),
        "P+": ("next",), "P-": ("previous",), "<<": ("big_back",),
        "<": ("small_back",), ">": ("small_forward",), ">>": ("big_forward",),
        "█▆▃▁": ("volume_down",), "▁▃▆█": ("volume_up",),
        "☰": ("channel_list",),
    }

    # Inputs: none.
    # Returns: float.
    # Purpose: Return how long the pointer must wait before a tooltip appears.
    def _tooltip_seconds(self) -> float:
        try:
            return float(self.config.get("tooltip_s").replace(",", "."))
        except ValueError:
            return 3.0

    # Inputs: sequence.
    # Returns: str.
    # Purpose: Convert a Tk keyboard shortcut into readable text.
    @staticmethod
    def format_key(sequence: str) -> str:
        names = {"Control": "Ctrl", "Return": "Enter", "space": "Space"}
        parts = sequence.strip().strip("<>").split("-")
        if parts and parts[0] == "KeyPress":
            parts = parts[1:]
        shown = []
        for part in parts:
            if part in names:
                shown.append(names[part])
            elif len(part) == 1:
                shown.append(part.upper())
            else:
                shown.append(part)
        return "+".join(shown)

    # Inputs: actions.
    # Returns: str.
    # Purpose: Create the keyboard shortcut text shown in the interface.
    def format_keys(self, actions: tuple) -> str:
        keys = [self.format_key(self.config.get("key_" + action))
                for action in actions if self.config.get("key_" + action).strip()]
        return " / ".join(keys)

    # Inputs: button, symbol.
    # Returns: None.
    # Purpose: Attach a keyboard shortcut hint to a button.
    def _add_button_tooltip(self, button: tk.Misc, symbol: str) -> None:
        if symbol == "⚙":
            ToolTip(button, lambda: "E", self._tooltip_seconds)
            return
        actions = self._BUTTON_ACTIONS.get(symbol, ())
        ToolTip(button, lambda a=actions: self.format_keys(a), self._tooltip_seconds)

    # Install the requested keyboard shortcuts for navigation, volume and player control.
    # Inputs: none.
    # Returns: None.
    # Purpose: Connect configured keyboard shortcuts to their actions.
    def bind_keys(self) -> None:
        if not self._overlay_bound:
            self.root.bind_all("<KeyPress>", self.show_key_overlay, add="+")
            self._overlay_bound = True
        actions = {
            "start": self.start, "stop": self.stop_key, "pause": self.pause,
            "next": self.next_channel, "previous": self.previous_channel,
            "small_back": lambda: self.seek(-self.small_jump()),
            "small_forward": lambda: self.seek(self.small_jump()),
            "big_back": lambda: self.seek(-self.big_jump()),
            "big_forward": lambda: self.seek(self.big_jump()),
            "volume_up": lambda: self.change_volume(5),
            "volume_down": lambda: self.change_volume(-5),
            "record": self.toggle_recording, "fullscreen": self.toggle_fullscreen,
            "record_pause": self.toggle_recording_pause,
            "info": self.toggle_program_info,
            "live": self.go_live,
            "aspect": self.cycle_aspect,
            "channel_list": self.toggle_channel_list,
        }
        for action, callback in actions.items():
            key = self.config.get("key_" + action).strip()
            if key:
                sequence = key if key.startswith("<") else f"<{key}>"
                self.root.bind(
                    sequence,
                    lambda event, fn=callback: self.run_key_action(event, fn),
                )
        self.root.bind(
            "<KeyPress-e>",
            lambda event: self.run_key_action(event, self.open_settings),
        )
        self.root.bind(
            "<KeyPress-E>",
            lambda event: self.run_key_action(event, self.open_settings),
        )
        info_key = self.config.get("key_info").strip()
        if info_key.lower() == "i":
            self.root.bind(
                "<KeyPress-I>",
                lambda event: self.run_key_action(event, self.toggle_program_info),
            )
        self.root.bind(
            "<Escape>",
            lambda event: self.run_key_action(event, self.on_escape),
        )

        for digit in "0123456789":
            self.root.bind(
                f"<KeyPress-{digit}>",
                lambda event, d=digit: self.run_key_action(
                    event, lambda: self.number_digit(d)
                ),
            )

    # Paint key feedback before a potentially slow action such as channel tuning.
    # Inputs: event, callback.
    # Returns: str.
    # Purpose: Run the selected keyboard action and report whether it was handled.
    def run_key_action(self, event: tk.Event, callback: callable) -> str:
        self.show_key_overlay(event, arm_timeout=False)
        self.root.update_idletasks()
        try:
            callback()
        finally:
            self.arm_key_overlay_timeout()
        return "break"

    # Show the last pressed key briefly so slow channel changes are visible to the user.
    # Inputs: event, arm_timeout.
    # Returns: None.
    # Purpose: Show the keyboard shortcut guide on screen.
    def show_key_overlay(self, event: tk.Event, arm_timeout: bool = True) -> None:
        key = event.keysym or event.char or "?"
        if len(key) == 1:
            key = key.upper()
        elif key == "space":
            key = "Space"
        self.key_overlay.configure(text=f"Key:{key}")
        self.key_overlay.update_idletasks()
        if arm_timeout:
            self.arm_key_overlay_timeout()

    # Inputs: none.
    # Returns: None.
    # Purpose: Schedule the shortcut guide to close after a delay.
    def arm_key_overlay_timeout(self) -> None:
        if self.key_overlay_after_id is not None:
            self.root.after_cancel(self.key_overlay_after_id)
        self.key_overlay_after_id = self.root.after(2000, self.hide_key_overlay)

    # Inputs: none.
    # Returns: None.
    # Purpose: Hide the keyboard shortcut guide.
    def hide_key_overlay(self) -> None:
        self.key_overlay_after_id = None
        self.key_overlay.configure(text="")

    # Load and parse the configured M3U file into the channel list.
    # Inputs: none.
    # Returns: None.
    # Purpose: Read channel names and stream addresses from the playlist.
    def load_playlist(self) -> None:
        self.channels.clear()
        playlist_url = ""
        if self.config.get("source_mode").lower() == "tvheadend":
            host = self.config.get("tvh_ip").strip()
            if ":" in host and not host.startswith("["):
                host = f"[{host}]"  # Support IPv6 literal addresses.
            base_url = f"http://{host}:{int(self.config.get('tvh_port'))}"
            playlist_url = urljoin(base_url + "/", self.config.get("tvh_playlist_path").strip().lstrip("/"))
            try:
                with open_tvh_url(
                    playlist_url,
                    self.config.get("tvh_username"),
                    self.config.get("tvh_password"),
                    self.config.get("tvh_login_mode"),
                    timeout=10,
                ) as response:
                    lines = response.read().decode("utf-8", errors="replace").splitlines()
            except Exception as exc:
                self.status_var.set(f"TVHeadend-Kanalliste nicht geladen: {exc}")
                return
        else:
            filename = Path(self.config.get("m3u_file")).expanduser()
            if not filename.is_absolute():
                filename = RESOURCE_DIR / filename.name
            try:
                lines = filename.read_text(encoding="utf-8", errors="replace").splitlines()
            except OSError as exc:
                self.status_var.set(f"M3U nicht gefunden: {exc}")
                return

        pending_name = "Unbenannter Sender"

        for line in lines:
            line = line.strip()
            if not line:
                continue
            if line.upper().startswith("#EXTINF:"):
                comma = line.find(",")
                if comma >= 0:
                    pending_name = line[comma + 1:].strip() or pending_name
                continue
            if line.startswith("#"):
                continue
            if line.lower().startswith(("rtsp://", "http://", "https://")):
                stream_url = urljoin(playlist_url, line) if playlist_url else line
                self.channels.append(Channel(pending_name, stream_url))
                pending_name = "Unbenannter Sender"

        self.status_var.set(f"{len(self.channels)} Sender geladen")

    # Inputs: none.
    # Returns: None.
    # Purpose: Switch between the configured stream sources.
    def change_source_mode(self) -> None:
        mode = self.source_mode_var.get()
        was_running = self.running
        self.stop()
        self.config.set("source_mode", mode)
        self.config.save()
        self.load_playlist()
        self.channel_index = 0
        if was_running and self.channels:
            self.start_channel(0)

    # Return the configured small jump in seconds.
    # Inputs: none.
    # Returns: int.
    # Purpose: Return the number of seconds used for a short seek.
    def small_jump(self) -> int:
        return max(1, int(self.config.get("small_jump")))

    # Return the configured big jump in seconds.
    # Inputs: none.
    # Returns: int.
    # Purpose: Return the number of seconds used for a long seek.
    def big_jump(self) -> int:
        return max(1, int(self.config.get("big_jump")))

    # Start the selected channel and create the local timeshift pipeline.
    # Inputs: none.
    # Returns: None.
    # Purpose: Start the relevant player, server, timer, or application action.
    def start(self) -> None:
        if not self.channels:
            self.load_playlist()
        if not self.channels:
            message = ("Keine Kanäle von TVHeadend geladen. Prüfen Sie Server-URL, Playlist-Pfad und Zugangsdaten."
                       if self.config.get("source_mode").lower() == "tvheadend"
                       else "Keine RTSP-Sender in der M3U-Datei gefunden.")
            messagebox.showerror(
                APP_NAME, message
            )
            return

        if self.channel_index < 0:
            self.channel_index = 0

        self.start_channel(self.channel_index)

    # Stop all streaming components while keeping the application window open.
    # Inputs: wait_cleanup, keep_player.
    # Returns: None.
    # Purpose: Stop the relevant player or service and release its resources.
    def stop(self, wait_cleanup: bool = False, keep_player: bool = False) -> None:
        self.running = False
        self.paused = False
        self.view_mode = "live"
        for attribute in ("watch_after_id", "no_data_after_id"):
            after_id = getattr(self, attribute)
            if after_id is not None:
                try:
                    self.root.after_cancel(after_id)
                except tk.TclError:
                    pass
                setattr(self, attribute, None)
        if self.buffer_status_after_id is not None:
            try:
                self.root.after_cancel(self.buffer_status_after_id)
            except tk.TclError:
                pass
            self.buffer_status_after_id = None
        self.now_next_pending = False
        self.close_now_next()
        self.close_program_info()

        if self.recording:
            self.recording.stop()
            self.recording = None

        if self.satip:
            self.satip.stop()
            self.satip = None

        if self.tvheadend:
            self.tvheadend.stop()
            self.tvheadend = None

        # Stop/join the old stream readers before dropping their EPG state.
        self.dvb.reset()
        for channel in self.channels:
            channel.service_id = None
        while True:
            try:
                self.epg_updates.get_nowait()
            except queue.Empty:
                break

        if self.relay:
            self.relay.close()
            self.relay = None

        if self.timeshift:
            # The old ring is renamed instantly and deleted in the background,
            # so switching channels does not wait for the disk. Only on exit
            # the deletion is awaited.
            self.timeshift.stop(wait_for_delete=wait_cleanup)
            self.timeshift = None

        if self.mpv and not keep_player:
            self.mpv.stop()
            self.mpv = None
        if not keep_player:
            self.live_direct_active = False

        self.status_var.set("Gestoppt")
        self.update_title()
        self.ts_var.set("")

    # Start a specific M3U channel by zero-based list index.
    # Inputs: index.
    # Returns: None.
    # Purpose: Tune the receiver and start playback of the selected channel.
    def start_channel(self, index: int) -> None:
        if not (0 <= index < len(self.channels)):
            return

        channel = self.channels[index]
        live_direct = self.config.get("live_path").lower() != "hls"
        # In direct mode the player process stays alive between channels.
        self.stop(keep_player=live_direct)
        t_switch = time.monotonic()

        try:
            player_kind = self.config.get("player").lower()
            source_mode = self.config.get("source_mode").lower()
            # The mpv-native disk cache is one opaque file and cannot rotate
            # old data safely. Use the managed rolling ring for chunk eviction.
            direct_tvh_mpv = False
            player_path = self.config.get("vlc_path" if player_kind == "vlc" else "mpv_path")
            ffmpeg_path = self.config.get("ffmpeg_path")

            if shutil.which(player_path) is None and not Path(player_path).exists():
                raise RuntimeError(f"{player_kind} nicht gefunden: {player_path}")
            if not direct_tvh_mpv and shutil.which(ffmpeg_path) is None and not Path(ffmpeg_path).exists():
                raise RuntimeError(f"ffmpeg nicht gefunden: {ffmpeg_path}")

            use_ram = self.config.get("timeshift_ram").lower() == "true"
            ram_size_gb = float(self.config.get("timeshift_ram_size_gb"))
            storage_note = ""
            archive_directory = None
            ram_capacity_gb = 0.0
            disk_directory = Path(self.config.get("timeshift_directory")).expanduser()
            disk_size_gb = float(self.config.get("timeshift_size_gb"))
            if not direct_tvh_mpv and use_ram and Path("/dev/shm").is_dir():
                available_gb = shutil.disk_usage("/dev/shm").free / 1024 ** 3
                ram_capacity_gb = min(ram_size_gb, available_gb * 0.8)
            if direct_tvh_mpv:
                storage_note = " (mpv-Timeshiftcache)"
            elif ram_capacity_gb >= 0.05:
                directory = Path("/dev/shm") / APP_NAME
                archive_directory = disk_directory
                size_gb = disk_size_gb
                storage_note = " (Timeshift RAM + Datenträger)"
            else:
                directory = disk_directory
                size_gb = disk_size_gb
                if use_ram:
                    storage_note = " (RAM nicht verfügbar, Datenträger aktiv)"

            if not direct_tvh_mpv:
                self.timeshift = Timeshift(
                    ffmpeg_path,
                    directory,
                    size_gb,
                    segment_seconds=max(1, min(4, int(float(self.config.get("segment_s") or 2)))),
                    archive_directory=archive_directory,
                    ram_size_gb=ram_capacity_gb,
                    playlist_window_min=float(self.config.get("playlist_window_min") or 0),
                    probe_s=float(self.config.get("probe_s").replace(",", ".") or 2),
                )
                self.timeshift.start()
                if live_direct:
                    self.relay = LiveRelay()
                    self.relay.start()

            if source_mode == "tvheadend":
                self.tvheadend = TvheadendClient(
                    channel.url,
                    self.config.get("tvh_username"),
                    self.config.get("tvh_password"),
                    self.config.get("tvh_login_mode"),
                    "127.0.0.1" if self.timeshift else None,
                    self.timeshift.input_port if self.timeshift else None,
                    payload_callback=self.dvb.feed,
                )
                if direct_tvh_mpv:
                    stream_url = self.tvheadend.start_proxy()
                else:
                    if self.relay:
                        self.tvheadend.tap = self.relay.push
                    self.tvheadend.start()
                    stream_url = None
            else:
                self.satip = SatIpClient(
                    self.config.get("exip_ip"),
                    int(self.config.get("rtsp_port")),
                    "127.0.0.1",
                    self.timeshift.input_port,
                    payload_callback=self.dvb.feed,
                )
                # SAT>IP RTP is forwarded to the UDP port consumed by ffmpeg
                # and, in direct mode, to the live relay for the player.
                if self.relay:
                    self.satip.tap = self.relay.push
                self.satip.tune(channel.url, self.timeshift.input_port)

            # The regular path waits for a completed file. Native TVHeadend
            # playback instead waits for bytes from its stream client above.
            if self.timeshift and not live_direct and not self.timeshift.wait_ready(15.0):
                details = []
                if self.config.get("source_mode").lower() == "tvheadend":
                    message = "TVHeadend-Stream gestartet, aber ffmpeg hat keine abspielbare Timeshift-Playlist erzeugt."
                    if self.tvheadend:
                        details.append(f"TVHeadend-Daten weitergeleitet: {self.tvheadend.bytes_forwarded} Bytes")
                        if self.tvheadend.error:
                            details.append(f"Relay-Fehler: {self.tvheadend.error}")
                    if self.timeshift.process and self.timeshift.process.poll() is not None:
                        details.append(f"ffmpeg wurde mit Status {self.timeshift.process.returncode} beendet")
                    details.extend(self.timeshift.ffmpeg_errors[-3:])
                else:
                    message = "Es wurde kein Timeshift-Segment empfangen. Bitte prüfen Sie EXIP-Adresse, M3U-Eintrag und SAT>IP-Verbindung."
                raise RuntimeError(
                    message + ("\n\n" + "\n".join(details) if details else "")
                )

            if not live_direct:
                dprint(f"[Start] erstes Segment nach {time.monotonic() - t_switch:.1f} s", flush=True)

            # Without speed control the player starts only when a small reserve
            # is already in the playlist, so it does not run into the live edge.
            # With speed control it starts at once, slowed down, and builds the
            # reserve while playing.
            adaptive_cfg: dict[str, float] | None = None
            if player_kind != "vlc" and self.config.get("adaptive_speed").lower() == "true":
                try:
                    adaptive_cfg = {
                        "target": max(1.0, min(9.0, float(self.config.get("buffer_target_s").replace(",", ".")))),
                        "min": max(0.5, min(1.0, float(self.config.get("speed_min").replace(",", ".")))),
                        "max": max(1.0, min(1.5, float(self.config.get("speed_max").replace(",", ".")))),
                    }
                    # mpv read-ahead: always clearly above the target reserve.
                    adaptive_cfg["cap"] = max(10.0, adaptive_cfg["target"] + 6.0)
                except ValueError:
                    adaptive_cfg = None
            if self.timeshift and not live_direct:
                live_delay = max(0.0, float(self.config.get("live_delay_s").replace(",", ".") or 0))
                if adaptive_cfg:
                    live_delay = 0.0
                if live_delay > 0:
                    self.status_var.set("Puffere …")
                    self.root.update_idletasks()
                    self.timeshift.wait_buffered(live_delay, timeout=live_delay + 20.0)

            volume = int(self.config.get("volume"))
            player_class = VlcPlayer if player_kind == "vlc" else MpvPlayer
            if live_direct:
                if self.mpv is not None and not (type(self.mpv) is player_class and self.mpv.alive()):
                    self.mpv.stop()
                    self.mpv = None
            else:
                self.mpv = player_class(player_path, volume)

            self.video_frame.update_idletasks()
            window_id = self.video_frame.winfo_id()
            if live_direct:
                assert self.relay is not None
                live_url = self.relay.url()
                if self.mpv is not None:
                    self.mpv.play_live(live_url, adaptive_cfg)
                else:
                    self.mpv = player_class(player_path, volume)
                    if isinstance(self.mpv, MpvPlayer):
                        self.mpv.start(
                            window_id, live_url, adaptive=adaptive_cfg, direct_live=True,
                            probe_s=float(self.config.get("probe_s").replace(",", ".") or 2),
                        )
                    else:
                        self.mpv.start(window_id, live_url)
                self.adaptive_cfg = adaptive_cfg
                self.view_mode = "live"
            elif direct_tvh_mpv:
                native_cache_dir = disk_directory / "mpv_native_cache"
                self.mpv.start(
                    window_id,
                    stream_url or "",
                    direct_stream=True,
                    cache_directory=native_cache_dir,
                    ram_size_gb=ram_size_gb if use_ram else 0.0,
                    disk_size_gb=disk_size_gb,
                )
                if not self.tvheadend or not self.tvheadend.wait_ready(15.0):
                    detail = f" ({self.tvheadend.error})" if self.tvheadend and self.tvheadend.error else ""
                    raise RuntimeError("TVHeadend hat keinen MPEG-TS-Datenstrom geliefert." + detail)
            else:
                assert self.timeshift is not None
                if isinstance(self.mpv, MpvPlayer):
                    self.mpv.start(window_id, self.timeshift.playlist_url(),
                                   adaptive=adaptive_cfg)
                else:
                    self.mpv.start(window_id, self.timeshift.playlist_url())

            dprint(f"[Start] Player gestartet nach {time.monotonic() - t_switch:.1f} s", flush=True)
            self.channel_index = index
            self.config.set("last_channel", str(index + 1))
            self.channel_var.set(
                f"{index + 1}: {channel.name}"
            )
            self.live_status_text = "Live" + storage_note
            self.status_var.set(self.live_status_text)
            dprint(f"[{APP_NAME}] channel {index + 1}: {channel.name}", flush=True)
            self.running = True
            self.live_direct_active = live_direct
            self.update_title()
            self.update_ts_info()
            if DEBUG_CLI:
                self.root.after(12000, lambda i=index: self._diagnose_service(i))
            self.apply_aspect_soon()
            self._sync_list_selection()
            if self.title_interval() > 0:
                # EPG data usually arrives a few seconds after tuning.
                self.root.after(4000, self.update_title)
            if live_direct and self.relay is not None:
                relay_ref = self.relay
                self.no_data_after_id = self.root.after(
                    8000, lambda: self._check_stream_data(relay_ref))
            if adaptive_cfg:
                self.buffer_status_after_id = self.root.after(1000, self._update_buffer_status)
            self.now_next_pending = True
            self.root.after(1500, self.show_now_next)
            self.paused = False

        except Exception as exc:
            self.stop()
            title = "TVHeadend-Fehler" if self.config.get("source_mode").lower() == "tvheadend" else "SAT>IP Fehler"
            messagebox.showerror(title, str(exc), parent=self.root)

    # Show buffer reserve and playback speed in the status line while live.
    # Inputs: none.
    # Returns: None.
    # Purpose: Refresh the on-screen message showing the available timeshift buffer.
    def _update_buffer_status(self) -> None:
        self.buffer_status_after_id = None
        if not self.running or not isinstance(self.mpv, MpvPlayer) or not self.mpv.adaptive:
            return
        if (not self.paused and self.mpv.buffer_ahead is not None
                and self.status_var.get().startswith("Live")):
            self.status_var.set(
                f"{self.live_status_text} · Puffer {self.mpv.buffer_ahead:.1f} s"
                f" · Tempo {self.mpv.current_speed:.2f}×"
            )
        self.buffer_status_after_id = self.root.after(1000, self._update_buffer_status)

    # Queue DVB updates from worker threads; Tk calls must stay on the UI thread.
    # Inputs: service_id, service_name, current, following.
    # Returns: None.
    # Purpose: Pass updated programme information to the main user-interface thread.
    def on_now_next(self, service_id: int, service_name: str, current: object,
                    following: object) -> None:
        self.epg_updates.put((service_id, service_name, current, following))

    # Apply queued DVB updates on Tk's main thread.
    # Inputs: none.
    # Returns: None.
    # Purpose: Apply queued programme-guide updates to the visible channel information.
    def process_epg_updates(self) -> None:
        latest = None
        while True:
            try:
                latest = self.epg_updates.get_nowait()
            except queue.Empty:
                break
        if latest is not None:
            self._handle_now_next(*latest)
        try:
            if self.root.winfo_exists():
                self.root.after(250, self.process_epg_updates)
        except tk.TclError:
            pass

    # Match DVB service information to the current channel on the UI thread.
    # Inputs: service_id, service_name, current, following.
    # Returns: None.
    # Purpose: Update the programme information shown for the selected channel.
    def _handle_now_next(self, service_id: int, service_name: str,
                         current: object, following: object) -> None:
        if self.channel_index < 0 or self.channel_index >= len(self.channels):
            return
        channel = self.channels[self.channel_index]
        # Once the service is known, ignore EIT data of all other services in
        # the multiplex. Otherwise similar names (e.g. "ZDF" / "ZDFneo") make
        # the overlay switch back and forth and rebuild itself endlessly.
        if channel.service_id is None:
            # Resolves via PMT PID or exact name and stores the result.
            resolved = self.find_service_id()
            if channel.service_id is None and resolved != service_id:
                # Only a partial name match (or nothing) is known: accept it
                # for the service it points to, ignore all others.
                return
        elif service_id != channel.service_id:
            return
        if self.now_next_pending or self.now_next_window is not None:
            self.show_now_next()

    # Debug aid: explain why no programme information could be assigned.
    # Inputs: index.
    # Returns: None.
    # Purpose: Check why a playlist channel has not matched a receiver service.
    def _diagnose_service(self, index: int) -> None:
        if not self.running or index != self.channel_index or index >= len(self.channels):
            return
        channel = self.channels[index]
        service_id = self.find_service_id()
        if service_id is not None and self.dvb.events.get(service_id):
            return
        names = {sid: name for sid, name in list(self.dvb.service_names.items())}
        dprint(f"[N&N] Keine Programminfo für '{channel.name}' (Service-ID: {service_id}). "
               f"URL-PIDs={sorted(channel.pids)} PAT={dict(self.dvb.pat_programs)} "
               f"EIT-Services={sorted(self.dvb.events)} SDT-Namen={names}", flush=True)

    # Find the best service ID for the selected M3U channel from parsed SDT data.
    # Inputs: none.
    # Returns: int | None.
    # Purpose: Find the receiver service number that matches a playlist channel.
    def find_service_id(self) -> int | None:
        if self.channel_index < 0 or self.channel_index >= len(self.channels):
            return None
        channel = self.channels[self.channel_index]
        if channel.service_id is not None:
            return channel.service_id
        # Most reliable: the M3U URL requests the PMT PID of the service, and the
        # PAT tells which service number that PMT belongs to. This also works for
        # channels whose SDT name differs from the M3U name (e.g. regional
        # variants of the ARD third programmes).
        if channel.pids:
            matches = [program for program, pmt_pid in dict(self.dvb.pat_programs).items()
                       if pmt_pid in channel.pids]
            if len(matches) == 1:
                channel.service_id = matches[0]
                dprint(f"[N&N] '{channel.name}': Service-ID {matches[0]} über PMT-PID "
                       f"(SDT-Name: {self.dvb.service_names.get(matches[0], '?')})", flush=True)
                return matches[0]
        target = self.normalize_name(channel.name)
        names = dict(self.dvb.service_names)
        # Exact name first, then partial match.
        for service_id, name in names.items():
            if target and target == self.normalize_name(name):
                channel.service_id = service_id
                return service_id
        for service_id, name in names.items():
            if target and target in self.normalize_name(name):
                # Partial matches are not stored: the exact entry may still
                # arrive with a later SDT section.
                return service_id
        return None

    # Return a filesystem-friendly normalized sender name for logo lookup.
    # Inputs: name.
    # Returns: str.
    # Purpose: Make a channel name easier to compare by removing formatting differences.
    @staticmethod
    def normalize_name(name: str) -> str:
        text = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode()
        return re.sub(r"[^a-z0-9]+", "", text.lower())

    # Background colour behind the logo in the Now/Next overlay (hex, with or without #).
    # Inputs: none.
    # Returns: str.
    # Purpose: Return the configured background color for channel logos.
    def logo_background(self) -> str:
        value = self.config.get("logo_bg").strip().lstrip("#")
        if re.fullmatch(r"[0-9a-fA-F]{6}", value):
            return "#" + value.upper()
        return "#A0A0A0"

    # Locate the PNG logo using the SDT/M3U service name, including a normalized fallback.
    # Inputs: service_name, channel_name.
    # Returns: Path | None.
    # Purpose: Find an image file that matches the channel name.
    def find_logo(self, service_name: str, channel_name: str) -> Path | None:
        candidates = [name for name in (service_name, channel_name) if name]
        # Second pass without a trailing " HD" if nothing was found.
        stripped = [re.sub(r"\s+HD$", "", name.strip(), flags=re.IGNORECASE)
                    for name in candidates]
        for name in candidates + [n for n in stripped if n not in candidates]:
            if not name:
                continue
            direct = LOGO_DIR / f"{name.strip()}.png"
            if direct.exists():
                return direct
            normalized = self.normalize_name(name)
            for path in LOGO_DIR.glob("*.png"):
                if self.normalize_name(path.stem) == normalized:
                    return path
        return None

    # Display the Now/Next overlay for the configured number of seconds.
    # Inputs: none.
    # Returns: None.
    # Purpose: Display the current and upcoming programmes for the channel.
    def show_now_next(self) -> None:
        service_id = self.find_service_id()
        if service_id is None:
            return
        events = self.dvb.events.get(service_id, [])
        now = datetime.now().astimezone()
        current = None
        following = None
        for event in sorted(events, key=lambda e: e["start"]):
            if event["start"] <= now < event["end"]:
                current = event
            elif event["start"] > now and following is None:
                following = event
        service_name = self.dvb.service_names.get(service_id, "") or self.channels[self.channel_index].name
        if current is None and following is None:
            return
        # Inputs: event.
        # Returns: tuple | None.
        # Purpose: Close or update the programme window when the user presses a key.
        def event_key(event: object) -> tuple | None:
            if not event:
                return None
            return (event["id"], event["title"], event["start"], event["end"])

        signature = (service_id, event_key(current), event_key(following))
        if (self.now_next_window is not None
                and self.now_next_window.winfo_exists()
                and signature == self.now_next_signature):
            return
        rebuilt = self.now_next_window is not None
        self.close_now_next()
        dprint(f"[N&N] {'neu aufgebaut' if rebuilt else 'angezeigt'}: "
              f"{service_name} | jetzt={current['title'] if current else '-'} | "
              f"danach={following['title'] if following else '-'}", flush=True)
        win = tk.Toplevel(self.root)
        self.now_next_window = win
        self.now_next_signature = signature
        self.now_next_pending = False
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        win.configure(background="#101010")
        frame = ttk.Frame(win, padding=14)
        frame.pack(fill="both", expand=True)

        logo = self.find_logo(service_name, self.channels[self.channel_index].name)
        if logo:
            try:
                image = tk.PhotoImage(file=str(logo))
                image = image.subsample(max(1, image.width() // 180)) if image.width() > 180 else image
                label_logo = tk.Label(frame, image=image, background=self.logo_background())
                label_logo.image = image
                label_logo.grid(row=0, column=0, rowspan=3, padx=(0, 14), sticky="n")
            except tk.TclError:
                pass

        clock = tk.StringVar()
        # Clock and station name share the same font, the station right of the clock.
        # The station name is passed as plain text: a local StringVar would be
        # garbage-collected after this method returns and the label would turn empty.
        clock_font = ("Sans", 18, "bold")
        ttk.Label(frame, textvariable=clock, font=clock_font).grid(row=0, column=1, sticky="w")
        ttk.Label(frame, text=service_name, font=clock_font).grid(row=0, column=2, sticky="w", padx=(20, 0))
        self._add_event_line(frame, 1, "JETZT", current)
        self._add_event_line(frame, 2, "DANACH", following)
        self._update_overlay_clock(clock)

        self.root.update_idletasks()
        x = self.root.winfo_rootx() + 25
        y = self.root.winfo_rooty() + self.root.winfo_height() - win.winfo_reqheight() - 70
        win.geometry(f"{win.winfo_reqwidth()}x{win.winfo_reqheight()}+{x}+{y}")
        timeout = max(1, int(self.config.get("now_next_timeout"))) * 1000
        if rebuilt and self.now_next_shown_at is not None:
            # A rebuild must not restart the timer, otherwise the overlay
            # would never disappear while updates keep arriving.
            elapsed = int((time.monotonic() - self.now_next_shown_at) * 1000)
            timeout = max(300, timeout - elapsed)
        else:
            self.now_next_shown_at = time.monotonic()
        self.now_next_after_id = self.root.after(timeout, self.close_now_next)

    # Toggle a persistent detail window for the event currently on air.
    # Inputs: none.
    # Returns: None.
    # Purpose: Show or hide the detailed programme information window.
    def toggle_program_info(self) -> None:
        if self.info_window is not None and self.info_window.winfo_exists():
            self.close_program_info()
            return

        service_id = self.find_service_id()
        now = datetime.now().astimezone()
        current = None
        if service_id is not None:
            for event in self.dvb.events.get(service_id, []):
                if event["start"] <= now < event["end"]:
                    current = event
                    break
        service_name = (
            self.dvb.service_names.get(service_id, "") if service_id is not None else ""
        ) or (self.channels[self.channel_index].name if self.channels else "Fernsehen")

        win = tk.Toplevel(self.root)
        self.info_window = win
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        win.configure(background="#101010")
        frame = ttk.Frame(win, padding=16)
        frame.pack(fill="both", expand=True)

        logo = self.find_logo(service_name, self.channels[self.channel_index].name)
        if logo:
            try:
                image = tk.PhotoImage(file=str(logo))
                if image.width() > 150:
                    image = image.subsample(max(1, image.width() // 150))
                label_logo = tk.Label(frame, image=image, background=self.logo_background())
                label_logo.image = image
                label_logo.grid(row=0, column=0, rowspan=3, padx=(0, 16), sticky="n")
            except tk.TclError:
                pass

        content_column = 1 if logo else 0
        ttk.Label(frame, text="PROGRAMMINFO", font=("Sans", 10, "bold")).grid(
            row=0, column=content_column, sticky="w"
        )
        ttk.Label(frame, text=service_name, font=("Sans", 14, "bold")).grid(
            row=1, column=content_column, sticky="w", pady=(2, 8)
        )
        if current:
            title = str(current.get("title", "(ohne Titel)"))
            time_text = (
                f"{current['start'].strftime('%H:%M')} – "
                f"{current['end'].strftime('%H:%M')}"
            )
            description = str(current.get("description", "")).strip()
        else:
            title = "Keine aktuelle Sendungsinformation verfügbar"
            time_text = ""
            description = "Für diese Sendung wurden noch keine EPG-Daten empfangen."

        ttk.Label(
            frame, text=title, font=("Sans", 19, "bold"), wraplength=760,
            justify="left",
        ).grid(row=2, column=content_column, sticky="w", pady=(0, 6))
        ttk.Label(
            frame, text=time_text, font=("Sans", 12),
        ).grid(row=3, column=content_column, sticky="w", pady=(0, 12))
        description_label = ttk.Label(
            frame,
            text=description or "Keine ausführliche Beschreibung verfügbar.",
            font=("Sans", 12),
            wraplength=760,
            justify="left",
        )
        description_label.grid(row=4, column=content_column, sticky="nw")

        ttk.Button(frame, text="Schließen (i)", command=self.close_program_info).grid(
            row=5, column=content_column, sticky="e", pady=(16, 0)
        )
        win.bind("<Escape>", self.close_program_info_event)
        win.bind("<KeyPress-i>", self.close_program_info_event)
        win.bind("<KeyPress-I>", self.close_program_info_event)

        self.root.update_idletasks()
        width = win.winfo_reqwidth()
        height = win.winfo_reqheight()
        x = self.root.winfo_rootx() + max(20, (self.root.winfo_width() - width) // 2)
        y = self.root.winfo_rooty() + max(20, (self.root.winfo_height() - height) // 3)
        win.geometry(f"{width}x{height}+{x}+{y}")

    # Close the persistent programme detail window, if it is open.
    # Inputs: none.
    # Returns: None.
    # Purpose: Close the detailed programme information window.
    def close_program_info(self) -> None:
        if self.info_window is not None:
            try:
                self.info_window.destroy()
            except tk.TclError:
                pass
            self.info_window = None

    # Inputs: _event.
    # Returns: str.
    # Purpose: Close the programme information window after a user event.
    def close_program_info_event(self, _event: tk.Event) -> str:
        self.close_program_info()
        return "break"

    # Add one Now/Next event line to the overlay.
    # Inputs: parent, row, label, event.
    # Returns: None.
    # Purpose: Add one programme detail and its label to the information window.
    def _add_event_line(self, parent: tk.Misc, row: int, label: str, event: object) -> None:
        if not event:
            text = "--:-- – --:--   keine Daten"
        else:
            text = f"{event['start'].strftime('%H:%M')} – {event['end'].strftime('%H:%M')}   {event['title']}"
        ttk.Label(parent, text=label, width=8, font=("Sans", 10, "bold")).grid(row=row, column=1, sticky="w")
        ttk.Label(parent, text=text, font=("Sans", 17)).grid(row=row, column=2, sticky="w", padx=(20, 0))

    # Keep the displayed clock current while the Now/Next overlay is visible.
    # Inputs: variable.
    # Returns: None.
    # Purpose: Refresh the clock shown in the information window.
    def _update_overlay_clock(self, variable: tk.StringVar) -> None:
        if self.now_next_window is None or not self.now_next_window.winfo_exists():
            return
        variable.set(datetime.now().strftime("%H:%M"))
        self.root.after(1000, lambda: self._update_overlay_clock(variable))

    # Close the Now/Next overlay and cancel its pending timeout.
    # Inputs: none.
    # Returns: None.
    # Purpose: Close the current and next programme display.
    def close_now_next(self) -> None:
        if self.now_next_after_id is not None:
            try:
                self.root.after_cancel(self.now_next_after_id)
            except tk.TclError:
                pass
            self.now_next_after_id = None
        if self.now_next_window is not None:
            try:
                self.now_next_window.destroy()
            except tk.TclError:
                pass
            self.now_next_window = None
        self.now_next_signature = None

    # Toggle pause/play in mpv without stopping the SAT>IP receiver.
    # Warn if the receiver delivers no data at all after the channel change.
    # Inputs: relay.
    # Returns: None.
    # Purpose: Check whether stream data is still arriving.
    def _check_stream_data(self, relay: LiveRelay) -> None:
        self.no_data_after_id = None
        if self.running and self.relay is relay and relay.total_bytes == 0:
            self.status_var.set("Keine Daten vom Sender – EXIP, Antenne und M3U-Eintrag prüfen")

    # How far the displayed picture lags behind the data arriving from the tuner.
    # Inputs: none.
    # Returns: float.
    # Purpose: Show how far playback is behind the live stream.
    def _display_lag(self) -> float:
        if isinstance(self.mpv, MpvPlayer):
            ahead = self.mpv.buffer_ahead
            return (ahead if ahead is not None else 0.5) + 0.3
        return 1.5

    # Distance to the live edge (seconds) below which timeshift hands over to live.
    # Inputs: none.
    # Returns: float.
    # Purpose: Return the time of the newest video received.
    def _live_edge(self) -> float:
        segment = self.timeshift.segment_seconds if self.timeshift else 2
        return 2.0 * segment + 2.0

    # Inputs: none.
    # Returns: float | None.
    # Purpose: Convert the playback position into its original broadcast time.
    def _timeshift_wall_position(self) -> float | None:
        if self.mpv is None:
            return None
        if isinstance(self.mpv, VlcPlayer) and self.view_mode == "timeshift":
            elapsed = max(0.0, time.monotonic() - self.ts_snapshot_started)
            return self.ts_anchor_wall + elapsed
        position = self.mpv.get_position()
        if position is None:
            return None
        return self.ts_anchor_wall + (position - self.ts_anchor_pos)

    # Inputs: none.
    # Returns: str.
    # Purpose: Return the current timeshift position and buffer information.
    def _timeshift_status(self) -> str:
        wall = self._timeshift_wall_position()
        if wall is None:
            return "Timeshift  (L = Live)"
        return f"Timeshift −{max(0.0, time.time() - wall):.0f} s  (L = Live)"

    # Switch the player from the live stream to the timeshift ring.
    # Inputs: target_wall, start_paused.
    # Returns: None.
    # Purpose: Switch from live playback to the requested point in the buffer.
    def _enter_timeshift(self, target_wall: float, start_paused: bool) -> None:
        if self.timeshift is None or self.mpv is None:
            return
        if time.time() - target_wall < self._live_edge():
            # Too close to live for the segment-based ring: show live.
            self._enter_live()
            return
        # Both players need a playlist that grows as new segments arrive.
        # A finite VLC snapshot ends after its initial backlog, even though
        # the timeshift ring continues receiving data.
        prepared = self.timeshift.prepare_from(target_wall, finite=False)
        if prepared is None:
            self.status_var.set("Timeshift: für diese Position noch keine Daten")
            return
        url, start_wall, end_wall = prepared
        start_offset = max(0.0, target_wall - start_wall)
        first_position = self.mpv.play_timeshift(url, start_paused, start_offset)
        self.view_mode = "timeshift"
        self.paused = start_paused
        if isinstance(self.mpv, VlcPlayer):
            self.ts_anchor_wall = target_wall
            self.ts_anchor_pos = 0.0
            self.ts_snapshot_duration = max(0.0, end_wall - target_wall)
        else:
            self.ts_anchor_wall = start_wall
            self.ts_anchor_pos = first_position if first_position is not None else 0.0
            self.ts_snapshot_duration = max(0.0, end_wall - start_wall)
        self.ts_snapshot_started = time.monotonic()
        if start_paused:
            self.pause_started = self.ts_snapshot_started
        self.status_var.set(self._timeshift_status())
        self.update_ts_info()
        if self.watch_after_id is None:
            self.watch_after_id = self.root.after(1000, self._timeshift_watch)

    # Switch the player back to the direct live stream.
    # Inputs: none.
    # Returns: None.
    # Purpose: Return playback to the live stream.
    def _enter_live(self) -> None:
        if self.mpv is None or self.relay is None:
            return
        self.mpv.play_live(self.relay.url(back_bytes=1_500_000), self.adaptive_cfg)
        self.view_mode = "live"
        self.paused = False
        self.ts_snapshot_duration = 0.0
        self.status_var.set(self.live_status_text)
        self.update_ts_info()

    # While in timeshift: show the lag and return to live when it is reached.
    # Inputs: none.
    # Returns: None.
    # Purpose: Periodically update playback and buffer status while timeshifting.
    def _timeshift_watch(self) -> None:
        self.watch_after_id = None
        if not self.running or self.view_mode != "timeshift":
            return
        if not self.paused:
            wall = self._timeshift_wall_position()
            if wall is not None:
                lag = time.time() - wall
                self.status_var.set(f"Timeshift −{lag:.0f} s  (L = Live)")
        self.watch_after_id = self.root.after(1000, self._timeshift_watch)

    # Stop key: while watching from the timeshift ring (or after a longer
    # pause) the first press returns to live, the next one stops playback.
    # Inputs: none.
    # Returns: None.
    # Purpose: Stop playback in response to the configured keyboard shortcut.
    def stop_key(self) -> None:
        if (self.running and self.live_direct_active
                and (self.view_mode == "timeshift" or self.paused)):
            self._enter_live()
            return
        self.stop()

    # Inputs: none.
    # Returns: None.
    # Purpose: Jump from delayed playback to the live broadcast.
    def go_live(self) -> None:
        if not self.mpv or not self.running:
            return
        if self.live_direct_active and (self.view_mode == "timeshift" or self.paused):
            self._enter_live()
        else:
            self.status_var.set(self.live_status_text)

    # Inputs: none.
    # Returns: None.
    # Purpose: Pause or resume the current channel.
    def pause(self) -> None:
        if not self.mpv or not self.running:
            return
        if self.live_direct_active and self.view_mode == "live":
            if not self.paused:
                self.pause_started = time.time()
                self.pause_wall = self.pause_started - self._display_lag()
                self.mpv.toggle_pause()
                self.paused = True
                self.status_var.set("Pause")
            elif time.time() - self.pause_started <= 2.0:
                # Short pause: the relay still holds the data, just continue.
                self.mpv.toggle_pause()
                self.paused = False
                self.status_var.set(self.live_status_text)
            else:
                # Longer pause: continue from the ring at the paused position.
                self._enter_timeshift(self.pause_wall, start_paused=False)
            return
        self.mpv.toggle_pause()
        self.paused = not self.paused
        if self.view_mode == "timeshift" and isinstance(self.mpv, VlcPlayer):
            if self.paused:
                self.pause_started = time.monotonic()
            else:
                self.ts_snapshot_started += time.monotonic() - self.pause_started
        if self.paused:
            self.status_var.set("Pause")
        elif self.live_direct_active:
            self.status_var.set(self._timeshift_status())
        else:
            self.status_var.set("Live")

    # Inputs: none.
    # Returns: None.
    # Purpose: Start or stop recording the current channel.
    def toggle_recording(self) -> None:
        if self.recording:
            self.recording.stop()
            self.recording = None
            if self.satip:
                self.satip.recording = None
            if self.tvheadend:
                self.tvheadend.recording = None
            self.status_var.set("Aufnahme beendet")
            return
        if not self.running or (not self.satip and not self.tvheadend):
            self.status_var.set("Zum Aufnehmen zuerst einen Sender starten")
            return
        directory = Path(self.config.get("recording_directory")).expanduser()
        directory.mkdir(parents=True, exist_ok=True)
        channel = self.channels[self.channel_index]
        safe_name = re.sub(r"[^A-Za-z0-9._-]+", "_", channel.name).strip("_") or "Sender"
        filename = directory / f"{datetime.now():%Y%m%d_%H%M%S}_{safe_name}.ts"
        try:
            self.recording = Recording(filename)
        except OSError as exc:
            messagebox.showerror("Aufnahmefehler", str(exc), parent=self.root)
            return
        if self.satip:
            self.satip.recording = self.recording
        if self.tvheadend:
            self.tvheadend.recording = self.recording
        self.status_var.set(f"Aufnahme: {filename.name}")

    # Inputs: none.
    # Returns: None.
    # Purpose: Pause or resume the current recording.
    def toggle_recording_pause(self) -> None:
        if self.recording:
            paused = self.recording.toggle_pause()
            self.status_var.set("Aufnahme pausiert" if paused else "Aufnahme läuft")

    # Tune the next channel, wrapping from the end to the beginning.
    # Inputs: none.
    # Returns: None.
    # Purpose: Tune and play the next channel in the list.
    def next_channel(self) -> None:
        if not self.channels:
            return
        index = (self.channel_index + 1) % len(self.channels)
        self.start_channel(index)

    # Tune the previous channel, wrapping from the beginning to the end.
    # Inputs: none.
    # Returns: None.
    # Purpose: Tune and play the previous channel in the list.
    def previous_channel(self) -> None:
        if not self.channels:
            return
        index = (self.channel_index - 1) % len(self.channels)
        self.start_channel(index)

    # Seek by the requested number of seconds inside the HLS timeshift window.
    # Inputs: seconds.
    # Returns: None.
    # Purpose: Move playback forward or backward by the requested number of seconds.
    def seek(self, seconds: int) -> None:
        if not self.mpv or not self.running:
            return
        if self.live_direct_active:
            if self.view_mode == "live":
                if seconds >= 0:
                    self.status_var.set(self.live_status_text)
                    return
                base = self.pause_wall if self.paused else time.time() - self._display_lag()
            else:
                base = self._timeshift_wall_position()
                if base is None:
                    return
            self._enter_timeshift(base + seconds, start_paused=self.paused)
            return
        self.mpv.seek_by(seconds)
        self.status_var.set(
            f"Seek {'+' if seconds >= 0 else ''}{seconds}s"
        )

    # Change the mpv volume and keep the value for the next program start.
    # Inputs: amount.
    # Returns: None.
    # Purpose: Change the player volume and refresh the displayed value.
    def change_volume(self, amount: int) -> None:
        if not self.mpv:
            return
        self.mpv.add_volume(amount)
        self.config.set("volume", str(self.mpv.volume))
        self.status_var.set(f"Lautstärke {self.mpv.volume}%")

    # Add one digit to the channel number and arm/rearm the timeout.
    # Inputs: digit.
    # Returns: None.
    # Purpose: Add a digit to the channel number being entered.
    def number_digit(self, digit: str) -> None:
        max_digits = 4
        if len(self.number_buffer) >= max_digits:
            self.number_buffer = ""

        self.number_buffer += digit

        if self.number_after_id is not None:
            self.root.after_cancel(self.number_after_id)

        timeout = max(
            1, int(self.config.get("number_timeout_ms"))
        )
        self.number_after_id = self.root.after(
            timeout, self.execute_number
        )

        self.status_var.set(f"Sendernummer: {self.number_buffer}")

    # Execute the buffered channel number after the configured timeout.
    # Inputs: none.
    # Returns: None.
    # Purpose: Tune the channel whose number the user entered.
    def execute_number(self) -> None:
        self.number_after_id = None
        if not self.number_buffer:
            return

        try:
            number = int(self.number_buffer)
        finally:
            self.number_buffer = ""

        if 1 <= number <= len(self.channels):
            self.start_channel(number - 1)
        else:
            self.status_var.set(f"Sender {number} nicht vorhanden")

    # Cancel an incomplete numeric channel entry.
    # Inputs: none.
    # Returns: None.
    # Purpose: Clear an unfinished channel number entry.
    def clear_number_buffer(self) -> None:
        if self.number_after_id is not None:
            self.root.after_cancel(self.number_after_id)
            self.number_after_id = None
        self.number_buffer = ""
        self.status_var.set("Bereit")

    # Open the configuration dialog and reload settings after saving.
    # Inputs: none.
    # Returns: None.
    # Purpose: Open the settings window.
    def open_settings(self) -> None:
        previous_source = self.config.get("source_mode")
        dialog = SettingsDialog(self.root, self.config)
        self.root.wait_window(dialog)
        if dialog.result:
            self.config.load()
            global DEBUG_CLI
            DEBUG_CLI = self.config.get("debug_cli").lower() == "true"
            self.close_channel_list()
            self.restart_title_timer()
            self.restart_ts_timer()
            self.bind_keys()
            if self.config.get("source_mode") != previous_source:
                self.source_mode_var.set(self.config.get("source_mode"))
                self.change_source_mode()
            else:
                self.load_playlist()
            self.status_var.set("Einstellungen gespeichert")

    # ----- compensate window manager position offsets -----------------------
    # Inputs: geometry, offset.
    # Returns: str.
    # Purpose: Adjust the saved window position to match its screen corner.
    @staticmethod
    def shifted_geometry(geometry: str, offset: tuple[int, int]) -> str:
        match = GEOMETRY_RE.fullmatch(geometry.strip())
        if not match:
            return geometry
        width, height, x, y = (int(value) for value in match.groups())
        return f"{width}x{height}+{x - offset[0]}+{y - offset[1]}"

    # Inputs: none.
    # Returns: tuple[int, int].
    # Purpose: Read the saved window position and size from the settings.
    def load_window_offset(self) -> tuple[int, int]:
        match = re.fullmatch(r"(-?\d+)\s*,\s*(-?\d+)", self.config.get("window_offset").strip())
        return (int(match.group(1)), int(match.group(2))) if match else (0, 0)

    # Compare the position the window manager really reports with the requested
    # one and correct the window (once) if they differ.
    # Inputs: attempt.
    # Returns: None.
    # Purpose: Convert the current window position into saved screen-corner distances.
    def calibrate_window_position(self, attempt: int = 0) -> None:
        if self.window_mode != 1:
            return
        if attempt < 10 and not self.root.winfo_ismapped():
            self.root.after(200, lambda: self.calibrate_window_position(attempt + 1))
            return
        wanted = GEOMETRY_RE.fullmatch(self.intended_geometry.strip())
        actual = GEOMETRY_RE.fullmatch(self.root.geometry().strip())
        if not wanted or not actual:
            return
        want_x, want_y = int(wanted.group(3)), int(wanted.group(4))
        error_x = int(actual.group(3)) - want_x
        error_y = int(actual.group(4)) - want_y
        if (error_x == 0 and error_y == 0) or abs(error_x) > 150 or abs(error_y) > 150:
            return                      # exact, or the user moved the window meanwhile
        offset_x = max(-150, min(150, self.window_offset[0] + error_x))
        offset_y = max(-150, min(150, self.window_offset[1] + error_y))
        self.window_offset = (offset_x, offset_y)
        self.config.set("window_offset", f"{offset_x},{offset_y}")
        self.config.save()
        self.root.geometry(f"+{want_x - offset_x}+{want_y - offset_y}")

    # ----- window position relative to the anchor corner --------------------
    # Inputs: none.
    # Returns: str.
    # Purpose: Return the selected corner used to position the application window.
    def window_anchor(self) -> str:
        anchor = self.config.get("window_anchor").strip().lower()
        return anchor if anchor in WINDOW_ANCHORS else "top-right"

    # Saved size and distances to the anchor corner -> geometry for this screen.
    # Inputs: none.
    # Returns: str.
    # Purpose: Choose the saved or default size and position for the main window.
    def initial_geometry(self) -> str:
        size = re.fullmatch(r"(\d+)x(\d+)", self.config.get("window_size").strip())
        margin = re.fullmatch(r"(-?\d+)\s*,\s*(-?\d+)", self.config.get("window_margin").strip())
        if size and margin:
            return geometry_from_margins(
                int(size.group(1)), int(size.group(2)), int(margin.group(1)), int(margin.group(2)),
                self.window_anchor(), self.root.winfo_screenwidth(), self.root.winfo_screenheight(),
            )
        return self.config.get("window_geometry")

    # Inputs: geometry.
    # Returns: None.
    # Purpose: Save the current window position relative to its selected screen corner.
    def remember_window_position(self, geometry: str) -> None:
        self.config.set("window_geometry", geometry)
        parsed = margins_from_geometry(geometry, self.window_anchor(),
                                       self.root.winfo_screenwidth(), self.root.winfo_screenheight())
        if parsed:
            width, height, margin_x, margin_y = parsed
            self.config.set("window_size", f"{width}x{height}")
            self.config.set("window_margin", f"{margin_x},{margin_y}")

    # ----- window modes ---------------------------------------------------
    # Inputs: flag.
    # Returns: None.
    # Purpose: Maximize or restore the application window.
    def _set_zoomed(self, flag: bool) -> None:
        try:
            self.root.attributes("-zoomed", flag)
        except tk.TclError:
            try:
                self.root.state("zoomed" if flag else "normal")
            except tk.TclError:
                pass

    # Inputs: visible.
    # Returns: None.
    # Purpose: Show or hide the playback controls.
    def _show_controls(self, visible: bool) -> None:
        if visible:
            self.middle.pack_configure(padx=5, pady=5)
            self.controls.pack(fill="x", after=self.middle)
        else:
            self.controls.pack_forget()
            self.middle.pack_configure(padx=0, pady=0)

    # 1 = normal window, 2 = maximized with all window elements,
    # 3 = true fullscreen showing only the video.
    # Inputs: mode.
    # Returns: None.
    # Purpose: Apply the selected window size and display mode.
    def set_window_mode(self, mode: int) -> None:
        if mode == self.window_mode:
            return
        if self.window_mode == 1:
            self.normal_geometry = self.root.geometry()
        if mode == 1:
            self.root.attributes("-fullscreen", False)
            self._set_zoomed(False)
            self._show_controls(True)
            self.root.update_idletasks()
            self.root.geometry(self.shifted_geometry(self.normal_geometry, self.window_offset))
        elif mode == 2:
            self.root.attributes("-fullscreen", False)
            self._show_controls(True)
            self.root.update_idletasks()
            self._set_zoomed(True)
        else:
            self._set_zoomed(False)
            self._show_controls(False)
            self.root.update_idletasks()
            self.root.attributes("-fullscreen", True)
        self.window_mode = mode
        self.root.focus_set()

    # Key "f": normal window -> maximized -> true fullscreen -> normal window.
    # Inputs: none.
    # Returns: None.
    # Purpose: Switch between full-screen and windowed display.
    def toggle_fullscreen(self) -> None:
        self.set_window_mode(self.window_mode % 3 + 1)

    # ESC: close overlays first, then leave the fullscreen modes.
    # Inputs: none.
    # Returns: None.
    # Purpose: Leave full-screen mode when the Escape key is pressed.
    def on_escape(self) -> None:
        if self.number_buffer:
            self.clear_number_buffer()
        elif self.now_next_window is not None:
            self.close_now_next()
        elif self.info_window is not None:
            self.close_program_info()
        elif self.list_frame is not None:
            self.close_channel_list()
        elif self.window_mode != 1:
            self.set_window_mode(1)

    # ----- channel list ---------------------------------------------------
    # Inputs: none.
    # Returns: None.
    # Purpose: Show or hide the channel list.
    def toggle_channel_list(self) -> None:
        if self.list_frame is not None:
            self.close_channel_list()
        else:
            self.open_channel_list()

    # Inputs: none.
    # Returns: None.
    # Purpose: Open the channel list beside the player.
    def open_channel_list(self) -> None:
        if self.list_frame is not None or not self.channels:
            return
        try:
            width = max(50, int(self.config.get("list_width")))
            size = max(6, int(self.config.get("list_font_size")))
        except ValueError:
            width, size = 120, 12
        family = tkfont.nametofont("TkDefaultFont").actual("family")
        frame = tk.Frame(self.middle, width=width, background="#1b1b1b")
        # Packed before the video so the list keeps its width and the video shrinks.
        frame.pack(side="right", fill="y", before=self.video_frame)
        frame.pack_propagate(False)
        scrollbar = ttk.Scrollbar(frame, orient="vertical")
        listbox = tk.Listbox(
            frame, font=(family, size), activestyle="none", exportselection=False,
            background="#1b1b1b", foreground="#e8e8e8", selectbackground="#2f6fb5",
            selectforeground="#ffffff", borderwidth=0, highlightthickness=0,
            yscrollcommand=scrollbar.set,
        )
        scrollbar.configure(command=listbox.yview)
        scrollbar.pack(side="right", fill="y")
        listbox.pack(side="left", fill="both", expand=True)
        for number, channel in enumerate(self.channels, start=1):
            listbox.insert("end", f" {number}  {channel.name}")
        self.list_frame = frame
        self.channel_listbox = listbox

        # Inputs: delta.
        # Returns: str.
        # Purpose: Move the selection window to the requested position.
        def move(delta: int) -> str:
            selection = listbox.curselection()
            current = selection[0] if selection else self.channel_index
            target = max(0, min(len(self.channels) - 1, current + delta))
            listbox.selection_clear(0, "end")
            listbox.selection_set(target)
            listbox.activate(target)
            listbox.see(target)
            return "break"

        # Inputs: _event.
        # Returns: str.
        # Purpose: Apply the value selected in the dialog.
        def choose(_event: object = None) -> str:
            selection = listbox.curselection()
            if selection:
                self.choose_list_channel(selection[0])
            return "break"

        # Inputs: event.
        # Returns: str.
        # Purpose: Apply the item that the user clicked.
        def choose_clicked(event: tk.Event) -> str:
            self.choose_list_channel(listbox.nearest(event.y))
            return "break"

        # Inputs: _event.
        # Returns: str.
        # Purpose: Close the related window or service and release its resources.
        def close(_event: object = None) -> str:
            self.close_channel_list()
            return "break"

        listbox.bind("<Up>", lambda _event: move(-1))
        listbox.bind("<Down>", lambda _event: move(1))
        listbox.bind("<Return>", choose)
        listbox.bind("<KP_Enter>", choose)
        listbox.bind("<Double-Button-1>", choose_clicked)
        listbox.bind("<Escape>", close)
        listbox.bind("<Button-3>", close)
        key = self.config.get("key_channel_list").strip()
        if key:
            sequence = key if key.startswith("<") else f"<{key}>"
            listbox.bind(sequence, close)
            if key.lower() == "control-l":
                listbox.bind("<Control-L>", close)
        self._sync_list_selection()
        listbox.focus_set()

    # Inputs: none.
    # Returns: None.
    # Purpose: Close the channel list.
    def close_channel_list(self) -> None:
        if self.list_frame is None:
            return
        try:
            self.list_frame.destroy()
        except tk.TclError:
            pass
        self.list_frame = None
        self.channel_listbox = None
        self.root.focus_set()

    # Highlight the running channel in the open list.
    # Inputs: none.
    # Returns: None.
    # Purpose: Highlight the channel that is currently playing.
    def _sync_list_selection(self) -> None:
        listbox = self.channel_listbox
        if listbox is None or not (0 <= self.channel_index < len(self.channels)):
            return
        listbox.selection_clear(0, "end")
        listbox.selection_set(self.channel_index)
        listbox.activate(self.channel_index)
        listbox.see(self.channel_index)

    # Inputs: index.
    # Returns: None.
    # Purpose: Tune the channel selected in the channel list.
    def choose_list_channel(self, index: int) -> None:
        if not (0 <= index < len(self.channels)):
            return
        autoclose = self.config.get("list_autoclose").lower() == "true"
        if autoclose:
            self.close_channel_list()
        self.start_channel(index)
        if not autoclose:
            self._sync_list_selection()

    # ----- window title -------------------------------------------------
    # Inputs: none.
    # Returns: int.
    # Purpose: Return how often the window title is refreshed.
    def title_interval(self) -> int:
        try:
            return max(0, min(3600, int(float(self.config.get("title_update_s")))))
        except ValueError:
            return 11

    # Inputs: none.
    # Returns: str | None.
    # Purpose: Build the programme title shown in the main window.
    def current_program_title(self) -> str | None:
        service_id = self.find_service_id()
        if service_id is None:
            return None
        now = datetime.now().astimezone()
        for event in list(self.dvb.events.get(service_id, [])):
            if event["start"] <= now < event["end"]:
                return str(event["title"])
        return None

    # Inputs: none.
    # Returns: None.
    # Purpose: Refresh the main window title with the channel and programme.
    def update_title(self) -> None:
        title = APP_NAME
        if self.running and 0 <= self.channel_index < len(self.channels):
            channel = self.channels[self.channel_index]
            title = f"{APP_NAME} - {self.channel_index + 1}: {channel.name}"
            program = self.current_program_title()
            if program:
                title += f" - {program}"
        if self.root.title() != title:
            self.root.title(title)

    # Inputs: none.
    # Returns: None.
    # Purpose: Refresh the window title and schedule the next update.
    def _title_tick(self) -> None:
        self.title_after_id = None
        self.update_title()
        interval = self.title_interval()
        if interval > 0:
            self.title_after_id = self.root.after(interval * 1000, self._title_tick)

    # Inputs: none.
    # Returns: None.
    # Purpose: Restart the timer that refreshes the window title.
    def restart_title_timer(self) -> None:
        if self.title_after_id is not None:
            try:
                self.root.after_cancel(self.title_after_id)
            except tk.TclError:
                pass
            self.title_after_id = None
        interval = self.title_interval()
        if interval > 0:
            self.title_after_id = self.root.after(interval * 1000, self._title_tick)

    # ----- timeshift figures: "TS=available/distance to live" -------------
    # Inputs: seconds.
    # Returns: str.
    # Purpose: Display seconds as hours, minutes, and seconds.
    @staticmethod
    def format_hms(seconds: float | None) -> str:
        if seconds is None:
            return "--:--:--"
        total = max(0, int(round(seconds)))
        return f"{total // 3600:02d}:{total % 3600 // 60:02d}:{total % 60:02d}"

    # Inputs: none.
    # Returns: int.
    # Purpose: Return how often the timeshift status is refreshed.
    def ts_interval(self) -> int:
        try:
            return max(3, min(600, int(float(self.config.get("ts_update_s")))))
        except ValueError:
            return 13

    # Inputs: none.
    # Returns: float | None.
    # Purpose: Return the time between playback and the live broadcast.
    def timeshift_distance(self) -> float | None:
        if not self.live_direct_active:
            return None
        if self.view_mode == "timeshift":
            wall = self._timeshift_wall_position()
            return None if wall is None else max(0.0, time.time() - wall)
        if self.paused:
            return max(0.0, time.time() - self.pause_wall)
        return 0.0

    # Gigabytes (1024^3) with decimal comma: at least 0,01 and no decimals from 10 on.
    # Inputs: num_bytes.
    # Returns: str.
    # Purpose: Display a byte count as gigabytes.
    @staticmethod
    def format_gb(num_bytes: float) -> str:
        gigabytes = max(0.01, num_bytes / 1024 ** 3)
        if round(gigabytes, 2) >= 10:
            return f"{gigabytes:.0f}"
        return f"{gigabytes:.2f}".replace(".", ",")

    # Inputs: none.
    # Returns: None.
    # Purpose: Refresh the timeshift status shown in the application.
    def update_ts_info(self) -> None:
        timeshift = self.timeshift
        if timeshift is None or not self.running:
            self.ts_var.set("")
            return
        available = sum(entry[2] for entry in timeshift.playlist_entries)
        self.ts_var.set(
            f"TS: {self.format_hms(available)} - {self.format_hms(self.timeshift_distance())}"
            f" - {self.format_gb(timeshift.used_bytes)} GB"
        )

    # Inputs: none.
    # Returns: None.
    # Purpose: Refresh the timeshift status and schedule the next update.
    def _ts_tick(self) -> None:
        self.ts_after_id = None
        self.update_ts_info()
        self.ts_after_id = self.root.after(self.ts_interval() * 1000, self._ts_tick)

    # Inputs: none.
    # Returns: None.
    # Purpose: Restart the timer that refreshes timeshift information.
    def restart_ts_timer(self) -> None:
        if self.ts_after_id is not None:
            try:
                self.root.after_cancel(self.ts_after_id)
            except tk.TclError:
                pass
        self.ts_after_id = self.root.after(self.ts_interval() * 1000, self._ts_tick)

    # ----- aspect ratio -------------------------------------------------
    # Inputs: none.
    # Returns: None.
    # Purpose: Select the next video shape option.
    def cycle_aspect(self) -> None:
        self.aspect_index = (self.aspect_index + 1) % len(ASPECT_MODES)
        label = ASPECT_MODES[self.aspect_index][0]
        self.aspect_var.set(label)
        self.config.set("aspect", str(self.aspect_index))
        self.config.save()
        self.apply_aspect()
        self.status_var.set(f"Seitenverhältnis: {label}")

    # Inputs: none.
    # Returns: None.
    # Purpose: Apply the selected video shape to the player.
    def apply_aspect(self) -> None:
        if self.mpv is not None:
            self.mpv.set_aspect(ASPECT_MODES[self.aspect_index])

    # The player applies file-specific settings only once the file is open.
    # Inputs: none.
    # Returns: None.
    # Purpose: Schedule the video shape change after the player starts.
    def apply_aspect_soon(self) -> None:
        self.apply_aspect()
        self.root.after(400, self.apply_aspect)
        self.root.after(1800, self.apply_aspect)

    # Save the last volume and shut down all streaming components cleanly.
    # Inputs: none.
    # Returns: None.
    # Purpose: Stop playback and close the application cleanly.
    def on_close(self) -> None:
        self.close_now_next()
        self.remember_window_position(
            self.root.geometry() if self.window_mode == 1 else self.normal_geometry)
        self.config.set("last_view_mode", str(self.window_mode))
        if self.mpv:
            self.config.set("volume", str(self.mpv.read_volume()))
        self.config.save()
        self.stop(wait_cleanup=True)
        self.root.destroy()


# Inputs: none.
# Returns: None.
# Purpose: Create the Tk application and enter its event loop.
def main() -> None:
    """Create the Tk application and enter its event loop."""
    # Let the network threads get the GIL back quickly from the Tk thread.
    sys.setswitchinterval(0.001)
    root = tk.Tk()
    app = MvTTV(root)
    root.mainloop()


if __name__ == "__main__":
    main()
