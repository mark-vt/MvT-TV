#!/usr/bin/env python3

import html
import logging
import os
import sys

import requests


# TVHeadend runs locally.
TVH_URL = os.getenv("TVH_URL", "http://127.0.0.1:9981").rstrip("/")

# External SAT>IP server used by the generated M3U stream URLs.
#STREAM_BASE = os.getenv("STREAM_BASE", "http://192.168.0.36").rstrip("/")
STREAM_BASE = os.getenv("STREAM_BASE", "rtsp://192.168.0.36:554").rstrip("/")

SOURCE = os.getenv("SOURCE", "1")

OUTPUT = os.getenv("OUTPUT", "tvheadend-dvbs.m3u")
TIMEOUT = int(os.getenv("TIMEOUT", "15"))

logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)s: %(message)s",
)
log = logging.getLogger("tvh-m3u")

session = requests.Session()
session.headers["User-Agent"] = "tvheadend-m3u-export/1.3"


class ExportError(Exception):
    """Error with a message that can be shown directly to the user."""


# Inputs: path, params.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Send a request to the TVHeadend API and return its JSON object, or explain the error.
def api(path, params=None):
    url = f"{TVH_URL}/api/{path}"

    try:
        response = session.get(url, params=params, timeout=TIMEOUT)
    except requests.exceptions.ConnectionError as exc:
        raise ExportError(
            f"TVHeadend ist unter {TVH_URL} nicht erreichbar. "
            "Prüfe, ob TVHeadend läuft und Port 9981 stimmt."
        ) from exc
    except requests.exceptions.Timeout as exc:
        raise ExportError(
            f"Zeitüberschreitung beim Abruf von {url} "
            f"(Timeout: {TIMEOUT} Sekunden)."
        ) from exc
    except requests.exceptions.RequestException as exc:
        raise ExportError(f"HTTP-Anfrage fehlgeschlagen: {exc}") from exc

    if response.status_code in (401, 403):
        raise ExportError(
            f"TVHeadend verweigert den Zugriff auf {url} "
            f"(HTTP {response.status_code}). Für dieses Skript muss "
            "anonymer API-Zugriff erlaubt sein."
        )

    if not response.ok:
        preview = response.text[:300].replace("\n", " ")
        raise ExportError(
            f"TVHeadend antwortete auf {url} mit HTTP "
            f"{response.status_code}. Antwort: {preview}"
        )

    try:
        data = response.json()
    except ValueError as exc:
        preview = response.text[:300].replace("\n", " ")
        raise ExportError(
            f"TVHeadend lieferte für {url} kein gültiges JSON. "
            f"Antwortanfang: {preview}"
        ) from exc

    if not isinstance(data, dict):
        raise ExportError(
            f"Unerwartetes API-Format von {url}: "
            "Erwartet wurde ein JSON-Objekt."
        )

    return data


# Inputs: path.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Fetch a list of entries from a TVHeadend API endpoint.
def get_entries(path):
    data = api(path, {"limit": 100000})
    entries = data.get("entries")

    if not isinstance(entries, list):
        raise ExportError(
            f"Die API-Antwort von /api/{path} enthält keine "
            "'entries'-Liste. Prüfe TVHeadend-Version und API-Antwort."
        )

    return entries


# Inputs: obj, default, *keys.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Return the first non-empty value found under the supplied object keys.
def first(obj, *keys, default=None):
    for key in keys:
        value = obj.get(key)
        if value is not None and value != "":
            return value
    return default


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Make sure a value is represented as a list.
def as_list(value):
    if isinstance(value, list):
        return value
    if value is None:
        return []
    return [value]


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert a value to a number, using zero when it is missing or invalid.
def as_number(value):
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Normalize a setting name so it can be compared consistently.
def enum(value):
    if value is None:
        return ""
    return str(value).strip().lower().replace(" ", "")


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert a frequency given in Hz, kHz, MHz, or GHz to SAT>IP MHz notation.
def frequency_satip(value):
    """Format a frequency as MHz for a SAT>IP URL, without separators.

    Examples:
      11494000000 Hz -> 11494
      11494000 kHz   -> 11494
      11494 MHz      -> 11494
      11.494 GHz     -> 11494
    """
    frequency = as_number(value)

    if frequency <= 0:
        return ""

    if frequency >= 1_000_000:
        frequency /= 1_000_000
    elif frequency >= 1_000:
        frequency /= 1_000

    # Some API or receiver values may be in GHz, for example 11.494 instead of 11494.
    if frequency < 100:
        frequency *= 1000

    return str(int(round(frequency)))


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert a symbol rate to the kSym/s value expected by SAT>IP.
def symbolrate_satip(value):
    """Format a symbol rate as kSym/s for a SAT>IP URL."""
    symbolrate = as_number(value)

    if symbolrate >= 1_000:
        symbolrate /= 1_000

    if symbolrate <= 0:
        return ""

    return str(int(round(symbolrate)))


# Inputs: value, msys.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert TVHeadend modulation labels to the notation expected by SAT>IP.
def normalize_modulation(value, msys):
    """Convert TVHeadend modulation names to SAT>IP notation."""
    modulation = enum(value)
    modulation = modulation.replace("-psk", "psk")
    modulation = modulation.replace("psk/", "")

    if modulation in ("8", "8psk"):
        return "8psk"

    if modulation in ("qpsk", "4psk", "4"):
        return "qpsk"

    if not modulation:
        return "8psk" if msys == "dvbs2" else "qpsk"

    return modulation


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Remove separators from the forward error correction value.
def normalize_fec(value):
    """Convert values such as '2/3' to SAT>IP notation such as '23'."""
    fec = enum(value)
    return fec.replace("/", "").replace(":", "")


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert rolloff values to the decimal notation expected by SAT>IP.
def normalize_rolloff(value):
    """Convert rolloff values to the decimal notation used by SAT>IP."""
    rolloff = enum(value)

    values = {
        "35": "0.35",
        "0.35": "0.35",
        "25": "0.25",
        "0.25": "0.25",
        "20": "0.20",
        "0.20": "0.20",
    }

    if rolloff in values:
        return values[rolloff]

    if rolloff in ("", "auto"):
        return "0.35"

    return rolloff


# Inputs: value.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Convert the pilot setting to the notation expected by SAT>IP.
def normalize_pilot(value):
    pilot = enum(value)

    if pilot in ("", "auto"):
        return "on"

    return pilot


# Inputs: service_uuid.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Fetch a service packet ID list and exclude subtitle and teletext streams.
def get_stream_pids(service_uuid):
    """Return service packet IDs, excluding DVB subtitle streams (DVBSUB)."""
    try:
        data = api("service/streams", {"uuid": service_uuid})
    except ExportError as exc:
        log.warning(
            "Streams für Service %s konnten nicht abgerufen werden: %s",
            service_uuid,
            exc,
        )
        return [], []

    streams = data.get("streams")
    if not isinstance(streams, list):
        log.warning(
            "Service %s: API-Antwort enthält keine 'streams'-Liste.",
            service_uuid,
        )
        return [], []

    pids = []
    removed_dvbsub = []

    for stream in streams:
        if not isinstance(stream, dict):
            continue

        pid = stream.get("pid")
        stream_type = str(stream.get("type", "")).strip().upper()

        try:
            pid = int(pid)
        except (TypeError, ValueError):
            if pid is not None:
                log.warning(
                    "Service %s: Ungültige PID %r ignoriert.",
                    service_uuid,
                    pid,
                )
            continue

        if stream_type in {"DVBSUB", "TELETEXT", "TEXTSUB"}:
            removed_dvbsub.append((pid, stream_type))
        else:
            pids.append(pid)

    return pids, removed_dvbsub


# Inputs: none.
# Returns: the value produced, or None if this function produces no value.
# Purpose: Fetch TVHeadend channel data, build SAT>IP stream URLs, and write them to an M3U playlist.
def main():
    log.info("TVHeadend-API: %s", TVH_URL)
    log.info("Sat>IP-Stream-Endpunkt: %s", STREAM_BASE)
    log.info("Sat>IP-Quelle (src): %s", SOURCE)

    # Fetch channels, services, and satellite transponders from TVHeadend.
    channels = get_entries("channel/grid")
    services = get_entries("mpegts/service/grid")
    muxes = get_entries("mpegts/mux/grid")

    log.info(
        "Daten erhalten: %d Channels, %d Services, %d Muxes.",
        len(channels),
        len(services),
        len(muxes),
    )

    if not channels:
        raise ExportError(
            "TVHeadend hat keine Channels zurückgegeben. "
            "Prüfe, ob Sender in TVHeadend angelegt sind."
        )

    if not services:
        raise ExportError(
            "TVHeadend hat keine Services zurückgegeben. "
            "Prüfe DVB-Services und den API-Zugriff."
        )

    if not muxes:
        raise ExportError(
            "TVHeadend hat keine Muxes zurückgegeben. "
            "Prüfe DVB-Muxes und den API-Zugriff."
        )

    # Build quick lookup tables to connect each channel to its service and transponder.
    mux_by_uuid = {
        str(mux["uuid"]): mux
        for mux in muxes
        if mux.get("uuid") is not None
    }

    # Group each service under the channel it is linked to.
    services_by_channel = {}

    for service in services:
        if service.get("uuid") is None:
            continue

        for channel_uuid in as_list(service.get("channel")):
            services_by_channel.setdefault(
                str(channel_uuid), []
            ).append(service)

    rows = []
    skipped = 0

    # Build one SAT>IP URL for each enabled channel with complete tuning information.
    for channel in channels:
        channel_uuid = channel.get("uuid")
        name = str(first(channel, "name", "val", default="Unbenannt"))
        channel_number = as_number(first(channel, "number", default=0))

        if channel.get("enabled") is False:
            log.info("Übersprungen: Channel '%s' ist deaktiviert.", name)
            skipped += 1
            continue

        linked_services = services_by_channel.get(str(channel_uuid), [])

        if not linked_services:
            log.warning(
                "Channel '%s' (Nr. %s) hat keinen verknüpften Service "
                "und wird ausgelassen.",
                name,
                channel_number,
            )
            skipped += 1
            continue

        service = linked_services[0]
        service_uuid = str(service["uuid"])

        if len(linked_services) > 1:
            log.warning(
                "Channel '%s' hat %d verknüpfte Services. "
                "Verwendet wird der erste: %s.",
                name,
                len(linked_services),
                service_uuid,
            )

        mux_uuid = first(service, "multiplex_uuid", "mux_uuid")
        mux = mux_by_uuid.get(str(mux_uuid)) if mux_uuid else None

        if not mux:
            log.warning(
                "Channel '%s': Kein passender Mux gefunden "
                "(multiplex_uuid=%r); Sender wird ausgelassen.",
                name,
                mux_uuid,
            )
            skipped += 1
            continue

        frequency = frequency_satip(first(mux, "frequency", "freq"))
        polarization = enum(
            first(mux, "polarisation", "polarization", "pol")
        )
        symbolrate = symbolrate_satip(
            first(mux, "symbolrate", "symbol_rate", "sr")
        )

        if not frequency:
            log.warning(
                "Channel '%s': Mux %s enthält keine brauchbare Frequenz.",
                name,
                mux_uuid,
            )
            skipped += 1
            continue

        if not symbolrate:
            log.warning(
                "Channel '%s': Mux %s enthält keine brauchbare Symbolrate.",
                name,
                mux_uuid,
            )
            skipped += 1
            continue

        if not polarization:
            log.warning(
                "Channel '%s': Mux %s enthält keine Polarisation.",
                name,
                mux_uuid,
            )
            skipped += 1
            continue

        polarization = {
            "horizontal": "h",
            "vertical": "v",
            "left": "l",
            "right": "r",
        }.get(polarization, polarization[:1])

        delivery = enum(first(mux, "delsys", "delivery_system"))

        if "s2" in delivery:
            msys = "dvbs2"
        elif "s" in delivery:
            msys = "dvbs"
        else:
            log.warning(
                "Channel '%s': DVB-System %r ist nicht eindeutig. "
                "Es wird dvbs2 ausgegeben; bitte Ergebnis prüfen.",
                name,
                delivery,
            )
            msys = "dvbs2"

        modulation = normalize_modulation(
            first(mux, "modulation", "mtype"),
            msys,
        )
        rolloff = normalize_rolloff(first(mux, "rolloff", "ro"))
        pilot = normalize_pilot(first(mux, "pilot", "plts"))
        fec = normalize_fec(first(mux, "fec", "fec_inner"))

        # Request the standard guide tables, the PMT, and discovered audio/video IDs.
        pids = {0, 17, 18}

        pmt_pid = first(service, "pmt")
        if pmt_pid is not None:
            try:
                pids.add(int(pmt_pid))
            except (TypeError, ValueError):
                log.warning(
                    "Channel '%s': Ungültige PMT-PID %r.",
                    name,
                    pmt_pid,
                )

        stream_pids, removed_dvbsub = get_stream_pids(service_uuid)
        pids.update(stream_pids)

        if removed_dvbsub:
            details = ", ".join(
                f"{pid} ({stream_type})"
                for pid, stream_type in removed_dvbsub
            )
            log.info(
                "Channel '%s': Untertitel-/Teletext-PIDs entfernt: %s",
                name,
                details,
            )
        else:
            log.info(
                "Channel '%s': Keine DVBSUB- oder TELETEXT-PIDs gefunden.",
                name,
            )

        if not stream_pids:
            log.warning(
                "Channel '%s': Keine Stream-PIDs gefunden. "
                "Ausgegeben werden nur Grund-PIDs und ggf. die PMT-PID.",
                name,
            )

        params = [
            ("src", SOURCE),
            ("freq", frequency),
            ("pol", polarization),
            ("ro", rolloff),
            ("msys", msys),
            ("mtype", modulation),
            ("plts", pilot),
            ("sr", symbolrate),
        ]

        if fec:
            params.append(("fec", fec))

        params.append(("pids", ",".join(map(str, sorted(pids)))))

        # Keep commas in the packet ID list unescaped, as in the working VLC example.
        query = "&".join(f"{key}={value}" for key, value in params)
        stream_url = f"{STREAM_BASE}/?{query}"

        rows.append((channel_number, name, stream_url))

        log.info(
            "OK: Channel %s — %s; freq=%s, pol=%s, msys=%s, "
            "mtype=%s, ro=%s, sr=%s, fec=%s, %d PIDs.",
            channel_number,
            name,
            frequency,
            polarization,
            msys,
            modulation,
            rolloff,
            symbolrate,
            fec or "(nicht gesetzt)",
            len(pids),
        )

    if not rows:
        raise ExportError(
            "Es konnte kein M3U-Eintrag erzeugt werden. "
            "Die Warnungen oben zeigen, welche Daten fehlen."
        )

    # Keep the exported playlist in channel-number order, then alphabetically by name.
    rows.sort(key=lambda row: (row[0], row[1].casefold()))

    # Write the channel names and stream addresses in standard M3U format.
    try:
        with open(OUTPUT, "w", encoding="utf-8", newline="\n") as out:
            out.write("#EXTM3U\n")

            for channel_number, name, stream_url in rows:
                safe_name = html.escape(name, quote=True)
                channel_number_text = f"{channel_number:g}"
                out.write(
                    f'#EXTINF:-1 tvg-chno="{channel_number_text}" '
                    f'channel-number="{channel_number_text}" '
                    f'tvg-name="{safe_name}",{name}\n'
                )
                out.write(f"#EXTVLCOPT:http-title={name}\n")
                out.write(f"{stream_url}\n\n")

    except OSError as exc:
        raise ExportError(
            f"Die Datei '{OUTPUT}' konnte nicht geschrieben werden: {exc}"
        ) from exc

    log.info(
        "Fertig: %d Einträge nach '%s' geschrieben; "
        "%d Channels ausgelassen.",
        len(rows),
        OUTPUT,
        skipped,
    )


if __name__ == "__main__":
    try:
        main()
    except ExportError as exc:
        log.error("%s", exc)
        sys.exit(1)
    except KeyboardInterrupt:
        log.error("Abgebrochen.")
        sys.exit(130)
    except Exception:
        log.exception(
            "Unerwarteter Fehler. Der vollständige Traceback steht oben."
        )
        sys.exit(1)
