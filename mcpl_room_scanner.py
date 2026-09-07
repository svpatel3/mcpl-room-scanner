#!/usr/bin/env python3
"""
MCPL study room scanner
========================

Scans the Montgomery County Public Libraries room-reservation system
(https://mcpl.libnet.info/reserve) for 10:00am-12:00pm openings at four
branches, over the next several days, and emails a summary with links.

HOW THE SITE WORKS (reverse-engineered, since there's no public API docs)
---------------------------------------------------------------------
The reservation page is a JS app built on the "Communico" (libnet.info)
platform. It calls this JSON endpoint under the hood:

    https://api.communico.co/v2/mcpl/roomsbyclass/<location_ids>?date=<YYYY-MM-DD>&class_id[]=580&external_only=1

- <location_ids> is a comma-separated list of branch IDs (see LOCATIONS below).
- class_id=580 is the "public/unmediated" booking class used site-wide for
  the online room-reservation flow (confirmed by inspecting the page's own
  requests).
- The response lists every room at those branches, each with:
    - "roomHours": {"<date>": {"open": "10:00AM", "close": "6:00PM"}}
      (closed days come back as open == close, e.g. Sundays)
    - "bookings": existing reservations as {"start_time", "end_time", ...}
      in "YYYY-MM-DD HH:MM:SS" (America/New_York, no explicit offset)
    - "restrictions": booking rules, including "furthest_booking_days" (the
      site currently only allows booking up to 7 days out)

A room is treated as OPEN for a target window (10:00-12:00 by default) if:
  1. The room is enabled, AND
  2. Its hours that day cover the whole window, AND
  3. No existing booking overlaps the window at all (any overlapping
     booking is treated as blocking, regardless of its "status" field,
     since that field's exact meaning wasn't confirmed - better to
     under-report openings than send you to a room that's actually taken).

NETWORK NOTE
------------
This script needs normal outbound internet access (to api.communico.co and
to your SMTP server). It will NOT work unmodified inside a locked-down
sandbox that only allows a small domain allowlist - run it from your own
computer, a small VPS, a Raspberry Pi, a GitHub Actions runner, etc.

RESERVATION LINKS
------------------
The site is a single-page app and doesn't support deep-linking straight to
a specific room/time slot - but ?date=YYYY-MM-DD on the reserve URL DOES
pre-select that date. The email links to that; you'll still need to check
the branch's box (one click) and pick the room/time shown in the email.

SETUP
-----
1. pip install requests
2. Copy mcpl_scanner.env.example to mcpl_scanner.env (same folder as this
   script) and fill in your SMTP details. Or just set the same names as
   real environment variables - either works.
3. Test it once by hand:  python3 mcpl_room_scanner.py --verbose
4. Schedule it (see the crontab line at the bottom of this file).

Nothing here is Montgomery County- or Communico-specific in a way that
can't be adapted; the location-id map below covers all 16 MCPL branches
in case you want to add more later.
"""

from __future__ import annotations

import argparse
import json
import os
import smtplib
import sys
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone as _utc, date as date_cls
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from zoneinfo import ZoneInfo

import requests

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

TIMEZONE = ZoneInfo("America/New_York")

# All 16 MCPL branches and their Communico location IDs, for reference.
# Only the ones listed in WATCHED_LOCATIONS (below) are actually scanned.
ALL_LOCATIONS = {
    "Aspen Hill Library": "1747",
    "Brigadier General Charles E. McGee Library": "1776",
    "Connie Morella Library": "1761",
    "Davis Library": "1763",
    "Gaithersburg Library": "1764",
    "Germantown Library": "1765",
    "Kensington Park Library": "1766",
    "Long Branch Library": "1768",
    "Marilyn J. Praisner Library": "1770",
    "Olney Library": "1772",
    "Potomac Library": "1773",
    "Quince Orchard Library": "1774",
    "Rockville Memorial Library": "1775",
    "Twinbrook Library": "1777",
    "Wheaton Library": "1778",
    "White Oak Library": "1779",
}

# The branches you asked to watch.
WATCHED_LOCATIONS = {
    name: ALL_LOCATIONS[name]
    for name in ("Aspen Hill Library", "Kensington Park Library", "Twinbrook Library",
                 "Wheaton Library", "Davis Library")
}

CLASS_ID = "580"  # public/unmediated booking class used by the site
API_URL = "https://api.communico.co/v2/mcpl/roomsbyclass/{ids}"
RESERVE_PAGE = "https://mcpl.libnet.info/reserve"

TARGET_START = "10:00"  # 24h "HH:MM", America/New_York (default; override with --start/--end)
TARGET_END = "12:00"


def window_label(start_hm: str, end_hm: str) -> str:
    """'10:00','12:00' -> '10am-12pm'  (drops ':00', lowercases am/pm)."""
    def fmt(hm: str) -> str:
        t = datetime.strptime(hm, "%H:%M")
        return t.strftime("%I:%M%p").lstrip("0").replace(":00", "").lower()
    return f"{fmt(start_hm)}-{fmt(end_hm)}"

DAYS_AHEAD_DEFAULT = 7  # the site's own furthest_booking_days at last check
REQUEST_TIMEOUT = 15
REQUEST_HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; mcpl-room-scanner/1.0)",
    "Accept": "application/json",
    "Referer": RESERVE_PAGE,
}


@dataclass
class OpenSlot:
    date: str            # "YYYY-MM-DD"
    branch: str
    room_name: str
    room_id: str
    capacity: str


@dataclass
class ScanResult:
    open_slots: list[OpenSlot] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)


@dataclass
class BookingResult:
    ok: bool = False
    dry_run: bool = False
    reference: str = ""
    booking_id: str = ""
    message: str = ""
    slot: OpenSlot | None = None
    start_time: str = ""      # "YYYY-MM-DD HH:MM:SS"
    end_time: str = ""
    payload: dict | None = None
    ics_path: str = ""


# --------------------------------------------------------------------------
# Scanning
# --------------------------------------------------------------------------

def fetch_rooms_for_date(day: date_cls, verbose: bool = False) -> list[dict]:
    """Call the Communico API for one date across all watched branches."""
    ids = ",".join(WATCHED_LOCATIONS.values())
    url = API_URL.format(ids=ids)
    params = {
        "date": day.isoformat(),
        "class_id[]": CLASS_ID,
        "external_only": "1",
    }
    resp = requests.get(url, params=params, headers=REQUEST_HEADERS, timeout=REQUEST_TIMEOUT)
    resp.raise_for_status()
    data = resp.json()
    rooms = data.get(CLASS_ID, [])
    if verbose:
        print(f"  {day}: {len(rooms)} rooms returned", file=sys.stderr)
    return rooms


def room_is_open_for_window(room: dict, day: date_cls, start_hm: str, end_hm: str) -> bool:
    if str(room.get("enabled", "0")) != "1":
        return False

    hours = (room.get("roomHours") or {}).get(day.isoformat())
    if not hours:
        return False

    try:
        open_t = datetime.strptime(hours["open"], "%I:%M%p").time()
        close_t = datetime.strptime(hours["close"], "%I:%M%p").time()
    except (KeyError, ValueError):
        return False

    start_t = datetime.strptime(start_hm, "%H:%M").time()
    end_t = datetime.strptime(end_hm, "%H:%M").time()

    # Closed days come back as open == close (e.g. midnight-midnight).
    if open_t > start_t or close_t < end_t:
        return False

    slot_start = datetime.combine(day, start_t)
    slot_end = datetime.combine(day, end_t)

    for booking in room.get("bookings") or []:
        try:
            b_start = datetime.strptime(booking["start_time"], "%Y-%m-%d %H:%M:%S")
            b_end = datetime.strptime(booking["end_time"], "%Y-%m-%d %H:%M:%S")
        except (KeyError, ValueError):
            continue
        # Any overlapping booking blocks the window, whatever its status -
        # better to under-report than send you to a room that's taken.
        if b_start < slot_end and b_end > slot_start:
            return False

    return True


def branch_name_for_location_id(location_id: str) -> str:
    for name, lid in WATCHED_LOCATIONS.items():
        if lid == location_id:
            return name
    return f"Location {location_id}"


def scan(days_ahead: int = DAYS_AHEAD_DEFAULT, verbose: bool = False,
         only_date: date_cls | None = None,
         start_hm: str = TARGET_START, end_hm: str = TARGET_END) -> ScanResult:
    result = ScanResult()
    today = datetime.now(TIMEZONE).date()

    if only_date is not None:
        days = [only_date]
    else:
        days = [today + timedelta(days=offset) for offset in range(days_ahead + 1)]

    for day in days:
        if day.weekday() == 6:  # Sunday - MCPL branches are closed
            if only_date is not None:
                result.errors.append(f"{day}: Sunday - MCPL branches are closed.")
            continue
        try:
            rooms = fetch_rooms_for_date(day, verbose=verbose)
        except requests.RequestException as exc:
            result.errors.append(f"{day}: request failed ({exc})")
            continue

        for room in rooms:
            if room_is_open_for_window(room, day, start_hm, end_hm):
                result.open_slots.append(
                    OpenSlot(
                        date=day.isoformat(),
                        branch=branch_name_for_location_id(str(room.get("location_id"))),
                        room_name=room.get("name", "Unknown room"),
                        room_id=str(room.get("id", "")),
                        capacity=str(room.get("capacity_standing", "?")),
                    )
                )
    return result


# --------------------------------------------------------------------------
# Email
# --------------------------------------------------------------------------

def load_env_file(path: Path) -> None:
    """Minimal .env loader (KEY=VALUE per line) - no extra dependency."""
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        key, value = key.strip(), value.strip().strip('"').strip("'")
        os.environ.setdefault(key, value)


def build_email_body(result: ScanResult, scope: str, window: str = "10am-12pm") -> tuple[str, str]:
    """Returns (plain_text, html) email bodies. `scope` describes the date
    range scanned, e.g. "next 7 days" or "on 2026-09-08"; `window` is the
    time-of-day label, e.g. "10am-12pm"."""
    if not result.open_slots:
        text = f"No {window} openings found {scope} at your watched branches."
        html = f"<p>{text}</p>"
        return text, html

    by_date: dict[str, list[OpenSlot]] = {}
    for slot in result.open_slots:
        by_date.setdefault(slot.date, []).append(slot)

    text_lines = [f"{window} study room openings - {scope}", ""]
    html_lines = [f"<h2>{window} study room openings</h2>"]

    for day in sorted(by_date):
        pretty_day = datetime.strptime(day, "%Y-%m-%d").strftime("%A, %B %d")
        day_link = f"{RESERVE_PAGE}?date={day}"
        text_lines.append(f"{pretty_day} ({day})")
        html_lines.append(f"<h3>{pretty_day} <small>({day})</small></h3><ul>")
        for slot in sorted(by_date[day], key=lambda s: (s.branch, s.room_name)):
            # ?roomId= makes the reserve page pre-select this exact room and its
            # branch; falls back to the date-only link if we somehow lack an id.
            room_link = f"{day_link}&roomId={slot.room_id}" if slot.room_id else day_link
            text_lines.append(
                f"  - {slot.branch}: {slot.room_name} (fits {slot.capacity})  ->  {room_link}"
            )
            html_lines.append(
                f"<li><a href=\"{room_link.replace('&', '&amp;')}\">{slot.branch}: "
                f"<b>{slot.room_name}</b> (fits {slot.capacity})</a></li>"
            )
        html_lines.append(
            f"</ul><p><a href=\"{day_link}\">Open the full day for {pretty_day}</a></p>"
        )
        text_lines.append("")

    if result.errors:
        text_lines.append("Some dates could not be checked:")
        text_lines.extend(f"  - {e}" for e in result.errors)

    return "\n".join(text_lines), "\n".join(html_lines)


# --------------------------------------------------------------------------
# Booking (submits a real reservation to Communico - only runs with --book)
# --------------------------------------------------------------------------

BOOKING_FIELDS = ("BOOK_FIRST_NAME", "BOOK_LAST_NAME", "BOOK_EMAIL", "BOOK_LIBRARY_CARD")
MYRESERVATIONS_URL = "https://mcpl.libnet.info/myreservations"


def pick_slot(slots: list[OpenSlot], branch_order: list[str]) -> OpenSlot | None:
    """Choose one slot: first branch (in branch_order, substring match, case-
    insensitive) that has an open room; within a branch, first room by name.
    Falls back to any room sorted by (branch, room_name)."""
    if not slots:
        return None
    for term in branch_order:
        term = term.strip().lower()
        if not term:
            continue
        matches = sorted((s for s in slots if term in s.branch.lower()),
                         key=lambda s: s.room_name)
        if matches:
            return matches[0]
    return sorted(slots, key=lambda s: (s.branch, s.room_name))[0]


def book_room(slot: OpenSlot, day: date_cls, start_hm: str, end_hm: str,
              dry_run: bool = False, verbose: bool = False) -> BookingResult:
    """Submit a room reservation to Communico for `slot` on `day` covering
    start_hm-end_hm. Reads patron details from BOOK_* environment vars."""
    missing = [k for k in BOOKING_FIELDS if not os.environ.get(k)]
    if missing:
        return BookingResult(ok=False,
                             message=f"missing booking details in env: {', '.join(missing)}")

    start_time = f"{day.isoformat()} {start_hm}:00"
    end_time = f"{day.isoformat()} {end_hm}:00"
    payload = {
        "room_id": slot.room_id,
        "layout_id": "",
        "start_time": start_time,
        "end_time": end_time,
        "expected_attendees": os.environ.get("BOOK_ATTENDEES", "1"),
        "patron_notes": os.environ.get("BOOK_NOTES", ""),
        "customQuestions": "{}",
        "class_id": CLASS_ID,
        "contact[first_name]": os.environ["BOOK_FIRST_NAME"],
        "contact[last_name]": os.environ["BOOK_LAST_NAME"],
        "contact[phone]": os.environ.get("BOOK_PHONE", ""),
        "contact[email]": os.environ["BOOK_EMAIL"],
        "contact[librarycard]": os.environ["BOOK_LIBRARY_CARD"],
        "contact[group_name]": (os.environ.get("BOOK_GROUP_NAME")
                                or f"{os.environ['BOOK_FIRST_NAME']} {os.environ['BOOK_LAST_NAME']}"),
        "contact[booking_title]": os.environ.get("BOOK_TITLE", "Study session"),
    }

    result = BookingResult(dry_run=dry_run, slot=slot,
                           start_time=start_time, end_time=end_time,
                           payload=payload)

    room_link = f"{RESERVE_PAGE}?date={day.isoformat()}&roomId={slot.room_id}"
    sess = requests.Session()
    sess.headers.update({
        "User-Agent": REQUEST_HEADERS["User-Agent"],
        "Referer": room_link,
        "Origin": RESERVE_PAGE.rsplit("/", 1)[0],
        "X-Requested-With": "XMLHttpRequest",
    })

    try:
        # 1. land on the reserve page to pick up session / LB cookies
        sess.get(RESERVE_PAGE, params={"date": day.isoformat(), "roomId": slot.room_id},
                 timeout=REQUEST_TIMEOUT).raise_for_status()

        # 2. pre-flight check (validates card, catches "already booked" etc.)
        try:
            chk = sess.get(f"{RESERVE_PAGE.rsplit('/', 1)[0]}/ajax/fetch/check_room_booking",
                           params={"room_id": slot.room_id, "start_time": start_time,
                                   "end_time": end_time,
                                   "librarycard": os.environ["BOOK_LIBRARY_CARD"],
                                   "email": os.environ["BOOK_EMAIL"], "class_id": CLASS_ID},
                           timeout=REQUEST_TIMEOUT)
            cj = chk.json() if chk.ok else {}
            if verbose:
                print(f"  check_room_booking -> {cj}", file=sys.stderr)
            if cj and cj.get("ok") is False and cj.get("message"):
                result.message = f"pre-check failed: {cj['message']}"
                return result
        except (requests.RequestException, ValueError):
            pass  # pre-check is best-effort; the submit below is authoritative

        if dry_run:
            result.ok = True
            result.message = "dry run - reservation NOT submitted"
            return result

        # 3. submit
        resp = sess.post(RESERVE_PAGE, params={"action": "submit"}, data=payload,
                         timeout=REQUEST_TIMEOUT)
        resp.raise_for_status()
        try:
            data = resp.json()
        except ValueError:
            result.message = f"non-JSON response from submit (HTTP {resp.status_code})"
            return result

        if verbose:
            print(f"  submit -> {data}", file=sys.stderr)
        if data.get("ok"):
            result.ok = True
            result.reference = str(data.get("reference", ""))
            result.booking_id = str(data.get("id", ""))
            result.message = str(data.get("message", "booking confirmed"))
        else:
            result.message = str(data.get("message") or "booking rejected (no message)")
    except requests.RequestException as exc:
        result.message = f"request failed: {exc}"
    return result


def _ics_escape(text: str) -> str:
    return (text.replace("\\", "\\\\").replace("\n", "\\n")
                .replace(",", "\\,").replace(";", "\\;"))


def write_ics(res: BookingResult, day: date_cls, start_hm: str, end_hm: str) -> str:
    """Write a calendar file for a confirmed booking; return its path."""
    def to_utc(hm: str) -> str:
        h, m = (int(x) for x in hm.split(":"))
        local = datetime(day.year, day.month, day.day, h, m, tzinfo=TIMEZONE)
        return local.astimezone(_utc.utc).strftime("%Y%m%dT%H%M%SZ")

    slot = res.slot
    uid = f"mcpl-{res.booking_id or res.reference or day.isoformat()}@mcpl.libnet.info"
    desc = (f"Montgomery County Public Libraries room reservation.\n\n"
            f"Room: {slot.room_name} ({slot.branch})\n"
            f"Time: {window_label(start_hm, end_hm)} ET\n"
            f"Confirmation ref: {res.reference}\nBooking id: {res.booking_id}\n\n"
            f"Manage or cancel: {MYRESERVATIONS_URL}")
    lines = [
        "BEGIN:VCALENDAR", "VERSION:2.0",
        "PRODID:-//mcpl-room-scanner//booking//EN",
        "CALSCALE:GREGORIAN", "METHOD:PUBLISH", "BEGIN:VEVENT",
        f"UID:{uid}",
        f"DTSTAMP:{datetime.now(_utc.utc).strftime('%Y%m%dT%H%M%SZ')}",
        f"DTSTART:{to_utc(start_hm)}", f"DTEND:{to_utc(end_hm)}",
        f"SUMMARY:{_ics_escape(f'Study room - {slot.room_name} (MCPL)')}",
        f"LOCATION:{_ics_escape(slot.branch)}",
        f"DESCRIPTION:{_ics_escape(desc)}",
        f"URL:{MYRESERVATIONS_URL}", "STATUS:CONFIRMED",
        "BEGIN:VALARM", "ACTION:DISPLAY",
        f"DESCRIPTION:{_ics_escape(f'Study room - {slot.room_name} in 30 minutes')}",
        "TRIGGER:-PT30M", "END:VALARM", "END:VEVENT", "END:VCALENDAR",
    ]
    branch_slug = "".join(c.lower() if c.isalnum() else "-" for c in slot.branch).strip("-")
    out_dir = Path(os.environ.get("BOOK_ICS_DIR") or Path(__file__).parent)
    path = out_dir / f"mcpl-{branch_slug}-{day.isoformat()}.ics"
    path.write_text("\r\n".join(lines) + "\r\n")
    return str(path)


def build_booking_body(res: BookingResult, day: date_cls, window: str) -> tuple[str, str, str]:
    """Returns (subject, text_body, html_body) for a booking outcome."""
    pretty = day.strftime("%A, %B %d")
    if res.slot is None:
        subj = f"MCPL booking: nothing open {window} on {pretty}"
        body = f"No {window} openings on {pretty} - nothing was booked."
        return subj, body, f"<p>{body}</p>"

    where = f"{res.slot.room_name} @ {res.slot.branch}"
    when = f"{pretty}, {window}"
    if res.dry_run and not res.message.startswith("pre-check failed"):
        subj = f"MCPL booking DRY RUN: would book {where}"
        lines = [f"DRY RUN - nothing was submitted.", "",
                 f"Would book: {where}", f"When: {when}", "",
                 "POST /reserve?action=submit payload:"]
        for k, v in (res.payload or {}).items():
            lines.append(f"  {k} = {v}")
        text = "\n".join(lines)
        return subj, text, "<pre>" + text.replace("<", "&lt;") + "</pre>"
    if res.ok:
        subj = f"MCPL room BOOKED: {where} - {when}"
        lines = [f"Booked: {where}", f"When: {when}"]
        if res.reference:
            lines.append(f"Confirmation ref: {res.reference}")
        if res.message and res.message != "booking confirmed":
            lines.append(f"Note: {res.message}")
        lines += ["", f"Manage / cancel: {MYRESERVATIONS_URL}"]
        text = "\n".join(lines)
        html = ("<h2>Room booked</h2><p><b>" + where + "</b><br>" + when +
                (f"<br>Confirmation ref: {res.reference}" if res.reference else "") +
                f'</p><p><a href="{MYRESERVATIONS_URL}">Manage / cancel this booking</a></p>')
        return subj, text, html
    subj = f"MCPL booking FAILED: {where} - {when}"
    text = (f"Tried to book {where} for {when} but it did NOT go through.\n\n"
            f"Reason: {res.message}\n\n"
            f"Book manually: {RESERVE_PAGE}?date={day.isoformat()}&roomId={res.slot.room_id}")
    html = (f"<h2>Booking failed</h2><p>Tried: <b>{where}</b><br>{when}</p>"
            f"<p>Reason: {res.message}</p>"
            f'<p><a href="{RESERVE_PAGE}?date={day.isoformat()}&amp;roomId={res.slot.room_id}">'
            f"Book it manually</a></p>")
    return subj, text, html


def send_email(subject: str, text_body: str, html_body: str) -> None:
    host = os.environ.get("SMTP_HOST")
    port = int(os.environ.get("SMTP_PORT", "587"))
    user = os.environ.get("SMTP_USER")
    password = os.environ.get("SMTP_PASSWORD")
    mail_from = os.environ.get("MAIL_FROM", user)
    mail_to = os.environ.get("MAIL_TO", "apps@dcba.me")

    if not host or not user or not password:
        print("SMTP not configured (set SMTP_HOST / SMTP_USER / SMTP_PASSWORD) - "
              "printing results instead of emailing:\n", file=sys.stderr)
        print(text_body)
        return

    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = mail_from
    msg["To"] = mail_to
    msg.attach(MIMEText(text_body, "plain"))
    msg.attach(MIMEText(html_body, "html"))

    with smtplib.SMTP(host, port, timeout=REQUEST_TIMEOUT) as server:
        server.starttls()
        server.login(user, password)
        server.sendmail(mail_from, [mail_to], msg.as_string())


# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--days", type=int, default=DAYS_AHEAD_DEFAULT, help="how many days ahead to scan")
    parser.add_argument("--date", help="scan ONLY this date (YYYY-MM-DD), ignoring --days")
    parser.add_argument("--next-business-day", dest="next_business_day", action="store_true",
                        help="scan ONLY the next day MCPL is open (tomorrow, or Monday if "
                             "tomorrow is Sunday); ignores --days and --date")
    parser.add_argument("--start", default=TARGET_START, metavar="HH:MM",
                        help=f"window start time, 24h (default {TARGET_START})")
    parser.add_argument("--end", default=TARGET_END, metavar="HH:MM",
                        help=f"window end time, 24h (default {TARGET_END})")
    parser.add_argument("--book", action="store_true",
                        help="SUBMIT a real reservation for the first open room (needs "
                             "BOOK_* vars in mcpl_scanner.env and a single target day via "
                             "--date or --next-business-day)")
    parser.add_argument("--dry-run", dest="dry_run", action="store_true",
                        help="with --book: do everything except the final submit; print the payload")
    parser.add_argument("--branches", default=None,
                        help="comma-separated branch preference order for --book "
                             "(substring match), e.g. 'Twinbrook,Aspen Hill,Davis'. "
                             "Defaults to BOOK_BRANCH_ORDER from the env file.")
    parser.add_argument("--room", default=None,
                        help="with --book: only consider rooms whose name contains this "
                             "text (case-insensitive), e.g. 'Wheaton 6'")
    parser.add_argument("--always-email", action="store_true", help="email even when nothing is open")
    parser.add_argument("--print", dest="print_only", action="store_true",
                        help="print the openings to the terminal and never send mail "
                             "(ignores SMTP config entirely)")
    parser.add_argument("--emit-json", action="store_true",
                        help="print the result as one JSON object on stdout and do NOT "
                             "send mail (for a caller - e.g. a Claude routine using the "
                             "Gmail connector - to deliver instead of SMTP)")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    only_date = None
    if args.next_business_day:
        if args.date:
            parser.error("use either --next-business-day or --date, not both")
        only_date = datetime.now(TIMEZONE).date() + timedelta(days=1)
        while only_date.weekday() == 6:  # Sunday - branches closed
            only_date += timedelta(days=1)
    elif args.date:
        try:
            only_date = datetime.strptime(args.date, "%Y-%m-%d").date()
        except ValueError:
            parser.error(f"--date must be YYYY-MM-DD, got {args.date!r}")

    times = {}
    for label, val in (("--start", args.start), ("--end", args.end)):
        try:
            times[label] = datetime.strptime(val, "%H:%M").time()
        except ValueError:
            parser.error(f"{label} must be HH:MM (24h), got {val!r}")
    if times["--start"] >= times["--end"]:
        parser.error(f"--start ({args.start}) must be before --end ({args.end})")
    # normalise to zero-padded HH:MM so "9:00" and "09:00" behave identically
    args.start = times["--start"].strftime("%H:%M")
    args.end = times["--end"].strftime("%H:%M")
    window = window_label(args.start, args.end)

    load_env_file(Path(__file__).with_name("mcpl_scanner.env"))

    if only_date is None and datetime.now(TIMEZONE).date().weekday() == 6:
        print("Today is Sunday - MCPL branches are closed today, but scanning "
              "the upcoming (non-Sunday) days anyway.", file=sys.stderr)

    if args.book and only_date is None:
        parser.error("--book needs a single target day: pass --date or --next-business-day")
    if args.dry_run and not args.book:
        parser.error("--dry-run only applies together with --book")

    result = scan(days_ahead=args.days, verbose=args.verbose, only_date=only_date,
                  start_hm=args.start, end_hm=args.end)

    # ---- booking path -------------------------------------------------------
    if args.book:
        branch_order = (args.branches
                        if args.branches is not None
                        else os.environ.get("BOOK_BRANCH_ORDER", "")).split(",")
        candidates = result.open_slots
        if args.room:
            candidates = [s for s in candidates if args.room.lower() in s.room_name.lower()]
        chosen = pick_slot(candidates, branch_order)
        if chosen is None:
            bres = BookingResult(message="no open room in the window")
        else:
            bres = book_room(chosen, only_date, args.start, args.end,
                             dry_run=args.dry_run, verbose=args.verbose)

        if bres.ok and not bres.dry_run:
            try:
                bres.ics_path = write_ics(bres, only_date, args.start, args.end)
            except OSError as exc:
                print(f"warning: could not write .ics ({exc})", file=sys.stderr)

        subject, text_body, html_body = build_booking_body(bres, only_date, window)
        if bres.ics_path:
            text_body += f"\n\nCalendar file: {bres.ics_path}"

        if args.print_only:
            print(subject + "\n\n" + text_body)
        elif args.emit_json:
            json.dump({
                "mode": "book",
                "should_notify": True,
                "subject": subject,
                "text_body": text_body,
                "html_body": html_body,
                "ics_path": bres.ics_path,
                "booking": {
                    "ok": bres.ok, "dry_run": bres.dry_run,
                    "reference": bres.reference, "booking_id": bres.booking_id,
                    "message": bres.message,
                    "branch": chosen.branch if chosen else None,
                    "room_name": chosen.room_name if chosen else None,
                    "room_id": chosen.room_id if chosen else None,
                    "date": only_date.isoformat(),
                    "start": args.start, "end": args.end,
                },
                "candidates": [vars(s) for s in result.open_slots],
                "errors": result.errors,
            }, sys.stdout, indent=2)
            sys.stdout.write("\n")
        else:
            send_email(subject, text_body, html_body)
            print(subject)
            if bres.ics_path:
                print(f"Calendar file: {bres.ics_path}")
        return
    # ----------------------------------------------------------------------

    if only_date:
        pretty = only_date.strftime("%A, %b %d")
        scope_human = f"on {pretty} ({only_date})"
        scope_short = f"for {pretty}"
    else:
        scope_human = f"in the next {args.days} days"
        scope_short = f"next {args.days} days"
    text_body, html_body = build_email_body(result, scope_short, window)
    subject = (
        f"MCPL rooms: {len(result.open_slots)} {window} opening(s) found"
        if result.open_slots
        else f"MCPL rooms: no {window} openings right now"
    )
    should_notify = bool(result.open_slots) or args.always_email

    if args.print_only:
        print(f"{subject}\n")
        print(text_body if result.open_slots else f"Nothing open {scope_human}.")
        if result.errors:
            print("\nSome dates could not be checked:")
            print(*result.errors, sep="\n  ")
        return

    if args.emit_json:
        json.dump({
            "scope": scope_short,
            "open_slot_count": len(result.open_slots),
            "should_notify": should_notify,
            "subject": subject,
            "text_body": text_body,
            "html_body": html_body,
            "open_slots": [vars(s) for s in result.open_slots],
            "errors": result.errors,
        }, sys.stdout, indent=2)
        sys.stdout.write("\n")
        return

    if not should_notify:
        print(f"No openings found {scope_human}. (Use --always-email to get a mail anyway.)")
        if result.errors:
            print("Errors:", *result.errors, sep="\n  ")
        return

    send_email(subject, text_body, html_body)
    print(f"Done. {len(result.open_slots)} opening(s) found; email "
          f"{'sent' if should_notify else 'skipped'}.")


if __name__ == "__main__":
    main()

# --------------------------------------------------------------------------
# Scheduling
# --------------------------------------------------------------------------
#
# Option A - standalone cron + SMTP (needs mcpl_scanner.env filled in):
#
#   crontab -e   (on a machine whose system time is America/New_York)
#     0 10 * * 1-6 /usr/bin/python3 /path/to/mcpl_room_scanner.py >> /path/to/mcpl_scanner.log 2>&1
#
#   If your server's system clock is UTC instead, convert 10:00am ET yourself
#   and remember it shifts by an hour between EDT (roughly Mar-Nov) and EST -
#   or just install a timezone-aware scheduler. The script also double-checks
#   and no-ops on Sundays on its own, so an "every day" cron line is harmless.
#
# Option B - Claude routine + Gmail connector (no SMTP, no app password):
#
#   The Gmail connector is an MCP tool available inside a Claude session, not
#   something this script can call directly. So the split is:
#     1. Claude runs:  python3 mcpl_room_scanner.py --date <tomorrow> --emit-json
#     2. Claude parses the JSON. If "should_notify" is true, it sends
#        "subject" + "html_body" to MAIL_TO via the Gmail connector's
#        send_message tool.
#   Wrap that in a scheduled routine (see the `schedule` skill) to run it
#   every morning. --emit-json never sends mail itself and never touches SMTP.
