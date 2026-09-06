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
from datetime import datetime, timedelta, date as date_cls
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

# The four branches you asked to watch.
WATCHED_LOCATIONS = {
    name: ALL_LOCATIONS[name]
    for name in ("Aspen Hill Library", "Kensington Park Library", "Twinbrook Library", "Davis Library")
}

CLASS_ID = "580"  # public/unmediated booking class used by the site
API_URL = "https://api.communico.co/v2/mcpl/roomsbyclass/{ids}"
RESERVE_PAGE = "https://mcpl.libnet.info/reserve"

TARGET_START = "10:00"  # 24h "HH:MM", America/New_York
TARGET_END = "12:00"

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
         only_date: date_cls | None = None) -> ScanResult:
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
            if room_is_open_for_window(room, day, TARGET_START, TARGET_END):
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


def build_email_body(result: ScanResult, scope: str) -> tuple[str, str]:
    """Returns (plain_text, html) email bodies. `scope` describes the date
    range scanned, e.g. "next 7 days" or "on 2026-09-08"."""
    if not result.open_slots:
        text = f"No 10:00am-12:00pm openings found {scope} at your watched branches."
        html = f"<p>{text}</p>"
        return text, html

    by_date: dict[str, list[OpenSlot]] = {}
    for slot in result.open_slots:
        by_date.setdefault(slot.date, []).append(slot)

    text_lines = [f"10am-12pm study room openings - {scope}", ""]
    html_lines = [f"<h2>10am–12pm study room openings</h2>"]

    for day in sorted(by_date):
        pretty_day = datetime.strptime(day, "%Y-%m-%d").strftime("%A, %B %d")
        link = f"{RESERVE_PAGE}?date={day}"
        text_lines.append(f"{pretty_day} ({day})")
        html_lines.append(f"<h3>{pretty_day} <small>({day})</small></h3><ul>")
        for slot in sorted(by_date[day], key=lambda s: (s.branch, s.room_name)):
            line = f"  - {slot.branch}: {slot.room_name} (fits {slot.capacity})"
            text_lines.append(line)
            html_lines.append(f"<li>{slot.branch}: <b>{slot.room_name}</b> (fits {slot.capacity})</li>")
        text_lines.append(f"  Reserve: {link}")
        html_lines.append(f"</ul><p><a href=\"{link}\">Reserve for {pretty_day}</a> (pick the branch/room above once there)</p>")
        text_lines.append("")

    if result.errors:
        text_lines.append("Some dates could not be checked:")
        text_lines.extend(f"  - {e}" for e in result.errors)

    return "\n".join(text_lines), "\n".join(html_lines)


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
    if args.date:
        try:
            only_date = datetime.strptime(args.date, "%Y-%m-%d").date()
        except ValueError:
            parser.error(f"--date must be YYYY-MM-DD, got {args.date!r}")

    load_env_file(Path(__file__).with_name("mcpl_scanner.env"))

    if only_date is None and datetime.now(TIMEZONE).date().weekday() == 6:
        print("Today is Sunday - MCPL branches are closed today, but scanning "
              "the upcoming (non-Sunday) days anyway.", file=sys.stderr)

    result = scan(days_ahead=args.days, verbose=args.verbose, only_date=only_date)

    scope_human = f"on {only_date}" if only_date else f"in the next {args.days} days"
    scope_short = f"on {only_date}" if only_date else f"next {args.days} days"
    text_body, html_body = build_email_body(result, scope_short)
    subject = (
        f"MCPL rooms: {len(result.open_slots)} 10am-12pm opening(s) found"
        if result.open_slots
        else "MCPL rooms: no 10am-12pm openings right now"
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
