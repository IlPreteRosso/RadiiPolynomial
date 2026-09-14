"""Prototype immutable file bus. Delivery does not imply session activation.

A complete message is retained at .messages/<id>.md and hard-linked into the
recipient inbox. The hidden store reserves IDs across recipients and survives
archival. Readers inspect only non-hidden inbox *.md files. Nothing here acquires,
expires, or releases resource locks, or infers peer liveness.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import tempfile
import time


MAX_WAIT = 55.0
TOKEN = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,159}\Z")
KEY = re.compile(r"[a-z][a-z0-9-]*\Z")
FIELDS = ("from", "to", "type", "id", "sender-session", "re", "task", "state",
          "deadline", "created-at")
REQUIRED = {"from", "to", "type", "id", "sender-session", "created-at", "body"}


class ConflictError(ValueError):
    """An ID already identifies different immutable bytes."""


def _token(value: str) -> str:
    if not isinstance(value, str) or not TOKEN.fullmatch(value):
        raise ValueError(f"Unsafe message or recipient ID: {value!r}")
    return value


def encode(message: dict[str, str]) -> bytes:
    missing = REQUIRED - message.keys()
    if missing:
        raise ValueError(f"Missing fields: {', '.join(sorted(missing))}")
    for key, value in message.items():
        if not KEY.fullmatch(key) or not isinstance(value, str):
            raise ValueError("Header keys and all values must be strings")
        if key != "body" and (not value or any(c in value for c in "\r\n\0")):
            raise ValueError(f"Invalid header value for {key}")
    for key in ("from", "to", "id"):
        _token(message[key])
    keys = [key for key in FIELDS if key in message]
    keys += sorted(message.keys() - set(FIELDS) - {"body"})
    header = "\n".join(f"{key}: {message[key]}" for key in keys)
    return (header + "\n\n" + message["body"]).encode("utf-8")


def decode(data: bytes) -> dict[str, str]:
    header, separator, body = data.decode("utf-8").partition("\n\n")
    if not separator:
        raise ValueError("Missing header/body separator")
    message = {"body": body}
    for line in header.splitlines():
        key, separator, value = line.partition(":")
        if not separator or key in message:
            raise ValueError("Invalid or duplicate header field")
        message[key] = value.strip()
    encode(message)  # Validate without requiring the incoming field order.
    return message


def _link_or_verify(source: Path, target: Path, data: bytes) -> None:
    try:
        os.link(source, target)
    except FileExistsError:
        if target.read_bytes() != data:
            raise ConflictError(f"Message ID conflict: {target.name}")


def publish(bus: Path, message: dict[str, str]) -> Path:
    """Publish complete bytes without overwriting; retry repairs interrupted delivery.

    Same ID and bytes return the existing inbox/archive artifact. Different bytes
    fail even when addressed elsewhere or already archived. Two filesystem links
    share one immutable inode. Never edit published files in place.
    """
    data = encode(message)
    store = bus / ".messages"
    inbox = bus / "inbox" / message["to"]
    store.mkdir(parents=True, exist_ok=True)
    inbox.mkdir(parents=True, exist_ok=True)
    canonical = store / f"{message['id']}.md"
    descriptor, temporary = tempfile.mkstemp(prefix=".tmp-", dir=store)
    staged = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        _link_or_verify(staged, canonical, data)
    finally:
        staged.unlink(missing_ok=True)
    archived = inbox / "done" / canonical.name
    if archived.exists():
        if archived.read_bytes() != data:
            raise ConflictError(f"Archived message ID conflict: {canonical.name}")
        return archived
    delivered = inbox / canonical.name
    _link_or_verify(canonical, delivered, data)
    return delivered


def messages(bus: Path, recipient: str) -> list[dict[str, str]]:
    """Read complete, unhandled inbox messages; staging and done/ are excluded.

    A malformed visible message raises an error instead of masquerading as silence.
    A concurrent recipient archive is harmless: that file is now handled.
    """
    inbox = bus / "inbox" / _token(recipient)
    result = []
    for path in sorted(inbox.glob("*.md")):
        if path.name.startswith("."):
            continue
        try:
            message = decode(path.read_bytes())
        except FileNotFoundError:
            continue
        if message["to"] == recipient:
            result.append(message | {"path": str(path.resolve())})
    return result


def wait(bus: Path, recipient: str, reply_to: str, timeout: float,
         *, task: str | None = None, exclude_ids: tuple[str, ...] = (),
         sender: str | None = None, sender_session: str | None = None,
         expected_headers: dict[str, str] | None = None,
         poll_interval: float = 0.1) -> list[dict[str, str]]:
    """Wait for an unhandled exact reply, including one published before this call.

    Unique re IDs prevent unrelated old files from waking the caller. Supply
    exclude_ids for replies already durably processed. Bind the expected sender,
    session and version headers when needed; these filters do not authenticate
    authorship. Domain-state and authorization checks belong to the caller/gate.
    A timeout is only no-match; it does not establish failure, acceptance, or
    permission to recover a lock.
    """
    if not 0 <= timeout <= MAX_WAIT:
        raise ValueError(f"timeout must be between 0 and {MAX_WAIT} seconds")
    if not 0 < poll_interval <= 1:
        raise ValueError("poll_interval must be between 0 and 1 second")
    _token(reply_to)
    if sender is not None:
        _token(sender)
    expected_headers = expected_headers or {}
    if any(not KEY.fullmatch(key) or key in {"body", "path"} or not isinstance(value, str)
           for key, value in expected_headers.items()):
        raise ValueError("Expected header filters require header names and string values")
    deadline = time.monotonic() + timeout
    while True:
        matches = [message for message in messages(bus, recipient)
                   if message.get("re") == reply_to
                   and (task is None or message.get("task") == task)
                   and (sender is None or message.get("from") == sender)
                   and (sender_session is None or message.get("sender-session") == sender_session)
                   and all(message.get(key) == value for key, value in expected_headers.items())
                   and message["id"] not in exclude_ids]
        if matches:
            return matches
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return []
        time.sleep(min(poll_interval, remaining))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    send = sub.add_parser("publish")
    send.add_argument("--bus", type=Path, required=True)
    send.add_argument("--message", type=Path, required=True, help="JSON file with header fields and body")
    receive = sub.add_parser("wait")
    receive.add_argument("--bus", type=Path, required=True)
    receive.add_argument("--to", required=True)
    receive.add_argument("--re", required=True)
    receive.add_argument("--task")
    receive.add_argument("--from", dest="sender")
    receive.add_argument("--sender-session")
    receive.add_argument("--match", action="append", default=[], metavar="KEY=VALUE")
    receive.add_argument("--exclude-id", action="append", default=[])
    receive.add_argument("--timeout", type=float, default=0)
    args = parser.parse_args()
    try:
        if args.command == "publish":
            path = publish(args.bus, json.loads(args.message.read_text()))
            print(json.dumps({"state": "published", "path": str(path.resolve())}))
            return 0
        expected_headers = {}
        for item in args.match:
            key, separator, value = item.partition("=")
            if not separator or (key in expected_headers and expected_headers[key] != value):
                raise ValueError("Each --match must be KEY=VALUE without conflicting duplicate keys")
            expected_headers[key] = value
        matches = wait(args.bus, args.to, args.re, args.timeout, task=args.task,
                       exclude_ids=tuple(args.exclude_id), sender=args.sender,
                       sender_session=args.sender_session, expected_headers=expected_headers)
        print(json.dumps({"state": "matched" if matches else "no-match", "messages": matches}))
        return 0 if matches else 2
    except (OSError, ValueError, TypeError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
