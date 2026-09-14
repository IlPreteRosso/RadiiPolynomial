"""Pure prototype release check, not an authenticity verifier.

The caller must supply actual peer-authored inbox records, never test fixtures.
Passing this check establishes consistency of supplied records only. Message
headers bind `design-sha256`, `manifest-sha256`, and `test-run`; expected values
use the JSON keys `design_sha`, `manifest_sha`, and `test_run`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re


AGREEMENT = "yes I agree with the design of this skill"
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")


def has_agreement(body: str) -> bool:
    """Recognize an exact bare line, excluding blockquotes and fenced examples."""
    fence_character, fence_length = "", 0
    for line in body.splitlines():
        match = FENCE.match(line)
        if match:
            marker, suffix = match.groups()
            if not fence_character:
                fence_character, fence_length = marker[0], len(marker)
            elif marker[0] == fence_character and len(marker) >= fence_length and not suffix.strip():
                fence_character, fence_length = "", 0
            continue
        if not fence_character and line == AGREEMENT:
            return True
    return False


def evaluate(packet: dict) -> dict:
    """Return ready/missing/evidence without publishing, writing, or changing locks.

    `messages` holds authored agreement records; `receipts` holds explicit peer
    receipts. Each opposite agreement can also acknowledge `received-agreement`.
    Receipts of receipts do not count. More than one historical message may be
    supplied; a pair must bind the exact expected design, manifest, run, and peers.
    """
    missing = []
    participants = packet.get("participants", {})
    if not isinstance(participants, dict) or len(participants) != 2 or any(
            not isinstance(role, str) or not role or not isinstance(session, str) or not session
            for role, session in participants.items()):
        return {"ready": False, "missing": ["Exactly two expected roles with nonempty session IDs are required."]}
    for name in ("design_sha", "manifest_sha"):
        if not isinstance(packet.get(name), str) or not SHA256.fullmatch(packet[name]):
            missing.append(f"Expected {name} must be a lowercase SHA256 digest.")
    if not isinstance(packet.get("test_run"), str) or not packet["test_run"]:
        missing.append("Expected test_run must be nonempty.")
    records = packet.get("messages", [])
    receipts = packet.get("receipts", [])
    if not isinstance(records, list) or not isinstance(receipts, list) or any(
            not isinstance(message, dict) for message in records + receipts):
        missing.append("messages and receipts must be lists of actual message records.")
    if missing:
        return {"ready": False, "missing": missing}
    # Conflicting copies cannot be arbitrarily chosen as evidence. Exact duplicates
    # are normal when a caller merges inbox and durable processing records.
    by_id = {}
    for message in records + receipts:
        identifier = message.get("id")
        if not isinstance(identifier, str) or not identifier:
            missing.append("Every supplied message must have a nonempty string ID.")
            continue
        # A local file path is provenance, not part of the immutable message.
        content = {key: value for key, value in message.items() if key != "path"}
        if identifier in by_id and by_id[identifier] != content:
            missing.append(f"Conflicting supplied records for message {identifier}.")
        by_id[identifier] = content
    if missing:
        return {"ready": False, "missing": sorted(set(missing))}
    roles = sorted(participants)
    context = {"design-sha256": packet["design_sha"],
               "manifest-sha256": packet["manifest_sha"], "test-run": packet["test_run"]}

    def bound(message, sender, recipient, state):
        return (message.get("from") == sender and message.get("to") == recipient
                and message.get("sender-session") == participants[sender]
                and message.get("type") == "reply" and message.get("state") == state
                and all(message.get(key) == value for key, value in context.items()))

    candidates = {}
    for sender, recipient in ((roles[0], roles[1]), (roles[1], roles[0])):
        candidates[sender] = [message for message in records
                              if bound(message, sender, recipient, "accepted")
                              and isinstance(message.get("body"), str)
                              and has_agreement(message["body"])]
        if not candidates[sender]:
            missing.append(f"Missing {sender} agreement: exact bare sentence, reply/accepted, "
                           "expected peer recipient/session, and current design/manifest/run are required.")

    def receipt_evidence(agreement, other_agreement):
        sender, recipient = agreement["from"], agreement["to"]
        if other_agreement.get("received-agreement") == agreement["id"]:
            return other_agreement["id"]
        for receipt in receipts:
            if (bound(receipt, recipient, sender, "received")
                    and receipt.get("re") == agreement["id"]):
                return receipt["id"]
        return None

    if not missing:
        for first in candidates[roles[0]]:
            for second in candidates[roles[1]]:
                first_receipt = receipt_evidence(first, second)
                second_receipt = receipt_evidence(second, first)
                if first_receipt and second_receipt:
                    return {"ready": True, "missing": [],
                            "agreement_ids": {roles[0]: first["id"], roles[1]: second["id"]},
                            "receipt_ids": {first["id"]: first_receipt, second["id"]: second_receipt}}
        for role in roles:
            other = next(value for value in roles if value != role)
            if not any(receipt_evidence(agreement, opposite)
                       for agreement in candidates[role] for opposite in candidates[other]):
                missing.append(f"Missing {other} receipt of {role}'s agreement for this design/manifest/run.")
        if not missing:
            missing.append("No single pair of agreements has both required peer receipts.")
    return {"ready": False, "missing": missing}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path, help="JSON containing expected bindings and actual inbox records")
    args = parser.parse_args()
    try:
        packet = json.loads(args.packet.read_text())
        if not isinstance(packet, dict):
            raise ValueError("The packet must be a JSON object")
        result = evaluate(packet)
    except (OSError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    print(json.dumps(result, indent=2))
    return 0 if result["ready"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
