"""Optional universal file-bus administration. Transport stays in bus.py.

No worker, scheduler, watcher, takeover, or recovery command is implemented.
Every occupied guard fails immediately; retry only after inspecting the result.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import bootstrap
import locking
import participants


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    location = argparse.ArgumentParser(add_help=False)
    location.add_argument("--bus", type=Path,
                          help="explicit bus candidate; does not override other discovered buses")
    location.add_argument("--root", type=Path,
                          help="start ancestor-marker discovery here (default: current directory)")
    location.add_argument("--join", metavar="BUS_ID",
                          help="select this 16-hex bus id when candidates conflict; all are still validated")

    initialize = commands.add_parser("init", help="initialize or complete a compatible bus")
    initialize.add_argument("--root", type=Path, required=True,
                            help="coordination root; publishes its .agents_bus discovery marker")
    initialize.add_argument("--bus", type=Path,
                            help="bus storage directory (default: ROOT/tmp/agents_bus)")
    initialize.add_argument("--agent", action="append", default=[],
                            help="declare an alias; repeat for others, then register each with hello")
    initialize.add_argument("--package-manifest-sha256",
                            help="explicit creating-package digest (default: detect the installed MANIFEST.json)")
    commands.add_parser("discover", parents=[location], help="validate candidates and locate one bus")

    registration = commands.add_parser("hello", parents=[location],
                                        help="register a new alias or refresh its same instance")
    registration.add_argument("--agent", required=True)
    registration.add_argument("--harness", required=True)
    registration.add_argument("--instance",
                              help="owned instance id; omission mints a fresh id, never adopts an existing alias; reuse the returned id for refreshes")
    registration.add_argument("--primary",
                              help="descriptive activation field; omitted fields are preserved on refresh (new alias default: user-relay)")
    registration.add_argument("--keepalive",
                              help="descriptive activation field; omitted fields are preserved on refresh (new alias default: unknown)")

    binding = commands.add_parser("bind", parents=[location])
    binding.add_argument("--agent", required=True)
    binding.add_argument("--instance", required=True)
    binding.add_argument("--key", required=True)
    binding.add_argument("--resource", type=Path, required=True)
    binding.add_argument("--kind", choices=["file", "dir", "build", "board"])

    lock = commands.add_parser("lock")
    actions = lock.add_subparsers(dest="action", required=True)
    for action in ("acquire", "release", "show"):
        command = actions.add_parser(action, parents=[location])
        if action != "show":
            command.add_argument("--agent", required=True)
            command.add_argument("--instance", required=True)
            command.add_argument("--key", action="append", required=True)
            command.add_argument("--token-file", type=Path, required=True)
        if action == "acquire":
            command.add_argument("--purpose", required=True)

    args = parser.parse_args()
    try:
        if args.command == "init":
            package = None if args.package_manifest_sha256 is None else {
                "name": "agents-bus", "manifest_sha256": args.package_manifest_sha256}
            result = bootstrap.initialize(args.root, args.agent, bus_path=args.bus,
                                          package=package)
        else:
            bus = bootstrap.discover(args.root, explicit=args.bus, join=args.join)
            if args.command == "discover":
                result = {"path": str(bus)}
            elif args.command == "hello":
                activation = {name: value for name, value in (
                    ("primary", args.primary), ("keepalive", args.keepalive)) if value is not None}
                result = participants.hello(bus, args.agent, args.harness, instance=args.instance,
                                            activation=activation or None)
            elif args.command == "bind":
                result = locking.bind(bus, args.agent, args.instance, args.key, args.resource,
                                      kind=args.kind)
            elif args.action == "show":
                result = {"locks": locking.show(bus)}
            elif args.action == "acquire":
                result = locking.acquire(bus, args.agent, args.instance, args.key,
                                         purpose=args.purpose, token_file=args.token_file)
            else:
                result = locking.release(bus, args.agent, args.instance, args.key,
                                         token_file=args.token_file)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, TypeError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
