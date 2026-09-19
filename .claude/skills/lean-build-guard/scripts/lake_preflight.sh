#!/bin/zsh
# lake_preflight.sh <package dir> — refuse a first build that would clone or compile dependencies.
set -u
P=${1:?package dir}; cd "$P" || exit 2
pd=$(command grep -E '^packagesDir' lakefile.toml 2>/dev/null | sed -E 's/.*= *"([^"]*)".*/\1/')
if [ -n "$pd" ]; then
  if [ ! -d "$pd/mathlib" ]; then echo "REFUSE: packagesDir '$pd' does not contain mathlib (would clone/compile)"; exit 1; fi
  echo "ok: packagesDir -> $(cd "$pd" && pwd -P) ($(ls "$pd" | wc -l | tr -d ' ') packages)"
else
  echo "WARN: no packagesDir in lakefile.toml — this package has its own dependency tree; run 'lake exe cache get' first"
fi
if [ -f lake-manifest.json ]; then
  python3 - <<'PY' || exit 1
import json, os, sys
m = json.load(open("lake-manifest.json")); bad = []
pd = m.get("packagesDir")
if pd and not os.path.isdir(pd): bad.append(f"manifest packagesDir '{pd}' does not resolve from here (copied manifest?)")
for p in m.get("packages", []):
    if p.get("type") == "path" and not os.path.isdir(p.get("dir", "")): bad.append(f"path dependency '{p.get('name')}' dir '{p.get('dir')}' does not resolve")
if bad: print("REFUSE:", *bad, sep="\n  "); sys.exit(1)
print("ok: manifest paths resolve")
PY
fi
before=$(find . -maxdepth 3 -type d 2>/dev/null | sort); [ -n "$pd" ] && before="$before
$(ls "$pd" | sort)"
lake env true > /tmp/lake_preflight.$$ 2>&1; rc=$?
after=$(find . -maxdepth 3 -type d 2>/dev/null | sort); [ -n "$pd" ] && after="$after
$(ls "$pd" | sort)"
if [ "$before" != "$after" ]; then echo "REFUSE: 'lake env true' created directories (Lake started materializing dependencies):"; diff <(echo "$before") <(echo "$after") | command grep '^>' ; exit 1; fi
if command grep -qi 'clon\|download' /tmp/lake_preflight.$$; then echo "REFUSE: lake resolution tried to clone/download:"; head -5 /tmp/lake_preflight.$$; exit 1; fi
rm -f /tmp/lake_preflight.$$; echo "ok: dependency resolution created nothing (rc=$rc)"; exit $rc
