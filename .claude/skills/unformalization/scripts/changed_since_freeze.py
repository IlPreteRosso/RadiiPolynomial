#!/usr/bin/env python3
"""PROPOSED (not a campaign tool): list API files whose .lean source or sidecar differs from the sha256
recorded in their unit's _records/<unit>/MANIFEST.json, plus API files with no MANIFEST entry and
MANIFEST entries no longer in API_FILES.txt.  Read-only.
usage: changed_since_freeze.py <Unformalization root> <library source root>"""
import os, sys, json, hashlib
U, SRC = sys.argv[1], sys.argv[2]
def sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.exists(p) else None
api = [l.strip() for l in open(os.path.join(U, "API_FILES.txt")) if l.strip()]
seen = {}
for u in json.load(open(os.path.join(U, "_tools", "launch_units.json"))):
    mp = os.path.join(U, "_records", u["unit"], "MANIFEST.json")
    if not os.path.exists(mp): print("NO-MANIFEST", u["unit"]); continue
    m = json.load(open(mp))
    for rel, e in m["files"].items():
        seen[rel] = u["unit"]
        lean_now = sha(os.path.join(SRC, rel)); side_now = sha(os.path.join(U, "_sidecar", rel[:-5] + ".sig.tsv"))
        tags = [t for t, a, b in (("lean", e["lean"], lean_now), ("sidecar", e["sidecar"], side_now)) if a != b]
        if tags: print("CHANGED", u["unit"], rel, "+".join(tags), "(frozen at", m["library_head"][:7] + ")")
for rel in api:
    if rel not in seen: print("NEW (no companion unit)", rel)
for rel in seen:
    if rel not in api: print("GONE from API_FILES", rel)
print("checked", len(seen), "frozen files;", len(api), "API files")
