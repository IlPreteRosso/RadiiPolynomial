# Pipeline commands (verbatim, with working directory, inputs/outputs and exit behaviour)

Notation: `UNF=/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization`,
`LAKE=/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial` (Lake root; sources in
`$LAKE/RadiiPolynomial`). The commands below are written with the literal paths, as the briefs
wrote them. Every tool computes its own paths from its file location or hard-coded constants, so the
working directory matters only for the relative `_tools/...` and `Dir/File` arguments: run them from
`$UNF` in a SUBSHELL (never a top-level `cd`; zsh). Source of each command in a trailing comment.

## 0. Scope and units

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/inventory.py)
# source: README.md; _tools/inventory.py docstring
```
Reads every `.lean` under `$LAKE/RadiiPolynomial` except `Examples/`, `tmp/` and files with no line
matching its declaration regex (hubs). Writes (overwrites) `API_FILES.txt`, `INVENTORY.md`,
`UNITS.md`, `_tools/units.json`. Prints `<n> files; <m> units` (2026-10-10: 129 files; 36 units).
Does NOT write `_tools/launch_units.json` / `LAUNCH_UNITS.md` (hand-merged; UNSETTLED procedure).

## 1. Sidecars (elaborated signatures; no build)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/signatures.py)
(cd ... && python3 _tools/signatures.py --unit A1 B9)
(cd ... && python3 _tools/signatures.py --file Core/Bounds.lean Core/Theorem.lean)
# source: _tools/signatures.py docstring: "usage: signatures.py [--unit A1 ...] [--file Dir/File.lean ...] (default: every launch unit)"
```
- `--unit` and `--file` take ALL remaining arguments; `--file` processes the listed files as one batch.
- Per unit: writes a scratch `.lean` (in `$TMPDIR`) importing the unit's modules + a `run_cmd` that dumps
  every constant of each module, runs `lake env lean <scratch>` with cwd `$LAKE`. Needs current oleans;
  fails closed (`LEAN FAILED …` / `NO OUTPUT <rel>`) if one is missing.
- Writes `_sidecar/<Dir>/<File>.sig.tsv`, rows sorted by span start, 6 tab-separated columns:
  `public|private  kind  start-end  authored|generated  FQN  signature`; prints
  `sidecar <rel>: N declarations (M authored)` per file; then rebuilds `_sidecar/ALL_FQNS.txt` from EVERY
  `.sig.tsv` present and prints `ALL_FQNS: n` (2026-10-11: 3311 lines). Exit 1 on any failure.

## 2. Tool self-test (after ANY tool change)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/selftest.py)
# source: _tools/selftest.py docstring; CONTRACT §4
```
Fixtures `_tools/fixtures/{src,side,cases}`; runs build.py and gates.py with `UNF_ROOT/UNF_SRC/UNF_SIDE`
overrides on cases good, comment_only (expects G6), index_only (G6), ambiguous_suffix (G7 ambiguous + G6),
fabricated_name (G7 unresolved), missing_pdf (G2 no pdf + G3 no log), corrupt_pdf (G2 pdfinfo failed),
plus broken_tex (build.py must exit 1). Prints `ok   <case> -> …` / `WRONG …`, then `SELFTEST PASS` or
`SELFTEST FAIL (n)`; exit 1 on any surprise. Smoke examples of the macros: `_tools/smoke/smoke.tex`,
`_tools/smoke/strand.tex` (G8 stranded-line test).

## 3. Build one or all companions (fail-closed)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/build.py Dir/File.tex)
(cd ... && python3 _tools/build.py --all)
# source: BRIEF_REPIN.md (subshell form); _tools/build.py docstring "usage: build.py <Dir/File.tex> [...] | build.py --all"
```
- Argument is the `.tex` path relative to `$UNF` (env `UNF_ROOT` overrides the root). `--all` = every
  API_FILES.txt entry.
- Deletes the old `.pdf`/`.log`, then three `pdflatex -synctex=1 -interaction=nonstopmode -halt-on-error`
  passes in the file's directory with `TEXINPUTS=.:<UNF>/_common//:`.
- Prints per file `OK    <rel> pages=N` or `FAIL  <rel> pages=N | reasons` (reasons: `pdflatex rc=[…]`,
  `no log`, `log error: …`, `no pdf`, `pdfinfo failed`, `pdftotext failed`, `?? xN`,
  `overfull>5pt xN (max …pt)`). Exit 1 if any file fails.

## 4. Resolve external names (real `#check`)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/resolve_external.py Dir/File.lean)
# source: _briefs/A1_DRAFTER.md "python3 _tools/resolve_external.py <each lean>"; docstring "usage: resolve_external.py [Dir/File.lean ...] (default: every file in API_FILES.txt that has a tex)"
```
- Collects every `\evidl{Mathlib|LeanCert|Lean core}{…}` token not yet in the registry, and every
  `\lean{…}` / `\evidl{Lean: …}{…}` token that resolves neither in the file's sidecar nor in ALL_FQNS.
- One scratch file per companion (`import RadiiPolynomial.<Dir>.<File>` + `env.find?` per name), one
  `lake env lean` run with cwd `$LAKE` (§7.64 batching).
- Writes `_sidecar/EXTERNAL_RESOLVED.txt` (`name<TAB>module`, sorted) under an exclusive lock
  (`EXTERNAL_RESOLVED.txt.lock`, §7.33); rows are only added/updated, never removed.
- Prints `nothing pending` (exit 0) or `resolved n (recorded in EXTERNAL_RESOLVED.txt)` then
  `STILL UNRESOLVED <rel> [toks]` per failure (exit 1). A STILL UNRESOLVED name is misspelt: fix it, never
  allow-list it (drafter briefs).

## 5. Gates G0–G10

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/gates.py Dir/File.lean)
(cd ... && python3 _tools/gates.py)      # every API file
# source: _briefs/*_DRAFTER.md; _tools/gates.py docstring "usage: gates.py [Dir/File.lean ...]"
```
- Argument is the `.lean` path (NOT the `.tex`). Env overrides `UNF_ROOT`, `UNF_SRC`, `UNF_SIDE`.
- G0 sidecar · G1 tex · G2 pdf + pdfinfo + pdftotext · G3 log without `!` · G4 no `??` · G5 no overfull
  > 5pt · G6 coverage (public authored → cited in a `\leanline` paragraph; public generated → cited
  anywhere) · G7 resolution (exact/unique suffix in the sidecar, then ALL_FQNS, then EXTERNAL_RESOLVED;
  external tags only from the registry with the right package prefix) · G8 no page starting with "Lean."
  · G9 `\evidl{Lean: <path>}` path = declaring file · G10 ADVISORY declaration-like name inside `\leanx`.
- Prints `PASS <rel>` or `FAIL <rel>  | <reasons>`, then `  NOTE G10 advisory: …` lines (§7.66), then
  `\n<k>/<n> pass`. Exit 1 if any file fails. Notes never fail.
- `% unf-allow: tok1 tok2` in a tex skips notation typeset with `\lean`; never for Mathlib names (§6).

## 6. Probes (drafter and checker, read-only)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial && lake env lean <scratch.lean>)
# source: HANDOFF §4 ("lake env lean for single files"); CONTRACT §7.36 ("runs simp? on a scratch file with lake env lean from the Lake root (no build)")
```
- Scratch file under a PRIVATE scratchpad subdirectory; contents e.g. `import RadiiPolynomial.<Module>`
  then the statement with `simp?` / `#check` / `set_option pp.explicit true` (§7.32) / `trace_state`.
- §7.53 alternative accepted: the v4.34.1 `lean` binary directly with `LEAN_PATH` = `$LAKE/.lake/build/lib/lean`
  plus every `$LAKE/.lake/packages/*/.lake/build/lib/lean` (the exact binary path is not recorded).
- Keep probe files under `_records/<unit>/probes/` (§8 P2; none exist yet).

## 7. Save a subagent hand-back

```
python3 /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/handback_extract.py <output.jsonl> <marker> <dest.md> [second-marker]
# source: _tools/handback_extract.py docstring; HANDOFF §4
```
Scans the task-output JSONL for the LAST text containing both `<marker>` and `<second-marker>` (default
`CHECKS`), writes it to `<dest.md>`, prints `wrote <dest> (<n> chars)`; exits with `marker not found`
otherwise. Pick a marker the report is sure to contain (e.g. "Checker C2" + "VERIFIED"). Destination of
record: `_records/<unit>/FINDINGS_checker_round1.md` (coordinator rulings are prepended by hand).

## 8. Freeze a unit

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/freeze.py <unit>)
# source: CONTRACT §5; _tools/freeze.py docstring "usage: freeze.py <unit-id>"
```
- `<unit>` is a launch-unit id from `_tools/launch_units.json` (A1 … E4).
- Runs `gates.check` on the unit's files → `REFUSED: gates fail: {…}` (exit 1); `git rev-parse HEAD` and
  `git status --porcelain -- RadiiPolynomial/` in `$LAKE` → `REFUSED: unit sources modified in the working
  tree: […]` (exit 1) if a porcelain line ends with a unit file.
- Writes `_records/<unit>/MANIFEST.json`, `SHA256SUMS`, and copies `ALL_FQNS.frozen.txt`,
  `EXTERNAL_RESOLVED.frozen.txt`, `CONTRACT.frozen.md`, `unformalization.frozen.sty`. Overwrites an
  existing MANIFEST.json (rename it first to `MANIFEST_round<k>_<sha8>.json` when a Codex round refers to it).
- Prints `frozen <unit>: n files; MANIFEST sha256 <16 hex>`; exit 0.
- Hand-check the first MANIFEST of a batch: `library_head`, `library_source_porcelain` == "".

## 9. Re-pin finalize (after the user's library commit)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/repin_finalize.py 5d0fa4f)
(cd ... && python3 _tools/repin_finalize.py <old7> --dry)
# source: HANDOFF_20261011.md §2 (exact first line, as executed 2026-10-11 by Haiku 5.5 medium); docstring "Usage: repin_finalize.py <old7> [--dry]"
```
Steps and messages:
1. `git status --porcelain -- RadiiPolynomial/` in `$LAKE` non-empty → `REFUSED: library working tree not
   clean under RadiiPolynomial/ (commit first):` + porcelain (exit 1).
2. new = `git rev-parse --short=7 HEAD`; regex `(\unfheader{[^}]*}{)<old7>(})` must match EXACTLY ONCE in
   every API companion, else `REFUSED: header field not found exactly once in <tex> (k)`; prints
   `header <old> -> <new> in n companions` (+ ` (dry)`; `--dry` stops here, writes nothing).
3. `build.py` on all → last line printed; `BUILD FAILURES:` + FAIL lines (exit 1).
4. `gates.py` on all → last line (`129/129 pass`); `GATE FAILURES:` (exit 1).
5. `freeze.py <u>` for every launch unit; prints `<u> frozen <u>: …`; `FREEZE FAILED for <u>` (exit 1).
6. `RE-PIN FINALIZED at <new7>`.
2026-10-11 result: `{5d0fa4f}` → `{d6fda60}` in 129/129, build 129/129 OK, gates 129/129, 26 freezes
(A1 857d7412 … E4 d5c41f8b) (PROGRESS.md).

## 10. Library side (only when the user unfreezes the library; NOT part of companion work)

```
python3 /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/docstring_remarks.py
# source: _tools/docstring_remarks.py docstring
```
Extracts every companion paragraph mentioning "docstring" into `_records/docstring_sweep/REMARKS_<TopDir>.md`;
prints `<n> files, <p> paragraphs` + a per-top-directory table (2026-10-11: 114 files, 511 paragraphs).

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial && lake env lean RadiiPolynomial/<Path>.lean)
# source: _records/docstring_sweep/BRIEF.md ("must exit 0 with no new output")
git status --short
git diff -- <file>
# source: _records/docstring_sweep/BRIEF.md ("Git: only `git status --short` and `git diff -- <file>`")
```
Full library builds: `(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial && lake build)`
(HANDOFF §4 form; library side only; 2026-10-11: 4414 jobs PASS). Never `lake --dir`.

## 11. Re-pin checker diff

```
diff -u /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_records/repin_20261011/before/<Dir>/<File>.tex /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/<Dir>/<File>.tex
# source: _records/repin_20261011/CHECK_REPIN.md ("Diff them (`diff -u` per file)")
```

## 12. Changed files since the last freeze (skill helper; not yet used in a campaign)

```
python3 -I /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/.claude/skills/unformalization/scripts/changed_since_freeze.py /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial
```
Read-only. Compares each MANIFEST `files[rel].lean` and `.sidecar` sha256 with the current files; prints
`CHANGED <unit> <rel> lean|sidecar|lean+sidecar (frozen at <sha7>)`, `NEW (no companion unit) <rel>`,
`GONE from API_FILES <rel>`, `NO-MANIFEST <unit>`, then `checked n frozen files; m API files`. Run AFTER
`signatures.py` (else sidecar changes are invisible). Tested 2026-10-11 at d6fda60: no CHANGED lines,
`checked 129 frozen files; 129 API files`.

## 13. Navigation page (mention only)

```
python3 -I /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/gen_reading_order.py /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/READING_ORDER.src.md
# source: _tools/gen_reading_order.py (shebang `python3 -I`; SRC = argv[1]; writes READING_ORDER.md; asserts every target exists)
```
