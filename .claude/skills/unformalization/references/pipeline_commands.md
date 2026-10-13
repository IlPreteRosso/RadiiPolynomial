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
- Extracts into the staging directory `_sidecar_stage_<run>/` and validates every staged file (6 tab-separated
  columns `public|private  kind  start-end  authored|generated  FQN  signature`, rows sorted by span start); prints
  `sidecar <rel>: N declarations (M authored) [staged]` per file. ANY failure (`LEAN FAILED …`, `NO OUTPUT <rel>`,
  `INVALID …`) → `FAILED: nothing published (live sidecars and _sidecar_prev/ unchanged)`, exit 1.
- Publication (under `_sidecar.lock`; CONSENSUS_sidecar_archive A2): writes `_sidecar_INCOMPLETE.json`, copies the
  COMPLETE previous live set (+ `ALL_FQNS.txt`) to `_sidecar_prev/` with `PREV_MANIFEST.json`, replaces the selected
  `_sidecar/<Dir>/<File>.sig.tsv` (other live files untouched) and `_sidecar/ALL_FQNS.txt` (= names of the live set
  only), removes the marker; prints `published n sidecar(s) (run <id>); previous generation in _sidecar_prev/` and
  `ALL_FQNS: n` (2026-10-11: 3311 lines); exit 0.
- `REFUSED: sidecar lock … is held` / `REFUSED: an earlier publication is INCOMPLETE …` → exit 2. An interrupted
  publication prints `INTERRUPTED: publication failed at <file> …` (exit 3) and leaves the marker; then
  `(cd ... && python3 -I _tools/signatures.py --recover)` → `RECOVERED run <id> (phase publish): live set = previous
  generation (n sidecars, hashes verified)` (or `phase rotate: live set untouched`); `--recover` also restores
  `_sidecar_prev/` to the generation preceding the failed run. Until then `freeze.py`, `finalize_manifest.py`,
  `semdiff.py` (live side) and `gates.py` (`G0 sidecar publication INCOMPLETE …`, exit 1) refuse as well.
- Roots: `--unf DIR --lake DIR`, else env `UNF_ROOT`/`UNF_LAKE`, else the live paths (scratch trials: redirect BOTH).

## 2. Tool self-test (after ANY tool change)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/selftest.py)
# source: _tools/selftest.py docstring; CONTRACT §4
```
Fixtures `_tools/fixtures/{src,side,cases}`; runs build.py and gates.py with `UNF_ROOT/UNF_SRC/UNF_SIDE`
overrides on cases good, comment_only (expects G6), index_only (G6), ambiguous_suffix (G7 ambiguous + G6),
fabricated_name (G7 unresolved), missing_pdf (G2 no pdf + G3 no log), corrupt_pdf (G2 pdfinfo failed),
plus broken_tex (build.py must exit 1), the finalization fixtures (`fixtures/finalize/`) and the archive fixtures
(`fixtures/archive/run_archive_fixtures.py`: freeze archive, `_sidecar_prev/`, interrupted publication + `--recover`,
`semdiff.py`, planner baseline rows, finalizer restore; cases A1–A13). Prints `ok   <case> -> …` / `WRONG …`, then
`SELFTEST PASS` or `SELFTEST FAIL (n)`; exit 1 on any surprise. Pass `--tmp <scratch dir>` to keep the fixture worlds
out of `$TMPDIR`. Smoke examples of the macros: `_tools/smoke/smoke.tex`,
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
- `REFUSED: sidecar publication INCOMPLETE …` / `REFUSED: sidecar lock … is held` (exit 1): freeze is serialized with
  sidecar publication.
- Archives FIRST (A1): the exact bytes of each unit sidecar → `_records/<unit>/sidecar/<sha256>.sig.tsv` (reused after byte
  verification; `REFUSED: archive object … exists with different bytes (corrupt); never overwritten`), every reference
  re-resolved with its digest; then writes `_records/<unit>/MANIFEST.json` (`files[rel].sidecar_archive`), `SHA256SUMS`, and
  copies `ALL_FQNS.frozen.txt`, `EXTERNAL_RESOLVED.frozen.txt`, `CONTRACT.frozen.md`, `unformalization.frozen.sty`.
  Overwrites an existing MANIFEST.json (rename it first to `MANIFEST_round<k>_<sha8>.json` when a Codex round refers to
  it; the archived objects it names stay valid — no rename of `sidecar/` is needed).
- Prints `frozen <unit>: n files; MANIFEST sha256 <16 hex>; sidecar archive w written, r reused`; exit 0.
- Backfill for a manifest without archived content (exact digest only, labelled in `sidecar/BACKFILL.json`; the manifest is
  not rewritten): `(cd ... && python3 -I _tools/freeze.py --backfill <unit> [--manifest MANIFEST_round1_<sha8>.json] [--from <file> …] [--dry])`
  — candidates `--from` files, the live sidecar, `_sidecar_prev/`; prints `BACKFILL <rel> <- <source>` or
  `BASELINE_UNAVAILABLE <rel> (no candidate bytes match the recorded digest; nothing substituted)`.
- Roots: `--unf DIR --lake DIR`, else env `UNF_ROOT`/`UNF_LAKE` (gates run on the same tree).
- Hand-check the first MANIFEST of a batch: `library_head`, `library_source_porcelain` == "".

## 9. Finalize after the user's library commit (generation-aware; FINALIZE_PROCEDURE.md)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 -I _tools/finalize_manifest.py --commit <C> --plan-out FINALIZE_PLAN.json --rows)
(cd ... && python3 -I _tools/repin_finalize.py --plan FINALIZE_PLAN.json --dry)
(cd ... && python3 -I _tools/repin_finalize.py --plan FINALIZE_PLAN.json [--run-dir DIR])
(cd ... && python3 -I _tools/repin_finalize.py --restore <RUN_DIR> --dry)      # then without --dry
# source: _tools/repin_finalize.py and _tools/finalize_manifest.py docstrings; _tools/FINALIZE_PROCEDURE.md
```
- The bare `repin_finalize.py <old7>` form of 2026-10-11 is REFUSED (exit 2, `REFUSED: the bare … form relabels every
  companion unconditionally`); `--legacy <old7> [--dry]` keeps that recorded whole-set swap, not generation-aware.
- Planner (read-only; `--target/--commit`, `--out/--plan-out`, `--date`, `--unf`, `--lake`, `--rows`): one row per API
  companion with `action` ∈ repin · skip-current · finalize-draft · needs-redraft · blocked · missing · orphan and its
  reasons; prints the summary (`actions:`, `reasons:`, `units:`, `finalize-draft: N (F1 a, F2 b, F3 c)`) and the plan
  sha256. REFUSED while `_sidecar_INCOMPLETE.json` exists. Under every `sidecar-changed`/`dep-changed` row `--rows`
  prints the A4 baseline line(s):
  `baseline sidecar: ARCHIVED _records/<unit>/sidecar/<sha256>.sig.tsv expected <12> observed <12> (manifest _records/<unit>/MANIFEST.json sha256 <12>); comparison complete: REMOVED a ADDED b SIGCHG c META d; hints …; compare: python3 -I _tools/semdiff.py --file <rel> --old frozen`
  or `baseline sidecar: BASELINE_UNAVAILABLE (<reason>) …; comparison baseline unavailable (no counts)`, and
  `baseline dep <file>: …` only for a dependency archive demonstrably at the companion's bound head. Diagnostic only:
  no disposition, reason or decision digest changes (plan JSON `row["propagation"]`).
- Executor `--plan`: preflight of the whole set (schema, HEAD == plan target, recomputed decision digests, headers,
  clean sources, finalize-draft rewrite re-derived) → `preflight OK: r repin rows in u units; deferred d; finalize-draft
  N rows`; `--dry` stops there. Live: run directory `_records/finalize_<C7>_<UTC>/` (PLAN.json, `before/` snapshots +
  SHA256SUMS, `journal.jsonl` with the archive inventory); per row swap/rewrite → `build.py` → `gates.py`; `freeze.py`
  per freezable unit; stops at the first failure (`FAILED at …; restore with: …`, exit 1); prints `FINALIZED at <C7>: …`.
- `--restore RUN_DIR`: copies `before/` back, deletes files the run created; NEVER touches `_records/<unit>/sidecar/`
  objects: refuses if a recorded object was altered (`append-only store violated`), re-resolves every restored MANIFEST
  (`archive: restored manifests resolve ARCHIVED n …; … retained as non-current evidence`); `RESTORED n paths from …`.
- 2026-10-11 (legacy form, as executed): `{5d0fa4f}` → `{d6fda60}` in 129/129, build 129/129 OK, gates 129/129, 26
  freezes (PROGRESS.md).

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
`checked 129 frozen files; 129 API files`. Kept as the small inventory helper (own source/sidecar hashes, not complete
dependency invalidation; Q3 of CONSENSUS_sidecar_archive); WHAT differs in a sidecar: `semdiff.py` (§12a).

## 12a. Inspection diff of sidecar records (CONSENSUS_sidecar_archive A3)

```
(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 -I _tools/semdiff.py --unit <u> --old frozen)
(cd ... && python3 -I _tools/semdiff.py --file <Dir/File.lean> ... --old frozen [--manifest _records/<u>/MANIFEST_round1_<sha8>.json] [--prefix RadiiPolynomial.] [--json OUT.json])
(cd ... && python3 -I _tools/semdiff.py --file <Dir/File.lean> --old prev)          # vs _sidecar_prev/
(cd ... && python3 -I _tools/semdiff.py --file <Dir/File.lean> --old <dir laid out like _sidecar/> [--new <dir>])
```
Read-only; NOT a semantic-equivalence check. Key = (relative file, reported name) — the name column is
`privateToUserName?`, not a guaranteed kernel FQN. Prints inputs (paths + sha256, manifest + sha256), the rules, the
completeness status, primary counts (REMOVED · ADDED · SIGCHG = exact signature text, with an inline `[-old-]{+new+}`
diff · META = kind/visibility/authored/span, span-only flagged · UNCHANGED · AMBIGUOUS_KEY with all rows), observations
(MOVED: a public name unique on both sides moving files; REMOVED/ADDED kept) and hints separately (RENAMED?, PRINT-ONLY?
after the explicit `--prefix` normalization at identifier boundaries, MOVED? for private/non-unique names). A missing
baseline is `BASELINE_UNAVAILABLE` (counts unknown), an empty file a valid baseline, a malformed row → incomplete.
Exit 0 complete, 1 incomplete, 2 refused (bad prefix without trailing `.`, unknown unit). Record of the F1 regression:
the deferF F1 scope compares to 306 = REMOVED 72 / ADDED 58 / SIGCHG 176 (the display-name probe showed 304).

## 13. Navigation page (mention only)

```
python3 -I /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/gen_reading_order.py /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/_tools/READING_ORDER.src.md
# source: _tools/gen_reading_order.py (shebang `python3 -I`; SRC = argv[1]; writes READING_ORDER.md; asserts every target exists)
```
