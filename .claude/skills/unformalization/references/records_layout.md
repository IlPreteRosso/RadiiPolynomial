# Records layout (`exterior/Unformalization/`, as on disk 2026-10-11)

## Top level
- `README.md` (8 lines: what the dir is, the four commands, pin), `CONTRACT.md`, `API_FILES.txt`, `INVENTORY.md`,
  `UNITS.md` (tool-generated), `LAUNCH_UNITS.md` (hand-merged), `READING_ORDER.md` (navigation; `gen_reading_order.py`).
- `<Dir>/<File>.tex|.pdf|.log|.aux|.out|.synctex.gz` mirroring the library (artefacts never versioned; the whole
  `exterior/` tree is local-only, not in git).
- `_common/unformalization.sty`, `_tools/` (scripts, `launch_units.json`, `units.json`, `fixtures/`, `smoke/`),
  `_briefs/` (`<UNIT>_DRAFTER.md` ×25, `U32_Core.md` pilot, `CHECKER_TEMPLATE.md`, `E1_Core_CHECKER.md`).

## `_sidecar/`
- `<Dir>/<File>.sig.tsv` — one row per declaration of the compiled module, sorted by span start (§7.9), tab-separated:
  `visibility` (public|private) · `kind` (theorem, def, axiom, opaque, inductive, structure, ctor, quot, instance) ·
  `span` (`start-end` lines, or `-`) · `authored|generated` (authored = the last name component matches a declaration line of
  the source) · `FQN` (private names in user form) · elaborated signature (`ppSignature`, one line). Filtered out: internal names,
  `_proof_`, `match_`, `sizeOf`, `noConfusion`, `below`, `brecOn`, `recOn`, `casesOn`, `injEq`, recursors, equation lemmas
  (`eq_<digits>`, `eq_def`, `eq_unfold`). Example row (Core/Bounds):
  `public	def	35-37	authored	RadiiPolynomial.X	RadiiPolynomial.X.{u_2} (Seq : RadiiPolynomial.PosReal → Type u_2) (ν : RadiiPolynomial.PosReal) (L : ℕ) : Type u_2`
- `ALL_FQNS.txt` — every FQN of every sidecar of the LIVE set `_sidecar/**/*.sig.tsv` (3311 lines on 2026-10-11); names
  only in `_sidecar_prev/` never enter it.
- `EXTERNAL_RESOLVED.txt` — `name<TAB>module` from real `#check`s (983 rows on 2026-10-11), e.g.
  `AddMonoidAlgebra.coeff_add	Mathlib.Algebra.MonoidAlgebra.Defs`; `EXTERNAL_RESOLVED.txt.lock` = the flock file.
  Single registry for Mathlib, LeanCert, Lean core and cross-module library names (§7.64); never edited by hand.

## Sidecar generations (`signatures.py`; CONSENSUS_sidecar_archive A2, 2026-10-14)
- `_sidecar_prev/` — sibling of `_sidecar/` (never beneath it: `signatures.py`, `gates.py` and `finalize_manifest.py`
  walk `_sidecar/` only): the COMPLETE previous successful live set (`<Dir>/<File>.sig.tsv` + `ALL_FQNS.txt`) captured by
  the last publication, with `PREV_MANIFEST.json` (`schema` sidecar-prev/1, `captured_by_run`, `captured_at`,
  `replacing_scope`, `replaced_files`, `files` rel → sha256, `ALL_FQNS.txt` sha256, `complete`: true). One generation,
  disposable; a review that needs it pins a copy/hash in its record. `--recover` also restores `_sidecar_prev/` to the
  generation preceding the failed run.
- `_sidecar_stage_<run>/` — staging of one extraction (removed after publication or failure).
- `_sidecar_INCOMPLETE.json` — present only after an interrupted publication (`run_id`, `phase` rotate|publish, `scope`,
  `files`, `stage`); `freeze.py`, `finalize_manifest.py`, `semdiff.py` (live side), `gates.py` (G0 failure) and
  `signatures.py` refuse until `signatures.py --recover` restores the previous generation.
- `_sidecar.lock` — the flock file of the single sidecar writer (`signatures.py` publication, `freeze.py`).

## `_records/<UNIT>/` (26 directories A1 … E4; file counts across all units in brackets)
| file | written by | content |
|---|---|---|
| `MATRIX_<File>.md` [129] | checker | header: inputs (tex lines, pages read and how, sidecar rows, source @ pin, instantiated declarations read), gates result, probes run and their results; then the table `FQN (span) \| effective hypotheses \| conclusion matches? \| proof route matches? \| exposition label \| verdict` in sidecar order; some end with a findings section |
| `FINDINGS_checker_round1.md` [26] | coordinator | title line; verdicts per file with severity counts; `RULING(S)` (usually "apply all n as written" + coordinator items + new §7 rulings + contract points answered); then the checker hand-back verbatim (saved with `handback_extract.py`), findings table `ID \| Sev \| File \| Anchor (verbatim) \| Problem \| Replacement` or a per-file list |
| `MANIFEST.json` [26] | `freeze.py` | fields below |
| `SHA256SUMS` [26] | `freeze.py` | `<sha256>  <Dir/File>.tex|.pdf|.log`, `<sha256>  lean:<rel>`, `<sha256>  sidecar:<Dir/File>.sig.tsv` |
| `ALL_FQNS.frozen.txt`, `EXTERNAL_RESOLVED.frozen.txt` [26 each] | `freeze.py` | registry copies at freeze time (Codex E1 acceptance note: shared registries drift) |
| `CONTRACT.frozen.md`, `unformalization.frozen.sty` [26 each] | `freeze.py` | contract and style copies (Codex B9) |
| `sidecar/<sha256>.sig.tsv` | `freeze.py` (since 2026-10-14, A1) | immutable, content-addressed copy of the exact sidecar bytes a MANIFEST recorded; written BEFORE the manifest; reused only after byte verification; never overwritten (a differing object = REFUSED); never rolled back by `repin_finalize.py --restore`; objects of an aborted freeze/finalization stay as non-current evidence |
| `sidecar/BACKFILL.json` | `freeze.py --backfill` | digest → {rel, manifest, source, at, label}: objects stored later for a manifest WITHOUT archived content, only from bytes whose sha256 equals the recorded sidecar digest; the manifest itself is not rewritten |
| `MANIFEST_round<k>_<sha8>.json`, `MANIFEST_accepted_<sha8>.json` [7, in E1 B9 D2 E4] | coordinator (rename before re-freeze) | the manifests Codex audit rounds referred to; `<sha8>` = first 8 hex of the MANIFEST's sha256 |
| `probes/` [0] | drafter (§8 P2) | prescribed for the next wave; none exist yet |
Fixer dispositions have no file of their own (UNSETTLED; they lived in the fixer's hand-back and the PROGRESS "fixes" cell).

### MANIFEST.json fields (`freeze.py`)
`unit`; `frozen_at` (UTC ISO); `library_head` (full sha of the Lake root HEAD); `note` ("source hashes + existing oleans; not a
fresh compilation or axiom audit"); `library_source_porcelain` (`git status --porcelain -- RadiiPolynomial/`; must be "" at a
clean freeze); `lean_toolchain` (e.g. `leanprover/lean4:v4.34.1`); `dependencies` (name → rev from `lake-manifest.json`: LeanCert,
mathlib, checkdecls, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli); `contract_sha256`;
`style_sha256`; `tools` (sha of build.py, gates.py, signatures.py, freeze.py, semdiff.py — NOT resolve_external.py/repin_finalize.py);
`build_command`; `sidecar_extraction`; `registries` (sha of ALL_FQNS.txt, EXTERNAL_RESOLVED.txt); `checker_records` (sha of every
`.md` in the unit dir except `*.frozen.*` and `MANIFEST*`); `files` → per `.lean` rel path: `lean`, `sidecar`, `olean` (or null),
`tex`, `pdf`, `log` sha256s, and (freezes since 2026-10-14) `sidecar_archive` = `sidecar/<sha256 of the sidecar>.sig.tsv`.
Archive resolution (`semdiff.resolve_archive`) always verifies the digest: `ARCHIVED` (field present, object verified),
`BACKFILL` (no field; a digest-matching object, labelled), else `BASELINE_UNAVAILABLE` (no field and no object, object
missing, or digest mismatch) — counts of a sidecar diff are then unknown, never zero, and the older freeze stays valid.
Hand-check after every batch freeze: `library_head` = intended commit, `library_source_porcelain` = "".

## `_records/PROGRESS.md` (campaign tracker; "rewritten at every step")
Table columns: `unit | files | drafter | checker | fixes | freeze | Codex audit`. Cell vocabulary as used: drafter `DONE (n/n; P pp)`;
checker `DONE: 0 ERROR/1 MAJOR (S1) + 20` or `DONE + recheck: ACCEPT ×3`; fixes `DONE (23 + 2 recheck residuals applied by the
coordinator; gates 3/3)`; freeze `FROZEN <sha8>` or `recheck ACCEPT ×n → FROZEN`; Codex `**ACCEPTED** …-<bus id tail>` /
`not a sample` / `Codex expansion candidate — …`. Below the table, dated free-text lines: contract state, deferred items, HALT
(rate limit: what was running, what to relaunch), pending contract suggestions, CAMPAIGN COMPLETE, FOLLOW-UP, DOCSTRING SWEEP DONE,
RE-PIN STARTED / CONTENT DONE / FROZEN — each with counts, record paths and the user's words that triggered it.

## `_records/HANDOFF_<YYYYMMDD>.md` (self-contained re-entry for another session/account)
Sections of `HANDOFF_20261011.md`: header line (seat, time, "Nothing is running; no agent, no Codex request, no watcher") ·
§1 What exists (dir contents, tools, records; library state: HEAD, working-tree modifications by category, build result) ·
§2 The ONE pending step (exact command, what it does, who may run it, what to hand-check, what to do on failure) ·
§3 Items the user may still decide (reported, not done) · §4 Standing rules that bound this seat (tiers, git, lake, zsh, bus,
classifier traps) · §5 Bus seat (alias, peer, open requests, re-seat procedure).

## `_records/repin_<YYYYMMDD>/` (one per re-pin)
`BRIEF_REPIN.md` (drafter brief), `CHECK_REPIN.md` (checker brief), `REPIN_<Group>.md` (7 drafter reports: COMPANIONS / EDITS /
LINE REFS / GATES / OBSTACLES), `CHECK_<Group>.md` (7 checker reports: GROUP / FINDINGS / VERIFIED / OBSTACLES), `before/<Dir>/<File>.tex`
(snapshot of all 129 companions before editing), `ALL_FQNS.before.txt` (registry before sidecar regeneration).
Groups 2026-10-11: Algebra, Analysis1, Analysis2, Applications1, Applications2, Certification, CoreOperatorsTactic.

## `_records/docstring_sweep/` (library side, feeds the re-pin)
`BRIEF.md` (worker brief), `REMARKS_<TopDir>.md` (from `docstring_remarks.py`: per file, `[tex line N] <paragraph>`),
`REPORT_<Group>.md` (FILES / EDITS `<file>:<line> <decl> | was | now | answers remark` / NO CHANGE / CHECKS / OBSTACLES),
`GLOSSARY_FIXES.md` (replacement text for UBIQUITOUS_LANGUAGE.md when the harness refused the edit).

## `_records/finalize_<C7>_<UTC>/` (`repin_finalize.py --plan`, live run)
`PLAN.json`, `before/` (tex/pdf/log of every touched row and the FROZEN_FILES of every unit to freeze, `before/SHA256SUMS`),
`journal.jsonl` (start · snapshot with `present`/`absent` and `archive` = {units, objects [path, sha256]} · per-row
begin/end · freeze · fail|done · restore/restored with the archive report).

## Other
`_records/CONTRACT_v0_fc5bb6e5.md` (v0 contract kept for history). Codex review artefacts live on the agents bus
(`tmp/agents_bus/checkpoints/codex-paper/UNFORMALIZATION_*`), e.g. the contract review `…/UNFORMALIZATION_contract_review_20261010/REVIEW.md`
and the E1 acceptance `…/UNFORMALIZATION_E1_recheck_20261010/` (paths from the memory note `project_unformalization.md`).
Memory: `~/.claude/projects/-Users-ilpreterosso-VSCode-Lean-RadiiPolynomial/memory/project_unformalization.md` is updated at each
milestone (COMPLETE, FOLLOW-UP, RE-PIN …) with the state of record and the lessons.
