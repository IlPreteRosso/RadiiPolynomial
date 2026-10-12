# Brief templates (copied from the campaign's briefs; placeholders in <ANGLE BRACKETS>)

Placeholders: `<UNIT>` launch-unit id (A1 … E4), `<CONTRACT_VERSION>` (campaign: "v1.2"; contract file
header says v1.2a), `<PIN>` library revision in the header field, `<FILE_LINES>` one line per file (format
below), `<DATE>`, `<GROUP>` re-pin group name. Every agent call pins the model (Opus for all four briefs
below), and the prompt names a PRIVATE scratchpad subdirectory for the worker.

The coordinator generates `<FILE_LINES>` from `_tools/launch_units.json` + `INVENTORY.md` line counts +
sidecar row counts (format copied from `_briefs/A1_DRAFTER.md`):
```
- <Dir>/<File>.lean (<lines> L, <rows> sidecar declarations) → <Dir>/<File>.tex ; sidecar _sidecar/<Dir>/<File>.sig.tsv
```

## 1. Drafter brief (verbatim from `_briefs/A1_DRAFTER.md`; all 26 wave briefs differ only in the unit and file lines)

```
# Launch unit <UNIT> — drafter brief (contract <CONTRACT_VERSION>, FROZEN for this wave)

Source root: /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial
Files (→ companions under /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/<same path>.tex):
<FILE_LINES>

Read first: CONTRACT.md (all of it; §6–§7 are the mechanics and rulings), the sidecars (effective hypotheses of record),
the house exemplars: the finished pilot companions exterior/Unformalization/Core/Bounds.tex and Core/Theorem.tex (copy their
structure: header, Setting with 'Book locators' and Who-is-who longtable, body sections, \leanline per environment, index longtable;
note they still carry a few v0-era evidence tags being repaired — follow CONTRACT §7.2 for tags), then the Lean sources in full.
Terminology: /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/UBIQUITOUS_LANGUAGE.md.
Architecture roles: /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/ARCHITECTURE.md.

Done = python3 _tools/build.py <each tex> prints OK for every file (no overfull>5pt), then
python3 _tools/resolve_external.py <each lean> (resolves Mathlib/LeanCert/library names you cite by a real #check; names it
reports STILL UNRESOLVED are misspelt — fix them, never allow-list them), then python3 _tools/gates.py <each lean> prints n/n pass.
Obstacles (unclear classical rendering, a proof route you cannot follow, a gate you cannot satisfy) go in your final report, not improvised around.
Do NOT run lake build, do NOT edit any .lean, tool, style or contract file, do NOT write outside your own companions' directories.
```

Header pin: the drafter writes `\unfheader{<source path>}{<PIN>}{…}{…}{…}`. In a re-pin campaign, `<PIN>` is
the OLD pin (the one `repin_finalize.py <old7>` will swap); otherwise the current library HEAD (7 chars).

### ADDENDUM for the next wave (§8 of CONTRACT.md; NOT in any on-disk brief yet — the wave briefs predate §8)
```
Rulings first: CONTRACT §7.1–7.70 is closed; follow every ruling; report only points no ruling covers.
Preconditions before build.py (CONTRACT §8):
(P1) read every Definition environment you wrote and move each property into a following Lemma/Fact with its own \leanline;
(P2) confirm every sentence that names what a proof uses against the proof text, and PROBE every substantive simp/rw route
     (§7.55) with simp? on a scratch file: (cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial && lake env lean <scratch>);
     keep the probe files under _records/<UNIT>/probes/;
(P3) check every description of an external definition on its whole domain (§7.58) before writing it;
(P4) find unused private declarations with `command /usr/bin/grep` before writing the §7.54 Remark.
Mechanics: zsh; `command /usr/bin/grep` (bare grep hangs); never a top-level cd (subshell form); scratch files only under <PRIVATE_SCRATCH>.
```

### Pilot variant (`_briefs/U32_Core.md`, the first unit; shorter, written before the per-wave form)
```
# Unit U32 — Core (PILOT)  — drafter brief
Files (source root …/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial): <File>.lean (<lines> L, <n> decl) → exterior/Unformalization/<Dir>/<File>.tex …
Contract: …/exterior/Unformalization/CONTRACT.md (read first, follow exactly).
House-style exemplar (voice, environments): …/exterior/tmp/foundation_note/ch1.tex and ch2.tex.
Smoke example of the macros: exterior/Unformalization/_tools/smoke/smoke.tex.
Terminology: …/UBIQUITOUS_LANGUAGE.md. Architecture: RadiiPolynomial/RadiiPolynomial/ARCHITECTURE.md.
Done = the four .tex build (python3 _tools/build.py Core/Theorem.tex …) and python3 _tools/gates.py Core/Theorem.lean … prints 4/4 pass.
Obstacles … go in your final report, not improvised around.
```
For a new library the pilot is the unit whose companions become the house exemplars named in §1.

## 2. Checker brief (verbatim from `_briefs/CHECKER_TEMPLATE.md`, then the unit line from `_briefs/E1_Core_CHECKER.md`)

```
# Checker brief (template; one Opus checker per launch unit, READ-ONLY except for its own MATRIX files)

Inputs: the unit's .tex files under exterior/Unformalization/<Dir>/ and their PDFs; the Lean sources under
/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial/<Dir>/; the ELABORATED sidecars
exterior/Unformalization/_sidecar/<Dir>/<File>.sig.tsv (visibility, kind, source span, authored/generated, FQN,
effective signature — the hypotheses of record); CONTRACT.md v1.

Deliverable 1 — per file, a per-declaration matrix written to exterior/Unformalization/_records/<unit>/MATRIX_<File>.md
(markdown table, one row per sidecar declaration, in sidecar order):
| FQN (span) | effective hypotheses (from the sidecar, abbreviated) | conclusion/definition in the companion matches? | proof route matches the Lean proof? (dependencies named) | exposition label (Def/Lem/Thm n.m or "folded into n.m" or "index only") | verdict (OK / ERROR / MAJOR / MINOR / MISSING) |

Checks per row:
1. PRESENCE — primary exposition exactly once (public authored); generated declarations covered by the parent and in the index.
2. HYPOTHESES — exactly the sidecar's effective binders: typeclass assumptions, explicit hypotheses, positivity,
   index ranges, finiteness; nothing generalized, added or dropped; visible no later than the claim. Watch:
   completeness vs normed space, real scalars vs general 𝕜, PosReal = positivity only, local instances, outParam fields.
3. CONCLUSION — the formula is the declaration's (direction of inequalities, which norm/space, order of application,
   exact constants and exponents; equivalent exact numerals only with the equality recorded).
4. PROOF ROUTE — the written proof follows the mathematical dependency route of the Lean proof (same material case
   split, auxiliary facts, instantiated theorems); every "unfold and compute" is really definitional; every simp
   that carries the argument names its substantive lemmas; every one-call proof states the cited theorem's conclusion,
   specialization and hypotheses; alternative proofs only in a tagged Remark.
5. LEAN LINE — \lean{name} byte-exact; \bookref copied from the docstring only.
6. EVIDENCE — every claim not proved in the file carries \evid{Lean: …} / \evid{Mathlib: …} / \evid{LeanCert: …} /
   \evid{not formalized here} (Remarks only); the trust-boundary sentence is present when the file uses native_decide/decide/axioms.
7. SETTING + WHO-IS-WHO — every persistent symbol has a row; the standing hypotheses match the variable blocks and are
   not stronger than the effective binders of the statements they introduce.
8. RENDERED PDF — read every page: clipping, overflow, broken Unicode in Lean names, orphaned headings, tables off-page.
9. STYLE — contract §3 bans; no \lean in headings or math; \( \) and \[ \] only; terminology per UBIQUITOUS_LANGUAGE.md.

Deliverable 2 — the reply text (not a file): a findings table with severity (ERROR = statement/proof wrong;
MAJOR = hypothesis or route deviation; MINOR = style/wording), file, an exact unique anchor (a verbatim substring
of the .tex), the problem, and the replacement text; then a one-line verdict per file: ACCEPT / FIX (n findings).
Do not edit any .tex, .lean or tool.
```
Unit line (form of `_briefs/E1_Core_CHECKER.md`):
```
# Checker brief — launch unit <UNIT> (<Dir family>)
Template: _briefs/CHECKER_TEMPLATE.md (follow it exactly). Contract: CONTRACT.md <CONTRACT_VERSION> (sha <8 hex>…).
Files: <File list> — tex + pdf under exterior/Unformalization/<Dir>/, sources under RadiiPolynomial/RadiiPolynomial/RadiiPolynomial/<Dir>/,
sidecars under _sidecar/<Dir>/*.sig.tsv. Matrices go to _records/<UNIT>/MATRIX_<File>.md.
<FOCUS ITEMS from the drafter's report (the campaign recorded them in PROGRESS.md / the Agent prompt, not in a file)>
```

### ADDENDUM (the template on disk predates these; add them to the prompt)
```
Severity scale of record (CONTRACT §7.5): ERROR · MAJOR (incl. an extra conclusion inside a statement environment the
declaration does not prove) · EVIDENCE (missing, unnamed or ill-formed evidence tag) · MINOR. Every class is fixed before the freeze.
Contract version: the current CONTRACT.md (§7.1–7.70, §8). Evidence form: \evidl{<tag>}{<name>} (§7.2), not \evid{Mathlib: …}.
Rulings first: raise only points no §7 ruling covers; cite the ruling number when a finding applies one.
Probes: re-probe a SAMPLE of the drafter's probes in _records/<UNIT>/probes/ (§8 P2); recipe §7.36 / §7.53; pp.explicit for
local-instance files (§7.32). Run gates.py yourself (read-only).
Start your reply with the line "Checker <UNIT>" and end it with a "VERIFIED" block, so handback_extract.py can find it.
```
(The last line is a suggestion derived from `handback_extract.py`'s marker logic; the campaign's markers are not recorded.)

## 3. Re-pin drafter brief (parameterized from `_records/repin_20261011/BRIEF_REPIN.md`)

```
# Companion RE-PIN — worker brief (<DATE>; user: "<the user's words>")

The library changed after the companions were frozen at <OLD7>. The companions must describe the CURRENT source. Nothing else
about them changes: structure, environments, theorem statements, labels, tags and evidence stay as they are unless the library
change makes them false.

PATHS. Library sources: /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial/ (Lake root one level up;
oleans CURRENT). Companions: /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization/<same path>.tex. Sidecars
(effective hypotheses of record, REGENERATED <DATE>): _sidecar/<path>.sig.tsv. Contract: exterior/Unformalization/CONTRACT.md
(§7.1–7.70 are the rulings; §7.54 private helpers, §7.57 history, §7.58 external descriptions). Pre-edit snapshot of every
companion: _records/repin_<DATE>/before/<path>.tex (do not edit; the checker diffs against it).

WHAT CHANGED IN THE LIBRARY (all of it)
1. <Docstring edits: "Your REPORT file (named in your task) lists every edit as `<file>:<line> <decl> | was | now | answers remark:
   tex line N`. Each "answers remark: tex line N" points at the companion paragraph (in the PRE-EDIT snapshot's line numbering) that
   recorded the old docstring's mismatch. "own finding" edits have no companion paragraph; check whether the companion mentions that
   docstring anyway.">
2. <Code changes, one lettered item per site: file, old form, new form, line shifts ("everything after it moved up 6 lines")>
3. <Other tree changes (deleted/added files), "no companion mentions them, but check">

YOUR JOB, per companion in your list
(a) Docstring Remarks. [verbatim from BRIEF_REPIN: remove a mismatch sentence that is now fixed; remove an emptied
    \begin{remark}[Docstring]…\end{remark} cleanly, keeping the following \leanline; keep still-accurate mathematics or
    intended-use reading; "Never write history ("the docstring used to say…"): §7.57"; re-read rewritten docstrings.]
(b) Code changes. <per-site instructions: which companion, which rows/remarks/expressions change>
(c) Line references. Every "(lines a--b)" / "Private steps (lines a--b)" / "(line n)" in your companions is re-derived from the
    CURRENT source (`command /usr/bin/grep -n` — never bare grep).
(d) Sidecar. If a sidecar row of your file changed (effective hypotheses), the companion's hypothesis text for that declaration
    follows the sidecar.
(e) Nothing else. No restyling, no new sections, no reordering, no change of theorem statements or numbered environments beyond
    what the library change forces, no edit to the header's revision field `{<OLD7>}` (the coordinator swaps it when the user commits).

MECHANICS
- Build: `(cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/Unformalization && python3 _tools/build.py Dir/File.tex)` must
  print OK for every edited companion; then `python3 _tools/resolve_external.py Dir/File.lean` if you cited a new external name;
  then `python3 _tools/gates.py Dir/File.lean` must print PASS (a `NOTE G10` line is advisory). Never `lake build`; `lake env lean`
  only for read-only probes on scratch files under your private scratchpad subdirectory.
- Never edit a .lean file, a tool, the style file, the contract, the sidecars, or the snapshot.
- Never bare `grep`; never top-level `cd`; zsh.

REPORT (plain text, this structure)
  COMPANIONS: n edited / m in list (unedited ones named, with the reason: no library change touched them).
  EDITS: per companion, one line per paragraph changed: `<tex path>:<snapshot line> | removed|rewritten | <gist> | answers REPORT
  edit <file>:<line> or "code change 2a/2b/2c" or "line ref"`.
  LINE REFS: every (lines a--b) you re-derived: old → new, or "unchanged".
  GATES: `build.py OK` and `gates.py PASS` per edited companion (exact output lines).
  OBSTACLES: anything the library change makes false that you could not fix within these rules.
```
Task line per worker: "Group <GROUP>: companions <list>; your REPORT file: _records/docstring_sweep/REPORT_<GROUP>.md; write your
report to _records/repin_<DATE>/REPIN_<GROUP>.md" (file naming as on disk; the exact task wording is not recorded).
If the change is NOT a docstring sweep, item 1 becomes the per-file list from R2 of the runbook (e.g. `changed_since_freeze.py`
output + `git diff -- <file>` per file) — UNSETTLED: not yet exercised.

## 4. Re-pin checker brief (verbatim from `_records/repin_20261011/CHECK_REPIN.md`, dates parameterized)

```
# Companion RE-PIN — checker brief (read-only; <DATE>)

You check one group of re-pinned companions. You edit NOTHING. Your output is a findings list.

INPUTS
- Brief the drafter followed: _records/repin_<DATE>/BRIEF_REPIN.md (read it first; its rules are the contract of this check).
- Pre-edit snapshot: _records/repin_<DATE>/before/<path>.tex. Current companion: exterior/Unformalization/<path>.tex. Diff them
  (`diff -u` per file) — the hunks are what you check.
- The drafter's report for your group: _records/repin_<DATE>/REPIN_<Group>.md. The library-change report it worked from:
  _records/docstring_sweep/REPORT_<Group>.md.
- Library sources (current): /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial/RadiiPolynomial/. Sidecars:
  _sidecar/<path>.sig.tsv (regenerated <DATE>).

CHECKS, per companion of your group
C1 Every hunk is within the brief's scope: Remark/paragraph text about docstrings, line references, the code-change sites, hypothesis
   text that follows a changed sidecar row. A hunk that changes a theorem statement, a numbered environment's mathematics, a label,
   an evidence tag, structure or the header revision field is a MAJOR finding.
C2 Every rewritten paragraph is TRUE at the current source: open the current docstring/declaration it describes and verify each claim
   (names exist — `command /usr/bin/grep -rn`, never bare grep; what the file proves vs. what it says; hypotheses). A false or
   unverifiable sentence is MAJOR; an inexact one MINOR.
C3 Nothing is left behind: for every REPORT edit pointing at a paragraph of your group's companions (and for the code changes where
   they apply), confirm the companion no longer records the fixed mismatch. Also grep the current companions for "docstring" and read
   each hit: any paragraph that still describes a docstring must match the CURRENT docstring text. Stale = MAJOR.
C4 Line references: every "(lines a--b)"/"(line n)" in the current companions points at the right lines of the current source (check
   the content at those lines). Wrong = MAJOR.
C5 History: no sentence of the form "the docstring used to…/formerly…/was corrected" (§7.57). = MINOR.
C6 Build evidence: the PDF of each edited companion is newer than its .tex, `python3 _tools/gates.py <lean>` passes when you run it
   yourself (run it; it is read-only).
C7 Removed environments: where a whole remark was removed, the surrounding `\leanline`s and blank lines are intact and the
   environment before/after is unbroken (read the tex around the hunk).

REPORT (plain text)
  GROUP: <name>; companions diffed: n; hunks: m.
  FINDINGS: one line each: `SEVERITY | <tex path>:<current line> | <what is wrong> | <evidence: source line / grep result> |
  <replacement text if obvious>`; MAJOR first. Or "none".
  VERIFIED: one line per companion: `<path> | hunks k | C1 ok | C2 ok | C3 ok | C4 ok (refs checked: …) | gates PASS`.
  OBSTACLES: anything you could not verify, or "none".
Mechanics: zsh; `command /usr/bin/grep`; never top-level `cd` (subshell ok); scratch files only under a private scratchpad
subdirectory; `lake env lean` only on scratch probes.
```
Output of record: `_records/repin_<DATE>/CHECK_<Group>.md`. MINORs were applied by the coordinator (2026-10-11: 7).

## 5. Library-side docstring sweep brief (pointer)

`_records/docstring_sweep/BRIEF.md` (Opus workers, library side, only when the user unfreezes the library): edit ONLY docstrings and
comments so each is a true description of what the file declares and proves; never change code to match a docstring; verify each
edited file with `(cd <Lake root> && lake env lean RadiiPolynomial/<Path>.lean)`; REPORT lines
`<file>:<line> <decl> | was: … | now: … | answers remark: <tex line n> or "own finding"` — these REPORT files are the change list the
re-pin drafters consume. Input lists: `_tools/docstring_remarks.py` → `REMARKS_<TopDir>.md`.
