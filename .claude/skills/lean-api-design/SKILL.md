---
name: lean-api-design
description: >-
  Process skill for Lean 4 formalization work with Mathlib — the unit pipeline (brief → prover → critic → freeze → review → insights → install), the worker-assignment table (which task goes to which model or harness), peer harnesses (Antigravity, Gemini Pro consults, Codex on the bus) with their friction logs, the escalation ladder to Aristotle, and the research-level-gap ladder. Use for any bounded Lean proof unit, review, scouting or research campaign, in any Lean project; project-specific API rules live in the project's own skill (RadiiPolynomial: radii-poly-api-design).
---

# Lean API Design — process

This skill holds the harness-neutral PROCESS of formalization work: how a unit is briefed,
proved, criticised, frozen, reviewed, harvested and installed; which model or peer harness does
which category of task; how a research-level gap is attacked; how Aristotle is used. Project API
rules (layering, boundaries, typeclasses, certificates, verification) live in the project's own
skill — RadiiPolynomial: `radii-poly-api-design` (split 2026-09-20); load both.

Standing rules that apply everywhere (user, 2026-09-13 → 2026-09-20): coordinators design and set
bounded goals, cheaper models do the mechanical work; pin the model (and effort, D102) on every
call; ≤ 5 agents in flight, sequential cohorts; never kill a fired worker; worker output is
non-final and the coordinator holds the fidelity gate of every marked statement; insights and
errata are harvested per unit before install; a bash script is never edited while an instance
runs.

## Worker Assignment

Task category → tier (standing rule, harness-neutral, 2026-09-20; cross-harness rows D102):
- Coordination, design, route notes, bounded-goal briefs (final form), fidelity GATE of
  any new or altered marked statement, install decisions, ledger truth: the coordinator
  (Fable). Never delegated; worker output is input to it. The coordinator also takes, on
  purpose and never as a fleet, what needs the best model: final gate-keeping review,
  important quality checks, particularly hard tasks (user 2026-09-22).
- Cross-harness tiers (D102, agreed with Codex; a role map by capability class, not a measured
  equivalence): Fable 5.1 = GPT-6 Astra (coordinators); Opus 5.5 = `gpt-6-sol` high, xhigh for
  a named hard unit (proof/critic units, designer + critic consults, source-first milestone and
  consult reviews); Sonnet 5.5 = `gpt-6-luna` medium, high if needed (mechanical tier).
  Limits: Claude ≤ 5 workers in flight per workflow; Codex FOUR active agents including itself
  (≤ 3 children, normally two substantive workers + one spare); sequential cohorts.
- Proof units (lift or infra block, one bounded brief, sorry-free target): opus prover,
  then opus adversarial critic (own compile, per-declaration axioms, marker/header diff).
  Fable as prover only for a big-token unit the coordinator owns (sorry-closing pass,
  research-pilot skeleton) — at most one at a time, never a fleet (D102: a coordinator-tier
  child is a purposeful exception for ONE named hard unit).
- Mechanical stages and chores (freeze/MANIFEST, importer shadow check, INSIGHTS draft,
  inventories, brief DRAFTS, scouting, fidelity SWEEPS, organising): the MECHANICAL TIER,
  non-final — `sonnet`; until Sonnet 5.5 ships it runs on `opus` (Opus 5.5, user
  2026-09-22), workflow freeze stages included; revert here and in the workflow scripts.
  Deterministic scripts are preferred for pure hashing (D102); "mechanical tier" elsewhere in
  this skill means this row.
- Bounded Lean review with `#check` probes on a comment-stripped freeze: Antigravity
  Flash 3.8 high (non-final; blocks ≤ ~1500 lines); a second reviewer is never a gate.
- Prose mathematics consult (route comparison, pitfalls, no formalization): Gemini 3.1 Pro
  high, one-shot; consolidated by the coordinator into ONE route note; every "missing in
  Mathlib" claim grep-verified before it enters a brief.
- Research-level gap: the ladder of "Research-Level Gaps" (route note → skeleton →
  opus/Fable/Aristotle grind → golf → canonical install → book fill-in on the user's call).
- Judgment continuity across days (adversarial peer, protocol partner): exactly one
  persistent peer (Codex on the bus) besides the coordinator; workers are disposable and
  all state lives in the brief, the freeze and the ledger.
Tiering is by difficulty AND by quota balance (re-checked at each quota report).

### Ownership → roles by stage (user decision 2026-09-24; design note ledger/bus/claude_units/DESIGN-ROLES-20260924/DESIGN.md)

There is no chapter ownership. Two roles, split by STAGE, with defaults for every chapter and per-item exceptions:
- AUTHOR (default: the coordinator's harness, Claude): scout → prover → critic → freeze → coordinator gate → INSIGHTS
  → install; writes its census files; applies approved errata to the edition under a decision line; owns the module
  directories.
- REVIEWER (default: the peer, Codex): the independent fidelity read (ACCEPTED lines bound to the Lean closure and the
  source contract); rules on readings and modelling contracts; approves §1.8 offers (proposer ≠ approver). The
  reviewer never authors the item it reviews.
- EXCEPTION per item: when the peer authors a face, the per-item override (author codex / reviewer claude) is proposed
  by the author with its C0 in ONE message and acknowledged in ONE reply; no batch, no separate adoption generation.
- HISTORY: a previous reviewer's ACCEPTED line keeps closing an item while its closure hash is unchanged (status.py
  reviewer-history rule); a changed closure goes to the current reviewer. Authorship history lives in ISSUES.md and
  module docstrings; the registry's `author` is a role label.
- MODES (user ruling 2026-09-24): roles by stage is the DEFAULT; split ownership (per chapter or section rows in the
  same roles table) is re-enabled whenever both coordinators author in parallel; a role flip (peer authors, coordinator
  reviews) is an OPTIONAL AGENDA item offered as a suggestion when the peer has budget — never a one-way door. The
  reviewer-history rule keeps every switch safe for existing closures.
- Packets: reply budgets state hard limits (receipt-first, reply length, no recompiles, input-sha256) and give the
  worker count as a SUGGESTION ("suggested ≤ k Sol agents, your call").
- Friction rules (same decision): one done notice per unit, in-flux notices only for edits of existing modules and
  protected transactions; mirror scratchpad artefacts into the ledger, never bus messages; build a tool only when it
  will run at least three times; done_notice.py writes the ISSUES line and the checkpoint entry from one record.

## Unit Pipeline

Unit pipeline (book formalization; 2026-09-20, amended 2026-09-22): brief (scout draft →
coordinator-verified args) → prover (opus; Fable only for a coordinator-owned big-token
unit) → adversarial critic (opus, own compile + per-declaration `#print axioms`,
marker/header fidelity; one fix round) → freeze (mechanical tier; MANIFEST, shadow importer
check) → Antigravity review of the comment-stripped freeze, the coordinator's call per unit
(non-final; ≤ ~1500-line blocks) → coordinator fidelity gate, prose-only v2 when needed
(comment-stripped code byte-identical, recompiled: `prose_v2.py`, `promote_v2.py`) →
INSIGHTS.md in the unit dir (API_INSIGHTS lines, STRUCTURE_INSIGHTS lines, errata screen
`none` or a candidate; drafted by a mechanical-tier chore from the prover, critic and review
reports, every line verified by the coordinator against its SOURCE pointer) → install
(`chain_generic2.sh` → `install_infra.sh`: in-flux notice, `install_unit.py`, audit, status,
`harvest_append.py`; durable copies + README in `ReferenceBook/ledger/bus/claude_tools/`) →
ISSUES line, done notice, NEXT + checkpoint. The insights and errata step is part of the main
task (user 2026-09-20): the installer refuses a unit without INSIGHTS.md, and an errata
candidate stops the install until the CHARTER §1.8 consult; only the final narrative report
is deferred.

From TOOL-EFF-20260922 — ACTIVATED only after its frozen scripts pass the Codex cross-audit AND the
accepted equivalence trial (installation alone is not the validation); until then the current
pipeline above applies (D103, agreed with Codex): the freeze is a deterministic fail-closed script (`freeze.py`: file/module sha, compile
result, per-declaration axioms, declaration and import sets, base-prefix comparison, hashes; raw
evidence kept; a boolean is never a gate), not a model stage; prose/provenance lint and the
coordinator's prose edits come BEFORE the freeze (provenance category and route in the brief);
the critic is two-phase (own compile, source/type and marker assessment recorded BEFORE it reads
the prover's report); installs run in generations of ≤ 3 validated units (disjoint, or one
ordered dependent chain): one record, one audit/status/harvest episode, one in-flux and one done
notice, abort on drift, no partial CLOSED; per-item fidelity/C1 outcomes are kept inside a batch
delivery, a post-freeze source or contract change is still notified explicitly, and compile/axiom
evidence is reused only under exact local source, dependency and toolchain fingerprints.

Edition application waves (book gap fill-in, 2026-09-24; user rule: every repeated ledger/edition
operation is a Python QC-gate script, improved after its shortcomings surface with Codex, never a
hand edit — memory `feedback_script_qc_gates`): drafting workflow per chapter (Opus drafter →
adversarial critic → fix → re-critic → minors; ORIGINAL blocks byte-identical to the live chapter,
Lean route per item, deviations declared) → coordinator gate (ORIGINAL blocks by script, Lean
headers re-read for every declared deviation) → ONE COV fidelity packet to Codex (manifest of
packet shas as input-sha256; verdicts ACCEPT/CHANGES per unit, deviations ratified) → packaging
workflow (packager + validator per chapter; exact-bytes offers for `apply_errata_offer.py`,
sequenced offers validated in a sandbox after the previous offer + skeleton regeneration;
numbered pairs only over proof_only/accepted records under D-i, applied records take the
contextual proof-insertion shape of D132) → ONE exact-bytes approval packet per wave (manifest of
OFFER.json shas) → `ledger/bus/claude_tools/apply_wave.py <plan> --apply` (plan = decisions +
per-entry approval ids + mirror entries; `precheck_plan.py` and `--mirror-test` first; the tool
writes decision lines, applies with the PROMOTED applier, regenerates the census between
sequenced offers, operation-4 rebinds, ONE per-chapter EDITORIAL_NOTES mirror pass on the FINAL
chapter (anchors tokenised first, stale anchors resolved by paragraph body, same-text gaps
monotonic, multi-line macros), ONE status, latexmk) → render read (pdftotext) → DONE with hashes
and the full-paragraph mirror diff → Codex's C1 report offer mirrored byte-exact → ONE status.
Applier changes are staged rounds (fixer → adversarial critic on copies with live defaults
redirected → Codex bounded read → byte-copy promotion with PROMOTION.json + backup); a wave is
applied under the tool its approval packet names.

Install-pipeline traps (2026-09-20, 19 installs): (a) an EXTENSION or lift unit's manifest
carries the target's current sha as `canonical_sha256` or `base_sha256` (`install_unit.py`
accepts either since 2026-09-21); with neither, the installer takes the new-module path and
refuses because the target exists; (b) the lake-build lock is held transiently by workflow
critic/freeze stages: install only through `install_infra.sh`, which waits for a quiet tree;
(c) one heading per insights section (`## API_INSIGHTS`, `## STRUCTURE_INSIGHTS`,
`## ERRATA`) — a repeated heading must accumulate, not overwrite; (d) stamp every ledger and
manifest line from `date -u` (hand-written stamps drifted ~35 min twice); (e) when scoping a
review to a line range, compute the range with an exact section-name grep and check the
prompt file is non-empty before launching — a name that prefixes another section returns
two lines, breaks the arithmetic, and `agy` still launches on an empty prompt.

## Peer Harnesses

A second general-purpose model joins this work as a **bounded worker**: one headless
invocation per goal, launched and checked by the coordinator. (A **peer** seat on the
`agents-bus` skill, which stays harness-neutral and is not amended here, is reserved for a
harness that runs its own long-horizon agenda; Codex holds that seat today.) Aristotle is
neither; it is a dedicated prover, not a general model, and has its own course below.

What a worker is for (user 2026-09-19): a second perspective and a double quality check on
something the coordinator has drafted; discussion and brainstorming before a unit starts;
and chores with no immediate substantial effect on the project that are useful as an
intermediate step or a reference: organizing, scouting, drafting an API suggestion from an
existing formalization, cataloguing lemmas, comparing candidate statements. Everything a
worker returns is **non-final**: a reference the coordinator reads, not a change that lands.
The coordinator guards the quality bar for Lean code, API orientation and library layering
(the project's API skill; RadiiPolynomial: `radii-poly-api-design`), and only the coordinator,
or a Fable/Opus proof unit it owns, writes what gets committed. Goals fed to a worker are
bounded, chopped down, specific and non-final: one unit, named targets, the existing
declarations to use, what done looks like, where to report obstacles instead of improvising
around them. Tiers: Worker Assignment; the tiering rules in the global instructions apply
unchanged (open conflict LAD-5, user decides).

Before a harness is used in either role, record its adapter in this section: one entry per
CLI, in the shape of the Antigravity entry. An adapter names, in this order:

1. **Binary and version.** The command, where it installs, how to read its version. The
   user runs installers and sign-in; the assistant never enters credentials or accepts
   terms, and never runs a downloaded installer from a tool shell.
2. **Headless form.** The exact non-interactive call: prompt flag, working directory (always
   the nested checkout), model pin, effort, structured output, timeout, permission mode.
   A worker call uses structured output with a schema and a wall-clock timeout; it never
   runs with auto-approval on the checkout root.
3. **What it reads.** Context files, skill directories, MCP configs. Mirror this skill and
   `lean-golfing` into its skill directory as symlinks to the canonical copy; do not fork.
4. **What leaves the machine.** For a cloud model everything it reads is uploaded: the
   Aristotle data rule applies verbatim (library source yes; `docs/reference_book/`, the
   rewrite-edition `.tex`, `tmp/` and any text derived from the book no, unless the user
   has set the consent variable for that run). Launch from a shell that has not sourced
   `~/.zshrc`, so `ARISTOTLE_API_KEY` and other secrets are not in its environment; check
   with `env | grep -c -i key` printing 0 in the launching shell. Turn the harness's own
   telemetry off in its settings.
5. **Bus activation.** Which lifecycle hook the harness offers for the cue route, and the
   config file it lives in. The hook itself is written per the bus skill's activation
   section; this skill only records the harness-side event name.
6. **Trust surface.** Every declaration a peer or worker returns goes through the project
   skill's Verification section and the Aristotle stage-2 gate: rebuild, per-declaration
   `#print axioms`, byte-identical statement, no upward imports, provenance under
   `tmp/<task>/checks/`. Then the stage-3 golf pass, since general models also produce
   search-shaped proofs. Nothing a cloud peer proved enters EI training or the local prove
   rate unless its statement leaves the evaluation pool first.
7. **Probe.** A recorded first run: date, the statement used, wall time, whether the proof
   compiled on the pinned toolchain with standard axioms. Until a probe is recorded the
   adapter is a draft and the harness takes no owned proof unit.

### Antigravity CLI (Google, `agy`)

Chosen 2026-09-19 as the non-Codex peer: independent quota pool, the other top general
model for Lean proof generation in the June 2026 formalization evaluation, hooks and skills
kept from Gemini CLI, which it replaced on 2026-06-18.

1. Install `curl -fsSL https://antigravity.google/cli/install.sh | bash` (user-run; sha512
   verified, lands at `~/.local/bin/agy`, then `agy install` edits the shell rc for PATH).
   First run of `agy` signs in through the browser. `agy --version`; `agy changelog`.
   Global settings `~/.gemini/antigravity-cli/settings.json`.
   Sign-in and `agy update` rewrite `settings.json`: re-check the allow rules after either.
2. Worker call. Headless mode does not take the invoking cwd as its workspace: without
   `--add-dir` the model lands in `~/.gemini/antigravity-cli/scratch` and goes hunting with
   `find`, and `--sandbox` re-homes it there too. So stage a scratch directory holding only
   the statement file and a `check.sh` (fixed `LEAN_PATH` from `lake env printenv LEAN_PATH`
   in the nested checkout, running the toolchain's `lean` on `Main.lean` or on one scratch
   file named as `$1`, refusing paths), and call
   `agy -p "<bounded goal>" --add-dir <dir> --model gemini-3.8-flash-high --effort high --output-format json --json-schema <schema.json> --print-timeout 25m --mode accept-edits`
   from that directory. Shell commands are soft-denied in headless mode unless an allow rule
   in `~/.gemini/antigravity-cli/settings.json` matches; the standing rules are
   `command(regex:(\./)?check\.sh.*)`, `command(pwd)`, `command(ls)`, `command(ls *)` and
   nothing else, so the worker's only route to Lean is the checker (it will otherwise try
   raw `lean`, heredocs and web lookups, which the denial ends). Say so in the prompt, and
   say that a `#check` scratch file through the checker is how to test lemma names. Never
   `--dangerously-skip-permissions`. Slugs come from `agy models` (read it at use; the
   2026-09-19 list is in references/ANTIGRAVITY_LOG.md).
   Default `gemini-3.8-flash-high`; `gemini-3.1-pro-high` only when Flash reports an
   obstacle, since on the probe it was 4x slower and produced the worse proof (item 7).
   `--conversation <id>` (id in the JSON envelope) resumes a worker with its context, which is
   the cheap stateful mode short of a bus seat.
   The envelope carries `status`, `structured_output` and a `usage` block; log `usage` to
   the ledger as the quota sample. Peer role: an interactive `agy` session in the checkout,
   coordinated through the bus.
   Review-worker pipeline (2026-09-20, first production runs): launch detached (`nohup … &`
   from a shell with a clean `env -i HOME=… PATH=~/.local/bin:/usr/bin:/bin`) and watch the
   pid with a Monitor, since a 25-minute call outlives the Bash tool's cap; prompt = the
   allowed commands, "run every `./check.sh` call in the FOREGROUND, never launch a background
   task, never end the turn while a command runs", "read only files in this directory; learn
   library signatures through `#check` probes", the bounded question list, and "report, do
   not fix", and the permitted shell commands named explicitly ("only `./check.sh [file]`,
   `pwd`, `ls`; read files with your file tool, no cat/grep/sed/cd, no compound commands").
   Three failure signatures, all `status: SUCCESS` with no `structured_output`: (1) stderr "root
   agent idle; waiting for background task(s)" means the worker backgrounded the checker and
   was killed at turn end; (2a) `denied_actions: read_file` means it opened a file outside
   `--add-dir` (it reaches for Mathlib sources); (2b) `denied_actions: [{action: command}]` with
   stderr "a tool required the command permission" means it ran a shell command outside the
   allow list (the run ends after ~60 s). All three are fixed by resuming with
   `--conversation <id>` and the missing rule. Cost: 160–370 s and 250k–860k tokens per review
   (samples in references/ANTIGRAVITY_LOG.md). Verdicts are non-final: file them under
   `ledger/bus/claude_units/<unit>/agy/` and record the coordinator's disposition per finding.
   Prose-math consults (user 2026-09-20): when the question is a specifically tricky piece of
   mathematics and the want is natural-language insight rather than a review, run
   `gemini-3.1-pro-high --effort high` (high is the CLI's top effort) instead of Flash;
   consolidate Gemini Pro's proof scratch with the coordinator's own scratch into one route
   note, and hand that consolidated note (never the two raw scratches) to the Aristotle grind.
   First A/B (2026-09-20, Liouville route): Pro and Flash gave the same route and quality,
   Flash faster and more detailed; both called `SymplecticGroup.det_eq_one` missing (it exists).
   Friction rules (16 headless runs, 2026-09-20; log in references/ANTIGRAVITY_LOG.md): (3) above
   ~1500 input lines the text can degenerate and `status: ERROR` still carries a usable
   `structured_output` — lower trust; review line-range blocks, not whole modules; (4) a DNS
   failure (`AGY_ERROR … no such host`) dies before the first model call — relaunch; (5) trap
   (1) recurs despite the foreground rule — resume with `--conversation <id>` restating it (the
   resumed run keeps its probes); (6) `--effort` tops out at high; (7) a wrong line count in the
   prompt is harmless. Verdict profile: strong on hypothesis strength, unused binders,
   probe-verified duplicates and docstring honesty; weak against the item MARKER (it judges the
   prompt's framing, so describe each face by its marker), prone to 'vacuous when the domain is
   empty' padding, never found a mathematical error: a second reading, never a gate.
3. Reads `AGENTS.md` in the workspace and `~/.gemini/GEMINI.md`; skills from
   `~/.gemini/antigravity-cli/skills/` (symlinks to the canonical copies: agents-bus,
   lean-api-design, lean-build-guard, lean-golfing, radii-poly-api-design; checked 2026-09-22)
   and `.agents/skills/` in the workspace; MCP from `~/.gemini/config/mcp_config.json` and
   `.agents/mcp_config.json`.
4. Cloud model: rule 4 applies in full. Telemetry is not a `settings.json` key (agy strips
   `enableTelemetry` on every run and posts trajectory analytics regardless): the user turns
   "Enable Telemetry" off in the interactive `/settings` menu, once per account. Do not point
   `--include` or the workspace at the checkout root's parent, which holds `exterior/` and the
   book material.
   A `ReferenceBook` module is a formalisation of the book, and its docstrings paraphrase
   and sometimes quote it: stage a comment-stripped copy (blank every `--` comment and every
   nested block comment, line-preserving, so the worker's line citations map onto the frozen
   file), recompile the stripped copy through the same `check.sh` before staging, and keep
   the prompt free of book text. The formal statements themselves are library source.
5. Hook events `PreToolUse`, `PostToolUse`, `PreInvocation`, `PostInvocation`, `Stop`;
   workspace file `.agents/hooks.json`, global `~/.gemini/config/hooks.json`. The cue route
   is a `Stop` hook (stdin carries `conversationId`, `transcriptPath`, `terminationReason`,
   `fullyIdle`), the counterpart of Codex's `notify` `turn-ended`. VERIFIED route 2026-09-20
   (`cli-queue`): a persistent headless conversation is cued by resuming it —
   `agy -p '[claude cue — NOT the user] <message path>' --conversation <id> --add-dir <bus>
   --add-dir <peer scratch> --mode accept-edits`; the peer scratch holds writable probes/ and
   chmod-a-w snapshots of the sources, and `permissions.allow` lists the few shell commands.
   An Antigravity APP session cannot be cued this way (separate conversation store).
6. As above.
7. Probe 2026-09-19, `probe_geom_tail`: both models compiled on v4.33.0 with standard axioms
   and a byte-identical statement; Flash high 62 s / six committable lines, Pro high ~5 min /
   golf-stage `calc` — hence the Flash default (details in references/ANTIGRAVITY_LOG.md).

## Code-Level Practice (distilled 2026-09-24; revision 2 after Codex review 2026-09-24T19:30:31Z)

Universal, correctly qualified guards from the FILTER triviality rounds; the evidence, the
refuted alternatives and the project-specific content are in
`ReferenceBook/ledger/bus/claude_units/FILTER-20260924/LEAN_PRACTICE_DISTILLED.md` (rev 2;
rules numbered as there). Reading order for a fresh unit: contract/fidelity → semantic face and
existing-API search → computable data/checkers → closure/trust/build audit; never optimise
thinness before specifying what the theorem means.

- **Fidelity (1–3)**: inhabit the imported original type (`theorem chk : type_of% @Orig := @Mine`)
  as a cheap proof-compatibility gate; SEPARATELY compare elaborated `Expr` + universe params for
  exact type identity, and source bytes for byte identity — three gates. Private constants via a
  hardened env-lookup elaborator (one candidate, name AND module, levels instantiated, fail
  closed). When you cannot import the original, capture baseline evidence independently; a
  restatement is not a gate.
- **Thinness (4–5)**: audit transitive dependencies through types AND values against a complete
  legacy inventory (private/generated names included) with a positive control; a namespace grep or filter alone cannot prove the cut. Compile the extracted API with the permitted transitive imports and inspect the
  import graph.
- **Checkers and trust (6–11)**: keep executed checker inputs/equality/arithmetic computable
  (separate semantic realizations where needed); expose a certificate proposition with a proved
  sound checker (Decidable conjunction, Bool reflection or split checks are all valid); prefer a
  kernel-checked method — on this toolchain `decide +kernel` when ordinary `decide` stalls on
  rational reducibility; trust is the axiom closure, never a count: a new native axiom is an
  expansion needing a disposition, block splits are fine when the assembly proves the SAME
  predicate; budgets are project agreements, not laws; when profiling shows repeated
  computation try sharing, split proofs or supplied witnesses checked by a generic soundness
  theorem.
- **Faces (12–23, E3)**: separate the bound-consuming theorem from computed recipes and keep
  proved sharper alternatives (override slots where a generated majorant exists); sharpness is
  a gate; a one-point centre-anchored derivative-difference bound recovered a sharp Z₂ where
  centring alone did not (Taylor shifts can still help in general); local hypotheses where they
  suffice with global wrappers derived, and strict inclusion / nondegeneracy PROVED from their
  residual/injectivity or finite-dimensional hypotheses; scalar bounds at a selected radius, per-radius
  bounds in interval wrappers; Prop output records without strengthening hypotheses; convexity
  (not monotonicity) propagates negativity, separately from zero certification; state costly
  calculus generically at the weakest adequate algebraic assumptions and specialise; for coexisting
  normed structures use a vetted type wrapper or synonym with coherent instances, never a
  conflicting global instance (a numerical weighted norm may stay a function); reuse
  homomorphism/evaluation/differentiation theorems and prove bridges once at the right layer;
  decompose product-carrier operators into blocks and TEST on coupled L > 1 data; a linear
  projection need not preserve products (prove it or multiply first); identical theorem types
  can hide changed definition bodies/instances (fingerprint the dependency closure, then read);
  audit every declaration of a changed module incl. private/generated plus consumers; a
  representation bridge does not erase an operator-bound assumption.
- **Work (25–30)**: frozen baseline + diff the intended change; bounded prioritised targets with
  an explicit achieved/frontier report (an omitted target is incomplete, never "done");
  independent checks proportionate to the claim with exact axiom/dependency parsing (source
  counterexamples count without recompiling); explicit scratch/write boundaries, locks and
  content fingerprints — command choice is not isolation (guarded `lake build` when
  dependencies change, `lake env lean` when they are freshly built); audit the bound actually
  USED; bounded probes + independent criticism for uncertain design claims.

## Autonomy Pacing: the frontier plan (2026-09-24T19:59:57Z; amended per Codex DEBATE 7; user question on busywork vs premature stop)

Autonomous work is directed by a FRONTIER file the session owns (worked instance:
`ReferenceBook/ledger/bus/claude_units/FILTER-20260924/FRONTIER.md`; proposal and Codex
dispositions in `AGENTS_BUS_FRONTIER_PROPOSAL.md` there). It is the owner's bounded PLAN for the
authorized objective, linked to accepted units and evidence — not an execution journal, not an
authority source, and (for now) a process practice, not bus protocol.
- Items have stable ids, a checkable completion criterion (a falsifiable target for claims and
  gates), explicit uncertainty, what they unblock, an estimated cost, and typed blockers (other
  items, the user, a pending peer request, budget/host, agent capacity, unknown). The
  CLAIM / GATE / TOOL / DECISION taxonomy is a project convention, not exhaustive.
- Substantive work is tied to an item; supporting coordination is charged to it; receipts, control
  handling, recovery, validation and maintenance stay legal on their own. Repeated work needs a
  named evidential purpose (independent verification, changed conditions, nondeterminism,
  suspected tool failure, a required gate) — never a re-run of a reported failure with unchanged
  input for its own sake. Two wording-only rounds are a review trigger, not an automatic stop.
- Continue actionable, authorized work while current user instructions, resource limits and the
  quota policy permit; record legitimate deferral instead of pretending completion; a row never
  authorises new scope or overrides a pause. Ranking by value over cost is advisory after
  explicit priorities, dependencies and the accepted queue; overrides are recorded.
- The STOPPING STATUS is durable and scoped: complete / awaiting external input / budget-or-host
  deferral / user pause / in-flight work / unknown evidence (never a bare "blocked"); it is written
  into NEXT CURRENT; the heartbeat may point to it as a hint, never as proof of no work.
- Done = the declared criteria met by the appropriate evidence: machine checks for recomputable
  facts (type identity, axiom parse, closure audit, replays); judgments recorded with evidence
  otherwise; an unexplained "looks fine" is inadequate.
- A peer proposes items; the owner admits them within existing user authority with provenance.
- A JSON record with a generated rendering and a small helper (validated atomic writes with a
  generation, evidence required for terminal transitions, drift refusal pending reconciliation,
  advisory stop-certification) is the intended next step, trialled in an isolated project
  prototype before any promotion.

## Escalation To Aristotle

Aristotle (Harmonic's cloud prover, `aristotlelib` in `exterior/data_pipeline`) is a bounded
worker for a single extra-hard `sorry`, not a default step. Use it only after the local ladder
is exhausted: `exact?`/`aesop`/`polyrith`, then one Fable sorry-closing pass. Submit one
lemma with its dependency chain, never a whole file. Three stages, each gated on the last.

1. **Grind.** `source ~/.zshrc &&` before any command; the key is not loaded in tool shells,
   and never dump the environment afterwards. Submit through
   `generate_proofs.py aristotle --input <stmts.jsonl>` (async) or
   `aristotle submit "<prompt>" --project-dir <dir>`; record the project id in the ledger.
   Two things leave the machine: the whole `--project-dir` tree (tarred with no extension
   filter, minus that directory's own `.gitignore`) and the prompt string itself. Library
   source is fine in either. The reference-book PDFs under `docs/reference_book/` (tracked
   in the nested checkout; listed in its `.gitignore` only to keep the client's walker out),
   the rewrite-edition `.tex`, the `tmp/` experiment tree and any text derived from the book
   are not, in the tree or in the prompt. So never pass the checkout root as `--project-dir`:
   stage a scratch directory holding only `lakefile.toml`, `lean-toolchain`,
   `RadiiPolynomial/`, `RadiiPolynomial.lean` and the statement file, the layout
   `create_lean_project` in `generate_proofs.py` builds, and before submitting confirm that
   `find <dir> -type f ! -name '*.lean' ! -name lakefile.toml ! -name lean-toolchain`
   prints nothing. `book_to_proofs.py` puts book prose in the prompt by construction and is
   gated behind `ARISTOTLE_ALLOW_BOOK_TEXT=1`; do not invoke it from this skill.
   Aristotle resolves Mathlib on its side and runs its own toolchain (v4.28.0 as of
   2026-09-19, against the library's v4.33.0; the CLI warns on submit), so a returned proof
   is a candidate, not a result, until it compiles against the pinned toolchain in the nested
   checkout. Expect renamed Mathlib lemmas and `simp` set drift across that gap. Collect
   with `aristotle tasks <id>` (status) and `aristotle download <id> --destination <tar.gz>`.
   The archive is Aristotle's copy of everything uploaded, possibly edited, plus its own
   `lean-toolchain` and `lake-manifest.json`: take only the statement file out of it, diff
   it against the one submitted, and accept only the proof-body hunk. Keep `aristotlelib`
   current in the pipeline's `pyproject.toml`; a stale client 404s on the API.
   Probe 2026-09-19: a Mathlib-only tsum lemma round-tripped in ~10 min and compiled on
   v4.33.0 with standard axioms.
2. **Trust surface.** Apply the project skill's Verification gate to the returned proof: rebuild,
   `#print axioms` for the target and for every declaration the diff touched (Aristotle may
   reach for `native_decide` or leave `sorryAx`), no upward imports, and a statement
   byte-identical to the one submitted. Keep the returned statement file under the task's
   `tmp/<task>/checks/` as provenance only, never the prompt or the uploaded tree. An
   escalated proof is a cloud result: it does not enter the EI training data or count toward
   the local prove rate unless its statement is first removed from the evaluation pool.
3. **Golf.** Aristotle proofs are search-shaped: long `have` chains, redundant rewrites,
   brute `nlinarith`/`simp` calls, and no use of the library's own API. Run the `lean-golfing`
   skill on the accepted proof on the mechanical tier (one tier up if it stalls) with the bounded
   goal: same statement, axiom set no larger, unfolding replaced by existing API lemmas, any
   generic sublemma the proof surfaces extracted into the right module. Re-run the trust gate
   after golfing, since golfing can pull in `decide` on large terms or `native_decide`.

The golfed proof is what gets committed. If Aristotle had to reprove something the library
should already offer, record it in the API insights ledger.

## Research-Level Gaps

A gap that is a theory, not a lemma (an invariant-manifold theorem, a conjugacy theorem, higher
regularity of a flow), is run as a campaign of bounded units, never as one prover call
(user 2026-09-20, D84). (1) Route note: the coordinator's scratch and an independent consult —
a Gemini 3.1 Pro prose consult (no book text in the prompt) or an opus designer → opus
adversarial critic pair (DESIGN.md + CRITIQUE.md, verdict GO_NOW | GO_AFTER_PREREQ |
WAIT_FOR_CODEX; D91–D94) — consolidated into one note naming the sub-lemmas (the "missing in
Mathlib" check of Worker Assignment applies to the note too). (2) Skeleton: an infra module
stating the sub-lemmas with `sorry` plus the ASSEMBLY proof of the endpoint from them, passed
through the critic so the statements are known to compose before any grinding; a module that
defines the chapter's vocabulary never hosts the campaign theorem — its marked block moves
verbatim (byte-identity checked) to a new campaign module first (D86, D89, D90). (3) Grind:
opus units per sub-lemma, Fable on a reported obstacle, Aristotle (the ladder above) on what
still resists — the sub-lemma's statement and its dependency chain only. (4) Canonicalize:
`lean-golfing` on the mechanical tier, generic sublemmas moved to the module they belong to,
API and structure insights recorded, and the proof route written as the docstring narrative.
(5) Only then, and per item, the prose proof is written into the rewrite edition at the printed
gap as an editorial proof under the errata recoverability discipline (snapshot, `\editorial`,
ERRATA/EDITORIAL_NOTES record); statements are never changed by this step.

