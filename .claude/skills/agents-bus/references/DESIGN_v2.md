# agents-bus DESIGN v2 — universal use (rev 13 = revision-4 amendments: delegation on receipt / bounded parent units, first-valid-reply receipts, cue lifecycle, typed project packets, force-termination re-entry; 2026-09-14; rev 12 = delegation adapter operative for Claude → Codex, 2026-09-13; rev 11 + §6.2 heading, §6.7 results, §6.8 adapter contract summary)

Delta over DESIGN_v1.md (approved 2026-09-13, sha256 d45a4844…). v1's message, state, lock,
status, silence/recovery, delivery ≠ activation, trust and release-gate semantics stay in force
unchanged. rev 3 takes Codex's "small version" (`checks/universal_review/DRAFT_REVIEW.md`,
sha256 d37daa60…): single domain, conservative atomic init, same-instance registration with new
aliases (no automatic replacement), exact bindings, tested locks; activation is an honest,
separately verified adapter. Previous drafts: rev 1 77f7aec7…, rev 2 5de876cb…, rev 3 70a8bf40… (kept beside). rev 4 folded Codex's six implementation constraints (message 20260913T190952Z-codex-accept-core-prototype-53289657); rev 5 folds the findings of the implementation itself (message 20260913T191516Z-codex-core-tested-cli-0e741df0): release runs under the `meta` guard too, board logging uses a short `meta` → `state` guard only after the participants/binding guards are released, a busy board is reported as pending, and the helper CLI is a separate `admin.py` (see §10). rev 8 (revision C) records the fixes made after Claude's independent core review (report `runs/universal-v2-20260913-b/claude_core_review.md`): OWNER stores a token digest, release reports per key, `state` is the explicit board-edit key, the explicit-bus selection sentence is removed, and the crash/staging claims are scoped honestly. rev 6/7 (operator-convention proposals) stay superseded. This is the design text the next freeze and release bind.
Prototype until the bilateral gate passes again for this design + helper manifest + actual runs.


rev 13 (revision-4 amendments, 2026-09-14): §11 below is the design-of-record for package revision 4. It is the agreed text of `prototype/rev4/candidate/DESIGN_v3_rev4.md` (sha256 890c9f50dc35abd06ca5ca769d7cb7c83400b392ec9d32da268ea2a9d4b41242) included verbatim, whose normative content is implemented by the candidate SKILL.md (sha256 98074305b5db2d932fdb5059b765f51cf492b93c23d03e97b576ecda7843c324) §5, §6, §7, §10, §11 and RECOVERY.md (sha256 2446d5e2fd537936e6c05c02616c99cd066039128d14d6fda18cab3eaadb8935) checklists G and H; authored by Claude from Codex's section verdicts (CODEX_SECTION_VERDICTS.77c24350.md) and Codex's incorporation patch (MINIMAL_PAYLOAD_FIXES.patch ed237ede…). Apart from the title line, this note and §11, the text (sections 0–10), helpers and tests are byte-for-byte unchanged from rev 12. Where §11 and §6 overlap (delegation adapter, cue route, armed continuations), §11 amends: the adapter's launch journal is the base of the §11 attempt record; the cue route must be VERIFIED per target/host/lifecycle; §6.6 registration applies to every continuation §11 names.

## 0. Scope and boundaries
"Universal" = any project directory on one machine, any pair of sessions of any harness that can
read/write that directory, using only the installed skill. ONE coordination domain per bus: a
resource is governed by exactly one bus, and this revision provides no mechanism to detect or
exclude across buses (nested repositories, outer workspaces and worktrees are distinct domains;
sharing a resource across them is a configuration the participants must avoid, stated in
`PROTOCOL.md`). Out of scope: background services, cross-machine transport, authentication,
editing global instruction files, mutating `.gitignore`, automatic same-alias replacement,
glob resources, rebinding established keys, checkpoint CRUD.

## 1. Discovery (executable rule)
- **Identity**: `bus.json` at the bus path: `{bus_id (16 hex, minted once), schema_version: 2,
  coordination_root (absolute, realpath), created_at, package {name, manifest_sha256}}`.
  Marker `R/.agents_bus` = `{bus_path, bus_id, schema_version}`. All paths compared by realpath.
- **Candidates**: every helper call collects ALL of: the explicit `--bus` (or `AGENTS_BUS`) if
  given; every marker found walking up from `--root` if given, else from cwd, to the filesystem
  root. Each candidate is validated (readable `bus.json`, marker `bus_id` = `bus.json.bus_id`,
  `schema_version` supported, marker `bus_path` realpath = the directory that holds `bus.json`);
  a corrupt or inconsistent candidate that was EXPLICITLY named (`--bus`, `AGENTS_BUS`) or whose
  marker lies on the walk is FATAL: the helper stops and reports; it never silently falls back to
  a different valid bus. Valid candidates are deduplicated by (realpath, bus_id).
- **Selection**: exactly one distinct valid candidate → use it. Several distinct valid candidates →
  refuse and list them, unless
  `--join <bus_id>` names one of them (the single explicit join operation; `AGENTS_BUS` or
  `--bus` alone is never an intentional join over a conflicting marker). Zero candidates →
  refuse with "no bus here" (then `init` is the authorized way to create one, or the user names
  the location). cwd is irrelevant when `--root` is explicit, so a helper invoked from its
  installed directory works with an explicitly selected root.

## 2. Initialization (`init --root <R> [--bus <path>] [--agent <alias>...]`)
`init` is the one bootstrap exception to §1 (discovery otherwise requires an existing bus): it
targets the explicitly given root/bus path and applies the same candidate validation to anything
already there. `publish` and `wait` keep their tested v1 transport semantics and explicit `--bus`
use; the administrative helpers (`init`, `hello`, `bind`, `lock`) additionally validate the v2
identity (`bus.json`, marker) before acting. Default bus path `R/tmp/agents_bus`. Every metadata file is STAGED fully written and fsynced
beside its target (`.staging/` exists only as a reserved, unused directory), then PUBLISHED with
no-replace semantics (hard link or
`link()`-style rename that fails if the target exists). The concurrent loser reads the winner's
`bus.json`, validates compatible configuration (same `coordination_root`, supported
`schema_version`), and adopts the winner's `bus_id`; incompatible configuration is refused with a
report. Artifacts: `bus.json`, `inbox/<alias>/done/`, `heartbeat/`, `locks/`, `participants/`,
`checkpoints/`, `.messages/`, `.staging/`, `bindings.json` (initially `{keys: {state: {resource:
<bus>/STATE.md, kind: board}}}`), `PROTOCOL.md` (template: pointer to the installed package, the
single-domain statement, "bindings live in bindings.json", re-entry pointer), `STATE.md` (board
template: one section per declared alias + Shared). The marker is published LAST, no-replace.
Repairable incomplete setup (valid `bus.json`, missing directories or templates) is completed
idempotently; corrupt records (unparsable `bus.json`, id mismatch) are refused; history is never
reset. `init` prints the `.gitignore` line and does not apply it. Creating a bus in an agreed
directory is ordinary authorized coordination; only an ambiguous location needs the user.
Crash claims are scoped to PROCESS interruption (a killed or failing helper), not to machine
power-loss durability. `init` refuses a bus path holding live foreign data (inbox, locks,
heartbeat, checkpoints or any recognisable earlier-layout file) without `bus.json`.
Tests: interrupted init (crash after staging, before publish; after `bus.json`, before marker),
concurrent init with adoption, incompatible-root refusal, corrupt-record refusal, live-foreign-data refusal.

## 3. Participants (`hello --agent <alias> --harness <kind> [--instance <id>] --activation …`)
- Record `participants/<alias>.json`: `{alias, harness, instance_id, generation, activation
  {primary, keepalive, delegate?}, registered_at, last_seen}`. Identifiers (`alias`, `instance_id`,
  lock keys) are validated against `[A-Za-z0-9][A-Za-z0-9_.-]{0,63}` before any path use.
- The WHOLE read/compare/update runs under the brief guard `locks/participants` (mkdir + OWNER,
  same shape as resource locks, never held while waiting for anything). Same alias + same
  instance_id → refresh (`last_seen`, `activation`) by staged write + rename inside the guard.
  Same alias + different instance_id → refused: use a new alias. (General replacement — history,
  notices, pending-work ledger for inbound AND outbound requests, retryable multi-step effect —
  is deferred; `generation` is reserved for it.)
- `instance_id` = the harness-exposed session/thread id when the caller supplies it, else a
  minted 16-hex id; a session never reuses an id read from shared state.
- `heartbeat/<alias>` = `<UTC> <instance_id> <state> …` (unchanged). Status-seq scope =
  (alias, instance_id); a receiver ignores seq ≤ last seen for that instance.
- `hello` creates the alias's board section from the template if absent (under the `state` key);
  otherwise it appends one log line INSIDE that alias's section. No prose rewriting. Activation
  values are descriptive metadata (no enforced vocabulary; a value is not a verified-capability
  claim); a same-instance refresh that supplies only some activation fields merges them and keeps
  the rest.

## 4. Bindings and locks
- `bindings.json` is the ONLY key → resource map: `{keys: {<key>: {resource: <realpath of an
  existing file or directory>, kind: file|dir|build|board}}}`. Participants and activation live in
  `participants/<alias>.json` only; `PROTOCOL.md`/`STATE.md` may quote bindings, never define them.
- **Reserved keys and guard order**: `meta` and `participants` are internal guards that cannot be
  requested as resource keys by any command (`lock show` may display them as diagnostics); `state` is pre-bound by `init` to `STATE.md`, never rebindable, and EXPLICITLY
  acquirable/releasable through `lock acquire|release --key state` — that is the operator's
  board-edit API (the helper takes `meta` internally to reserve it; holding `state` defers other
  board writes like any resource lock; a crashed holder is the ordinary abandoned-lock case). User
  bindings may not use these names, and no user binding may name a path under `<bus>/locks/`,
  `<bus>/participants/`, `<bus>/bindings.json` or `<bus>/bus.json`. Guard order (acquire in this
  order, release in reverse, never re-enter, never hold any guard while waiting for a peer):
  `meta` → resource keys (alphabetical) ; `state` is taken alone for board edits ;
  `participants` is taken alone by `hello` and is NEVER held while acquiring `meta` or `state`
  (`hello`'s board-section creation happens after the participants guard is released).
- **Metadata critical section**: `locks/meta` (brief guard; ordered BEFORE any resource key;
  never held while waiting; never re-entered). Both `bind` and `lock acquire` run inside it:
  `bind --key --resource` (additions only in this revision; established keys are frozen) validates
  the identifier, realpaths the resource, refuses if any existing binding's resource equals it or
  is a path-COMPONENT ancestor/descendant of it (`/src/a` vs `/src/ab` are distinct), stages and
  publishes the new map, logs one line; `lock acquire --key <k>... --purpose <p> --token-file <f>`
  resolves every key from the CURRENT map inside the guard, `mkdir`s the keys in alphabetical
  order writing `OWNER {alias, instance_id, token_sha256, utc, resource, purpose}` for each, and on any
  failure removes only the directories it created in this call, then leaves the guard. An
  ownerless lock directory is occupied. There is no `break` command (recovery = v1/RECOVERY B).
- **Token bundles** are the caller's, outside the bus: each `lock acquire` call writes a NEW
  capability bundle `{bus_id, alias, instance_id, keys: {<key>: token}}` to the caller-supplied
  `--token-file` (a writable location of the caller's choosing, e.g.
  `$HOME/.agents_bus/<bus_id>/<alias>-<instance>-<utc>.json`, mode 0600; the helper creates no
  directories); it never clobbers a pre-existing bundle (refuse if the path exists). Ordering
  inside the guard: mint tokens → fully persist the bundle (write + fsync) → then `mkdir` +
  `OWNER`; so a process interruption can never strand a resource whose token was not persisted.
  `OWNER` (resource locks AND internal guards) stores `token_sha256` only, never the token; for
  resource locks the secret exists only in the caller's bundle, for internal guards it is
  transient process memory of the helper invocation that holds the guard. `lock release --token-file <f> --key <k>...`
  compares alias + instance_id + the DIGEST of each bundle token with `OWNER` and releases exact
  matches only; wrong owner or missing token → refused; reading `OWNER` or `lock show` can no
  longer reconstruct a release capability (this is NOT authentication against a writer with full
  shared-filesystem control — such a writer is outside the protocol). `lock show` returns an
  allowlist of public metadata (alias, instance_id, utc, resource, purpose; digest optional),
  never a token. `release` performs its owner check AND the removal inside the `meta` guard (a
  release racing with an acquire of the same key must see one consistent OWNER) and reports per
  key: `released: [...]`, `not_held: [...]`, overall state `not_held` when nothing was removed;
  re-acquire after release mints a fresh token. A bundle written for an acquire that then failed
  on contention is RETAINED as per-attempt evidence; the retry uses a NEW token path (the
  contention error says so and names the occupied key).
- **Guard robustness**: a guard whose directory exists with a failed or foreign `OWNER` is never
  entered; a guard cleans up only the new, empty directory it created itself. A bound resource
  that is missing or renamed raises a `BusError` naming bus, key and path and directing an
  explicit coordinated repair/restore (no unbind/rebind; the frozen-map safe refusal is the
  design). `bind` refuses special files (fifo, socket, device) BEFORE committing. Board logging
  failures of the expected classes (I/O errors, an occupied guard, undecodable board text) are
  reported as `pending`, never raised after the primary effect committed.
- **Board logging by helpers**: `hello` and `bind` append their one-line board entries only after
  their own guards (`participants`, `meta`) are released (`lock acquire`/`release` do not log), via a short `meta` → `state`
  guard pair; if the board is busy the helper still succeeds at its primary effect and reports
  the board update as `pending` for the caller to retry. No helper ever waits under any guard.
- Before acquiring, the helper reads the project's claim registries (`R/.claude/coordination.json`,
  `R/.Codex/coordination.json`) and refuses when the resource is claimed there by another agent —
  a conservative courtesy check, not an exclusion guarantee against writers outside the protocol.
- Key names are project-bound examples (docs, source, build, config, skill, state).

## 5. Installed package versus project state
The skill's maintainers keep a canonical copy of the package in their own repository; every
installed copy is byte-identical (`MANIFEST.json`). A project that USES the skill never becomes a
source of truth for it and carries no copy of the package in its bus. `bus.json.package` records
the creating package; helpers check `schema_version` only. The SKILL.md sentence "treat the
tracked repository copy as canonical" is reworded accordingly. Markers and trigger lines locate
the bus and invoke the skill; neither creates activation.

## 6. Activation (rev 11: §6.0–§6.7 replace the rev 9 section)
rev 11 (activation amendment): §6 of rev 9 (sha256 8cff8793…) is replaced by §6.0–§6.7 — R1/R2 requirements kept separate, harness-local routes recorded per participant as configured|verified (a recorded convention), the delegation adapter contract (a NEW participant for ONE bounded job; never launched by these helpers; §6.2.1/§6.2.3 gained the exact-prompt envelope digest rule after drill A), the dispatch rule (target fixed before dispatch, no reassignment on timeout), task classes, the armed-continuations registry, and the routes and limits measured on 2026-09-13 (delegation drills under `prototype/activation_v4/`, watcher/heartbeat/queue observations under `checks/activation/`). Apart from the title line, this heading and note, and §6, the text (sections 0–5 and 7–10), helpers and tests are byte-for-byte unchanged.

## 6.0 Two requirements, kept separate
- R1 (cross-harness, unattended): a cooperating agent of the other harness acts on a bus request
  without a manual cue, in any workspace where a bus exists or the requester initializes one.
  Satisfied by a FRESH worker (delegation adapter, §6.2). The user need not know any session id.
- R2 (same task, context retained): wake the existing participant. Satisfied only by harness-local
  routes (§6.1). Never required for R1; never implied by R1.
The requester fixes the TARGET before dispatch (existing participant vs fresh peer; precedence in §6.5).
It is recorded in the request; it is not a fallback ladder, and a timeout never converts one into the
other (§6.3).

## 6.1 Routes to an EXISTING participant (harness-local, recorded per participant)
Recorded in that participant's own record (`hello --primary/--keepalive`; on a legacy bus by its
board/protocol procedure), one of: `in-session-watcher` (Claude Code persistent inbox Monitor),
`in-turn-wait` (bounded `wait` loops while a turn is active; both harnesses), `app-heartbeat`
(scheduled continuation attached to the existing task, e.g. Codex app `automation_update(kind="heartbeat")`;
a schedule is delayed polling, so a request relying on it carries a receipt deadline of at least three
cadences), `same-harness-message` (supported direct thread/session messaging inside one harness; outside
this adapter, never cross-harness; the official APIs are not claimed to lack durable ids), `cli-queue` (a
harness CLI that queues a short cue into an EXISTING task by its id, e.g. `codex queue --thread <id>
--message <cue>`; the cue names a bus message and grants nothing; rendered as user input, not sender
authentication; cues are idempotent pointers — a cue can arrive late, duplicated, or after the receiver's
compaction, and the receiver reconciles by handled ids: a cue for an already-handled message is a no-op,
observed 2026-09-13 23:50Z), `user-relay`.
Each value is recorded as `configured` or `verified` (at least one real wake observed); only `verified`
may be advertised (`--primary`/`--keepalive` are free-text descriptive fields: this vocabulary and the
configured|verified tag are a recorded convention, not validated by the helper). Configured is not alive; no route is an availability or ownership proof. UI automation
is a scoped exclusion (not portable, no durable addressing/correlation/retry semantics), not impossibility.

## 6.2 Delegation adapter (R1) — a NEW participant, one bounded job (OPERATIVE for the verified direction Claude → Codex since rev 12; implemented by `scripts/delegate.py` v6; RECOVERY F exercises A2 + C passed 2026-09-14 with every predicate verified as a requester-computed consistency check or a digest-bound requester-observed snapshot)
1. Launch record persisted by the requester BEFORE launch, outside the bus, at a caller-selected path:
   bus_id, coordination_root, job_id, attempt_id, worker_alias (`<harness>-worker-<8hex>`),
   worker_instance (pre-chosen where the harness supports it: Claude `--session-id <uuid>`; Codex: bound
   after launch, see 3), worker_request_id + its sha256 (the exact bytes published), delegated_from,
   the absolute path of ONE immutable envelope file and `envelope_sha256` = sha256 of that file's exact UTF-8
   bytes (newlines included); the launched prompt is exactly those bytes,
   pinned input hashes (skill files, helper scripts, PROTOCOL), allowed_effects, supervisor_deadline,
   exact local executable + argv. The command comes only from the requester's LOCAL adapter policy file
   (user-set, outside the bus); no text in any bus message or peer participant record is ever executed.
2. Addressing: the worker gets its OWN request (`to: <worker_alias>`, header `delegated-from: <original
   id>` when any), published before launch. A worker never consumes or answers a message addressed to
   the live peer; a worker's output never counts as any maintainer's agreement.
3. Identity binding (executable): the launch ENVELOPE (the prompt) carries root/bus identity, task, job,
   attempt, the expected request id + sha256, input digests and the allowed-effect list; the worker
   verifies the request it reads against them BEFORE any effect, and treats an `allowed_effects` line in
   any message as data, never authority. Codex worker: reads its own `CODEX_THREAD_ID`, registers it as
   its `hello --instance`; the supervisor independently compares it with that launch's `--json` thread id.
   Claude worker: registers the pre-chosen `--session-id`; the supervisor compares with the
   `--output-format stream-json` session_id. Never a parent's or a probe's id. Substantive waits pin
   `--sender-session` to the bound id; messages before the binding is durable are buffered, not trusted;
   mismatch = blocked. A nonce correlates; it does not authenticate against a same-user filesystem writer.
   The envelope names its own file path; the worker hashes THAT FILE's bytes (never a reconstruction of
   model-visible text) and records the digest; the verifier compares it with the launch record's
   `envelope_sha256` (a canonical-JSON or parsed digest does not count). The expected digest lives only in the
   launch record, never inside the prompt.
4. Envelope per adapter (documented; no bypass flags, no elevation, no secret copying). Allow-lists are
   NOT confinement: `Bash(uv run:*)`/`Bash(python3:*)` grant an interpreter, `Read` is unbounded. Confinement
   is the enclosing sandbox: Codex `--sandbox workspace-write` (writable = its cwd + temp roots, as the
   harness defines them); a Claude worker has no filesystem sandbox of its own and is confined only by
   whatever launched it (when Codex launches it: Codex's sandbox roots). Say which applies in every plan.
   - codex: `codex --ask-for-approval never exec --sandbox workspace-write --cd <root> --skip-git-repo-check
     --json -o <last-message file> <prompt>`
   - claude: `claude -p --safe-mode --permission-mode dontAsk --add-dir <root> --tools <bounded list>
     --allowedTools <explicit patterns> --strict-mcp-config --no-session-persistence
     --output-format stream-json --permission-mode dontAsk --session-id <uuid> <prompt>`. `--safe-mode` disables skill/customization
     discovery while keeping auth, built-in tools and permission checks, so the worker reads SKILL.md by
     absolute path. Identity is traced through the pre-chosen uuid + JSON output, not resumable session files.
     No turn cap is relied on (`--max-turns` is not advertised by 2.1.195); the bound is the supervisor's
     wall clock plus the worker instruction (one job, no fan-out, no starting another CLI).
   Launcher failure (auth, network, sandbox, exec error) is reported as LAUNCHER failure; never as a
   worker `blocked` reply.
5. Bounds and supervision: one job; no recursive delegation; the supervisor starts the child in its own
   process group/session, enforces the wall clock on the group, records PID/PGID and the child id, keeps
   stdout/stderr/exit under `runs/<job_id>/` (stdout need not be bus data). Cessation is verified for the
   PROCESS GROUP only (no live process in the group, after a sweep), never inferred from the parent's exit
   code; a descendant that left the group is NOT covered, and a query error or unknown state is not
   cessation. Success =
   matching reply + verified effects + released owned locks + verified cessation. A crash may strand a
   lock: recovery follows the existing owner/cessation rules; nothing is inferred from a timeout or an
   exit claim; nobody acquires another participant's authority by reading its token bundle.
6. Retry of a MUTATING job (new attempt_id AND new alias) only when (a) the launcher provably failed
   before any child was spawned, or (b) cessation of the process group is verified, there is no evidence of
   an escaped descendant (unknown = not satisfied; group absence alone does not prove whole-tree cessation),
   AND every allowed effect has been reconciled from durable evidence. The same scope limit applies to any
   lock-recovery decision. Negative artifact checks alone are insufficient (a worker
   still awaiting its first model response satisfies them and can act later). Independent read-only work
   stays distinct from retrying the original effect. Same rule for route failover.
7. Participants stay monotone: no retirement API; terminal status, checkpoint and exit evidence are
   recorded; an ended worker is never a route for a later job.
8. Worker durable lifecycle (this paragraph is normative; the experiment template `WORKER_PROMPT.md` under
   `prototype/activation_v4/` is not part of the package and predates the file-digest rule): (1) validate envelope,
   canonical root/bus identity, expected request digest, task/job/attempt, actual input digests; resolve
   own identity by the harness rule; if a checkpoint exists read + validate it before any write and
   reconcile completed/uncertain effects — never overwrite a record with initial values; create a new
   checkpoint only when absent, atomically, no-replace. VALIDATION FAILURE (bus identity, request or
   input digest, identity, conflicting/foreign checkpoint) = preserve all existing files, NO bus
   bookkeeping, hello, publish, archive or lock operation; the worker returns a structured
   WORKER_VALIDATION_FAILURE result through the normal harness response and ends its turn. The launcher
   extracts it from the CLI JSON result and records spawned=true, task_outcome=validation_failed and the
   process exit code separately (a zero exit is not success; a missing/malformed result = failed or
   inconclusive launch) — never a fabricated bus `blocked` reply. The writable finalizer (4) is gated on a validated bus AND a validated/owned checkpoint.
   (2) register the fresh alias with that identity; bookkeeping recorded separately from project effects;
   `received` with all correlation headers after validation; pre-effect mismatch → finalizer, no effects.
   (3) only the envelope's allowed effects, durable progress after each; any detected failure → outcome
   blocked → finalizer (never return early; never retry an uncertain prior effect). (4) ONE finalizer for
   done and blocked: record outcome + evidence + uncertainty; safe release of own locks only; persist the
   actual release results and remaining owned-lock state (release failure or lost exclusion → blocked);
   persist handled ids + final checkpoint BEFORE the terminal reply; `done` only with verified effects and
   released resource locks; archive own request; heartbeat `idle` with the actual outcome; exit. The
   supervisor records the process exit; a crash is the separately tested recovery case. Optional barrier:
   the envelope may name a barrier file the worker waits for after `received` and before any project effect
   (used by drills to prove a message was injected DURING execution).
9. Effect resources exist before dispatch: the maintainer creates the effect directory and binds it under
   the declared key (`bind` requires an existing resource); the worker acquires that key and writes inside.
10. Supervisor record keeps `spawned: true|false|unknown` separately from the outcome: auth/network failures
   can occur after the CLI spawned; only a PROVEN pre-spawn failure counts as "no child" for 6.2.6(a).

## 6.3 Dispatch rule
Route and target are fixed before dispatch from the peer's recorded (verified) activation and the
requester's local adapter policy. Receipt timeout leaves the original request pending and the peer
possibly active: no automatic reassignment of delivered mutating work. Alternatives: choose the fresh
worker before dispatch, launch a separate read-only task, or reconcile/cancel the original attempt
with evidence (6.2.6). Failover with a shared effect ledger and fencing is future work.

## 6.4 What stays
keepalive as in rev 9; receipt-first; user relay recorded truthfully when no route is eligible; no
same-alias takeover; no silent installation of any scheduler or watcher.
## 6.5 Task classes and dispatch precedence
### 6.5.1 Facts kept separate (never collapsed into one "gone" bit)
- identity: recorded | unrecorded (a missing participant record does not prove no session exists; on a
  legacy bus participants are recorded by its own procedure);
- route: configured | verified | unavailable (unavailable through the known routes ≠ the session ended);
- pending obligations: the peer's open requests and accepted work from the board/ledgers; HELD LOCKS are
  observed from the actual lock directories (OWNER records), never inferred from the board;
- known-ended: only with harness evidence (task deleted, process ceased) — never a user-written marker;
  no marker API. A user may choose a NEW target for NEW work; that choice recovers no locks and settles
  no pending mutation. Prior mutations stay pending until reconciled from evidence (§6.2.6, §6.3).

### 6.5.2 Precedence (one deterministic default, decided by the requester at dispatch; recorded in the request header `class:` + `target-reason:` and in the launch record; never changed by a timeout)
1. Context-bearing work (`session`) goes to an eligible recorded peer: identity recorded AND route
   verified AND the request honours that route's receipt deadline (>= 3 cadences for a schedule).
2. An explicitly self-contained `consult` or `job` MAY select a fresh worker instead, for a recorded
   reason (peer context hygiene, a second independent reading, parallelism, no eligible existing target).
   A different harness is not by itself proof of statistical independence or of a particular model.
3. When no eligible existing target is known, a fresh worker is the practice for NEW work of any class;
   for `session` work the new participant re-enters from durable state (below), it does not continue as
   the old one.
4. Consultation attempts are bounded and separately recorded: each attempt has its own job id and alias,
   its input hashes, and a stated acceptance rule (e.g. first `done` whose input hashes match; later
   ones archived as superseded). Worker caps apply. Read-only work still spends quota, may carry network
   side effects, and can return competing stale answers; it is never "free" to re-dispatch.

### 6.5.3 Classes
- `consult`: read-only with respect to project/task artifacts. Control-plane effects it DOES have: hello +
  participant record, heartbeat, checkpoint, the helpers' brief participant/state guards, its own
  received/done replies, handled ids, archiving its own request. No project-resource locks. The result
  travels in the `done` reply (no separate artifact needed); inputs are pinned by path + sha256 and
  rechecked at the end; changed inputs are reported, and no unqualified "consistent snapshot" claim is
  made because no resource lock was taken. No sub-agents and no starting another CLI: this is a WORKER
  INSTRUCTION plus the supervisor's bound, not an enforced cap (a Bash-enabled worker could start a CLI;
  tool allow-lists narrow but do not prevent it; `--max-turns` is not advertised by Claude 2.1.195 and is
  not relied on).
- `job`: bounded effects, self-contained: tests/builds in a declared directory, a report file, a small
  patch under a named lock. Requires pinned inputs, `allowed_effects` in the envelope, the lock keys it
  may take, a supervisor deadline. It must be solvable from its explicitly supplied, pinned inputs (source
  and artifact files the bus did not write, plus checkpoints/ledgers) and the operating instructions the
  envelope names; nothing is assumed from any session's context. Fresh worker allowed; the recorded peer
  is preferred when it already holds the relevant locks or ledger.
- `session`: context-bearing, multi-step, may fan out sub-agents, owns resources over time (ongoing
  audits, design negotiation, this release process). Recorded peer only. If no eligible recorded peer
  exists, the replacement is a NEW participant that RE-ENTERS from durable state (checkpoints, ledgers,
  board, RECOVERY checklist) under a new alias; it inherits no token and no lock, never claims to be the
  former session, and reconciles outstanding requests AND locks before claiming any continuation.

### 6.5.4 Worker caps (adapter policy, user-set, outside the bus)
max concurrent workers, max launches per hour, wall clock per class (supervisor-enforced), allowed
classes per direction, allowed roots. A misclassified request (e.g. `consult` asking for a project
effect) is answered `blocked` by the worker, never silently upgraded.

### 6.5.5 Memory and context note
"Fresh context" means no inherited live conversation. It does not guarantee the absence of instructions
or memory the harness supplies at startup (Claude `--safe-mode` disables customization/skill discovery;
whether project memory files load under that envelope is not established and is not relied on). The bus
relies only on files the protocol writes plus the pinned inputs the envelope names.
## 6.6 Armed continuations registry (watchers, heartbeats, schedulers)
Rule (every armed continuation: Claude Monitor tasks, Codex heartbeat/cron automations, any future watcher):
1. REGISTER in two steps: (a) the INTENDED arming (owner alias + session/task id, watched path(s), scope =
   task or run id, expected END = scope closure, cancellation, or an explicit UTC time) written BEFORE the
   arming tool call; (b) the ACTUAL returned handle + state written right after. Location: the bus
   workspace, `<bus>/checks/watchers/<alias>.json`, or the session's own checkpoint file (no helper writes a
   participant-record field for this). The registry is informational; the harness task list / automation status is the truth.
2. RETIRE on scope closure, cancellation, or expiry — NOT at every turn end: a pending authorized scope is
   exactly when a watcher/heartbeat must stay armed across turn ends and compactions. Retire = request the
   stop through the harness (Claude TaskStop; Codex the supported automation tool, never a shell
   scheduler), then record the actual result. A failed or unconfirmed stop stays `stop-pending` with its
   handle preserved; it is never deleted or labelled retired because a stop was requested.
3. CRASH GAP: an arming may succeed without its registry write. On re-entry, reconcile ACTUAL harness
   handles (task list / automation status) against the registry before arming anything; "no entry" never
   means "no watcher". Re-entry (RECOVERY checklist A step): verify each entry's handle; retire only those
   whose scope is closed; re-arm at most ONE watcher per bus per session; never duplicate an alive handle.
4. OWNER INDEX: each session keeps a durable index of the bus/run registries it owns at ONE explicitly
   selected, already-authorized location (e.g. its checkpoint file in the primary bus, or a caller-selected
   path recorded in the launch record) — never automatic global configuration. A registry that lives only
   inside a forgotten scratch root is undiscoverable after compaction.
5. AUTHORITY: an entry never lets another session stop an arbitrary handle. Stopping requires matching
   owner instance, watched path, scope AND the actual harness metadata; unknown status stays unknown;
   another session's watcher is never terminated, and no lock is inferred free from watcher state.
6. SHAPE: one watcher per session that re-reads an allow-listed path set from the registry each poll is
   PREFERRED where the harness genuinely supports it — a separate capability to verify in a drill, not
   something the registry implements. Codex: one heartbeat per task with an explicit END and a recorded
   stop result at freeze, managed only through the supported automation tool.
7. STATUS notices name the armed handles (already required as "activation mechanism"); "nothing to wait
   for; nothing to do" is only truthful when no out-of-scope watcher remains armed.
## 6.7 Routes and limits measured on 2026-09-13 (delegation drills on scratch bus 6a3e0f4385c04f4a; watcher, heartbeat and queue observations on this project's primary bus)
Records: `prototype/activation_v4/EXPERIMENT_RESULTS_claude.json`, `checks/activation/CODEX_EXPERIMENT_RESULTS.json`,
`checks/activation/HEARTBEAT_AFTER_TURN_RESULT.json`, `checks/activation/HEARTBEAT_DURING_TURN_RESULT.json`,
`checks/activation/QUEUE_ROUTE_EXPERIMENT.json`, `checks/activation/QUEUE_ROUTE_OBSERVATION.json`,
`checks/activation/RESULTS.md`, `checks/activation/claude_checkpoint.json` (`watchers`).
- `in-session-watcher` (Claude Code persistent `Monitor`): re-invocation on inbox arrivals observed throughout
  the day's exchanges; the scratch-bus watcher was retired at scope closure with a recorded stop result
  (`claude_checkpoint.json` → `watchers`). No separate watcher record file exists on the Claude side.
- `app-heartbeat` VERIFIED after turn end (Codex app `automation_update(kind="heartbeat")`, 5-minute cadence,
  explicit END): the native event at 21:34:03Z resumed the same task in a new turn 19 s after the previous
  turn completed; checkpoint and handled ids were reconciled before handling; no manual relay. NOT
  determined: a tick during a running turn (queued, coalesced or dropped); NOT tested: a message already
  pending in the inbox at wake. Receipt deadline >= 3 cadences stands. Retired (PAUSED) with the recorded result.
- `cli-queue` VERIFIED for an IDLE Codex task: `codex queue --thread <task id> --message <cue>` (app-bundled CLI)
  started a new turn ~2 s after the CLI acknowledgment (21:50:39Z → 21:50:41Z); the receiving task saw the cue
  as an ordinary user-role message with no sender identity and without the queued-message id; it ran its
  re-entry checklist and answered over the bus. Use only for a short correlation cue that names a bus message,
  under the user's authorization; it authenticates nothing and grants nothing. NOT tested: arrival during an
  active turn, app closed, retries.
- Claude -> Codex delegation (`codex exec`; a job by §6.5.3's definition — the drill OMITTED the `class:` and
  `target-reason:` headers that the accepted §6.5.2 already required; recorded as an omission): probe 0 passed; probe 1 passed steps 1–4 (step 5, the outside-root denial, UNVERIFIED — prose
  only); drill A BEHAVIOURALLY PASSED (fresh identity from `CODEX_THREAD_ID` == harness `thread.started`,
  pinned request/input digests, lock acquire/release with a token bundle outside the bus, effect, hold/release
  barrier with an injected unrelated message left unhandled, archive, heartbeat idle, process-group cessation,
  transport dedup) but the FROZEN-ENVELOPE CONTRACT WAS NOT MET (the worker hashed a canonical-JSON parse;
  the verifier did not enforce equality). The rev 11 contract (§6.2.1/§6.2.3 digest rule, stdin=/dev/null,
  version-matched executable) has NOT yet been re-drilled; RECOVERY F prescribes that drill before any change
  to the adapter contract is agreed again.
- Codex -> Claude delegation (`claude -p`) BLOCKED in this environment: both probes timed out at startup inside
  the Codex sandbox with no output, identity or tools; a separate DNS check there could not resolve the API
  host, consistent with host network policy; the exact internal cause was not exposed. Recorded as a
  limitation, no widening, no bidirectional claim.
- rev 12 (delegation adapter `scripts/delegate.py` v6, scratch bus 2b1252fa6c364697, 2026-09-13 23:23Z – 2026-09-14
  01:42Z): final drill A2 run a7-013614 ALL PASS, contract PASS with 47 predicates verified and NONE unverified
  or failed, gated replay idempotent (task result classified from the `-o` last-message file: unclassified;
  finalization resolved; envelope file bound). What "verified" means there: requester-COMPUTED consistency (identity
  chain harness output == hello == checkpoint == final record == terminal sender-session; envelope FILE digest
  equality; request bytes prepared digest == plan, stored == prepared == archived; typed checkpoint fields with
  `handled_ids == [request id]` exactly; final record fields exact and consistent; `release_results[key]` the
  parsed helper object; token bundle outside the bus; exactly the declared artifacts as real files with the
  declared digests and the `effect-sha256` header; late unrelated message left unhandled; timing received ≤
  late ≤ GO ≤ done; heartbeat idle; process-group cessation; task result unclassified from the designated
  final response; launch finalization resolved; envelope file present with the plan's digest) plus
  requester-OBSERVED, digest-bound SNAPSHOTS (lock OWNER with the worker alias + bound identity; the artifact's
  bytes, equal to its final bytes and the contract, read while that OWNER with the same token digest was
  present before and after the read; the final record's bytes, equal to the validated record, snapshotted
  with no terminal reply for the request anywhere in `.messages`, before the selected reply was observed).
  Continuous ownership and fsync durability are NOT claimed. Drill C run c7-014018 PASS: STOP through the
  supervisor-owned stop file while the worker held the lock → outcome `stopped`, group cessation verified,
  lock stranded with its OWNER preserved, no artifact, recovery left PENDING. Run history kept as evidence:
  a2-232337 29/30 (naive mtime ordering → immutable final record); a2b-232948 36/36 under v2 and c-233150
  PASS; a3-000550 never launched (a v1-format ledger record correctly counted live; `bind` then sat out its
  timeout → early exit with the reason; the record had been moved out on age at 00:14Z — insufficient
  grounds — and the decision was later reconciled against evidence in `SMOKE_PLAN_ONLY.json`: the v1 plan
  wrote the record at plan time and never updated it, the run directory has no launch/supervisor/output
  files, the plan invocation is exported verbatim, no launch was ever invoked (peer attestation, kept
  separate), while the worker request WAS published by that plan and is still pending, untouched); a4-001701 NOT PASS on one predicate (the worker stored the release result as a JSON
  string → template says "the parsed JSON object", check kept strict, `string_release` witness); a5-002233
  PASS 39/39 under v3; a6-010547 PASS 45/45 under v4 and c6-010959 PASS. The v3 → v4 review (Codex, 8 findings) produced: observations bound to bytes and to the
  bound worker's OWNER, per-artifact predicates, store-wide terminal absence after the snapshot;
  publish/replay preflight on the exact buffer with a recomputed snapshot; replay only after PASS, distinct
  exit statuses; validation-first worker lifecycle with the launcher classifying `WORKER_VALIDATION_FAILURE`
  as `task_outcome`; exact handled ids and the remaining schema bindings; the reservation bracket closed with
  persistence errors reported and capacity retained; mandatory bare `--json`; evidence-bound ledger
  reconciliation. The v4 → v5 review (Codex, 4 corrections): the ledger ends only after every final record
  persisted and `verify` refuses an unresolved finalization; the envelope file is bound at verify time; the
  task result is classified from the designated final response only (commentary never counts, malformed or
  foreign results are inconclusive, not failures); the smoke reconciliation evidence corrected (plan-only
  with a published request). The v5 → v6 correction (Codex, 1 residual): a missing, unreadable or empty
  designated final response is `inconclusive`, never the success label. Deterministic suite: 55 tests (adversarial witnesses incl. bad/extra handled ids, false
  and string release, extra artifact, symlink escape, wrong/split identity, late message handled, wrong
  digest, reply before the final record, final record swapped after the reply, artifact swapped after
  release, second artifact after release, foreign OWNER; validation failure before any bookkeeping and
  after registration; publish/replay preflight; --json policy; capacity refusal + reconciliation; setup and
  persistence failure injection; exit statuses; doctored journal). Limits unchanged: process-group
  cessation only; Codex → Claude direction not operative (sandbox network policy).
- UNVERIFIED: sandbox denial of writes outside the root appeared only in worker prose, never as a command
  record in the harness event stream (three runs); a worker claim counts only when the event stream carries
  the command and its exit/output. Cessation is verified for the process group only.
- Launcher rules learned: the executable must be the CLI version that parses the user's configuration (the
  adapter policy records executable + version); headless CLIs read piped stdin, so the launcher passes
  stdin=/dev/null; child identity comes from harness output (`--json` events / pre-chosen session id), never
  from a parent's or probe's id; evidence writes are atomic and run directories exclusive.
- UI automation stays excluded. One unexplained observation stays open: a transient `locks/<job id>`
  directory during drill A, created by neither participant's records.

## 6.8 Adapter contract as implemented (`scripts/delegate.py` v6, rev 12)
Evidence vocabulary. Every predicate in RESULT.json is `verified`, `failed` or `unverified`. Verified means
either a requester-COMPUTED consistency check (bytes, digests, headers, records compared with the immutable
plan) or a requester-OBSERVED SNAPSHOT (the observation journal, digest-bound to the bytes verified later).
A changed or contradictory binding fails; a missing observation is unverified. Polling never proves
continuous ownership or fsync durability, so no predicate claims them: the ownership predicate says "the
artifact's content (== its final content == the contract) was read while the bound worker's OWNER, with the
token digest first seen at acquisition, was present before and after the read"; the ordering predicate
says "the final record's bytes (== the bytes validated later) were snapshotted while no terminal reply for
this request existed anywhere in `.messages`, before the selected reply was observed". A matching
worker-written digest is a consistency observation, not proof that the worker performed the operation.
Process exit (`outcome`) and the worker's task result (`task_outcome`) are separate fields.
plan: validates the LOCAL adapter policy (harness codex|claude; absolute executable; argv template starting
with `<EXE>` and ending with one `<ENVELOPE>`; forbidden resume/bypass flags incl. `=` forms; codex needs
`exec`, a read-only or workspace-write sandbox, `--ask-for-approval never` and the bare `--json` exactly
once (identity is bound from its `thread.started` event); claude needs `-p`, `--output-format stream-json`,
`--permission-mode dontAsk`, `--session-id <WORKER_INSTANCE>`; wall clock > launch floor; classes ⊆
{consult, job}); class rules (consult: no lock/effects/artifacts; job: bound lock key + empty effect
directory + artifact contract `NAME=line:<text>` or `NAME=sha256:<hex>`, one or more); pins the operating
files (SKILL, RECOVERY, helpers, PROTOCOL, template) by sha256; computes the worker-addressed request bytes
and ONE immutable envelope file; persists PLAN.json, REQUEST.bytes and STATE.json (`prepared`) BEFORE
publishing; `publish` is an idempotent continuation (prepared → published).
publish / replay preflight: REQUEST.bytes is read once; that exact buffer must hash to the plan's request
digest and carry the plan's id and recipient, or nothing is published.
launch: re-checks policy and envelope hashes; refuses a finished run and a deadline within the launch floor;
`starting`; reserves capacity atomically in `<root>/.adapter/launch/` (reserved/starting/running/unknown
records count as live; corrupt or unsupported records count as live AND recent until moved out under a
recorded decision bound to actual evidence — a pre-spawn certainty or a verified cessation record, never
elapsed time; a refused reservation returns the run to `published`). From the reservation on, the attempt
is bracketed: the monotonic deadline is anchored at the reservation (setup and record writes count), the
annotation and every record write are inside the bracket, the child is spawned with stdin=/dev/null in its
own process group, LAUNCH.json + SUPERVISOR.json are written, the STOP file is honoured (owned
cancellation), the group is reaped and swept, the harness response is classified (`task_outcome`
validation_failed when the worker returned `WORKER_VALIDATION_FAILURE`, else unclassified), and the final
supervisor record is written on every path (outcomes ok / timeout / stopped / nonzero-exit / launcher-failed
/ setup-failed / supervisor-error / cleanup-unknown). Final persistence order: the supervisor record, then
STATE and the journal, then the ledger LAST; the ledger becomes `ended` only when every earlier record was
durably written, otherwise it is written `unknown` (capacity retained), and a failed ledger write leaves it
as it was. Every persistence failure is recorded as `persistence_errors` (in the supervisor record when
writable, in a fallback PERSISTENCE_ERRORS.json, in the caller's result and on stderr); `verify` then fails
"launch finalization resolved" and replay is impossible until the run is reconciled. Durability is never
promised when storage fails. The worker's task result is classified from the DESIGNATED final response only
(the `-o` last-message file; else the last completed agent message of the event stream; else, for the raw
route, the last non-event stdout line): `validation_failed` when it starts with `WORKER_VALIDATION_FAILURE`
and carries a JSON object with a reason and this run's job/attempt; `inconclusive` when the marker is at the
result boundary but the payload is malformed or belongs to another job, and also when the designated
response is missing, unreadable or empty (never a success label); `unclassified` for an ordinary non-empty
response — mentions in commentary never count.
bind: OBSERVED identity from harness output (codex `thread.started`; claude stream-json `session_id`, which
must equal the pre-chosen `--session-id`; every identity event must agree) == the alias's hello instance →
BIND.json (provisional); otherwise BIND.pending.json. Bind gives up early, with the reason, when the run has
ended or its launch was refused (unchanged on two consecutive polls after the launch floor).
wait: polls the bus every 0.25 s for the pinned terminal reply (sender alias + observed identity + task/job/
attempt) and journals the requester's OWN first sightings in OBSERVATIONS.jsonl: lock OWNER with the
worker alias + bound identity (token digest remembered); each expected artifact's bytes hashed between two
OWNER reads (`held_by_bound_worker` only when both reads show alias, identity and that token digest); the
final record's bytes hashed FIRST, then the whole `.messages` store scanned for a terminal reply
(`terminal_absent_after_snapshot`); the terminal reply with the final record's digest at that instant.
WAIT.json on success, else WAIT.pending.json.
verify (read-only): supervisor outcome + task result (must be unclassified) + cessation + launch finalization
resolved (no persistence errors, ledger ended, run ended) + the envelope file present as a regular file
with the plan's digest; identity chain (harness output ==
provisional == hello == checkpoint == final record == terminal sender-session); terminal reply re-read from
`.messages` with exact correlation headers, `envelope-sha256`, `input-digests` and `effect-sha256` (one
artifact: its sha256; several: the sha256 of the sorted `NAME SHA256` map); request bytes: prepared digest
== plan, stored == prepared == archived, not pending; checkpoint request_id/class/task/job/attempt exact and
`handled_ids == [request id]` exactly; final record fields exact, `envelope_file` == plan, `handled_ids ==
[request id]` exactly, consistent with the checkpoint; final record bytes == the requester's first snapshot
(write-once); the ordering snapshot predicate; lock directory absent + `release_results[key]` exact (parsed
object) + token bundle outside the bus; effect directory holds exactly the declared artifacts as real files
with the declared digests; per-artifact ownership snapshot predicate; heartbeat idle with the identity;
optional late-message and barrier timing checks. RESULT.json is write-once with a snapshot RECOMPUTED from
bytes (plan, request, envelope, archived copy, terminal record, artifacts, worker inbox);
`frozen_envelope_contract` = PASS (no failed, no unverified) / PASS-WITH-UNVERIFIED / NOT PASS;
`no_failed_checks` is the weaker Boolean.
replay (gated exercise): only after contract PASS; refuses unless the snapshot's envelope/request digests
equal the plan's; recomputes the snapshot from the current bytes and refuses on any drift; republishes the validated buffer and proves the archived copy is returned, nothing is
re-enqueued and artifact hashes are unchanged.
Exit statuses (CLI): 0 only for the documented success (published, launch outcome ok without a validation
failure or persistence error, bound, terminal reply, contract PASS, replay idempotent); 2 = refusal or
pending; 3 = PASS-WITH-UNVERIFIED; 1 = every other non-success. Callers inspect the structured verdict.
Not implemented on purpose: any external signalling of a worker (only the supervising process stops its own
child), retries of uncertain effects, participant retirement, whole-tree cessation claims, reinterpretation
of unsupported ledger records in place, claims of continuous ownership or durability from polling.

## 7. Triggers (optional, user-applied)
`references/TRIGGERS.md`: one-line snippets for a global `CLAUDE.md` and a global `AGENTS.md`:
"If another agent session works on the same checkout, coordinate through the agents-bus skill."
The package never edits instruction files.

## 8. Exercises and gate (all under tmp until the real agreement)
1. Unit tests (helper owner): discovery candidates (two markers → refuse / `--join`; marker vs
   bus.json mismatch → corrupt; realpath aliases deduplicated; explicit root from the install
   dir), interrupted and concurrent init with adoption, incompatible-root refusal, duplicate-alias
   refusal, same-instance refresh under the guard, bind/acquire serialization (bind cannot slip
   between resolve and mkdir), component-overlap refusal, partial multi-key rollback, wrong-owner
   and missing-token release refusal, ownerless directory treated as occupied, identifier
   validation, claim-registry refusal, compatible retries.
2. Real peer portability: scratch root `/private/tmp/agents_bus_scratch_<date>/`; one of us
   `init`s, both `hello`, one request/reply round trip with receipt-first + keepalive wait, one
   lock acquire/release each with token files, one wrong-owner release refused, one alias
   collision refused, one `bind` followed by an acquire of the new key.
3. Context-free discovery reader (part of the core tests): a fixture reader with no conversation
   context, given only the installed instructions and the scratch root, must resolve the bus via
   the marker rules of §1 and read one message. Kept separate from any future delegation
   capability experiment; a fixture never counts as peer consent.
4. Controlled recovery drill (RECOVERY D) RE-RUN for this design on the scratch bus, since
   identity and locks changed. Wording: "controlled simulation", never "a real crash was tested".
5. Then: manifest v2 (design rev + helper bytes + test log + scratch-run + drill evidence), both
   literal agreements with reciprocal receipts, package v3 (SKILL/RECOVERY/TRIGGERS text +
   helpers) cross-reviewed, mirrors synced and hash-verified.

## 10. Helper surface (CLI)
Transport stays in the tested `bus.py` (`publish`, `wait`) and the gate in `gate.py`, both
byte-unchanged. Administration is a separate `admin.py` addressing the bus by coordination root:
```
admin.py init     --root R [--bus B] [--agent NAME …]        (aliases optional; an empty bus is valid, hello adds aliases later)
admin.py discover --root R [--bus B] [--join BUS_ID]
admin.py hello    --root R --agent A --harness H --instance S [--primary P] [--keepalive K]
admin.py bind     --root R --agent A --instance S --key K --resource PATH
admin.py lock acquire --root R --agent A --instance S --key K [--key K …] --purpose P --token-file NEW_PATH
admin.py lock release --root R --agent A --instance S --key K [--key K …] --token-file PATH
admin.py lock show    --root R
```
Same-instance `hello` with omitted or partial activation flags preserves/merges the recorded
capability. Unknown claim-registry formats fail conservatively; every registry claim is treated
as external (alias equality proves no identity). An empty `AGENTS_BUS` value is ignored, not
treated as an explicit candidate. `lock release` prints `{state: released|not_held, released:
[...], not_held: [...]}`; `lock show` prints public metadata only. `init` records the installed
package identity (`MANIFEST.json` digest) when it can detect it.

## 9. Ownership
Codex: core helpers (`init`, `hello`, `bind`, `lock`, discovery) + unit tests + local test log
under `prototype/universal_v2/`; no `delegate` module in this release. Claude: this design, SKILL.md/RECOVERY.md/TRIGGERS.md
text, the scratch-run, drill and capability-experiment ledgers. Each reviews the other's part
before the gate. Neither touches the installed package or mirrors before the gate passes.

## 11. Revision-4 amendments (rev 13) — verbatim DESIGN_v3_rev4.md sha256 890c9f50dc35abd06ca5ca769d7cb7c83400b392ec9d32da268ea2a9d4b41242

# agents-bus v3 → revision 4 — CANDIDATE DESIGN (Claude, 2026-09-14; staged, not operative)

Status: staged candidate. It supersedes the proposal `DESIGN_v3_rev4_proposal.md`
(d7416cad2be4f92fcbed113394186f98e2a63e615d3cb7026bc33cfa74ef2eca) by incorporating every
replacement text of `CODEX_SECTION_VERDICTS.77c24350.md`. Nothing here is operative: revision 3
and the legacy bus rules stay in force until the activation records of §8 exist. No installed or
canonical skill, protocol or helper file is touched by this candidate; the staged payload lives
beside this file (`SKILL.md`, `references/RECOVERY.md`, `CHANGES.md`).

## Scope

S1 is the portable agents-bus package amendment, including the transport-envelope convention. S2
is an explicitly recorded opt-in for this established primary legacy bus; installing S1 alone does
not activate S2. S3 is the ReferenceBook project amendment, including its typed disposition-packet
adapter and the separately named A7 inventory/audit change. Book item ids, correction decisions,
proof status and ledger mutations are not generic bus semantics. Each scope names its affected
files, candidate and evidence hashes, tests, and activation record. Existing trust, ownership and
session-local user authorization remain unchanged.

Use the checkpoint base prescribed by the ACTIVE bus version: v2 participant files and admin
commands are never silently required on this legacy bus. That caveat is carried in the payload
itself — SKILL §10 (unit journal), SKILL §11 (handled record and lock inspection) and RECOVERY G
(preamble) each name the active bus version as the source of their paths and commands — because
the primary legacy bus at `tmp/agents_bus/` has no `bus.json`, no `checkpoints/` directory (it
uses `checks/<task>/`), hand-managed `OWNER` records without token bundles, and a `PROTOCOL.md`
stating that no admin command of the new package is run against it. Correction of record: the
review request's receipt deadline (13:45Z) preceded its own creation time (14:09:07Z); Codex
acknowledged it promptly and inferred no timeout authority from it. Nothing in S1 changes SKILL §8
(trust) or §9 (governance).

**Per-scope bindings.** Each scope names its affected files, candidate and evidence hashes, tests
and activation record. Only S1 is staged and hashed today; the S2 and S3 rows are the contract
those scopes owe before release step 2, and review has nothing to check them against until they
are filled in.

| scope | affected files | candidate / evidence hashes | tests | activation record |
|---|---|---|---|---|
| S1 portable package | `SKILL.md`, `references/RECOVERY.md`, `references/DESIGN_v2.md` rev 13 (staged here); `MANIFEST.json` at release; 20 further package files byte-identical to the preceding revision | in `CHANGES.md` (payload table) + the five evidence hashes of §0 | R1–R4 (§7) on a scratch bus, plus the §9-required RECOVERY C handoff and D joint recovery | the canonical copy and both installed mirrors, verified byte-identical, with the install recorded per §8 step 5 |
| S2 legacy-bus opt-in | OWED: this bus's `PROTOCOL.md` (the opt-in paragraph and the checkpoint base it keeps) and the bus-level activation note; NO file is staged or edited by this candidate | OWED: the pre- and post-hash of each file it touches | OWED: the re-entry rehearsal of RECOVERY G against THIS bus's own paths | OWED: a dated opt-in entry in the bus's `STATE.md` Shared log naming the S1 release manifest it opts into; installing S1 does not write it |
| S3 ReferenceBook adapter + A7 | OWED: the project's typed disposition-packet adapter and schema file, the A7 inventory/audit change, and the ledger docs they govern — all outside this package | OWED: adapter, schema and frozen-packet hashes | R5 (§7) against SCRATCH ledgers only, plus the A7 snapshot-binding checks of §6 | OWED: the project's own activation entry; neither S1 installation nor the S2 opt-in writes it |

## 0. Measured motivation — corrected census (primary bus, headers only)

Headers with `created-at` in [2026-09-14T03:00Z, 13:00Z) contain 209 unique messages, including
41 requests and 44 `received`-state messages (21.05%). Exact matching uses `re`, `task`, reversed
sender/recipient, expected session and a non-negative timestamp difference.

| measure | value |
|---|---|
| unique messages / requests / `received` | 209 / 41 / 44 (21.05%) |
| first separate receipts observed | 39 of 41; median 220 s; nearest-rank p90 1395 s |
| first substantive (`accepted`/`blocked`/`done`) observed | 37 of 41 |
| Claude → Codex substantive, n = 32 | median 772.5 s; p90 5428 s; max 6039 s |
| Codex → Claude substantive, n = 5 of 9 | median 205 s; four cases right-censored at 13:00Z |
| substantive response within 30 min | 30 of 41 |
| substantive response within the 120 s receipt budget | 2 of 41, and both already omitted a separate receipt |

Therefore 30-minute responses do NOT show that those receipts were redundant. All 14 separate
receipts that arrived within 120 s preceded substantive answers later than 120 s; this sample
contains no separate receipt the same-window optimization of §2 would have removed. A fast
substantive-first reply remains a sensible PROSPECTIVE optimization, and that is the only claim
§2 rests on. These are reported creation-time latencies — not delivery, activation or CPU
measurements, and not proof of the cause of any queueing. The population fingerprint
(`e4999359d64e09bebf76bd31fc0ad44798804a60e1cc943e76db0b718bc50df8`) and all 41 request rows are in
Codex's metrics report, which is NOT beside the verdicts copy staged here but in Codex's own
evidence directory (all paths under `RadiiPolynomial/tmp/agents_bus/checks/book_formalization/`
`codex/protocol_rev4_review_140907/`):

| evidence file | sha256 |
|---|---|
| `METRICS_RECEIPTS_CUES.md` (§0 census, §2–§3 review) | `d4ffe30020ed7fdb62a1ad1aa01d7bc4cf0aaa101d4b7c5eb84d677bde860858` |
| `RECOVERY_DRILLS.md` (§5, §7) | `5bac4341def48e0770cc5aa4b2ffc4f6c04a70a70f6a4c955819d8588d11a630` |
| `SCHEMA_RELEASE_AUDIT.md` (§4, §6, §8) | `539bb272a92e2dbd51e90954c84581157b5fd8719fa6dc05aa56a60bace6c20e` |
| `SECTION_VERDICTS.md` = the staged `CODEX_SECTION_VERDICTS.77c24350.md` | `77c2435096cf101dd66cbde25848b26c46a6731b4663a48b8a87b1e1b421ae5d` |
| `DESIGN_FROZEN.md` = the reviewed proposal | `d7416cad2be4f92fcbed113394186f98e2a63e615d3cb7026bc33cfa74ef2eca` |

Those five hashes are what release step 2 binds for the §0 numbers; "beside this file" in the
verdicts text refers to that directory, not to the staging directory.

Separately evidenced OPERATIONAL OBSERVATIONS, not established by this header census and labelled
as such wherever they are used: cue counts and the two caller mistakes; the 10:53Z quota
force-termination event and its child-death report; the packet-shape count. In particular, one
peer-reported quota event does not establish that every future Claude child dies with its parent.

## 1. Delegation on receipt — bounded parent units (SKILL §10)

**Scheduling.** Main handles intake, deduplication, short control work and final responsibility.
It routes substantive work into bounded independent child units when scope and capacity permit.
With no eligible child slot it queues work truthfully or performs only a bounded permitted parent
unit; it does not recurse into unlimited delegation. Follow the project's worker rules. Parent
intake occurs before and after each bounded main unit and at tool/wait boundaries; waits are at
most 55 s. A 10-minute worker unit is not permission for 10 minutes of uninterrupted parent work.
Time and size limits trigger checkpoints, never a fabricated completed verdict.

Answer with the FIRST reply required by §2, rather than mandating a separate `received` message
where §2 permits a substantive first reply. If the parent ends its turn, only an actually
available later activation route can resume it; an in-turn wait cannot reopen an ended turn.

**Unit journal.** Before each launch OR reuse/follow-up, persist a new ATTEMPT RECORD: unit,
attempt and request ids; request and input-manifest digests; task; parent instance; intended
worker label/route; null observed handle; `launch_intent_at`; null `launched_at`; the
attempt-specific scratch path; expected outputs; canonical targets and expected base hashes;
validation profile; next safe action. Persist `launch_pending` immediately before the call and
bind the returned identity afterwards. Interrupted dispatch is `launch_unknown` until actual
evidence resolves it. Keep earlier attempts; never reset them.

Execution distinguishes `planned`, `launch_pending`, `running`, `candidate_ready`, `validated`
and `closed`, with explicit `launch_unknown` / `effect_unknown` / `failed` / `cancel_requested`
conditions. Publication separately distinguishes `not_started`, `prepared`, `publishing`,
`committed` and `publication_unknown`; SKILL §10 gives each of the five an operational
consequence, so none is enum-only. The current headless adapter (`scripts/delegate.py`) already
supplies much of this pattern, but under its OWN names — ledger
`reserved`/`starting`/`running`/`unknown`/`ended` and plan `prepared`/`starting`/`published`, with
none of `launch_pending`, `launch_unknown`, `candidate_ready`, `closed`, `effect_unknown`,
`cancel_requested`, `not_started`, `publishing`, `committed`, `publication_unknown`,
`observed_handle` or `launch_intent_at` present in the helper, and its `prepared` meaning a
prepared PLAN rather than a prepared publication. The mapping is therefore owed work, not an
existing conformance, and native children need an equivalent thin journal, not an assumed
enrolment.

**Publication.** A completion record binds unit, attempt, request/input digests, the exact output
set with hashes, and evidence. Worker `compiled: true` is only a report. The parent freezes and
independently validates those bytes under the intended module, toolchain and dependency
generation with artifact-specific checks. Only a validated candidate can enter publication, after
the authorized publisher acquires its locks, rechecks current base/dependency hashes and persists
publication intent.

One rename is atomic for one file. Multiple files require either an immutable generation pointer
pinned by readers, or a journaled `unavailable` batch whose cooperating readers hold exclusion,
pin a snapshot, or validate/reject concurrent generations. A one-time marker check is
insufficient. Readers must not ACCEPT a partial generation; this does not guarantee that no reader
ever physically sees mixed files. Reconcile old/new hashes after interruption; an unexpected third
hash is a conflict. Clear unavailability only after the complete intended generation and its
validation record are established.

## 2. First reply and cues (SKILL §5, §7)

**Receipt rule (replaces "receipt first").** The first valid, correctly correlated reply satisfies
the receipt requirement; its state retains its meaning. Small control work may answer `accepted`,
`blocked` or `done` immediately instead of sending `received` first. Otherwise send `received`
promptly before longer work, not near the deadline based on an optimistic completion estimate.
Explicit receipt-first instructions take precedence. Match `re`/`task`/sender/session and required
input hashes. A terminal-first reply is processed once; a later weaker receipt never regresses the
state. `accepted` satisfies the receipt clock, not a job's completion criterion. Handoff
acceptance precedes effects; special release/agreement receipts remain explicit. Info/status
notices and receipts need no acknowledgment. Keep existing inquiry/timeout defaults and their
no-permission semantics.

**Cue rule.** Publish first; use only the target/host/lifecycle route actually verified.
`idle`/`waiting` heartbeat values are historical observations, not proof of native task idleness.
Record the command in the host's route configuration, not in portable policy. Coalesce pending ids
and generation under one caller/target cue attempt, with intent before dispatch, actual
result/handle or `dispatch_unknown` afterwards, and explicit target re-entry/drain evidence for
`observed`. Reconcile uncertainty before duplicating a dispatch.

Task, cue attempt and long-lived watcher are separate lifecycles. A receipt does not finish the
task, cancel its watcher or settle other covered requests. An observed cue CAN be settled while
work remains; otherwise a "never retire" rule strands the next activation. Recheck pending
generation and uncovered ids after drain/retirement so a concurrent new request gets the next
eligible cue. Late duplicate cues are harmless after reconciliation. Unknown runtime status does
not authorize reassignment or takeover.

Route surface, checked 2026-09-14 by Codex without dispatching a cue:
`/Applications/ChatGPT.app/Contents/Resources/codex queue --help` succeeds and exposes
`--thread`/`--message` (the `PATH` `codex` has no `queue`). That confirms the command surface, not
guaranteed execution after deletion, force termination or quota denial.

## 3. Work units, delivery groups and independent review (SKILL §10)

Work units have exact item/part membership, input digest, outputs and a safe checkpoint; use the
project's stricter limit. ReferenceBook currently uses AT MOST 8 NUMBERED ITEMS within one
section. A report packet may aggregate about 25 endpoints across several completed units, but this
is a DELIVERY GROUP — not a new uninterruptible work unit, and not permission to mark the whole
request done early.

Interleave independent review and drafting at checkpoints, with priority for older blocking work
and bounded capacity, preserving evidence before switching and holding no peer-needed lock during
waits. Include source/declaration snapshots and correction-contract records with requests.
Self-checks may be attached, but independent reviewers record their OWN source/type assessment
before reading the author's findings. Changed inputs reopen the affected unit only.

## 4. Transport envelope (S1) vs versioned typed project packets (S3)

`envelope: 2` is an optional transport-version convention activated per adopted bus; header values
remain strings. Ordinary v1 transport stays readable. A transport version never grants automatic
project-ledger mutation.

ReferenceBook uses a VERSIONED PROJECT ENVELOPE naming schema/kind, packet/request/task identity,
author/reviewer session, creation time, input-manifest digest, and the proposal or consultation
being decided. Replacing an effective record also binds its expected prior digest. Correction
items carry their current source-item digest using the declared extractor algorithm and length,
the exact replacement or an explicit endpoint-unchanged meaning, reason and location, and
content-hashed typed evidence.

The six correction decisions retain separate meanings: `accepted` approves a proposal;
`proof_only` leaves its endpoint unchanged; `interpretation` records an exact scoped reading;
`rejected` rejects that proposal without erasing another accepted record; `needs_consult` settles
nothing; `applied_to_edition` reports an actual authorized effect with before/after file and item
hashes, the preserved original, errata/editorial evidence and regenerated binding.
`coverage_repair` belongs only to the separate typed coverage map and never counts as correction
approval, proof or closure.

Validate the WHOLE packet — correlation, source/base hashes, required fields, schemas, duplicate
and conflicting keys — before any binding effect. Unknown or free-text values are retained for
explicit consultation or rejection, not silently normalized into accepted records. Keep one
effective replacement, with old versions as provenance. Pin input bytes and publish the resulting
project update atomically or journaled; do not partially promote a malformed packet. The generic
bus `state` enum remains unchanged.

The proposal's packet shape (`evidence: [paths]` plus `request_id` alone) is insufficient. S3 owns
the actual adapter and its mapping to current ledger states; S1 only describes how a typed, hashed
artifact is transported.

## 5. Force termination and re-entry (SKILL §11; the proposal's §5 is REJECTED and replaced)

Stopping a parent may or may not stop children/watchers; behavior is harness- and event-specific.
Read the active protocol and durable task/attempt/publication records, inspect actual handles and
ownership, and publish recovery status before resumed effects. Reconcile continuations before
re-arming; an arming may have succeeded before its handle was recorded.

Missing COMPLETE means incomplete/unknown evidence, never death by inference. Matching COMPLETE
means `candidate_ready`, never immediate publication. Reconcile launch identity, actual
status/cessation scope, output/input hashes and publication state independently. A retry requires
proven non-spawn, or verified cessation within the required scope PLUS reconciled effects. Use a
new attempt and scratch identity for the same logical unit. If publication already happened,
recognize its hashes and finish the record once instead of applying again.

Locks do not expire. 30 minutes is an ESCALATION THRESHOLD, not a lease; there is no renewal
semantic. At most one notice per episode gives observed age/owner/key/dependency and leaves
ownership unchanged. Same-instance owners release or continue only matching locks after checking
that delegated work is not still using them; replacement instances inherit no token authority.
Predecessor recovery follows the active verified-cessation and explicit-decision rule.

Activity/heartbeat timestamps and progress sequences are observations, not a busy/dead classifier.
A 45-minute threshold may trigger a single user notification but does not restart expired polling,
override earlier response budgets, cancel remote work or free locks. Respect known quota pauses.
Defaults act only on the sender's authorized work. Queue submission is not guaranteed activation
across force termination; reconcile route/watcher lifecycle evidence before relying on it.

Explicitly NOT retained from the proposal: "running without a completion record → `dead`, relaunch"
and "running with a completion record → publish". Those were the central remaining correctness
failures. Re-entry order: `references/RECOVERY.md` checklist G.

## 6. Tooling cross-reference (S3, ReferenceBook only) — A7 with snapshot binding

A7 is a separate ReferenceBook amendment; installing the generic skill does not implement it. Bind
THREE scopes: (i) current root-reachable proof/configuration/library/dependency/trust/tool
evidence; (ii) an immutable all-draft inventory generation and its digest; (iii) source-contract
inputs. Marker and candidate scans read those SNAPSHOTS, never unbound live drafts. Reachable
inventory entries agree with the proof snapshot. Recompute current root reachability and recheck
the affected set and bytes before publication; missing or unsupported headers, new imports,
renames/deletions and mismatches FAIL CLOSED. Report inventory freshness explicitly. An
unavailable publication generation remains unreadable for acceptance until resolved.

Unrelated isolated scratch edits can avoid invalidating this snapshot; relevant source changes
must still refuse a stale generation. The existing per-module freshness and root-reachability
checks are preserved. A multi-file canonical replacement uses the generation pointer or journaled
`unavailable` batch of §1.

## 7. Drills before the §9 agreement gate

Every drill needs its OWN scenario checker and hashed evidence. `gate.py` checks only the later
bilateral agreement-record consistency: it does not inspect filesystem hashes, authenticate
actors, run drills or prove behavioral predicates. Do not feed fake-actor drill fixtures to the
real agreement gate. The drills below are Codex's offered responsibilities after the corrected
candidate and a concrete immutable scratch drill packet are frozen and the round is coordinated;
they start no services, release no locks and authorize no production writes. No R1–R5 drill has
run yet.

| drill | required cases | ownership |
|---|---|---|
| R1 first-reply | `accepted`-first without `received`; `done`-first; a late weaker receipt; wrong-task/sender/hash replies. `accepted` leaves work pending where appropriate; no false timeout or state regression | Codex owns the scratch requester/waiter checks |
| R2 coalesced cue | publish-during-drain; one-of-many receipts; uncertain submission; an active parent with a `waiting` heartbeat; coalescer records verified | Codex receives/drains on the scratch bus and verifies the coalescer records; Claude owns its already available native queue caller. A fake cue checks state logic only; an actual activation claim needs a separately observed real route |
| R3 unit recovery | deterministic scratch recovery simulations for unbound launch, absent/stale completion, candidate validation, mid-publication, and post-swap/pre-receipt. Unknown attempts preserved; unsafe replay rejected | Codex owns them. An optional stop of a specifically owned scratch child needs the actual stop and cessation evidence and proves only that scope. Codex will not kill a live parent/Claude session and will not treat a native interrupt acknowledgment as proof that every subprocess stopped |
| R4 escalation threshold | a scratch sentinel aged past the threshold: exactly one notice, no takeover. Actor status stays UNKNOWN initially, otherwise the test misses the dangerous inference. Same-owner release follows reconciliation, not expiry | Codex ages the sentinel and verifies |
| R5 typed packet | the frozen typed schema validated/applied against SCRATCH ledgers: all decisions, duplicate keys, unknown schema/tags, stale item/base/input digests, cross-map conflicts, and an applied-effect record with absent/mismatched evidence. Invalid packets have no binding effect | Codex independently validates/applies and both sides compare outputs |

Retain the §9-required real handoff exercise (RECOVERY C) and joint recovery drill (RECOVERY D);
these scenario tests do not erase that gate.

**Native children when the Codex parent ends: still UNVERIFIED.** Active-parent parallel execution
is observed; after-final-turn and force-termination survival and re-cue are not established. The
design is finalized by treating that route as unsupported/unverified and retaining the
ACTIVE-PARENT default; it does not wait on an unsafe or unrequested whole-session termination
experiment. Claude Code children dying with the session is likewise recorded as an observation
with ONE source — the 2026-09-14T10:53Z peer-reported quota force-termination — and that single
event establishes nothing about every future Claude child.

## 8. Release order

1. Agree per-scope design and stage the complete candidate under prototype paths; do not replace
   operative canonical/installed files.
2. Freeze candidate payloads before testing, exercise the corrected drills and the required
   handoff/recovery exercises, and preserve independently checked evidence. Freeze the release
   manifest with the exact tested payload and evidence hashes. Any later semantic, helper or
   payload change reopens the affected review and tests.
3. Exchange actual bilateral §9 agreements and reciprocal evidence bound to that design, release
   manifest and test run. Run `gate.py` for record consistency, and separately verify provenance,
   behavioral evidence and authority.
4. Use applicable direct session-local authorization to install only those payloads. Keep the
   release manifest DISTINCT from the installed `MANIFEST.json`: either freeze the latter too, or
   use a pre-reviewed deterministic metadata derivation whose actual output is checked
   byte-for-byte. Do not create circular self-hashes or silently change payload bytes after
   agreement. The byte checks at this step include: `MANIFEST.json` `version`/`revision` agree with
   the release manifest; the `SKILL.md` and `references/RECOVERY.md` hashes in `MANIFEST.json`
   equal the frozen payload hashes; and `SKILL.md` carries NO hand-written revision number, so the
   number has exactly one source (`command grep -nE '[Rr]evision [0-9]' SKILL.md` returns nothing
   asserting a number).
5. Verify the required canonical and installed mirrors, then record activation. S1 installation,
   this legacy bus's S2 opt-in, and the S3 schema/A7 changes activate SEPARATELY. Revision 3 and
   the legacy rules remain operative until THEIR actual activation records exist — not merely the
   agreement messages.

No installation authorization is requested at this design stage. A peer-authored user paste is not
authorization until the user directly supplies it in the relevant session.

## Change log vs proposal d7416cad

| # | proposal location | incorporation |
|---|---|---|
| 1 | Scope paragraph | REPLACED by Codex's scope text: S1 portable package (incl. transport envelope), S2 explicit legacy-bus opt-in not activated by S1 installation, S3 ReferenceBook adapter + A7; per-scope files/hashes/tests/activation record; project item ids and ledger mutations are not bus semantics; active-bus checkpoint base, no silent v2 requirement; recorded the 13:45Z-vs-14:09:07Z receipt-deadline correction |
| 2 | §0 table | REPLACED by the corrected census (209/41/44 = 21.05%; 39/41 receipts, median 220 s, p90 1395 s; 37/41 substantive; Claude→Codex n=32 median 772.5 s, p90 5428 s, max 6039 s; Codex→Claude n=5 of 9, median 205 s, four right-censored; 30/41 within 30 min; 2/41 within 120 s). The claimed p90 54 min and 28/41 are dropped |
| 3 | §0 inference | REMOVED: "receipt carried no information" / receipts-were-redundant. Replaced by Codex's finding that all 14 within-120 s receipts preceded later substantive answers, so the sample contains no receipt the optimization would have removed; the optimization is prospective only |
| 4 | §0 non-header claims | Cue counts, the force-termination/child-death event and the packet-shape count are relabelled separately evidenced operational observations; one quota event does not establish universal child death |
| 5 | §1 scheduling | REPLACED by Codex's text: intake/dedup/short control/final responsibility in main; route when scope and capacity permit; queue truthfully or one bounded parent unit with no slot; no unlimited recursion; project worker rules; intake at boundaries; waits ≤ 55 s; a 10-min worker unit is not 10 min of uninterrupted parent work; limits trigger checkpoints, never a fabricated verdict. The proposal's "> 10 minutes or > 1 file" delegation trigger is no longer a licence for uninterrupted parent work |
| 6 | §1 receipt coupling | Uses the §2 first reply instead of mandating a separate `received`; an ended parent turn is resumable only by an actually available route (an in-turn wait cannot reopen it) |
| 7 | §1 UNIT JOURNAL | REPLACED by the attempt-record text: a new attempt record before each launch OR reuse/follow-up; unit/attempt/request ids, request and input-manifest digests, parent instance, intended route, null observed handle, `launch_intent_at`, null `launched_at`, attempt-specific scratch path, expected outputs, canonical targets + expected base hashes, validation profile, next safe action; `launch_pending` before the call, identity bound after; `launch_unknown` on interruption; attempts kept, never reset |
| 8 | §1 single `state` enum | REPLACED by two state sets: execution (`planned`/`launch_pending`/`running`/`candidate_ready`/`validated`/`closed` + `launch_unknown`/`effect_unknown`/`failed`/`cancel_requested`) and publication (`not_started`/`prepared`/`publishing`/`committed`/`publication_unknown`). The proposal's single `planned|running|complete|published|dead|abandoned` is dropped |
| 9 | §1 publication | REPLACED: a completion record is a CANDIDATE only; worker `compiled: true` is a report; the parent freezes and independently validates under the intended module/toolchain/dependency generation; publication only after the authorized publisher takes locks, rechecks current base/dependency hashes and persists publication intent |
| 10 | §1 multi-file swap | REPLACED: one rename is atomic for one file; several files need an immutable generation pointer pinned by readers or a journaled `unavailable` batch with the reader rules (exclusion, pinned snapshot, or validate/reject); a one-time marker check is insufficient; readers must not ACCEPT a partial generation (no physical-visibility guarantee); reconcile old/new hashes after interruption, third hash = conflict; clear unavailability only after the complete generation and validation record |
| 11 | §2 R-a/R-b/R-c | REPLACED by the first-valid-correlated-reply rule with its explicit exceptions (prompt `received` otherwise; explicit receipt-first instructions win; correlation on `re`/`task`/sender/session/input hashes; terminal-first processed once; no state regression by a later weaker receipt; `accepted` ≠ completion; handoff acceptance before effects; release/agreement receipts explicit; no acknowledgment of info/status/receipts; inquiry and timeout defaults unchanged) |
| 12 | §2 CUE POLICY | REPLACED: verified route only; heartbeat `idle`/`waiting` is a historical observation, not proof of native idleness; command recorded in host route configuration, not portable policy; coalescing with intent/actual/`dispatch_unknown` and drain evidence for `observed`; three separate lifecycles; an observed cue IS retired while work continues (the proposal's "receipts never retire a cue" wording would strand the next activation); recheck pending generation and uncovered ids after drain; reconcile before duplicating; unknown status authorizes nothing. Codex's 2026-09-14 `--help` check of the app binary recorded as a surface check only |
| 13 | §3 unit size | REPLACED: exact item/part membership, input digest, outputs, safe checkpoint; project's stricter limit; ReferenceBook = at most 8 numbered items per section. The proposal's "≤ ~25 endpoints" survives only as a DELIVERY GROUP for report packets — not a work unit and not early completion |
| 14 | §3 review independence | ADDED: interleave at checkpoints with priority for older blocking work and bounded capacity, evidence preserved before switching, no peer-needed lock held during waits; requests ship source/declaration snapshots and correction-contract records; self-checks attached but the reviewer records its own source/type assessment BEFORE reading them; changed inputs reopen only the affected unit |
| 15 | §4 envelope | REPLACED: `envelope: 2` is OPTIONAL and per-bus-activated, v1 stays readable, values stay strings, and a transport version grants no ledger mutation. The proposal's "header on every message written under rev 4" is dropped |
| 16 | §4 packet schema | REPLACED by the versioned PROJECT envelope owned by S3 (schema/kind, packet/request/task identity, author/reviewer session, creation time, input-manifest digest, decided proposal; prior-digest binding when replacing an effective record; per-item source digest with declared extractor algorithm/length, exact replacement or explicit endpoint-unchanged meaning, reason/location, content-hashed typed evidence) |
| 17 | §4 dispositions | REPLACED by the six separated meanings plus `coverage_repair` confined to the typed coverage map; whole-packet validation before any binding effect; unknown/free-text retained for consultation or rejection, never normalized; one effective replacement with old versions as provenance; atomic/journaled project update; no partial promotion; the generic bus `state` enum untouched. The proposal's `evidence: [paths]` + `request_id` shape is recorded as insufficient |
| 18 | §5 (whole section) | REJECTED AS WRITTEN and REPLACED by Codex's force-termination text. Removed: "missing COMPLETE → `dead` + relaunch" and "`running` with a completion record → publish"; LEASE language and lock renewal; "watchers of a dead Claude session are gone" as a settled generality about queue activation |
| 19 | §5 locks | REPLACED: locks never expire, 30 min is an escalation threshold with no renewal semantic, one notice per episode with observed age/owner/key/dependency, ownership unchanged, same-instance release only after checking delegated work, replacement instances inherit no token authority, predecessor recovery by verified cessation + explicit decision |
| 20 | §5 liveness | REPLACED: timestamps, heartbeats and progress sequences are OBSERVATIONS, not a busy/dead classifier; the 45-minute threshold triggers a SINGLE user notification and changes no budget, lock, or remote work; quota pauses respected; defaults act only on the sender's own work; queue submission is not guaranteed activation across force termination |
| 21 | §6 A7 | AMENDED per Codex: three bound scopes (current root-reachable evidence; immutable all-draft inventory generation + digest; source-contract inputs); scans read snapshots, never unbound live drafts; reachable inventory agrees with the proof snapshot; recompute reachability and recheck affected bytes before publication; fail closed on missing/unsupported headers, new imports, renames/deletions, mismatches; report inventory freshness; an unavailable generation is unreadable for acceptance; per-module freshness and root-reachability checks preserved; installing the skill does not implement A7 |
| 22 | §7 drills | AMENDED: each drill gets its own scenario checker and hashed evidence, and `gate.py` is scoped to bilateral agreement-record consistency only (no filesystem hashes, no actor authentication, no drill execution, no behavioral predicates; no fake-actor fixtures at the real gate). R1–R5 rewritten with Codex's required cases and ownership; R3's "journal → `dead`, relaunch" outcome removed in favour of preserved unknown attempts and rejected unsafe replay; R4 keeps actor status UNKNOWN initially; the §9 handoff (C) and joint recovery (D) exercises are retained |
| 23 | §7 native children | ADDED: after-parent-end survival is UNVERIFIED for Codex and Claude children die with the session — both as observations; the active-parent default finalizes the design without a whole-session termination experiment |
| 24 | §8 release order | REPLACED by Codex's five steps: stage without replacing operative files; freeze payloads before testing and freeze the release manifest with tested payload/evidence hashes (later changes reopen review); bilateral §9 agreements + reciprocal evidence, `gate.py` for record consistency plus separate provenance/behavior/authority verification; install only those payloads under direct session-local authorization, keeping the release manifest distinct from `MANIFEST.json` and avoiding circular self-hashes; verify mirrors and record activation, with S1/S2/S3 activating separately and revision 3 operative until real activation records. The proposal's "Codex's installed copy only via the user's direct paste (prepared by Claude)" is retained only as: a peer-authored paste is not authorization until the user supplies it directly |
| 25 | user constraint (no liveness from speed) | CARRIED into SKILL §6: reply speed is never evidence of liveness and every deadline stays generous per episode; reinforced by §0's observation-only framing and §5's observation rules |

## Verifier-round corrections (16 findings against the first staged candidate)

| # | finding | correction |
|---|---|---|
| V1 | Codex's §3 replacement reached this design but never the payload | SKILL §10 gains **Work units, delivery groups, review**: exact item/part membership, input digest, outputs and a safe checkpoint; the project's stricter limit (ReferenceBook: ≤ 8 numbered items in one section); the ~25-endpoint report packet as a DELIVERY GROUP that is neither a new uninterruptible unit nor early completion; interleaved independent review at checkpoints with priority for older blocking work, bounded concurrency, evidence preserved before switching and no peer-needed lock held while waiting; source/declaration snapshots and correction-contract records shipped with requests; reviewers recording their own source/type assessment before reading the author's self-check; changed inputs reopening the affected unit only. §3's heading now points at §10, which is the one place these rules live |
| V2 | the payload imposed v2 surfaces on the legacy bus the scope paragraph exempts | SKILL §10 (unit journal), SKILL §11 (checkpoint base, handled record, `admin.py lock show`) and RECOVERY G (preamble) each defer to the ACTIVE bus version, and G explicitly runs against a pre-v2 bus's own paths rather than being skipped by A.0 |
| V3 | S2 and S3 named no files, hashes, tests or activation record | the per-scope binding table in Scope; S1 is filled in, S2/S3 rows state exactly what each owes before release step 2 and that nothing is staged for them |
| V4 | a hand-written "Package revision 4" marker in the payload | removed; the preamble now says the number and payload hashes live in `MANIFEST.json` and nowhere else in the file, keeps the scope sentences, and claims byte-identity of "every section it does not name" so the claim survives the next revision. Release step 4 gains the byte checks that bind `MANIFEST.json` and forbid a hand-written number |
| V5 | "a watcher of a dead session is simply gone" stated as fact | SKILL §11 aligned to RECOVERY's "a watcher of a session that ACTUALLY died", with an explicit pointer back to the no-inference-from-silence rule |
| V6 | "Claude Code children die with the session" as a general present-tense fact | SKILL §7, DESIGN §7 and RECOVERY H each name the single 2026-09-14T10:53Z quota force-termination as its source and deny the generalization |
| V7 | "Follow the project's worker rules" narrowed to "where stricter, they govern" | SKILL §10 restores the unconditional sentence AND adds the stricter-wins clause plus "nothing here relaxes them"; recorded in `CHANGES.md` |
| V8 | the portable route label carried a literal `codex queue` argv | the `cli-queue` label now names the host's recorded queue command and sends the executable path and argv to the target's participant record (the app path was already design-only) |
| V9 | BLOCKER: "`delegate.py` already keeps this shape" is false against the helper | SKILL §10 restores "already supplies much of this pattern" and names the helper's actual vocabulary; DESIGN §1 lists the twelve journal names absent from the helper and flags the mapping as owed work |
| V10 | BLOCKER: the three evidence reports were cited by a location that does not hold them | §0 cites Codex's evidence directory by absolute path with the five sha256 values release step 2 binds |
| V11 | the `in-turn-wait` row still keyed its keepalive to `received` | the row keys it to the FIRST reply of §5, whatever its state, while work remains |
| V12 | the no-acknowledgment rule stated twice in §5 | the new copy is a pointer to the Truthful-status sentence that already carries it |
| V13 | publication `not_started` and `prepared` were enum-only, and `prepared` collided with the helper's plan state | SKILL §10 gives all five publication states a consequence and separates the two senses of `prepared`; RECOVERY G gains `not_started` and `prepared` branches |
| V14 | RECOVERY H presented Codex's drill ownership as settled | H's preamble now carries "offered, pending coordination", the freeze precondition, and "no R1–R5 drill has run yet" |
| V15 | §10's journal path was unconditional (same root cause as V2) | closed by V2 |
| V16 | the revision marker was a second source of truth (same root cause as V4) | closed by V4, with the step-4 byte check and a `grep` that must return nothing |

## C7 bookkeeping (Codex incorporation check b0b9160f, 2026-09-14T15:09Z)
- `references/DESIGN_v2.md` revision 13 (the design-of-record update for revision 4) is PAYLOAD: it IS staged under this candidate (sections 0–10 byte-identical to rev 12; title line, rev-13 note and §11 = this document embedded verbatim); its digest is recorded in `CHANGES.md` and the input manifest, never here (no circular self-hash). It is reviewed and hash-bound before testing and freeze (release step 2).
- The '20 files unchanged' list (revision-3 payload minus `SKILL.md`, `references/RECOVERY.md`, `references/DESIGN_v2.md` and `MANIFEST.json`) describes the CURRENT STAGE only; it is not a MANIFEST-metadata exception — at release step 4 every payload byte, including MANIFEST.json, is frozen or deterministically derived and checked byte-for-byte.
- Codex's six narrow payload fixes (C1–C6: first-reply `done` needs no second-result wait; queue route VERIFIED not merely recorded; G never routes candidate_ready to publication; G defers watcher/retry/swap/lock actions until delegated-work/ownership checks and pre-effect status, a differing base hash is unresolved not proof of a begun swap; a dead parent does not prove its watcher is gone; R3 outcomes conditioned on mid-publication/unknown-actor cases) were applied from MINIMAL_PAYLOAD_FIXES.patch ed237ede….

## 12. Revision-5 amendments (rev 14) — design provenance and record roles
rev 14 (revision-5 amendments, 2026-09-15): this section is the design-of-record for package revision 5 and the ONLY change from rev 13 — every other byte of this file, including the title line, is unchanged (diff-verified in the candidate's `DELTA.md`), so rev 13 stays readable as lineage. The revision is NARROW: R5.1 (accepted-unstarted units) and R5.3 (session continuity, documentation only) plus an advisory §12 in `SKILL.md`; R5.2 (self-cue before turn end) is DEFERRED, NOT_RUN; R5.4 (inbox hygiene) is a follow-up revision with its own helper change and drill. It installs no hook, service, scheduler or lock action and changes no helper.

### 12.1 Normative content (implemented by the candidate payloads)
- Journal authority: an accepted, unstarted unit is a `planned` attempt record in the unit journal under the ACTIVE bus's checkpoint base; the heartbeat `idle-with-queue:` line is a hint whose absence proves nothing (`hello` rewrites the heartbeat to two lines; a stop may precede the line); every re-entry ENUMERATES the queue from the journal, and a name the journal lacks is reported, never fabricated (SKILL §6, §10; RECOVERY A.3, A.8, A.11(d)).
- Stay-active default: an actionable accepted unit is worked in the current turn; a turn ends with a queue only for the user's interruption, a host limit, or a dependency that blocks ALL remaining accepted work; the heartbeat is rewritten at every unit checkpoint as an action of the active turn, never by a timer (SKILL §5, §6, §10).
- Freshness by the NEWEST valid observation: heartbeat age and the latest observation of the alias/instance are kept apart; stale = newest observation older than two hours (a conservative threshold that exceeds the named default thresholds, not a measured optimum); a newer message postpones staleness only by its own age; a mismatched instance is no observation; stale is never dead and permits no cue, takeover, lock action or idleness inference (SKILL §6).
- Cue binding, route-independent (exact generation, current actionability, no stale/blocked replay, intent → result → observation) plus route-specific lifecycle gates; `observed` only on target-origin evidence bound to the covered set and generation, never a changed heartbeat or an unrelated status; cue observed ≠ work completed; during-drain arrivals rechecked as uncovered (SKILL §7).
- Never-launched constraint: a changed input reopens a unit as a new attempt only when the earlier attempt was never launched (`planned` / `not_started`); `launch_pending`, `launch_unknown` and `running` attempts keep their condition until §11's cessation and effect gates; a cancellation counts only when correlated and from the requester's own alias; late results never revive cancelled or superseded work (SKILL §10; RECOVERY A.8, G.3).
- ONE merged re-entry order: RECOVERY A steps 0–9 read, reconcile and plan (receipts only), A.10 publishes the single pre-effect recovery status, A.11 executes effects in a fixed order ending with the preserved queue, A.12 rewrites the heartbeat; checklist G's rules apply at the A steps they name (G.2 at A.6, G.1 at A.7, G.3 at A.8, G.4 at A.9, G.5 = A.10), and the drill order log must show them before G.5 and G.5 before A.11's first effect (RECOVERY A, G; SKILL §6, §10, §11).
- Continuity contract, documentation only: what must be on disk before any compaction or halt, re-entry by A regardless of harness, per-harness routes recorded as observed / configured / unverified with no crash, kill or cap delivery of any hook guaranteed, observed or relied on, and the `install-hooks` adapter described, not implemented (RECOVERY I).

### 12.2 Payloads of record
- `SKILL.md` sha256 b8085d4f8a9c664ce001a6f4025d4759ba78f0904cbe60bf503d1ce789d8bb4d
- `references/RECOVERY.md` sha256 5a34fdff89889fb38e9f445b72e3ae2491f5383bc0f44a956616d25d872b8704
- `references/DESIGN_v2.md` = this file at rev 14; its own sha256 is recorded in the candidate `MANIFEST.json` and in the release record, never here (no self-hash).
- 20 further package files byte-identical to revision 4 (hashes in the candidate `MANIFEST.json`); no helper, test, template or trigger file changes.

### 12.3 Provenance (the inputs this revision answers; sha256)
- Codex design verdict `REV5_DESIGN_REVIEW.md` d697961632156dc7fe23b052ad20cd0c6e994a98d18ba2ea7370c1016df0b354 (bus message a6d6318d, e4df6e259d0971bd9b4784f9cfd83df07df2f2bb638657600b5eef47797d57ff): R5.1 accepted with ordering and eligibility corrections, R5.2 deferred, R5.3 factual documentation, non-binding model-tiering reference.
- Codex independent exact review of candidate 1, `REVIEW.md` 17846e23b6c1db369cf938fb2e9bec681d1a4123663b5a7ca942b1c57be229b5 (corrections C1–C10, questions Q1–Q7; `RESULT.json` b7a5d71404ec8f195824ceb90ea24d5b4744c0b1c684135e7e3070c04c79b6c8; `A8_REFERENCE_SCAN.json` f0164c74b1db113879541823df803fb5545fadbadd9b0b8a089825a117945f17; `PROVENANCE_AUDIT.json` 5b2972b9565ce4c2e36e94fd34496356f95111d985a79eda6ad7068d246c147c).
- Codex parent disposition `PARENT_REVIEW.md` c935dbf26a564aaee2714105f4ae7be22ec82d14c56df11ee404c466aebabaaa and `PARENT_RESULT.json` ae078ccb6cea582ba8e73cb044c927f58d8ef4552eeb6de8f8d4545fe723b358 (bus message bb326c6f, aec876912e32a25bc4ca350dc39b222e3e733ce2218713f665628955eecac440): C1–C10 adopted, C4 supplement (inspect/plan only until control and worker-use checks; one pre-effect status), Q1–Q7 answered.
- Candidate 1 (preserved byte-for-byte at `prototype/rev5/candidate/`, superseded): `SKILL.md` 7ef2d50e7cfacceb028658960c9b494575e8746427c7d95d59d1934b69b2f676, `RECOVERY.md` 17f4532efc4320359c70df47632ef82ebf344fe48b097b72cc997a5c878a5b21, `DELTA.md` 7f3f80ae895380e571b350e94b2e36e00523e679fb9372e1d7f11c888a37671d, `DRILL_PACKET.md` 4795f8f4f91acf0e4c05a91ddc1a3e602d8dca40be22eb754b9b92065c571ef6, `MANIFEST.json` 81b4e9098dbd61a5b75873dca6a956bce5f22b72a767fb5604034fc93bd150b4.
- Dispositions of C1–C10 and Q1–Q7: candidate 2 `DISPOSITIONS.md`; candidate 1 → candidate 2 deltas: `DELTA.md`; the drill plan: `DRILL_PACKET.md` — each hashed in the candidate `MANIFEST.json`, not here.
- Baseline: installed revision 4 (`MANIFEST.json` 9c5384c28df355333c0016160a52ceeaf2845b43e4fbbdcef8dd604029d2345e; this file at rev 13 bab4952e56c680c4a5382f377eb929046a0c620d215df3be2ef88f9571a2b3fa).

### 12.4 Drill plan and roles (Q7)
Scratch bus; deterministic simulations described as simulations (R6a–h and R7 in RECOVERY H and the drill packet). Claude: scratch bus, runner and checker authoring, both simulated aliases, the producer checker run, the negative mutation set, the evidence freeze. Codex: review of the frozen runner and checker CODE (a hash-only receipt is insufficient), read-only independent verification to its own output path, and MANDATORY adversarial negative cases with expected failure signatures. Results are deterministic simulated trace checks — not proof of real harness effects, authenticity or any activation capability. Agreement to a role is separate from permission to start a particular packet. The real handoff cycle (RECOVERY C) and the joint recovery drill (RECOVERY D) remain required before any agreement sentence; simulated aliases never satisfy the SKILL §9 gate.

### 12.5 Record roles at release (distinct objects, no cycle)
1. `design-sha256` in the SKILL §9 agreement headers = the sha256 of THIS file at rev 14.
2. `manifest-sha256` = the sha256 of the INTENDED INSTALLED `MANIFEST.json` bytes (the revision-5 inventory: payload hashes, revision number, test-run id), frozen or deterministically derived at release step 4 and reviewed before the agreement; that inventory never hashes itself and never contains a release-record hash.
3. `FINAL_RECORD.json` — the evidence-bound final record, produced AFTER the drill under `prototype/rev5/release/<utc>/`: it binds (1), (2), the `test-run` id, the drill evidence-manifest hashes, the code-review and independent-verification result hashes, and the real C/D exercise records; it is the object the bilateral `state: accepted` replies and reciprocal receipts are reconciled against by `gate.py`. It is NOT the candidate `MANIFEST.json` and is NOT hashed into the installed inventory.
4. The candidate `MANIFEST.json` of this stage is a review inventory only.

### 12.6 Boundaries restated
No vendor, model or account names in the portable core; no new hooks, services, schedulers or lock actions; the `install-hooks` adapter is described only; S2 (established-bus opt-in) and S3 (project adapter) activate separately with their own records; volatile provenance inputs (a session checkpoint, a project issues ledger) are cited by their historical digests, and their relevant excerpts are frozen with the drill packet rather than treated as reproducible path/hash pairs.

## 13. Revision-5 amendments (rev 15) — agreement binding restored to the revision-4 convention; drill evidence order; renewed cue gate
rev 15 (revision-5 amendments, candidate 3, 2026-09-15): this section is appended after §12 and is the ONLY change from rev 14 — every other byte of this file, including the title line and §12, is unchanged (rev 14 is the exact byte prefix of rev 15, as rev 13 is of rev 14; `cmp`-verified in the candidate's `DELTA_v3.md`), so §12 stays readable as lineage and the items it names remain in force except where this section says it supersedes them. It answers the peer's exact recheck of candidate 2 (`REVIEW.md` c82193a668a03bb28c8c406441fefc20e7ffd6ab37337ccb82267322677d429c, `RESULT.json` 90ad2daa0809302b312f138d02a62eba830852bc28c0191b8357deecbd4d7b5c, `INPUT_AUDIT.json` f1e2b5e9cb6feac17ca0142d5090795f7b27d87155488115c3be35aa57c9d350, bus message 9a17c09e f7b0b5ef7a9a94c0cc25b39d46d80f2317e185bfc53cedd8af224f28ffa08a9d: residuals R2-1, R2-2, R2-3 and its answers to candidate 2's three questions). It changes no normative rule of §12.1 beyond the alignments stated in 13.3 and 13.4, installs no hook, service, scheduler or lock action, and changes no helper.

### 13.1 Agreement binding (supersedes §12.5 items 1–3; item 4 stands) — R2-1
1. `design-sha256` in the SKILL §9 agreement headers = the sha256 of THIS file as installed, i.e. rev 15 (rev 14 f3d7fd0fe178e575d90dd7dcdf2703874ed621170148f7a89b4cf1c91f897713 is its exact byte prefix; rev 13 bab4952e56c680c4a5382f377eb929046a0c620d215df3be2ef88f9571a2b3fa the exact byte prefix of rev 14).
2. `manifest-sha256` = the sha256 of the FROZEN, EVIDENCE-BOUND `FINAL_RECORD.json` — the revision-4 convention, NOT the installed inventory. Precedent, verified against the immutable records before this section was written: the revision-4 agreement pair `20260915T020339Z-codex-agree-rev4-final-v3-f5967262` / `20260915T020435Z-claude-agree-rev4-final-v3-cf264022` with receipt `20260915T020530Z-codex-received-rev4-peer-agreement-1b279095` (`prototype/rev4/gate/ACTUAL_AGREEMENT_PACKET.json`; `GATE_RESULT.json` ready) carried `design-sha256` bab4952e… (this file at rev 13) and `manifest-sha256` 3face7b512dc131e0362337e1baf97a74ab12c78d78086af92bd43f4be479695 = `prototype/rev4/release/20260915T020239Z/FINAL_RECORD_v3.json`, while the intended installed `MANIFEST.json` 9c5384c28df355333c0016160a52ceeaf2845b43e4fbbdcef8dd604029d2345e was bound INSIDE that record (`manifest_derivation.intended_installed_manifest`: path, sha256 and full content; `RELEASE_POINTER.json` `intended_installed_manifest_sha256`) and became the installed inventory, which carries no release-record hash and no self-hash. Revision 5 uses exactly that shape.
3. `FINAL_RECORD.json` (produced AFTER the drill, RECOVERY C and RECOVERY D, under `prototype/rev5/release/<utc>/`, written once, immutable) binds: (1); the exact INTENDED INSTALLED `MANIFEST.json` (path, sha256 and full content — the revision-5 inventory: payload hashes, revision number, test-run id; it never hashes itself and never contains a release-record hash); the `test-run` id; the drill's `TRACE_INPUT_MANIFEST.json` sha256 and the `RESULT.json`, `NEGATIVES_RESULT.json`, `RESULT_independent.json` and peer-negatives result hashes; the aggregate `EVIDENCE_MANIFEST.json` sha256; the peer's code-review record of the frozen runner and checker; the real RECOVERY C and D records; and the pre-install byte facts the install is checked against. It contains no self-hash. Consequently the unchanged `scripts/gate.py` (0a0299f147c5490bd8cab496a50d94262784a2c5b3b1f0cbd5b5ce9ad6217107; it compares exactly `design-sha256`, `manifest-sha256`, `test-run` and the participants' sessions on both sides' actual records) binds the evidence bytes through the header itself: two records with different evidence hashes cannot satisfy the same agreement. No gate change and no new user paste is needed; the installed inventory's bytes are verified at install time against the record, not by the gate.
4. The candidate `MANIFEST.json` of this stage remains a review inventory only (§12.5 item 4).

### 13.2 Drill evidence order and manifests (the packet's §1, §4.1–§4.4, §6) — R2-2
Runner per case → `TRACE_INPUT_MANIFEST.json` frozen (sha256 of every file under `packet/` and `runs/`; it lists no checker output, no negative run and no aggregate; immutable once written and published to the peer before any checker runs) → producer checker bound to that manifest by its frozen CLI mode, writing outside `packet/` and `runs/` → negatives, each on its own copy of `runs/` with a separately derived, labelled manifest that binds the original trace manifest's sha256 and the exact mutation, so a semantic or file-set mutation reaches its predicate; distinct checksum and file-set INTEGRITY negatives run against the original manifest → the peer's independent read-only run and its own negatives, bound to the same trace manifest → the aggregate `EVIDENCE_MANIFEST.json` LAST. Reports bind the trace manifest, never the aggregate that lists them; the final record binds both (13.1(3)). Negatives are matched by exit code AND signature. R7's declared runtime-input set is the argv paths plus the one-level checkpoint-index expansion that discovers the registry contents and the token bundle(s), each hashed before it is read.

### 13.3 During-drain arrivals (aligns §12.1's "during-drain arrivals rechecked as uncovered") — R2-3
A request that arrives during a drain is recorded as uncovered and PENDING; uncovered status and the retirement of the covered cue establish no eligibility. A further cue needs a RENEWED, separately recorded native-idle observation of the target on the verified route, bound to the new intent (SKILL §7 (a), unchanged: the target has just started work, and a busy or unknown observation, or none, yields no intent); otherwise the request stays pending for the next eligible route event. The packet's R6d main case shows the pending recheck, a busy observation with no intent, and the second intent only after a new idle observation; RECOVERY H's R6 (d) row says the same.

### 13.4 Drain evidence per covered id (answer 2)
`covered-cue` and `cue_ref` stay drill conventions of the runner, not SKILL headers. Whatever the record shape, the checker resolves the cue id to the immutable intent (target instance and exact covered generation), and `observed` needs an actual declared drain outcome for EVERY covered unit and request id; a one-of-many receipt, or a status that names the cue but omits an id, establishes nothing for the omitted id (the packet's sub-run 6 and negative N16). A.6 intake stays before A.7 continuations (answer 1); the foreign-lock escalation is PLANNED at A.9 and published with or after A.10, consistently with A's prelude (RECOVERY A.9, A.10, G.4, G.5).

### 13.5 Payloads of record (supersedes §12.2 for the file whose hash changed)
- `SKILL.md` unchanged from candidate 2: sha256 b8085d4f8a9c664ce001a6f4025d4759ba78f0904cbe60bf503d1ce789d8bb4d (§12.2).
- `references/RECOVERY.md` sha256 c89a84bd98dda886d2364c7e4edd5d60f7c96afe09adae327928af553b552e03 — candidate 3 changes only A.9, A.10, G.4, G.5 (escalation planned, published with or after the single status) and H's R6 (d) row (13.3, 13.4); every other byte is candidate 2's.
- `references/DESIGN_v2.md` = this file at rev 15; its own sha256 is recorded in the candidate `MANIFEST.json` and in the release record, never here (no self-hash).
- 20 further package files byte-identical to revision 4 (§12.2; hashes in the candidate `MANIFEST.json`).

### 13.6 Provenance of this step
- Peer recheck of candidate 2: the four digests named above; candidate 2 preserved byte-for-byte at `prototype/rev5/candidate2/` (seven hashes in the candidate `MANIFEST.json`, `lineage_candidate_2`); candidate 1 as §12.3.
- Dispositions of R2-1–R2-3 and answers 1–3: candidate 3 `DISPOSITIONS_v3.md`; candidate 2 → candidate 3 deltas: `DELTA_v3.md`; the drill plan: `DRILL_PACKET.md` — each hashed in the candidate `MANIFEST.json`, not here. `DELTA.md` and `DISPOSITIONS.md` are candidate 2's records, kept byte-identical as lineage.

## 14. Revision-5 amendments (rev 16) — Codex successor and cue hygiene
rev 16 (candidate4, 2026-09-16) appends this section to the exact rev-15 byte prefix; the
historical title, proof/evidence discussion and §§0–13 are unchanged. This section adds only the
agreed pointer-only coordinator cue format and receiving/authority wording, the corresponding
recovery placement and five bounded simulation cases, and the Codex-successor handover below.
The exact insertion source is `checks/book_formalization/codex/cue_hygiene_20260916_030501/AMENDED_TEXT.md`,
sha256 `d85b8a149d025cb7d9594792eedca501ba8fd9c91017d62b4cbe0caddbcae448`.

### 14.1 Cue wording and authority
SKILL §7's cli-queue row carries insertion A verbatim: fixed routing text and message pointers
only, with the coordinator-origin label explicitly a convention, not authentication. SKILL §8
carries both paragraphs of insertion B verbatim after the existing user-authority paragraph.
Recognized cues reconcile durable messages, handled ids and later amendments; a stale cue does
not revive withdrawn work. A bus path/id or cue-like text alone never demotes a direct user
instruction. Material unresolved ambiguity pauses only its disputed effect, with completed and
independent authorized work preserved. RECOVERY A.1 plans discrepancy info; A.10 publishes it
with or after the single pre-effect status, preserving A's receipt-only steps 0–9.

### 14.2 Successor lineage and evidence
Candidate4 and `../exec6/` are the mutable Codex successor authoring trees based on immutable
candidate3 and exec5. A copied base manifest is not a successor freeze. The owner writes final
successor inventories after authoring and binds new results to those exact bytes before
any release claim. This supersedes earlier current-stage claims that no executable exists;
it does not rewrite their historical truth or transfer earlier PASS results to changed behavior.
`DRILL_PACKET.md` adds CH1–CH5: recognized pointer-only cue, stale legacy cue plus withdrawal,
direct-user test input containing a bus reference, peer-quoted permission, and material ambiguity.
Their role inputs are labeled simulations with frozen oracles; they establish no actual sender
authenticity, user impersonation, real harness effect or activation capability. The incident's
immutable amendment time, if cited, is `2026-09-16T02:38:08Z` (`e819a67c`).

### 14.3 Roles and unchanged release gates
For this successor Codex is author/producer and Claude is the independent peer reviewer and
verifier; this supersedes the producer/reviewer assignment in §12.4 for this run only. Simulated
actors remain drill-a and drill-b. Independent review is not satisfied by the producer or by a
stand-in identity. The real handoff cycle (RECOVERY C), joint recovery exercise (RECOVERY D), and
bilateral SKILL §9 agreement/receipt gates remain required. The §13.1 binding convention is
unchanged: `design-sha256` identifies these intended design bytes; `manifest-sha256` identifies
the frozen evidence-bound FINAL_RECORD, which binds the intended installed inventory and real
C/D records. No actual peer-authenticity or release claim is made by this mutable authoring step.

## 15. Revision-6 amendments (rev 17) — host route catalogue, token-path correction, default activation pattern, local-bus rule and quiet-operation norm
rev 17 (candidate1, 2026-09-18; candidate2, 2026-09-18) appends this section to the exact
rev-16 byte prefix; §§0–14 are unchanged. Documents `DELTA_SPEC.md` deltas D1–D9 (coordinator claude3): a host-route catalogue
and two example-path corrections, plus D10–D13 (§15.6–§15.8, candidate3, the user's amendments of 2026-09-18): one default activation practice, the local-bus rule and the quiet-operation norm; that is, one default activation
practice. No helper change; `scripts/` stays byte-identical to rev 5.

### 15.1 The two measured problems

The `cli-queue` route is unrecoverable by a fresh session on a new bus: rev-4 item V8 moved the
queue command's path/argv out of SKILL.md into the target's participant record (RECOVERY I.3,
"never here"), so a new-bus session finds no record, greps the `codex` on PATH (Homebrew,
codex-cli 0.136.0, no `queue` subcommand), and concludes the route does not exist — observed
repeatedly (user: "Many sessions struggle on recovering the thing below"). It exists at
`/Applications/ChatGPT.app/Contents/Resources/codex queue --thread <id> --message "<cue>"
</dev/null` (codex-cli 0.155.0-alpha.2.6, 2026-09-18; 0.154.0-alpha.6.2, 2026-09-13–17 — the app updates itself; the path has been stable across these observed versions — an observation, not a guarantee across future installations); verified by the RadiiPolynomial bus's
`checks/activation/QUEUE_ROUTE_EXPERIMENT.json` (2026-09-13T21:50:39Z, exit 0).

The skill's own examples break discovery: SKILL §3/§4 recommend `$HOME/.agents_bus/<bus_id>/…`
for instance-id and token files. `scripts/bootstrap.py:88-90` walks every ancestor of
`--root`/cwd and, on any `.agents_bus` path, calls the marker reader
(`scripts/common.py:41-44`), which raises `BusError` on a directory; SKILL §1 makes a corrupt
walk candidate FATAL. So a directory at `$HOME/.agents_bus` — what the example creates — fails
every discovery-based helper call (admin commands and hand reading; `publish`/`wait` name their
bus directly) from any cwd under `$HOME`, on every bus (memory
`reference-agents-bus-codex-route`); current practice uses
`$HOME/.config/agents-bus-tokens/<bus_id>/`.

### 15.2 What changes, and why the catalogue does not reverse V8

D1–D7 add a documentation-only catalogue (`references/HOST_ROUTES.md`, D6) and correct the two
example paths (D2, D3; D4 states the reason in §1); D5 rewords the scope paragraph; D7 points
RECOVERY I.3 at the catalogue. V8 removed a literal argv from SKILL.md's route LABEL so it would
not go stale as the app updates; the catalogue is a separate, dated OBSERVATION table, not a
label. D1 therefore carries the pointer only — the row label names no executable path or argv
(V8 upheld; the peer review of candidate1 found the literal path there and it was removed in
candidate2). The participant record stays the sole eligibility authority (SKILL §7). No
eligibility rule, hook, service, scheduler, lock action or new route is added. HOST_ROUTES §0
restates SKILL §7's eligibility conjunction verbatim (the route VERIFIED and recorded, the
user's authorization, and the caller's own native-idle evidence) and adds no first-use exception
to it. The first wake on a brand-new bus — where no target record yet says `verified` — is not
itself §7-eligible: it is a user-authorized EXPERIMENT, recorded with intent, result and
observation the way RadiiPolynomial's `checks/activation/QUEUE_ROUTE_EXPERIMENT.json` was; the
target registers `verified` only after that experiment's observed wake. This ruling is recorded
in the release evidence of this revision. HOST_ROUTES §2 binds the target thread to the
participant record's `instance_id` regardless of heartbeat age (SKILL §6: stale is
uninformative, never a change of identity) and treats enumerated threads as candidates that only
the target's registration or the user resolves.

### 15.3 The token-path example is superseded, not edited in place

§3/§4's `$HOME/.agents_bus/<bus_id>/…` examples are SUPERSEDED by
`$HOME/.config/agents-bus-tokens/<bus_id>/…` (D2, D3); D4 states the reason inline in §1. No
token or instance file on any live bus is moved by this revision.

### 15.4 Boundaries

Documentation (SKILL.md §1, §3, §4, §7, scope paragraph, §1 local-bus rule, §5 quiet-operation
norm; RECOVERY.md I.3; this file §15; new HOST_ROUTES.md) plus ONE default practice (SKILL.md §5 turn end and §7, the asymmetric activation
pattern of §15.6 — a default on routes that already exist, each keeping its own gates). `scripts/`
byte-identical to rev 5; no hook, service, scheduler, lock action, new route or eligibility change;
the watcher the practice names is the session's own continuation, registered and retired per §6.6,
never installed by the package. Nothing under `~/.claude`, `~/.agents` or the RadiiPolynomial repo
is touched; the candidates live under `tmp/agents_bus/checks/rev6/` and install nothing.

### 15.5 Provenance

The user's 2026-09-18 instruction, quoted in one line: "update the agent bus skill … so that I don't have to paste the things below for every other fresh agent bus runs in a new session" (received directly by the coordinator
session; the peer sees only this relay). Supporting evidence: memory
`reference-agents-bus-codex-route`; Grading bus cue `checks/cues/20260917T201500Z-claude2-cue2.json`;
RadiiPolynomial's `checks/activation/QUEUE_ROUTE_EXPERIMENT.json` (2026-09-13T21:50:39Z).

### 15.6 Default activation pattern (user amendment, 2026-09-18)

The user's instruction, quoted in one line: "claude end should arm the reminder and cue codex.
codex no reminder background task needed." SKILL §5 (Turn end) and §7 (Delivery ≠ activation) now
state an asymmetric default: the side whose harness can re-invoke it on an incoming file (the
WATCHING side) arms one inbox watcher per bus and is also the CUE DISPATCHER, coalescing and
dispatching a cue on the target's verified route when its own native-idle evidence holds; the
side whose harness is only woken by cues (the CUE TARGET) arms no watcher, scheduler or service
of its own. This is a default PRACTICE, not a new route or a rule change: both routes it names
(`in-session-watcher`/inbox watching and `cli-queue`) already existed and keep their §7 gates
(VERIFIED and recorded route, the user's authorization, the caller's own native-idle evidence)
unchanged; the watcher itself is the session's own continuation, registered before and after
arming and retired at scope closure exactly as design §6.6 already required, so nothing new is
installed. The observation behind it: 2026-09-18, a watching-side coordinator that let its
one-shot watcher lapse missed two peer replies for about ten minutes until the user asked; the
cued peer had answered within a minute of its cue. Drill evidence: the live bus's
`checks/watchers/claude3.json` and `checks/cues/` records, and the scratch-bus RECOVERY D run in
which the watching side's watcher caught each peer reply.

Corrections from the peer's candidate-2 review: re-arm only while the coordination scope stays
open and authorized after a confirmed handle exit (scope closure and cancellation are not expiry;
unknown or stop-pending handles are reconciled, never duplicated); the cued side ends its turn
only as §5/§10 allow, after completing actionable accepted work and reconciling in-flight
children. A deterministic lifecycle case table for these rules (`drill/lifecycle_cases.md`, bound by hash) is part of this revision's release
evidence. The recommended watcher shape is the persistent per-message monitor (one handle per
harness timeout window, re-armed on expiry); the one-shot loop is permitted with re-arm at each
firing — both observed 2026-09-18 and recorded in the lifecycle case table (§D).

### 15.7 Local-bus rule (user amendment, 2026-09-18)

The user's instruction, verbatim: "Always prioritize local bus instead of remote bus (in fact prevent as much as possible from using remote bus, causing contamination) default to that i will push claude and codex under the same working dir and initial the agent bus skill on both sides." The rule (SKILL §1): a session coordinates on
the LOCAL bus — the one whose coordination root contains its own working directory, found by the
marker walk from its own cwd; data, evidence or a task under another root is read by path only,
never joined by `hello`, `bind`, `lock`, `publish` or `wait`, and discovery is never run from a
path outside the local root; only the user's explicit naming of a remote bus puts a session on
it. This is discovery hygiene, not a change to the one-bus-per-domain invariant: §1 already
forbids putting one resource under two buses; this rule instead names which bus a SESSION belongs
to when it must read data that lives under a different root. Observed (user report, 2026-09-18):
a worker session in project A, told that something to work with lay under project B, registered
on B's bus instead of A's. It activates nothing: no new route, hook, service, scheduler or lock
action; it constrains only which bus a session's own coordination calls target.

### 15.8 Quiet operation (user amendment, 2026-09-18)

The user's words, quoted in one line: "Talk less. Only report briefly on checkpoints and major
issue. auto and quiet. get the job done. This should be a norm in the agent bus skill. This skill
is for autonomous tasks." The rule (SKILL §5): the user hears checkpoints (task acceptance, a
handoff, completion with its evidence, an installation, a §9 agreement) and major issues (a
blocked dependency, a §8 dispute, an authorization the session lacks, a peer silent past §6's
thresholds, a conflict with the user's instructions) only; everything else is written to the bus,
the board and checkpoints, for a reader who was away to find. It activates nothing: no rule of
eligibility, exclusion, delivery or activation changes; it governs only what a session narrates to
its user, not what it records.

## 16. Revision-7 amendments (rev 18) — quota observation, warning bands, recovery package, resume timer

### 16.1 The failure and the invariant
Today's practice is a manual HANDOFF.md written ad hoc, if at all, before a session hits a hard
usage stop; work in flight is lost when nobody writes it first. Quoting Codex's counter-position
(checks/rev7/CODEX_COUNTERPOSITION.md): "The robust invariant is continuously durable
task/attempt/publication state; a final handoff is best-effort consolidation while execution
remains available." RECOVERY A/I.1 already carry that invariant; the recovery package (QUOTA §5)
is an additional best-effort artifact layered on top of it, never a replacement, and never claimed
to run before every possible stop.

### 16.2 What changes
D1 — NEW references/QUOTA.md (≤185 lines, raised from ≤140 in fix round 1 and ≤170 in candidate 2:
candidate 3's aggregate-recompute, modeled-artifact and timer-re-arm rules do not fit under the old
ceiling; 182 lines): observation record with a non-sensitive `pool` label scoping comparability,
sampling, forecast, bands/states with AGGREGATE admission over every binding window and explicit
PAUSE GENERATIONS, recovery package, peer relay, per-harness sources, resume timer and binding
windows.
D2 — SKILL.md §5: quota-state/quota-window/resets-at headers on status infos; resume as an
owner-observed transition, never a peer command; the package-pointer sentence; the peer rule.
D3 — SKILL.md §10 (§5's Turn-end mirror, fix round 1; §7's cue-target mirror, fix round 2): the
quota-admission pause is the single quota reason for which accepted actionable work is deferred,
whether within a turn or by ending it, recorded per QUOTA §4, launching nothing; listed as a fourth
turn-ending reason alongside the user's interruption, a host limit and an all-work-blocking
dependency, consistently in all three lists. Fix round 2 also adds a QUOTA ADMISSION step to §10's
fixed wake order, before the old actionable queue, so a control or recovery wake cannot drain a
queue the pause is holding.
D4 — SKILL.md §12: the QUOTA §1 observation record is mandatory at every checkpoint, fetched per
QUOTA §2's rate limits; fix round 2 narrows the section's "binds nothing" opening to its
worker-profile guidance, which stays advisory, so the mandatory observation no longer contradicts
it.
D5 — SKILL.md scope paragraph: this revision's content in one sentence; sections amended §5, §7, §10, §12.
D6 — RECOVERY.md: A.1 reads the recovery-package pointer; I.1 gains (i) the quota sample and (j) the
package pointer; a new checklist J of simulated quota-policy traces. Fix round 2 gates A.11(d)'s
preserved queue on the persisted pause state and corrects J's oracles O1–O7: J.1 scoped to the
interrupted attempt; J.2 forecast vs band; J.3 from three prior states; J.6 tombstones kept, no
automatic acknowledgment; J.7 one accepted generation, not one directory; J.13 no partial timer;
J.14 no override of a user cancellation. Candidate 3 extends that gate to (c) — RESUMED validation
or publication waits with the queue, bounded reconciliation of an interrupted effect never does —
splits J.3's artifacts by initial state, and takes J to 21 cases: 16-18 (aggregate hold, a second
generation inside one epoch, a forecast pause from `observe`), 19-21 (a pool or source change
fabricating no forecast; a changed blocker set retiring a now-ineligible timer; a forecast blocker
arising DURING a pause).
D7 — this section: rationale, invariant, debate record, boundaries, provenance.
D8 — MANIFEST.json: built LAST by the coordinator, not this worker; revision 7, design revision 18.
D9 — SKILL.md §7 (fix round 1): the resume timer as a distinct continuation kind in the "every armed
continuation" list, registered and retired like any other, at most one live per PAUSE GENERATION and
never counted toward the one-watcher-per-bus rule.

Debate record (message ids, checks/rev7/): proposal 20260918T053657Z-claude3-rev7-proposal-e33fba4e;
counter-position 20260918T054340Z-codex-rev7-counterposition-f29c671d; merged
20260918T054520Z-claude3-rev7-merged-ef8325f5; R1–R3
20260918T054706Z-codex-rev7-merged-answers-5af3d102; user amendment
20260918T055003Z-claude3-rev7-user-amendment-9acc8335; P1–P4
20260918T055303Z-codex-rev7-amendment-answers-b3475e18.

Dogfooding observation, not a hard-stop test: the drafting session itself entered `prepare` at 24 %
and, on a forecast-driven early pause (QUOTA §4) rather than the LOW-band default, `quota-paused` at
15 % of its 5-hour window on 2026-09-18 (statuses 20260918T060439Z-claude3-quota-prepare-4f71ff8f,
20260918T061957Z-claude3-quota-paused-24db853a), armed one one-shot resume timer, and resumed after
the reset (status 20260918T075244Z-claude3-quota-resume-0c3efadd). Worked forecast example from the
same samples, kept here so QUOTA §3 stays rule text: 49 % at 05:00:00Z and 33 % at 05:49:00Z give
`b ≈ (49−33)/49 ≈ 0.33 pts/min` and `T ≈ 33/0.33 ≈ 101 min` against the 121 min then left to the
07:50:00Z reset — a WARNING roughly 20 min short of the real reset, never a bound. Likewise QUOTA §8's
"Codex arms none BY POLICY": that app does expose scheduling primitives, so the sentence records a
design assignment (timer-arming belongs to the watching side), not an incapacity.

### 16.3 Boundaries
No helper change; no scheduler installed by the package; no route, eligibility or per-attempt token
budget change; no post-hard-stop execution guarantee; placement stays inside agents-bus (P1).

### 16.4 Provenance
The user's two briefs, one line each: "keep track of quota and fall back to 'prepare handoff to
fresh session' when quota draining… the single most important thing is the automatically triggered
handoff"; and "when it's the 5hr quota running out… set a timed background reminder to right after
the 5hr quota reset… weekly… no timer, just handoff… a non-model-specific session ignores
the model-specific quota" (model name replaced with "model-specific" per this revision's
no-vendor-name rule). Observation evidence: checks/rev7/claude/OBSERVATIONS.json sha256
37b5714d2eb6b6c880e28c713d264c01f4f51e0ad5971c3e2c9e2ea55bd9a0fd; checks/rev7/codex/OBSERVATIONS.json
sha256 e3090c43943fa1bae81c6e3c66e103617d374cc84e6c0e2b2561079b23b1c21c.

### 16.5 Candidates 2 and 3
Candidate 2 applies the consolidated peer review 20260918T090305Z-codex-rev7-c1-review-387a64d2
(state corrections S1–S6, Recovery-J oracles O1–O7, same-pool comparability, the §12
advisory/mandatory split) and the round-3 adversarial fidelity review
`checks/rev7/drill/review_round3.md` (S14 an in-episode resume followed by a later pause, S15 the
DELTA_REFS header hashes and labels, S16 D3's wording above, notes N19–N23). Coordinator rulings
settled the open choices and QUOTA §4/§8 now carry them: admission is AGGREGATE over every binding
window; a PAUSE GENERATION is one `prepare`→`quota-paused`→`resume` cycle while a RESET EPOCH is a
window's reset period, so the one-preparation rule binds the generation and a later trigger in the
same epoch opens a new one; an observed new reset epoch resolves a prior pause when nothing else
blocks; a forecast-driven pause may start from `observe`, counting as entering LOW for §8; and U2/U3
turn on whether every blocking reset is known and within 5 h. Drill evidence so far binds candidate
1 only: the controlled simulation D, record `DRILL_D_RECORD.json` sha256
d3f4ce13073b882add70f63752210b4637a6576cd8bb81aa847742eb6bf43f84, on the already-registered scratch
bus as an unchanged-core exercise — proving neither this state machine nor any native quota stop. J
and C must run against these corrected bytes before the §9 gate.

Candidate 3 applies the second peer review 20260918T101538Z-codex-r7c2-review-436f210b. Its two
source corrections: RECOVERY A.11 gates RESUMED project validation and publication with the
preserved queue, excepting bounded safety reconciliation of an already-interrupted effect, so SKILL
§10's "before any FRESH project effect" and A.11's placement now read alike; and J.3's artifacts are split
by initial state, its fresh-LOW branch being a NEW pause that does need the package and U2 timer the
blanket oracle denied. The review's adversarial findings against the J runner became cases 19-21 and
QUOTA §4's rule that blocker membership and timer disposition are recomputed on EVERY aggregate
update, while paused as much as at entry, without a duplicate pause transition. J's wording and
QUOTA §5 now separate a trace's MODELED package/lock/cue/timer flags from validated durable
artifacts and native gates, so no passing case reads as durable-publication or hard-stop evidence.
The same review carries checklist C over candidate 2's bytes: `DRILL_C_RECORD.json` sha256
5d7a4593b8bbb1e369adb2ca080811ef1cad9c272779ad7397ecfa0823d30a64, under the registered scratch bus
at `checks/drill7-c-record/`, PASS, binding candidate 2's four payload hashes — a reconstruction
result, not policy approval. J must be re-frozen and re-run against candidate 3's bytes before the
§9 gate.

## 17. Revision-8 amendments (rev 19) — context-aware pause and planned compaction

### 17.1 The failure
A resume timer wakes the same session after a reset longer than the harness's stated prompt-cache
TTL. At this session's own numbers (PROPOSAL §0): a 5-hour window at 26 % remaining, reset 17:50Z;
context at 90 % of a 1M window, ~900k tokens; a stated 1-hour TTL. The resumed turn then re-reads
the whole context cold, re-read as new input volume before any work resumes — a cheaper
resume needs a smaller context BEFORE the pause, not after the timer fires.

### 17.2 What changes
P1 QUOTA §1 — the context record gains `cache_ttl` and a `resume_risk` LABEL (`cache-expired`,
`cache-may-hold`, `unknown`), never a predicted cost. P2 QUOTA §4 — `prepare` decides the
context-aware disposition: `compact-first` when `cache-expired` AND `tokens_used` is at or above
CTX (default 40 % of `context_window`, overridable only via the versioned policy record), else
`same-session`; the ordering for `compact-first` is checkpoint+package, then the §5 status, then
the compaction REQUEST — the resume timer is unaffected by any of it. P3 QUOTA §8 — the timer arms
exactly as without the disposition; keep-warm turns are FORBIDDEN during a pause; `successor` is
never a default, only an explicit user decision. P4 RECOVERY.md — I.1 gains the context record and
disposition; I.3 gains both harnesses' dated compaction/cache observations; checklist J gains
cases 22-28. P5 SKILL.md — §5 gains the `pause-disposition` header (`same-session | compact-first
| successor`) and its peer rule; the scope paragraph is rewritten for this revision. P6 this
section and `MANIFEST.json` (revision 8, design revision 19).
Fix round 1 (after the user's question of 2026-09-18T16:1xZ, whether the user can be notified to
compact before the cache runs cold): the request goes to the USER by the harness's notification
route — push notification and sidebar flag, tested once — or the turn-end line, with a `compact-by`
deadline = last request + TTL; a peer without a route asks the watching side to relay (QUOTA §4,
§7; RECOVERY I.3; J case 22).

Candidate 2 (fix round 2, Codex's blocking review of candidate 1): S1 the context record gains a
dated `cache_anchor` and computes `resume_risk` from age at resume, never the remaining pause
alone. S2 the disposition text drops every deterministic cache-hit, cold-read-count and
quota-saving claim. S3 RECOVERY A.7 only records and plans a lost or unverifiable timer handle;
A.11(a) alone executes ONE replacement, and only while the route, lifecycle, generation,
admission test and a still-future firing time all hold. S4 reserves a new gen5 fixture set on the
scratch bus (outside this payload) for the amended request record and corrected provenance. S5
the resume estimate is the known blocking reset plus the §8 margin whether or not a timer is
eligible, `unknown` only with no known reset. S6 a late first eligibility publishes a new status
and ONE request without a new pause transition. S7 an observed compaction's after-volume replaces
the latest context measurement; the before-volume survives only as request-outcome history. S8
the request is addressed to the user, never the peer, and a notification's submission is never
evidence of sight.

### 17.3 Debate record
Message ids under `checks/rev8/`: proposal 20260918T155715Z-claude3-rev8-proposal-1753dc8b;
Codex's answers 20260918T160807Z-codex-rev8-position-623fd09a. The user's question of
2026-09-18T16:1xZ (notify the user before the cache runs cold) was folded in as fix round 1 of this
candidate.
Codex's blocking review of candidate 1: 20260918T172034Z-codex-r8c1-review-blocked-3df87a21; this
addendum (`DELTA_SPEC_c2.md`) sha256
35dd9464ced7e7ae8593679e2bcc9be7ab97428ff29bdc6406e318658b133213.

### 17.4 Boundaries
No rule here claims the agent compacts, guarantees a warm resume, or survives a hard stop. The
agent never triggers a compaction itself — no verified agent-triggerable route is observed on
either harness; the request is a REQUEST, always through the harness's own route or the user
relay. No keep-warm traffic; no launcher route for `successor`; no hook, service or scheduler
installed; no per-attempt token budget; no change to bands, admission, U2/U3, eligibility,
exclusion or any helper. `references/QUOTA.md`'s line ceiling, raised from ≤185 to ≤230 for
candidate 1, is raised again to ≤250 for candidate 2, since the anchor, resume-estimate and
post-compaction-measurement additions to §1, unabridged, do not fit the prior cap.

### 17.5 Provenance
The user's brief (2026-09-18T15:0xZ, quoted in substance): quota at 80 %, reset in 2 hours, coming
to a halt, wake up in 2 hours — however the context is at 90 % of 1M and the cache will be cold on
restart; follow-up: can you initiate compaction whenever it's ready? Observation evidence:
`checks/rev8/claude/OBSERVATIONS.json` sha256
5e79c78e40376cd605c0bd935fb8a14b6e60a3a761f6f64df7f621ffcf33ef15;
`checks/rev8/codex/OBSERVATIONS.json` sha256
7b387f74271479c95ff1a6c9e4a9670f67c921fc4fe713ae4e106b4c224037ff.

### 17.6 The peer's drafting qualifications
Codex's qualifications (message 20260918T160807Z-codex-rev8-position-623fd09a), carried into the
rule text above, quoted in substance: a pause shorter than the TTL never guarantees a cache hit —
age, key and eviction stay unobserved; a predicted cold cost is never written as an observation
unless telemetry actually measures it at firing; 900k versus 100k input tokens is a volume
comparison, never a 9x quota or monetary cost; "the timer is armed exactly as without it" states
the policy's intention, not a demonstrated survival guarantee; keep-warm traffic is forbidden
while legitimate controls, receipts and safety reconciliation keep flowing; and any unchanged-core
reuse of revision 7's checklist C and D evidence keeps its original binding in FINAL_RECORD rather
than silently omitting those gates.

## 18. Revision-9 amendments (rev 20) — continuation snapshot

### 18.1 The failure
REPORTED FACTS (the authoring session's own records; the approximate values of earlier candidates
are replaced here by the recorded ones). (i) A self-scheduled quota-health wakeup was ARMED at
2026-09-18T19:28:21Z with a requested delay of 1200 s — the harness scheduled it for 19:49:00Z,
reporting "in 1239 s" — as a routine fallback; the last quota sample before it, at 19:13:21Z, read
5-hour 6 %, weekly all-model 65 %, weekly Fable 71 %, so no window was inside any warning band
(`references/QUOTA.md` §4). (ii) It was DELIVERED as an INTERRUPTING user message at
2026-09-18T19:54:46.777Z — later than its nominal firing time, the harness having waited for the
running tool call to finish — and at that same millisecond an interrupt marker appears in the
coordinator transcript and in the transcripts of two background workers launched earlier in that
turn; the two worker transcripts carry the IDENTICAL marker at 19:54:46.777Z. (iii) Later task
lookups of those two worker handles returned `No task found`; no completion record and no task
notification exists for either; both units were relaunched, at 20:30Z and 21:24Z. (iv) A third
worker launched in the same batch continued to produce output afterwards. (v) The divergence was
noticed about 90 minutes later by comparing transcript mtimes.
CAUSAL HYPOTHESIS, stated as such and NOT as an observation: the timer's delivery interrupted the
active turn, and that interruption terminated the two workers. It is not verified. Correlated
interrupt markers and later unavailable handles are the evidence actually held; transcript mtimes
alone do not verify process cessation, and `No task found` is not a cessation record with a stated
scope. The peer ran no timer-interruption or destructive experiment for its answer, so arbitrary
user-input, force-stop, timer and parent-turn-end survival remain unverified on that side too
(`HARNESS_OBSERVATIONS.json`: `interruption_semantics`,
`automatic_resume_from_child_after_parent_end`).
SCOPED CLAIM: these rules REDUCE exposure to known or unverified INTERRUPTING self-wakeups and
PRESERVE recoverable uncertainty about what a wakeup did. They do not remove exposure: external
interruptions, host policy, usage caps and crashes remain possible, and nothing here claims
survival of any child, watcher or timer.

### 18.2 What changes
(i) §17.2's S3 ("A.11(a) alone executes ONE replacement, and only while the route, lifecycle,
generation, admission test and a still-future firing time all hold") is SUPERSEDED, not edited in
place, by E6 below: `references/RECOVERY.md` A.11(a) retains timer inspection, retirement and the
watcher re-arm, and A.13 alone executes the replacement, its conditions unchanged.
(ii) §6.6 "Armed continuations registry (watchers, heartbeats, schedulers)" is EXTENDED, not
edited: its kinds gain the WORKER and the dispatched CUE, and its rule 1 location gains
`<bus>/checkpoints/<alias>/continuations.json` — the legacy `<bus>/checks/watchers/<alias>.json`
and the session-checkpoint branch are both RETAINED, so no bus is forced to rewrite or rename
anything — while its rules 1–7 otherwise stay in force as written.
(iii) §12.1's enumeration of the ONE merged re-entry order ("RECOVERY A steps 0–9 read, reconcile
and plan (receipts only), A.10 publishes the single pre-effect recovery status, A.11 executes
effects in a fixed order ending with the preserved queue, A.12 rewrites the heartbeat") is
EXTENDED by step 13 (TERMINAL YIELD) and by the sub-step 11(c-bis) inserted BEFORE (d), so that
order still ends with the preserved queue; its steps 0–12 and its G-rule mapping are unchanged.
(iv) §17.4's `references/QUOTA.md` line ceiling of ≤250 is SUPERSEDED PROSPECTIVELY by ≤260,
following §17.4's own precedent of raising it. The increase applies from this revision onward and
only to a final file that meets it with NO rule compressed or omitted.
E0 DEFINITIONS AND HEALTH LATTICE. A CONTINUATION is a handle this session owns OUTSIDE the bus
that can wake it, wake its peer, or do work for it: the inbox WATCHER, a TIMER (self-wakeup; the
`references/QUOTA.md` §8 resume timer), a WORKER (subagent, workflow run, background job it
launched), or a CUE it dispatched to a cue-only peer. Each entry names its OWNER and, where they
differ, its TARGET; the ROUTE actually VERIFIED and recorded for that owner/target (SKILL §7); and
the WORK generation, plus for quota continuations the PAUSE generation (§4). CONTINUATION STATE is
`intent | dispatch-unknown | live | stop-pending | closed | unknown` — states of the CONTINUATION
only, which never replace or restate job, attempt, execution or publication state: SKILL §10's
unit/attempt journal keeps that authority and a worker entry LINKS to its unit/attempt id. A CUE
entry gets NO reduced state set of its own: it carries the EXISTING SKILL §7 cue lifecycle exactly
— the intent before dispatch; the ACTUAL dispatch RESULT, either a CONFIRMED dispatch (recorded
exit code and output) or an UNCERTAIN one (`dispatch_unknown`), these being DIFFERENT FACTS
(`references/HOST_ROUTES.md` §2 steps 5–6); the OBSERVED DRAIN on target-origin evidence bound to
that cue's covered set and generation; and a separately evidenced RECONCILED RETIREMENT. A
confirmed dispatch awaiting observation is not an uncertain dispatch; an uncertain dispatch stays
reserved until reconciled; SILENCE proves neither failure nor retirement; the lifecycle is scoped
PER CALLER AND TARGET INSTANCE; and `<bus>/checks/cues/<id>.json` remains THE RECORD OF THE
DISPATCH, which the registry only INDEXES. HEALTH is `ok | violation | unknown | not-applicable`
per invariant per entry, and an UNKNOWN observation pauses ONLY the effects that depend on it —
receipts, control handling (cancellation, supersession, changed hashes), bounded safety
reconciliation and unrelated authorized safe work continue, so there is no global "repair
everything before any effect" deadlock. VOCABULARY: the installed informal "an alive handle"
(`references/RECOVERY.md` A.11(a) and R7, §6.6 rule 3) denotes this lattice's `live`, not a
seventh state.
E1 THE PER-OWNER CONTINUATION REGISTRY. ONE authoritative index per owner at a NAMED checkpoint
path — not a second worker state machine and not task-local snapshots scattered per run. For a bus
of the current schema the path is `<bus>/checkpoints/<alias>/continuations.json`; on an
ESTABLISHED PRE-V2 bus it is the path that bus's own `PROTOCOL.md`/checkpoint layout names, and
for this project's legacy bus the EXISTING registry location `<bus>/checks/watchers/<alias>.json`
extended to all continuation kinds and NOT renamed, conditional on that bus's own protocol and
adoption record; the v2 checkpoint paths are not required of it (`references/RECOVERY.md` A.0).
That extension of an established bus's registry is that bus's own opt-in (S2), never a consequence
of installing the package (S1). COMMON entry fields: `intent_id`; `owner_instance`;
`target_instance` (where different); bus identity or an explicit legacy path; `route` with its
record; `kind` (`watcher | timer | worker | cue`); `state` (E0); `handle` (nullable); `expires_at`
and `last_activity_at` (both nullable); `registered_intent_at` and `registered_actual_at`;
`last_observation` = `{source, time, scope, result}`; and, for workers, `journal_ref` = the SKILL
§10 unit/attempt id. TIMER entries additionally bind `work_generation`; `pause_generation`, which
is `not-applicable` for a NON-QUOTA justification and is never an invented quota pause;
`justification`, exactly one of E2 H2's three admissible values; and its `evidence`. CUE entries
additionally bind `covered_ids`, `thread_provenance`, `native_idle_evidence`, the caller/target
scope of the outstanding-attempt rule, and — for a cue naming work the target has already ACCEPTED
— the exact unit id, attempt, request and input generation and the current-actionability finding
SKILL §7 already requires; their intent/result/observation records ARE the
`<bus>/checks/cues/<id>.json` record, which the registry indexes and never copies. Null expiry and
null last activity are ALLOWED where the harness exposes none, recorded as null, never as zero or
"fresh". NEVER in the registry: tokens, token-bundle contents, account identifiers, credentials,
or any cue CONTENT beyond the pointers the cue itself carried. The registry carries a
`snapshot_generation` and an `observation_coverage` of `complete | partial | unavailable`; a
retained sample keeps its ORIGINAL observation timestamp and is never restamped at copy time; a
`verified: <time>` field with no accompanying RESULT is read as `unknown`. Native inventory reads
are BATCHED at existing checkpoints — one task-list/automation-status read per checkpoint — and
transcript scans and process polling never become a per-token or per-tool-call loop. The registry
index is recorded in the session's own durable checkpoint (§6.6 rule 4 as extended here).
E2 THE INVARIANTS H1–H7. H1 WATCHER, ROUTE-CONDITIONAL: at most ONE unresolved watcher intent or
handle per owner and bus; exactly one VERIFIED watcher is expected only where the WATCHING route
applies, the CUE-TARGET side records `not-applicable` rather than a violation, a closed or
cancelled scope expects none, an `unknown` or `stop-pending` handle is RECONCILED rather than
duplicated, and bounded in-turn waits are not persistent watchers. H2 TIMER JUSTIFICATION —
NECESSARY, NOT SUFFICIENT, NOT AUTHORIZATION: a timer entry names its justification WITH evidence,
its actual owner and target, its VERIFIED route and its work and pause generations, and the
ADMISSION PREDICATE admits EXACTLY THREE justifications and no fourth — `cap-near` = a FRESH
binding-window OBSERVATION that SATISFIES `references/QUOTA.md` §4's WARN or LOW condition or its
VALID-FORECAST condition — §4 is expressed in REMAINING capacity, so the numeric branch means
remaining AT OR BELOW the WARN threshold (default 25 %); a high remaining percent such as 80 % ALONE
does not qualify, while a valid §4 forecast still can — that observation recorded as the evidence with its time, window and source;
`resume-after-pause` = the §8 resume timer BOUND to its pause generation, the evidence being that
generation and its blocking-window set; `poll-external` = a NAMED external state the harness
cannot notify about, with its EXPECTED CHANGE RATE, the evidence being that state, the source
actually read and that rate, and NEVER a peer's reply, whose silence and escalation SKILL §6
governs. EXPLICIT BAN: a routine fallback, a keep-alive or an "in case" wakeup is NOT an
admissible justification and no timer is armed on one ("routine sampling needs no timer" is a
separate statement and does not carry this prohibition). A NON-QUOTA justification records
`pause_generation: not-applicable`. Admission is NECESSARY ONLY: a purpose is not an exemption,
and H3 and the route authorization of SKILL §7 remain INDEPENDENT gates that no justification
satisfies, weakens or waives, while §8's aggregate-window test, user-cancellation rule,
future-reset requirement and no-repeat gates continue unchanged. An unjustified or unverifiable
timer is RETIRED as PLANNED at the inspection step and PERFORMED as an authorized stop in the
effect phase; a failed or unconfirmed stop stays `stop-pending` with its handle preserved. The
predicate is the ORACLE of checklist K's justified/unjustified timer cases. H3 NO SELF-WAKEUP OVER
OWNED WORK — NO CAP-NEAR EXEMPTION: for EITHER harness, absent a VERIFIED non-interrupting
delivery route, no self-wakeup timer may overlap a potentially active owned worker or an in-flight
tool call, INCLUDING `launch_unknown` work whose start is not established, and an owned worker in
state `closed` whose DESCENDANTS are UNKNOWN or whose effects are unreconciled counts as protected
owned work; quota is sampled inside the active turn instead; an ELIGIBLE resume timer is armed
only after owned work has drained or been otherwise reconciled; and an earlier idle timer is
RECONCILED and CANCELLED BEFORE protected work resumes, arming at turn end not being sufficient on
its own. No claim is made that a child's completion reopens an ended parent turn. H4 WORKER
OBSERVATIONS — NOT INFERENCES OF DEATH: native task status, timestamped activity, a TERMINAL task
state and verified process-group cessation are FOUR different kinds of evidence recorded
distinctly with their source and scope; silence, an old transcript, an exceeded expected window,
`not found` and a missing completion record all mean UNKNOWN; an exceeded expected duration
triggers a BOUNDED investigation, never retirement and never a retry. FRESH-ATTEMPT ALTERNATIVES,
preserved in substance: a fresh attempt requires EITHER (i) a PROVEN NON-SPAWN — the unit accepted
and NEVER LAUNCHED, so there is no terminal worker whose cessation could be evidenced, the branch
installed `references/RECOVERY.md` A.8 already carries — OR (ii) VERIFIED CESSATION in the
NECESSARY SCOPE with that scope stated; BOTH branches then require reconciliation of descendants,
of output and publication state and of retained locks, and BOTH remain under the EXISTING SKILL
§10 fresh-attempt gates and the ownership gates of SKILL §11 and `references/RECOVERY.md` G.3, so
installed rules are preserved and no new retry permission is granted. A MISSING HANDLE and OLD
ACTIVITY prove NEITHER branch; a successfully completed unit may need VALIDATION, not relaunch;
and a handle the harness shows and the registry does not name stays `unowned_unknown`, reported,
neither adopted nor stopped. H5 LOCAL DURABLE CONSISTENCY — NOT PEER SYNCHRONIZATION: the registry
is consistent with the session's own LATEST PUBLISHED local generation and with the peer NOTICE
actually seen, never blocking on the peer's current quota band, heartbeat or snapshot generation
(SKILL §6); a `prepare` or `quota-paused` record MAY legitimately retain draining, unknown,
interrupted or completed worker entries, recorded explicitly, and the mere presence of workers is
no violation; no worker is ever killed and no entry ever erased to make a snapshot look healthy.
H6 ARMING DISCIPLINE — THE FINAL OPERATIONAL PHASE BEFORE YIELDING: arming is not literally the
last action, since the actual handle, the checkpoint, the heartbeat and a permitted status still
have to be written; BEFORE arming, current controls (cancellation, supersession, user instruction)
and current eligibility are rechecked; AFTER arming only registration of the actual handle, the
checkpoint write, the heartbeat rewrite, a permitted status and the yield are allowed; the ACTUAL
arming RESULT is persisted in the registry and, where it changed, in the heartbeat, and the
announced PLAN alone never records a successful arming; new input or new work RECONCILES the timer
before work resumes; an `unknown` dispatch never causes a duplicate timer; on firing or on an
observed interruption the EXISTING merged `references/RECOVERY.md` A sequence is entered, so
identity, intake and control, inspection and the ONE pre-effect status precede every stop, re-arm
or retry, and this revision's health check is part of A.7/A.8 and never a second repair sequence;
interruption events are bound to their ACTUAL source and DEDUPLICATED, a quoted historical marker
or the same marker re-read from a transcript being no new interrupt; and a pending peer reply is
not an in-flight tool or process and does not by itself forbid an otherwise eligible idle wait. H7
CUE DUTY (WATCHING SIDE) — PUBLISHING IS DELIVERY, NOT ACTIVATION; THE DUTY IS TO EVALUATE SKILL
§7's EXISTING PROCEDURE: it DEFINES NO SECOND CUE STATE MACHINE and WEAKENS NO EVIDENCE RULE. On
the WATCHING side, after publication and after ordinary reconciliation, EVALUATING §7's existing
eligible-cue procedure is a DUTY, not a discretion; when that procedure PERMITS dispatch for the
CURRENT TARGET INSTANCE and the PENDING GENERATION, ONE coalesced cue is dispatched, otherwise the
REASON FOR DEFERRAL is recorded and the duty stays pending. The INSTALLED trigger and coalescing
rules apply unchanged and are NOT replaced by an exhaustive three-type list — they include a
reply-required request, a handoff, a re-entry or recovery status, a newly supplied REPLY OR RESULT
that makes already-accepted work actionable, and pending ids DISCOVERED AT RECONCILIATION — while
neither a `dependency-blocked` line nor an unchanged `waiting:` state independently creates
another cue. The two GATES that decide dispatch are the route's required NATIVE-IDLE evidence and
the TARGET LIFECYCLE evidence, exactly as SKILL §7 condition (a) and `references/HOST_ROUTES.md`
§2 step 3 state them; an ACTIVE or UNKNOWN target means RECORD A PENDING DUTY, NOT DISPATCH. Role
evidence is NOT a gate: a heartbeat line, a participant/activation-role description, the END OF A
BOUNDED WAIT and an unchanged blocked state IDENTIFY THE ACTIVATION ARRANGEMENT ONLY — a bounded
wait can finish while its parent turn is still active. The duty binds only the WATCHING side of a
route the TARGET's own record marks `verified`; a first-use route EXPERIMENT is separately
authorized, is not a §7 activation and creates no ongoing duty (`references/HOST_ROUTES.md` §0).
ACTION AND CONTENT: ONE coalesced cue per target per caller over the VERIFIED route, following
`references/HOST_ROUTES.md` §2 — the intent recorded under `<bus>/checks/cues/<id>.json` with the
fields §2 step 5 lists, stdin from `/dev/null`, the result recorded with its exit code and output
— and its BODY is the INSTALLED EXACT CUE TEMPLATE of SKILL §7, i.e. that FIXED ROUTING TEXT plus
MESSAGE POINTERS and nothing else: no summaries, no extra bus-location paths, no scope, deadline,
permission or ruling text; an UNRESOLVED target-to-bus location follows the EXISTING user location
handoff, since "the cue is never broadened to carry paths" (§2 step 7). DRAIN: `observed` requires
TARGET-ORIGIN evidence bound to THIS cue's covered set and generation SHOWING the covered requests
or units handled or drained, while a generic receipt, a `task_started`, a changed heartbeat or an
unrelated status id is SUPPORTING DATA ONLY and retires nothing; after a drain OR a retirement the
pending generation and any UNCOVERED ids are RECHECKED, and neither a cancellation nor a
retirement may strand new uncovered work or let a late callback revive a superseded generation.
LIMITS: no second cue while the prior attempt is UNRESOLVED, the exits being a VERIFIED FAILED
DISPATCH, a CANCELLATION or a RECONCILED RETIREMENT and silence none of them; an uncertain
dispatch is reconciled before any repeat; exit 0 and a "Queued …" line prove DISPATCH only; the
duty is SYMMETRIC if the roles reverse; and it NEVER creates, activates or broadens a route.
EXECUTION: the cues the watching side CURRENTLY owes — those PLANNED at `references/RECOVERY.md`
A.7 AND those first RECORDED OR UPDATED through the A.10 status — are dispatched in the named
effect sub-step A.11(c-bis), with the route authorization, the target lifecycle, the caller's
native-idle evidence, the covered generation, actionability and any outstanding attempt ALL
re-evaluated there; no cue is dispatched at A.7, publishing the A.10 status RECORDS OR UPDATES the
duty and is NEVER an immediate dispatch, and a duty arising during the terminal timer phase A.13
is RECORDED there and reconciled in the next permitted phase. H1's "the CUE-TARGET side has none"
and H7 are the two halves of ONE rule — the side that has no watcher is woken by the side that
carries the duty — and the cue is itself a CONTINUATION entry, registered
intent-before/result-after like any other, with the `checks/cues/` record remaining the record of
the dispatch.
E3 SKILL §6. The heartbeat gains one OPTIONAL derived `continuations:` line (`route`, `watcher`,
`timers`, `workers`, `cues`, `unknown`, `coverage`, `checked`, `snapshot`) that distinguishes a
KNOWN zero from an UNAVAILABLE observation, is never liveness evidence, never proof of the peer's
or its own idleness and never authority to retry, relaunch, cue, take over or release a lock; the
authoritative index and the uncertainty records stay REQUIRED and a missing hint proves nothing.
Beside the exhausted-receipt-budget rule a NON-GATING note records that, where the peer's
REGISTERED activation is CUE-ONLY, a bus-only inquiry is not a substitute for a cue — publication
into an inbox the peer has no mechanism to notice is DELIVERY, not activation — while §6's own
escalation (ONE inquiry, ONE `peer-unreachable` notice, the "availability unknown" marking, the
stop-polling rule) keeps its installed conditions EXACTLY and is NOT gated on any cue evaluation.
E4 SKILL §7. The armed-continuation sentence gains any other self-wakeup, every WORKER this
session launched and every CUE it dispatched; registration is E1's per-owner registry, with
workers LINKED to their §10 record and a cue INDEXING its `checks/cues/` record; the self-wakeup
text carries H2's three-justification admission predicate with its explicit ban and its
independence from the other gates, and H3's no-arming-over-owned-work rule with the FINAL
OPERATIONAL PHASE before yielding — a general yield-phase rule whose RE-ENTRY instance is
`references/RECOVERY.md` A.13 and not its only occasion. The default activation pattern gains the
cue DUTY of H7 as the other half of its asymmetric pair.
E5 SKILL §11 and SKILL §10. §11 (with `references/RECOVERY.md` A.5) gains the `interrupt` re-entry
event: an OBSERVED interruption of this session's own active turn, bound to its actual source and
DEDUPLICATED by that binding, recording what was in flight as observations with their scope and
inferring no cessation. §10's fixed wake order keeps every step; its final clause now states that
a turn which then arms an ELIGIBLE resume timer does so in the TERMINAL YIELD phase AFTER the
heartbeat rewrite, not as a step of that order — reaching the broadest statement of the order,
including the ordinary `quota-paused` turn, and not merely the re-entry sequence.
E6 `references/RECOVERY.md` A AND `references/QUOTA.md` §8. Checklist A's step map and
numbering-history note gain step 13; A.7 inspects WATCHER, TIMER, WORKER and dispatched CUE alike,
batches its inventory reads, classifies by E0, records observations rather than inferences, plans
retirements, at most ONE watcher re-arm and any owed cue with its gate findings, and arms, stops
and dispatches nothing; A.11(a) keeps retirement, the watcher re-arm and handle registration and
no longer arms the resume-timer replacement; the new effect sub-step A.11(c-bis) OWED CUES,
inserted after (c) and before (d), takes the cues CURRENTLY owed — those planned at A.7 and those
first recorded or updated through A.10 — and rechecks route, lifecycle, native-idle evidence,
covered generation, actionability and any outstanding attempt and then dispatches at most ONE
coalesced cue or records the deferral reason; the new terminal step A.13 TERMINAL YIELD rechecks
controls and eligibility and arms at most ONE eligible resume timer under the conditions §8
states, publishing a further status only where the outcome DIVERGES from the plan step 12
announced; checklist J case 28 is re-decided against A.13, its stem's discriminator evaluated at
the same step as the rule it tests; and §8 names A.13 as the execution point and states the
admission predicate and the no-arming-over-owned-work rule. The move is PROSPECTIVE: evidence
written under revision 8 or earlier KEEPS ITS OWN LABEL AND VERSION, revision-9 evidence cites
A.13, and G.1's watcher re-arm / cue-route reconciliation and SKILL §10's interrupted-effect
citation of A.11(a)-(c) are unchanged in every revision.
E7 `references/RECOVERY.md` checklist K, the continuation-snapshot drill on an isolated scratch
root, run after this revision's text and its exact plan are frozen and after checklist C's real
handoff cycle, checklist D's controlled joint recovery drill and the FULL frozen checklist J
regression — every case, including subcases such as 23b and all of case 28's branches, an
unchanged case reused only under an explicit VERIFIED unchanged-input justification — and before
the SKILL §9 agreement gate. K supplements §9, C, D and J and replaces none of them.
E8 This section, the SKILL scope paragraph (which REPLACES rather than accumulates, following
revision 8's own precedent, the prior denials staying binding through the "remain in force as
amended here" clause, and the paragraph's own S1/S2/S3 sentences lying outside the replaced span)
and `MANIFEST.json` (revision 9, design revision 20).

### 18.3 Boundaries
No helper is added or changed and no `snapshot.py` is introduced. No route is created, activated
or broadened; no delivery rule, receipt, exclusion, binding/lock, item/ledger or unit-journal
semantic changes; `references/HOST_ROUTES.md` is byte-identical and H7 only CITES its §0 and §2.
No first-use route experiment is converted into an ongoing duty. No hook, service or scheduler is
installed by the package, and installing it (S1) by itself extends no established bus's registry
and activates neither S2 nor S3. H7 states a DUTY TO EVALUATE an already-verified route's existing
§7 procedure and replaces none of §7's gates, and the §6 cue clause is a NON-GATING note beside
the peer-unreachable escalation, which keeps its installed conditions exactly. No survival,
non-interruption or child-reopens-parent property is claimed for any harness.
`references/QUOTA.md`'s line ceiling, ≤250 at §17.4, is ≤260 from this revision onward, accepted
only because the final file meets it with no rule compressed or omitted.

### 18.4 Provenance
Candidates: `PROPOSAL_v3.md` sha256
880b2008781fea905e7f2069e26f8c8b4e4e787e04c3739b469a23e7cee573fe, and the v4 candidate
`PROPOSAL_v4.md` this section implements, whose own sha256 is recorded in the EXTERNAL release
record rather than inside the payload it specifies — a file cannot carry its own hash. Verdicts
and tool evidence: `checks/skill_rev9_snapshot/codex/packet_v1/REVIEW_v1.md` (BLOCKED AS WRITTEN)
sha256 ec9caaf4988dde0617bdb5518456e88394288cba13ae63f3ce6ed7b49428459e;
`checks/skill_rev9_snapshot/codex/packet_v1/HARNESS_OBSERVATIONS.json` sha256
36f89d4d39b682c79d4d1904ef7ebd195128be1c8cd020f43b130b658e3505d6;
`checks/skill_rev9_snapshot/codex/v3_review/INCORPORATION.md` sha256
4aa1c2b35a1db7f41519a9ae793e3dd77666a2d5e8bbfa6e885196ec55c2dea4;
`checks/skill_rev9_snapshot/codex/v3_review/H7_DIRECTION.md` sha256
59f8751c10408c09a6905f15bf82a604290b4758327f3f56cf34237c4b0b7434;
`checks/skill_rev9_snapshot/codex/v3_review/h7_review/REVIEW.md` sha256
79fd62bdb3452eb232b957b34ff24eaf64985e74e853142d6ee8f729127a2025; and
`checks/skill_rev9_snapshot/codex/v3_review/RESULT.json` (BLOCKED_RESIDUAL_CORRECTIONS) sha256
ebb754ae743c69176e02a5936279419baa0f79beede0d9e552e55a83212c77c1. The four message ids of the
round: consult `20260918T213658Z-claude-consult-skill-rev9-continuation-snapshot-e61bc89e`; review
`20260918T215230Z-codex-rev9-continuation-snapshot-review-q1-q5-9c5d8af4`; v3 request
`20260918T230607Z-claude-request-rev9-candidate-v3-incorporation-check-30fb62eb`; v3 verdict
`20260918T231918Z-codex-rev9-v3-incorporation-h7-residuals-a307c877`.
H7's MOTIVATION, WITH ITS LIMITATIONS (2026-09-18, this project's bus) — reported dispatch and
response evidence, NOT a witness of compliant H7 dispatch. FOURTEEN messages were published to
`inbox/codex` between 19:22:55Z and 21:21:49Z, one of them a reply-required review packet
(`…-47cc5b8c`, 20:28:57Z) that went unread for about 75 minutes while the target's heartbeat read
"dependency-blocked … no service or scheduler"; a bus-only availability inquiry published at
21:21:49Z could not be read either, for the same reason. The cue dispatched at 21:44:41Z
(`checks/cues/20260918T214441Z-claude-cue-rev9-f102a-3bbdc8da.json`) returned exit 0, a
`task_started` followed at 21:45:13Z, and at 21:45:57Z the target published TWO REQUEST RECEIPTS —
`…-a480a52f` re the F-102a packet, which also answers the 21:21:49Z inquiry, and `…-aeaf9f17` re
the consult — PLUS ONE HANDLED INFO, `…-0149d040`, that same 21:21:49Z inquiry; never "three
receipts". Codex's own outgoing recovery-status info `…-d00f59fb` is separate SUPPORTING recovery
evidence, not that handled item. LIMITATIONS: that record's `native_idle_evidence` field holds
`thread_settings_applied` events plus historical heartbeat and message data, which do NOT
establish the native-idle and target-lifecycle predicates H7 requires, and its `message_text`
carries summaries, a bus-location path and recovery/pause instructions rather than SKILL §7's
exact cue template; later target-origin drain evidence, if separately verified, cannot
retrospectively validate the pre-dispatch gates or the cue content; and the reviewer scanned no
transcripts and did not independently inspect the referenced receipts.
`checks/activation/QUEUE_ROUTE_EXPERIMENT.json` is cited as a user-authorized FIRST-USE EXPERIMENT
and not as a source of duty.

### 18.5 The peer's drafting qualifications
Carried in substance, as §17.6 does. R1: the H2 admission predicate must stay CHECKABLE — exactly
three defined justifications with their evidence, an explicit ban on routine fallbacks,
keep-alives and "in case" wakeups, `pause_generation: not-applicable` for a non-quota
justification rather than an invented quota pause, and admission necessary only, with H3 and route
authorization as independent gates. R2: the PROVEN NON-SPAWN branch of the fresh-attempt rule is
preserved verbatim in substance beside verified cessation in the necessary scope, both under the
existing §10 fresh-attempt and ownership gates, a never-launched unit having no terminal worker
and a missing handle or old activity proving neither branch. R3: historical records keep their own
label and version — evidence written under revision 8 is not reinterpreted as A.13 — and the old
operative rule is superseded PROSPECTIVELY. R4: the drill plan is the real checklist C handoff,
the controlled checklist D drill, the FULL frozen checklist J regression and only then K, which
supplements. The seven H7 corrections: role evidence is not a gate and first-use experiments are
separate; the existing dispatch/result/drain/retirement lifecycle is kept rather than reduced to
three values; the trigger set is not narrowed to three message types; the exact installed cue
template is retained with no arbitrary paths; the full target-origin drain criterion stands, a
receipt or `task_started` finishing nothing; the execution phase is named, publication never being
a dispatch; and K case 12 carries the negative and race branches. The H7 evidence qualification:
the cited 21:44 cue is MOTIVATION with its limitations, not a compliant-dispatch witness. D1: the
existing-path branch of §6.6 rule 1 is retained and S1 installation alone extends no established
bus's primary legacy registry and activates no S2. D2: the heartbeat hint is a MAY while the
authoritative index and the uncertainty records stay required and a missing hint proves nothing.
D3: actual arming results are persisted and an announced plan alone records no successful arming.
D6: the ≤260 ceiling is a PROSPECTIVE supersession accepted only for a file that compresses and
omits no rule. D7: watcher repair stays at A.11(a), A.13 is timer-only and the cue phase is named.
D8: the scope paragraph REPLACES by the established convention, without broadening S2 or S3.
