# agents-bus DESIGN v2 — universal use (rev 12 = delegation adapter operative for Claude → Codex, 2026-09-13; rev 11 + §6.2 heading, §6.7 results, §6.8 adapter contract summary)

Delta over DESIGN_v1.md (approved 2026-09-13, sha256 d45a4844…). v1's message, state, lock,
status, silence/recovery, delivery ≠ activation, trust and release-gate semantics stay in force
unchanged. rev 3 takes Codex's "small version" (`checks/universal_review/DRAFT_REVIEW.md`,
sha256 d37daa60…): single domain, conservative atomic init, same-instance registration with new
aliases (no automatic replacement), exact bindings, tested locks; activation is an honest,
separately verified adapter. Previous drafts: rev 1 77f7aec7…, rev 2 5de876cb…, rev 3 70a8bf40… (kept beside). rev 4 folded Codex's six implementation constraints (message 20260913T190952Z-codex-accept-core-prototype-53289657); rev 5 folds the findings of the implementation itself (message 20260913T191516Z-codex-core-tested-cli-0e741df0): release runs under the `meta` guard too, board logging uses a short `meta` → `state` guard only after the participants/binding guards are released, a busy board is reported as pending, and the helper CLI is a separate `admin.py` (see §10). rev 8 (revision C) records the fixes made after Claude's independent core review (report `runs/universal-v2-20260913-b/claude_core_review.md`): OWNER stores a token digest, release reports per key, `state` is the explicit board-edit key, the explicit-bus selection sentence is removed, and the crash/staging claims are scoped honestly. rev 6/7 (operator-convention proposals) stay superseded. This is the design text the next freeze and release bind.
Prototype until the bilateral gate passes again for this design + helper manifest + actual runs.

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
