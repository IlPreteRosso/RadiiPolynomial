# Recovery checklists

## A. Re-entry after any compaction, restart, reconnect
0. Discover the bus by SKILL §1 (marker walk; a corrupt named candidate is fatal). If the bus is
   an ESTABLISHED PRE-V2 bus (identifiable earlier layout, no `bus.json`), stop here and follow
   that bus's own `PROTOCOL.md` re-entry procedure and checkpoint paths; the v2 steps below
   (participants, `hello`, token bundles) do not exist there.
1. Read `<bus>/PROTOCOL.md`, `STATE.md`, your `participants/<alias>.json`, your
   `heartbeat/<alias>`, then your inbox oldest → newest and `<bus>/checkpoints/<alias>/handled.json`.
2. Present the SAME instance id (your harness session id, or the minted one at the location your
   checkpoint recorded): `hello` refreshes your record. A new instance under a registered alias
   is REFUSED: announce under a new alias and treat the predecessor's pending requests as work to
   reconcile explicitly — you inherit no task, request or token.
3. Read `<bus>/checkpoints/<alias>/*.json`; reconcile completed artifacts by hash.
4. Locate your token bundles at the paths your checkpoints recorded and compare with the ACTUAL
   lock directories (`lock show`): continue or release only locks whose OWNER matches your
   alias, instance and a bundle you hold; never touch others (a predecessor's locks are recovered
   only by its release, or verified cessation plus an authorized decision, SKILL §4).
5. Recover your last `status-seq` (highest among `<bus>/.messages/*-<alias>-*.md` with your
   `sender-session`) and publish a recovery status with a higher seq before resuming effects.
6. Answer only the requests you have not yet acknowledged (per `handled.json`) with at least
   `reply state: received`; a late matching reply may finish a still-pending request exactly once;
   replies for cancelled, superseded or changed-hash work are recorded but do not revive it; ask
   for current evidence if a reply is insufficient.
7. Reconcile ARMED CONTINUATIONS before arming anything: read your durable registry index (your session
   checkpoint) and follow the registry locations it records (`<bus>/checks/watchers/<alias>.json` or the
   checkpoint itself; no helper provides a watcher field or discovery, design §6.6), verify each handle with the harness itself (task list, automation
   status), retire those whose scope is closed and record the actual stop result (a failed stop stays
   `stop-pending` with its handle preserved), and only then re-arm at most ONE watcher per bus for this
   session — never duplicate an alive handle; "no entry" never means "no watcher". Re-arm only the
   activation your session actually has and has verified (persistent inbox watcher, bounded in-turn
   waits, a user-armed app schedule, otherwise the recorded user relay); never install a new service
   silently. Register the new handle (intended before the call, actual after).
8. Rewrite your heartbeat. Publish a status only if something changed since your last published
   one; if the scope is truly empty and that is new, say "nothing to wait for; nothing to do".

## B. Peer silent (receipt budget exhausted)
1. One availability inquiry (`info`) at the inquiry mark; one `peer-unreachable` notice at budget
   end — never more per episode; retries keep the logical request id.
   A peer reachable only through a schedule (`app-heartbeat`) has a receipt budget of at least three
   cadences; do not declare silence earlier.
2. Checkpoint the dependency as "availability unknown": pending, not cancelled.
3. Stop your own related work; release only your own locks; never the peer's, and never re-use
   the peer's alias or identity — a stale heartbeat proves nothing about its writes.
4. Continue independent authorized work or prepare an isolated proposal; tell the user the exact
   blocked dependency and the recovery path (relay line `→ <to>: <absolute path>`).
5. On the peer's return it runs checklist A; you reconcile its late replies against the still
   pending generation. Silence never satisfies an agreement gate or frees a lock.

## C. Handoff cycle (the real-work exercise)
offer (`handoff`, sender's locks released, input hashes stated) → `reply state: received` within
seconds → `accepted | blocked` → receiver takes the resource lock(s) with a token bundle, works,
rebuilds/validates, releases → `done` with per-item dispositions, output hashes, gate results →
sender re-verifies against those hashes → `done` closing the task, or a smaller handoff for
residuals.

## D. Joint recovery drill (run it before agreeing to a changed design)
Own run directory under the bus's evidence area (`<bus>/checks/<run-id>/`; on a scratch bus when
the drill re-runs for a changed design); no real process killed, no real lock touched (a sentinel
file stands in for a peer-owned lock); wording "controlled simulation", never "a real crash was
tested".
1. Peer replies READY (`accepted`) to a preparation request and reads the packet.
2. Sender sends HOLD; peer deliberately stays silent; sender's short drill budget expires; sender
   persists `peer-unreachable`, the pending HOLD id, design/input hashes, sentinel hash, zero
   completed effects, next action; publishes a timeout status (no reply expected).
3. Sender sends RECOVER pointing at the packet and checkpoint. Peer reconciles from those files
   only, publishes a recovery status, performs ONE idempotent effect (`effect.json`: HOLD id,
   design hash, actor/instance, `application_count: 1`; reuse if identical, `blocked` on conflict),
   replies `done` naming the original HOLD id, effect path/hash, checkpoint facts.
4. Sender republishes the SAME HOLD id/bytes and sends DUPLICATE CHECK; peer answers from its
   durable record: count still 1, hash unchanged, archiving did not reactivate the work.
5. Both post a scoped final status: "nothing to wait for; nothing to do", listing unrelated
   pending work separately. Then the real handoff cycle (C) before any agreement sentence.

## E. Bootstrapping a new project (portability exercise)
1. Choose `R` as SKILL §1 says; one of you runs `init`; both run `hello` under distinct aliases
   with your harness session ids; each records its real activation.
2. `bind` one key per shared resource, exact paths.
3. One request/reply round trip with receipt-first and a keepalive wait; acquire the key you just
   bound with a token bundle and release it; one wrong-owner release attempt (must be refused);
   one alias collision (must be refused).
4. Record the run under `<bus>/checks/<run-id>/` and quote its hashes in the first real handoff.

## F. Delegation drill (fresh worker; `scripts/delegate.py`; run on a scratch bus before agreeing to any change of the adapter contract)
0. Adapter policy (user-set, outside the bus; see design §6.8 for the validated shape): executable + version
   that parses the user's configuration, argv template, runner argv, caps, wall clock. Scratch root + bus by
   `init`; maintainer `hello`; `bind` an empty effect directory under a fresh key.
1. Probe 0 (startup/auth/exit only): the harness CLI with a trivial prompt, read-only sandbox, stdin=/dev/null;
   child id from harness output only.
2. Probe 1 (permissions inside the sandbox): one effect inside the root, the runner and skill file read from
   inside; a negative check (write outside the root) counts only with a raw command record in the event stream.
3. Drill A2: `delegate.py plan --worker-class job --lock-key K --effect-dir D --expect effect.txt=line:<job>
   --barrier <run>/GO ...` → `launch` (in its own thread or process; it blocks until the child ends; a refused
   capacity reservation returns at once — check the launcher's error before binding) → `bind` → wait for the
   worker's pinned `received`, inject an unrelated request addressed to the worker alias, record its time,
   create the barrier file → `wait` → `verify --late-id <id> --go-at <time>` (contract PASS: no failed and no
   UNVERIFIED predicate; ask the worker for observation pacing so ordering/ownership are requester-observed)
   → `replay` (idempotent; refused unless the contract is PASS). `verify` exits 0 only on PASS, 3 on
   PASS-WITH-UNVERIFIED. Evidence: the run directory (PLAN/STATE/LAUNCH/SUPERVISOR/BIND/WAIT/OBSERVATIONS/
   RESULT/REPLAY), the worker's checkpoint + final record, the ledger record.
3a. Capacity refusal: an unsupported or corrupt record in `<root>/.adapter/launch/` counts as live AND recent
   and refuses every launch; never edit it in place. Move it out (`reconciled/` + a note) ONLY under a
   recorded decision bound to actual evidence: a pre-spawn certainty (the record shows no spawn and the
   launch was never invoked or failed before spawning) or a verified cessation record for its process
   group; elapsed time and absent output are not evidence. Otherwise keep the uncertain capacity. Then
   relaunch and rerun `bind`. A run whose final records could not all be written (`persistence_errors`,
   ledger `unknown` or still `running`) is reconciled the same way: verify refuses it until then.
4. Drill C (interruption): a request variant that sleeps after acquiring the lock; when the lock OWNER shows
   the worker alias + observed identity, write `<run>/STOP`; the supervisor stops its own child group →
   outcome `stopped`, cessation verified; the stranded lock is NOT touched and recovery stays PENDING (owner
   release, or verified cessation plus an authorized decision, SKILL §4); no retry of the uncertain effect.
5. If one direction is blocked by host policy, publish the limitation; no bidirectional claim.
6. Deterministic suite: `scripts/test_delegate.py` with the fake harness `scripts/fake_worker.py` (the
   adversarial witnesses, the observation-binding witnesses, validation-failure lifecycle, publish/replay
   preflight, capacity refusal + reconciliation, launch-bracket failure injection); run it before and after
   any helper change, with `PYTHONDONTWRITEBYTECODE=1`, and record the count in the release evidence.
