# Recovery checklists

## A. Re-entry — the ONE merged order (any compaction, restart, reconnect; after a force termination the steps marked [G.n] also apply checklist G's fuller rules at that step)
Steps 0–9 read, reconcile and PLAN (the only messages they send are the receipts SKILL §5
requires); step 10 publishes the single pre-effect recovery status; only step 11 executes anything
resumed, in a fixed order; step 12 rewrites the heartbeat; step 13 is the terminal yield phase —
the only step that ARMS an eligible resume timer (QUOTA §8), after which nothing remains but
registering the actual handle, the checkpoint, a permitted status and the yield. No step before 10
releases, continues, re-arms, retries, publishes a project effect or resumes queued work. The
on-disk checkpoint is the
state of record against any harness-injected summary (I.2), but it never overrides the live user's
current instructions or a control notice received since it was written.
0. Discover the bus by SKILL §1 (marker walk; a corrupt named candidate is fatal) and read the
   ACTIVE protocol version FIRST. If the bus is an ESTABLISHED PRE-V2 bus (identifiable earlier
   layout, no `bus.json`), stop here and follow that bus's own `PROTOCOL.md` re-entry procedure and
   checkpoint paths; the v2 steps below (participants, `hello`, token bundles) do not exist there.
1. READ (nothing written to the bus): `<bus>/PROTOCOL.md`, `STATE.md`, your
   `participants/<alias>.json`, your `heartbeat/<alias>` — keep its text as a SNAPSHOT in your
   recovery log, because step 2 rewrites it to two lines; the snapshot is optional corroboration
   for step 8, never the queue's membership source — then your inbox oldest → newest,
   `<bus>/checkpoints/<alias>/handled.json`, and your last `status-seq` (highest among
   `<bus>/.messages/*-<alias>-*.md` carrying your `sender-session`). If your checkpoint carries a recovery-package pointer (`references/QUOTA.md` §5), read the package too; the journal remains the state of record. For a recognized coordinator
   cue, apply SKILL §8: reconcile named messages, handled ids and later amendments from the
   expected participant/session; its label or bus pointers grant no user authority. PLAN any
   stale-cue discrepancy `info` (`re:` the affected request) for publication with or after step 10,
   never as an extra message in steps 0–9. A direct user instruction containing a bus pointer
   retains precedence; unresolved material ambiguity pauses only its disputed effect.
2. IDENTITY. Present the SAME instance id (your harness session id, or the minted one at the
   location your checkpoint recorded): `hello` refreshes your record and rewrites your heartbeat
   (two lines, `active`). A new instance under a registered alias is REFUSED: announce under a new
   alias and treat the predecessor's pending requests and queued units as work to reconcile
   explicitly — you inherit no task, request, unit or token.
3. DURABLE WORK STATE. Read `<bus>/checkpoints/<alias>/*.json` and ENUMERATE the unit journal under
   the checkpoint base the ACTIVE bus prescribes (this schema:
   `<bus>/checkpoints/<alias>/units/*.json`), every unit, latest attempt first; reconcile completed
   artifacts by hash. The journal is the authority for accepted work: a `planned` unit is queued
   whether or not any heartbeat line named it; a unit a line names but the journal lacks is
   reported as an unknown reference, never created.
4. LOCKS — INSPECT ONLY. Locate your token bundles at the paths your checkpoints recorded and
   compare with the ACTUAL lock directories (`lock show`); classify each lock: yours with a matching
   bundle, yours without one, foreign. Continue or release NOTHING here: the decision is step 9 and
   the effect step 11(b), after step 8 shows no delegated work still using a lock; never touch
   others (a predecessor's locks are recovered only by its release, or verified cessation plus an
   authorized decision, SKILL §4).
5. EVENT AND LIVE INSTRUCTIONS. Record the re-entry event (`compaction`, `restart`, `reconnect`,
   `force-termination`, `interrupt`, …) and the live user's current instructions for this scope;
   every reconciliation below is made against them — the checkpoint cannot override them. An
   `interrupt` event is an OBSERVED interruption of this session's own active turn, bound to its
   actual source (the harness event or the transcript position where it landed) and DEDUPLICATED
   by that binding: the same marker re-read, quoted, or copied into another file is the SAME event
   and opens no second re-entry. An `interrupt` records what was in flight at that instant — owned
   workers, tool calls, armed timers — as observations with their scope, and infers no cessation
   from any of them (SKILL §11, 'No inference of death').
6. INTAKE and CONTROL [G.2]. Diff the inbox against `handled.json`, oldest first; answer each
   request you have not yet acknowledged with the first reply SKILL §5 requires — here `received`
   or `blocked`; an `accepted` or `done` that promises or performs resumed work waits for step 10; a
   late matching reply may finish a still-pending request exactly once; replies for cancelled,
   superseded or changed-hash work are recorded but do not revive it; ask for current evidence if a
   reply is insufficient. Apply every control notice found here — cancellation (correlated and from
   the requester's own alias, SKILL §10), supersession, changed input hashes, ownership changes,
   lock releases, receipts — to your checkpoints and unit journal now; a message that makes an
   accepted unit actionable or blocked is recorded on that unit now. Delivery is at-least-once:
   inspect task evidence before repeating any effect.
7. CONTINUATIONS — INSPECT AND PLAN [G.1]. Read your durable registry index (your session
   checkpoint) and follow the registry locations it records (the per-owner continuation registry
   `<bus>/checkpoints/<alias>/continuations.json`, or on an established pre-v2 bus the location
   that bus names — `<bus>/checks/watchers/<alias>.json` or the checkpoint itself; no helper
   provides a continuation field or discovery, design §6.6 as extended by §18); verify each handle
   — WATCHER, TIMER, WORKER and dispatched CUE alike — with the harness itself (task list,
   automation status, process group, the cue's own intent/result record), BATCHING those inventory
   reads at this checkpoint rather than polling per token or per tool call; treat every entry AND
   every gap as unknown until verified — "no entry" never means "no watcher", and a handle the
   harness shows but no registry names is `unowned_unknown`, neither adopted nor stopped; classify
   `intent | dispatch-unknown | live | stop-pending | closed | unknown` (a cue by the §7 cue
   lifecycle its own record carries: intent, the actual dispatch result — confirmed or uncertain —
   an observed drain, a reconciled retirement); PLAN retirements, at most ONE watcher re-arm per
   bus for this session, and any cue the watching side still owes (SKILL §7) — recording for each
   owed cue the covered ids and generation, the route authorization, and whether the native-idle
   and target-lifecycle gates are SATISFIED or the reason they are not; arm, stop and dispatch
   nothing here, and dispatch no cue here: an owed cue is EXECUTED at 11(c-bis). An `unknown`
   observation at this step pauses ONLY the effects that DEPEND on it: receipts (SKILL §5),
   control handling (cancellation, supersession, changed hashes), bounded safety reconciliation
   and unrelated authorized safe work continue — there is no 'repair every unhealthy entry before
   any effect' gate. Record OBSERVATIONS, never inferences: native task status, timestamped
   activity, a terminal task state and verified process-group cessation are different evidence
   with different scopes, and silence, an old transcript, an exceeded expected window, `not found`
   or a missing completion record are `unknown`. An exceeded expected duration PLANS a bounded
   investigation, never a retirement and never a retry; a fresh attempt needs EITHER a proven
   non-spawn (the unit accepted and never launched — step 8's branch) OR verified cessation in the
   necessary scope with that scope stated, and in both branches reconciliation of descendants,
   output and publication state and retained locks under the existing SKILL §10 and §11/G.3 gates;
   a missing handle or old activity proves neither; and a completed unit may need VALIDATION, not
   relaunch. A worker entry LINKS to its §10 unit/attempt record and never restates it. A
   resume-timer handle (QUOTA §8) verified lost is RECORDED here retired with that stop result and
   PLANNED for ONE replacement, never armed at this step and no longer armed at A.11(a): the
   eligible arming happens at A.13. Unverifiable is recorded `unknown`, never duplicated.
8. UNIT-JOURNAL WALK — PLAN [G.3]. Per unit, latest attempt first, apply G.3's branch table: a
   missing completion record is unknown evidence, never death; a matching one is `candidate_ready`,
   never publication. For `planned` units (accepted, never launched) recheck the recorded request
   and input digests against the tree as it is NOW and against what step 6 learned: cancelled or
   superseded → recorded, not revived; changed inputs → that unit alone reopens as a NEW attempt
   (permitted only because attempt 1 was never launched; SKILL §10), never a silent resume;
   blocked → stays queued with its dependency named, no cue of your own; actionable → queued for
   step 11(d). `launch_pending`, `launch_unknown` and `running` attempts keep their condition
   (G.3): a changed hash alone never retries them.
9. LOCK DECISION [G.4]. Plan release or continuation only for locks whose `OWNER` matches your
   alias, your instance and a bundle you hold, and only where step 8 shows no delegated work still
   using them; for a foreign lock past the 30-minute threshold PLAN at most one `lock-escalation`
   notice (SKILL §6) — it is published with or after step 10, never from this step (steps 0–9 send
   receipts only) — ownership unchanged.
10. ONE RECOVERY STATUS [G.5]. Publish exactly one status with a `status-seq` higher than step 1
   found, header `recovered-from: <event>` (step 5), listing the reconciled units, the unresolved
   ones with their condition, the locks you hold and the foreign ones you are escalating (the
   notice planned at step 9 goes out with or after this status), the continuations planned, and
   your next action — BEFORE any resumed effect. Publish any cue-discrepancy `info` planned at
   step 1 with or after this status, without reviving withdrawn work or asking the user to
   adjudicate an already-resolved duplicate.
11. EFFECTS — gated, in this order, each rechecking current ownership and generation immediately
   before it: (a) continuations: retire the closed ones and record the actual stop result (a failed
   stop stays `stop-pending` with its handle preserved), then re-arm at most ONE watcher per bus for
   this session — never duplicating an alive handle, only the activation your session actually has
   and has verified (persistent inbox watcher, bounded in-turn waits, a user-armed app schedule,
   otherwise the recorded user relay), never a silently installed service; register the new handle
   (intended before the call, actual after); a resume-timer replacement PLANNED at A.7 (QUOTA §8)
   is NOT armed here; it is armed, if at all, at step 13 under the conditions stated there; (b)
   your own locks, per step 9; (c) BOUNDED SAFETY RECONCILIATION of an
   INTERRUPTED effect — recording its actual outcome and abandoning an intent per SKILL §10/§11 and
   G.3, each under its own gates — which is not a new project effect and is never deferred by the
   test in (d), while RESUMED validation or publication of project work IS a fresh project effect
   and waits for that test with the queue; (c-bis) OWED CUES: for each cue the watching side
   CURRENTLY owes — those PLANNED at A.7 AND those first RECORDED OR UPDATED through the A.10
   status — RECHECK NOW: the route authorization, the target's CURRENT lifecycle and the caller's
   OWN native-idle evidence (SKILL §7; `references/HOST_ROUTES.md` §2), the current covered
   generation and current actionability, and any outstanding cue attempt for this caller/target
   instance — then dispatch at most ONE coalesced cue per target under §7's existing rules and the
   exact cue template, or RECORD THE REASON FOR DEFERRAL and leave the duty pending; an active or
   unknown target defers, and an unresolved prior attempt defers. A cue names only work the target
   already holds, grants nothing and is not a fresh project effect, so (d)'s admission test does
   not defer it (QUOTA §6); it is not an interrupted effect either, so (c)'s rules are untouched.
   No cue is dispatched at A.7, and publishing the A.10 status RECORDS or UPDATES an owed cue but
   never dispatches one — a duty first recorded or updated there is EXECUTED HERE, under these
   same rechecks; (d) the QUOTA ADMISSION GATE and the PRESERVED QUEUE:
   first test the persisted quota-pause state (`references/QUOTA.md` §4) against current samples of
   every binding window — a persisted `quota-paused` whose resume condition is unmet DEFERS every
   fresh project effect, this queue and (c)'s resumed validation/publication alike, whatever woke
   the session, while steps 6, 10, (a), (b) and (c)'s reconciliation run in full and controls,
   results, receipts and recovery information keep flowing (QUOTA §6) — then (c)'s resumed
   validation or publication under its own gates, then the actionable `planned` units of step 8
   within THIS turn, ahead of newly arrived ordinary long jobs (a scheduling priority — intake in
   step 6 was not skipped for them); the substantive first replies deferred at step 6 go out here. A
   replacement instance finds the predecessor's queue as pending work to reconcile explicitly, not
   as its own accepted units (step 2).
12. HEARTBEAT. Rewrite it, with an `idle-with-queue:` line only for what the journal still shows as
   unstarted. Publish a further status only if something changed since step 10; if the scope is
   truly empty and that is new, say "nothing to wait for; nothing to do".
13. TERMINAL YIELD — the final operational phase of this re-entry, after step 12's heartbeat and
   only once 11(d)'s queue and quota-admission disposition is settled. Recheck current controls
   (cancellation, supersession, the live user's instructions) and current eligibility, then arm at
   most ONE eligible resume timer PLANNED at A.7 (QUOTA §8) — ONLY if the route is still
   authorized, the target lifecycle is unchanged, no user cancellation stands for this pause
   generation, the same pause and work generation hold, the aggregate admission test (QUOTA §4)
   still fails, and the original firing time is still in the FUTURE — an elapsed firing time
   instead takes the ordinary fresh-admission path, never a re-arm at that timestamp. Absent a
   VERIFIED non-interrupting delivery route, arm nothing over a potentially active owned worker or
   in-flight tool call (SKILL §7); never duplicate an `unknown` or `stop-pending` handle. Step
   12's heartbeat and its conditional further status already announce the PLANNED arming this step
   carries out — A.7's plan, as part of the re-entry disposition; step 12's own text is unchanged.
   After the arming call, only these remain: register the actual handle with its ACTUAL result,
   update the checkpoint and the registry, rewrite the heartbeat if the arming changed it, and
   publish a further status ONLY where the outcome DIVERGES from that announced plan — a
   `dispatch-unknown` handle, a refusal, or a changed disposition — never a third status of this
   re-entry for an arming that matched the plan; then yield. A cue duty arising in THIS phase is
   RECORDED and reconciled in the next permitted phase — never dispatched here, and this step's
   no-further-effect rule is not bypassed. If new input or new work arrives in this phase,
   reconcile the timer and return to the appropriate earlier step instead of arming.
Numbering history (kept for readers of older evidence): revision 4 had steps 0–8 (5 = status,
6 = intake, 7 = continuations, 8 = heartbeat); candidate 1 of this revision inserted a
preserved-queue step 8 and moved the heartbeat to 9; this text keeps 6 = intake and 7 =
continuations, moves the status to 10 after the reconciliation gates, makes 8 the unit-journal walk
and resumes the preserved queue only as effect 11(d). A bounded scan (501 files) found no installed
text or Codex record citing the earlier A.8; historical evidence keeps its own numbering.
Revision 9 appends step 13 (terminal yield) and moves the ELIGIBLE resume-timer arming there from
11(a), which keeps timer inspection, planned retirement and the watcher re-arm, and inserts the
effect sub-step 11(c-bis) OWED CUES, which executes the cues CURRENTLY owed — those planned at A.7
and those first recorded or updated through A.10. That move is PROSPECTIVE: it supersedes the
operative rule from revision 9 onward, and evidence written under revision 8 or earlier KEEPS ITS
OWN LABEL AND VERSION — a record citing A.11(a) for a resume-timer replacement records revision
8's rule under revision 8 and demonstrates nothing about this ordering; it is neither re-read nor
re-labelled as A.13. Evidence written under revision 9 cites A.13 for that arming. Citations of
A.11(a) for a WATCHER re-arm or a CUE-ROUTE reconciliation (checklist G.1) and for an interrupted
effect (SKILL §10's wake order, A.11(a)-(c)) are unchanged in every revision.

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
   pending work separately. The operative sequence is C-pre → D → C-post: a real handoff cycle
   (C) runs BEFORE D as the baseline handoff, and a second real handoff cycle with a DISTINCT id
   runs AFTER D as the post-recovery handoff, both before any agreement sentence. No exchange
   beyond those two cycles is required by this step (revision 10: this replaces the earlier
   wording that read as "D then C" against J's "C first"; the plan records the actual order).

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

## G. Re-entry after force termination (usage cap, crash, kill, host policy; SKILL §11)
A's merged order is the ONLY re-entry order — there is no second list to run after it, and no
step of A executes a resumed effect before A.10's status. After a force termination the numbered
rules below apply AT the A step each names (G.1 at A.7, G.2 at A.6, G.3 at A.8, G.4 at A.9, G.5 =
A.10); where G's historical numbering and A's order differ (G.2 runs before G.1), A's order
governs. A drill's order log must show G.2, G.1, G.3 and G.4 before G.5, and G.5 before A.11's
first effect; publishing one status is not by itself sufficient. Read the ACTIVE protocol version
before anything else; nothing below is authorized by elapsed time.
Every path and command named below is the one a bus of THIS schema prescribes. A bus whose active
version is older keeps its own checkpoint base, handled record and lock commands (A.0 sends you to
that bus's PROTOCOL.md): apply the numbered steps below to ITS surfaces, and never create v2
participant files or run v2 admin commands against it. A pre-v2 bus that carries delegated work
therefore runs G against its own paths rather than skipping G.
Steps 1–4 OBSERVE, checkpoint and PLAN the next safe action. They do not execute watcher
stop/re-arm, worker retry, project publication, intent abandonment or resource-lock release.
Step 5 publishes recovery status before any such resumed action. Execute an eligible plan only
after those checks and the applicable SKILL §10/§11 gates, rechecking current ownership and
generation immediately before the effect. Those effects run only at A.11, in A.11's order.
1. (at A.7) RECONCILE CONTINUATIONS BEFORE RE-ARMING. An arming may have succeeded before its handle was
   recorded, so treat every registry entry AND every gap as unknown: verify each handle with the
   harness itself (task list, automation status, process group), plan retirement of the closed ones and later record
   the actual stop result (`stop-pending` keeps the handle); plan at most ONE eligible watcher
   per bus for this session, re-armed only at A.11(a) after G.5. "No entry" never means "no watcher", and a handle the
   harness shows but no registry names is `unowned_unknown` — neither adopted, re-armed nor stopped; watcher survival after the owning
   session stops is harness- and event-specific; a cue already queued to a dead thread may still be consumed at that
   thread's next turn — reconcile that route before relying on or repeating it (A.7, A.11(a)).
2. (at A.6) INBOX vs HANDLED. Diff `<bus>/inbox/<me>/` against `<bus>/checkpoints/<alias>/handled.json`
   and process every unhandled id OLDEST FIRST, each with the first reply SKILL §5 requires —
   `received` or `blocked` here; a substantive reply that promises or performs resumed work follows
   G.5 — and apply every control notice (cancellation, supersession, changed hashes, ownership,
   lock releases, receipts) to the journal now, reconciled against the live user's current
   instructions, which the checkpoint never overrides.
   Delivery is at-least-once: inspect the task evidence before repeating any effect.
3. (at A.8) UNIT-JOURNAL WALK (`<bus>/checkpoints/<alias>/units/*.json` — the authority for accepted
   work: enumerate it, never a heartbeat line), per unit, latest attempt first, PLANNING only:
   - `closed` / publication `committed` → verify the recorded output hashes against the canonical
     targets; a mismatch is a conflict, not a re-application.
   - running with a matching completion record, or candidate_ready → plan independent binding
     of the record to this attempt/request/input generation, hash verification and freezing of the
     outputs, and validation under the intended module/toolchain/dependency generation. Perform
     that validation only after the pre-effect checks/status below; record validated only after
     it succeeds. A completion record is neither validation nor publication.
   - validated → verify that the recorded validation still applies to these exact bytes and
     dependencies; plan publication with locks, current base-hash recheck and publication intent.
     Do not execute that plan before the ownership and pre-effect recovery-status steps below.
   - `running` WITHOUT a completion record → `effect_unknown`, NOT dead: leave every canonical
     target untouched, check the actual status and the SCOPE of any cessation evidence, and
     retry only on proven non-spawn, or verified cessation within that scope PLUS reconciled
     effects — then as a NEW attempt with a new scratch identity under the same unit id.
   - `planned` (accepted, never launched; `actionability` per SKILL §10) → no launch identity to
     resolve and no effect to reconcile; it is queued whether or not any heartbeat line named it,
     and resumed only at A.11(d) after step 5 (= A.10) — as a NEW attempt if its inputs changed
     (permitted only because attempt 1 was never launched), not at all if cancelled or superseded
     (a late result is recorded, never applied), and never by inference from the heartbeat line.
   - `launch_pending` / `launch_unknown` → resolve the launch identity from actual evidence
     (harness output, process group, the worker's own records) before any relaunch; an
     unresolved launch keeps its capacity reserved, and a changed input hash alone resolves
     nothing, starts no attempt 2 and makes the unit eligible for no cue.
   - publication `not_started` → nothing was published and no canonical target was touched;
     continue from the execution state above.
   - publication `prepared` → the intent is persisted but no canonical byte was written: verify
     every target still carries its expected base hash (a differing hash makes publication
     unresolved; reconcile old/new/third hashes below), then plan either the swap or abandonment
     of the intent and release of the locks, subject to steps 4–5.
   - publication `publishing` / `publication_unknown` → reconcile the old and new hashes of each
     target: old = not published, new = published (finish the record once), a third hash =
     CONFLICT, stop and report. Clear a journaled `unavailable` batch only when the complete
     intended generation and its validation record are both established.
4. (at A.9) LOCKS: plan release or continuation (effect at A.11(b)) only for locks whose `OWNER` matches your alias, your instance and a
   token bundle you hold, and only AFTER step 3 shows no delegated work still using them. Never
   touch a foreign lock: no expiry, no renewal, at most one `lock-escalation` notice past the
   30-minute threshold (SKILL §6), planned here and published with or after step 5 (= A.10). A
   replacement instance inherits no token authority.
5. (= A.10) Publish ONE recovery status with a higher `status-seq`, header `recovered-from: <event>`,
   listing the reconciled units, the unresolved ones with their condition, the locks you hold and
   the foreign ones you are escalating (the step-4 notice goes out with or after this status), and
   your next action — before any resumed effect; A.11 then executes in its fixed order.

## H. Revision-4 scenario drills (scratch bus, before the §9 agreement gate)
Each drill has its OWN scenario checker and hashed evidence packet under `<bus>/checks/<run-id>/`.
`gate.py` checks only the consistency of the later bilateral agreement records: it does not
inspect filesystem hashes, authenticate actors, run drills or prove behavioral predicates — never
feed fake-actor drill fixtures to the real agreement gate. Freeze the immutable drill packet
before the round; no live parent or peer session is killed by any drill. The "side" column records
Codex's OFFERED responsibilities, PENDING COORDINATION: they bind only after the corrected
candidate and the immutable scratch drill packet are frozen and the round is agreed, and they
start no service, release no lock and authorize no production write. NO R1–R5 DRILL HAS RUN YET.

| drill | required cases | side |
|---|---|---|
| R1 first-reply correlation | `accepted`-first with no `received`; `done`-first; a LATE weaker receipt (no state regression); wrong-`task`, wrong-sender and wrong-hash replies (satisfy nothing). `accepted` leaves the work pending where appropriate; no false timeout | Codex owns the scratch requester/waiter checks |
| R2 coalesced cue | two pending requests drained under one cue; publish-DURING-drain; one-of-many receipts; uncertain submission (`dispatch_unknown`); an active parent whose heartbeat reads `waiting`. Lifecycle recorded once, `observed` retired while work continues | Codex receives/drains on the scratch bus and verifies the coalescer records; Claude owns its native queue caller. A fake cue checks state logic only — an activation claim needs a separately observed real route |
| R3 unit recovery | deterministic scratch simulations of: unbound launch (`launch_unknown`), absent completion record, stale completion record, candidate validation, mid-publication, post-swap/pre-receipt. Unknown attempts are PRESERVED, unsafe replay REJECTED, production targets untouched; scratch publication fixtures retain their observed old/new state, and a new attempt requires the accepted retry gates | Codex owns the simulations. An optional stop of a specifically owned scratch child needs actual stop and cessation evidence and proves only that scope; no live parent or Claude session is killed, and a native interrupt acknowledgment is never proof that every subprocess stopped |
| R4 escalation threshold | a scratch sentinel aged past 30 minutes with the actor status kept UNKNOWN initially (otherwise the test misses the dangerous inference): exactly ONE notice, no takeover, no expiry, no renewal; same-owner release follows reconciliation, never the threshold | Codex ages the sentinel and verifies the single notice |
| R5 typed packet | the frozen project schema applied to SCRATCH ledgers only: all six correction decisions, duplicate keys, unknown schema or tags, stale item/base/input digests, cross-map conflicts, and an applied-effect record with absent or mismatched evidence. An invalid packet has NO binding effect | Codex independently validates/applies and both sides compare outputs |

**Native children after the parent ends: UNVERIFIED.** Active-parent parallel execution is
observed for Codex; survival and re-cue after a final turn or force termination are not
established, and ONE peer-reported quota force-termination (2026-09-14T10:53Z) is the single
source for Claude Code children dying with the session — not a general capability claim. This
revision therefore treats that
route as unsupported and keeps the ACTIVE-PARENT default (SKILL §7, §10); no whole-session
termination experiment is required to finalize the design.
**These drills do not replace the §9 gate.** The real handoff cycle (C) and the joint recovery
drill (D) remain required before any agreement sentence, together with the exact-byte and
evidence bindings of SKILL §9.

**Revision-5 scenario drills** (scratch bus; deterministic simulations described as simulations: no
live session is cued, killed or compacted; a heartbeat fixture proves state logic only, never an
activation capability; every result is a deterministic simulated trace check, never proof of a real
harness effect or of authenticity). Same evidence discipline and `gate.py` limits as above. Roles
(the drill packet): Codex authors and runs the frozen successor runner and checker on the scratch bus and
freezes the evidence; Claude reviews the frozen executables' CODE (a hash-only receipt is
insufficient), re-runs the checker read-only to its OWN output path, and supplies MANDATORY
adversarial negative cases with expected failure signatures; agreement to a role is not permission
to start a particular packet.

| drill | required cases |
|---|---|
| R6 accepted-unstarted units (SKILL §5, §6, §7, §10; A.3/A.6/A.8/A.11(d); G.3) | (a) a turn ends with accepted actionable units and NO new request: journal current with `actionability`, heartbeat first line `idle`, `idle-with-queue:` line present, status names the queue, unit files unchanged; (b) a BLOCKED unit: the line may name it, no cue is eligible, no cue loop across repeated wakes; (c) native state UNKNOWN or busy, or no native fixture, with the line present: no cue, and no decision cites the heartbeat as idleness evidence; (d) native-idle evidence present + actionable unit: exactly ONE coalesced cue bound to the recorded unit/attempt/input generation, intent before and result after, `observed` ONLY on target-origin evidence bound to the covered set and generation — an unrelated status, a registration-only heartbeat rewrite (`hello`) and a wrong-generation record are NEGATIVE evidence that retire nothing; a request arriving during the drain is recorded as uncovered and PENDING — no further cue without a renewed, separately recorded native-idle observation bound to the new intent (a busy or unknown observation, or none, yields no intent); every covered unit and request id needs its own declared drain outcome (a one-of-many receipt establishes nothing for the rest); cue observed ≠ work completed; a `dispatch_unknown` cue reconciled from target evidence and a late duplicate a no-op; (e) control before queue at re-entry, A's merged order logged step by step: a SUPERSEDED unit recorded and not revived; a CANCELLED unit (correlated, from the requester's alias) with a LATE result that is recorded and never applied; a changed input reopening a never-launched unit as attempt 2 with attempt 1 preserved and unaffected units untouched; a `launch_unknown` unit that stays unknown — no attempt 2, no cue, no effect; the old actionable queue resumed after the single recovery status and ahead of a newly injected long job; (f) freshness by the NEWEST valid observation under a deterministic clock: recent, old-but-newer-message (still stale), old-with-recent-message, absent, boundary in/out, mismatched instance — typed `stale`, `dead` always false, exactly one inquiry when a dependency is pending and zero otherwise, no takeover, no lock action, no cue; (g) parser check: a three-line heartbeat with `idle` on the first line passes the existing first-line reader unchanged, and the unchanged revision-4 suites run from a scratch copy under frozen invocations; (h) JOURNAL AUTHORITY: planned units with no queue line, a line stripped by an actual `hello` before the queue step, and a line naming a unit the journal lacks — the queue is enumerated from the journal in every case, the stray name is reported, nothing is fabricated |
| R7 continuity contract (checklist I; A's merged order with G's rules at its steps) | the registry INDEX (the checkpoint), the registry CONTENTS and a labelled SIMULATED native handle list as separate hashed files; every item I.1 lists, frozen by hash before a SIMULATED compaction/halt; a fresh process with declared argv, cwd and environment runs A from those files only (no memory), recording the files it consulted: unit queue (from the journal), handled ids, armed-handle registry, pending offers and `status-seq` recovered, ONE recovery status with a higher seq, its lock continued or released only at A.11(b) after A.10, no duplicate re-arm of an alive handle; negative sub-runs — absent index, absent entry while the native list shows the handle, stop-pending/unknown — preserve uncertainty (no re-arm, no invented stop, no fabricated entry) and PASS when the gap is reported; the positive completeness predicate FAILS on a checkpoint missing an item, and the frozen checkpoint snapshot stays byte-identical |

## I. Session continuity across compaction and halts (cross-harness contract; documentation only)
This checklist installs nothing: no hook, service, scheduler or lock action. It states what MUST be
on disk before your context is compacted or your session halts, what re-entry does whatever the
harness, and which per-harness routes have actually been OBSERVED. Hooks are observations about one
harness: none is assumed to fire on a crash, kill or usage-cap failure, none promises that children,
watchers or schedules survive, and none replaces the durable-checkpoint rule.
1. BEFORE any compaction or halt — which means continuously, at every unit checkpoint, because a
   halt is not announced: (a) the durable checkpoint file(s) under `<bus>/checkpoints/<alias>/` (or
   the project re-entry ledger your checkpoint names), current; (b) `handled.json` current and the
   inbox archived to `done/` for everything it lists; (c) the armed-continuation registry (A.7) with
   every handle you hold; (d) pending offers and requests with their ids, deadlines, input hashes and
   recorded defaults; (e) your last published `status-seq`; (f) held locks with their token-bundle
   paths; (g) accepted-unstarted units in the journal — the authority — and, as a hint only, the
   heartbeat `idle-with-queue:` line (SKILL §6, §10); (h) the heartbeat itself. (i) the latest quota
   observation record with its original observed_at (`references/QUOTA.md` §1); (j) the
   recovery-package pointer (QUOTA §5) when a package exists; (k) the context record with its
   `resume_risk` and, once decided, the pause disposition and the compaction request (QUOTA §4). A
   planned compaction or turn end also publishes the §5 status beforehand — under `pause-disposition:
   compact-first` that status precedes the compaction REQUEST, and the compaction itself is the
   harness's or the user's act, never this checklist's.
2. ON RE-ENTRY, regardless of harness: checklist A — one merged order in which the preserved queue,
   enumerated from the journal, is resumed only as effect A.11(d) after intake, control, the
   unit-journal walk and the single recovery status; after a force termination G's rules apply at
   the steps A marks. A harness-injected summary is a hint: the on-disk checkpoint is the state of
   record, and where the two disagree the checkpoint wins — but neither overrides the live user's
   current instructions or a control notice received since.
3. ROUTES as OBSERVED on a bus of this schema, recorded per participant (the paths and command text of a route live in that participant's records and the project's own configuration; the host layouts observed so far, and how a fresh session locates a target's thread id, are catalogued in `references/HOST_ROUTES.md`, which describes and never activates):

| harness | route | status and evidence |
|---|---|---|
| Claude Code | a `PreCompact` hook (matchers `auto` and `manual`) that stamps the project re-entry ledger with the compaction time, session and transcript path and appends a capped `compactions[]` entry to the session's bus checkpoint; a `SessionStart` hook (matcher `compact`) that prints a re-entry instruction ("run RECOVERY A first") and the bounded CURRENT section of that ledger into the fresh context; both configured as observational, never-blocking commands in the harness project directory's `.claude/settings.json` (here one level above the coordination root) | `PreCompact`: OBSERVED — two `compactions[]` entries written by the hook (2026-09-15T02:07:30Z and 04:21:57Z) in the session's checkpoint. `SessionStart[compact]`: CONFIGURED; its firing is visible only in the session transcript, so it is recorded as reported, not bus-observed. No delivery of either hook on a crash, kill or usage cap is guaranteed, observed or relied on. The usage-cap incident of 2026-09-15 (~05:1xZ–05:50Z) is that session's REPORTED observation, not a bus-observed fact: the session survived, in-flight workers of one workflow were reported lost (no separate cessation record exists), and an hourly in-session schedule served as the resume cue — an observation, not a route of this table. Hook paths, settings and event provenance are frozen by hash in the candidate's DELTA inputs. Planned compaction: OBSERVED 2026-09-18T15:43:53Z–15:5xZ — status 20260918T154353Z-claude3-pre-compaction-status-38e22090 and recovery package gen7 published first, a user-run manual compaction, 895198 → 100554 of 1 000 000 tokens, same alias/instance re-entered per A; no agent-triggerable compaction route observed; a persistent inbox watcher survived the compaction; a session-scoped one-shot resume timer surviving a compaction is NOT observed either way; the compaction REQUEST reaches the user by the harness's push notification and sidebar unread flag (both tested once 2026-09-18T16:1xZ) and by the turn-end report line (`checks/rev8/claude/OBSERVATIONS.json`), where a submission result such as "Mobile push requested" is submission evidence only, never evidence that the user saw it |
| Codex | native automatic context compaction of the same task; no configurable compaction-hook mechanism recorded for that session; continuity = durable checkpointing + A on the actual resumed turn | OBSERVED — a status carrying `recovered-from: automatic-context-compaction` (2026-09-15T05:26:46Z) with its re-entry record; not generalized to every runtime of that harness. Cache and compaction: 2026-09-18T16:06:28Z — TTL unavailable, a per-request cache-hit counter observed but no retention guarantee, one compaction event 2026-09-18T01:42:50Z with trigger unknown, no manual or agent-triggerable compaction route verified, timer survival unavailable (`checks/rev8/codex/OBSERVATIONS.json`) |
| any other harness | durable checkpoint only (item 1) + A on whatever re-entry the harness offers | UNVERIFIED until a participant records it |

4. FUTURE optional adapter, DESCRIBED here and NOT part of this revision: `admin.py install-hooks
   --harness <name> --scope user|project` would install a harness's hook pair idempotently from
   templates that read the snapshot path from the bus checkpoint (no project hard-coding) and report
   the settings entries written. That is a separate revision with its own scratch drill and
   activation record; nothing in this checklist installs or presumes it.

## J. Quota drill (scratch bus; before the §9 gate of any revision that changes `references/QUOTA.md`)
Deterministic SIMULATED trace cases on a scratch bus; each states its inputs (recorded
sample/episode fixtures), the expected transition under QUOTA §4's state machine, and the
expected artifacts (recovery-package generation per QUOTA §5, status headers per SKILL §5's
`quota-state`/`quota-window`/`resets-at`, and continuation-registry entries per QUOTA §8/design
§6.6).
1. Cap/crash injected immediately before each final-package write (`prepare` and `quota-paused`
   alike): inputs = a fixture forcing process death at that exact write; expected transition =
   nothing recorded past `prepare`/`quota-paused`; expected artifacts = no NEW completed package
   generation — the scope is the INTERRUPTED attempt, so any prior complete generation and its
   committed pointer survive and the ordinary journal is retained, and no new generation counts as
   complete without its own verification; RECOVERY A recovers fully from that journal alone.
2. Two binding windows (5-hour and weekly-all-models) with different horizons and correctly
   computed per-window burn/units (QUOTA §3): expected transition = the FORECAST follows the
   SHORTEST valid horizon only, never a mixed-window figure, while the BAND decision stays separate
   — a fresh LOW binding window still blocks admission when its own burn is unknown, and differing
   horizons alone force no transition while every admission condition holds; expected artifacts =
   one `prepare` or `quota-paused` status naming the deciding window_id and the blocking-window set
   (QUOTA §4).
3. Missing/stale samples, a negative delta, and a `resets_at` timestamp passing with no fresh
   observed capacity, each run from THREE prior states: expected transition = forecast `unknown` in
   every case; from `observe` with nothing blocking the state stays `observe` (no fabricated
   trend); from an existing
   `quota-paused` the pause STAYS — missing or stale trend evidence never returns a pause to
   `observe`; and with fresh remaining LOW plus an invalid trend (4 % → 5 %) that window still
   blocks admission; expected artifacts BY INITIAL STATE, one blanket oracle being wrong for at
   least one branch: from `observe` with nothing blocking, NONE — no package write, no timer; from
   an existing unchanged pause, none NEW — no second package generation, no re-armed timer, the
   open generation untouched; from the fresh-LOW branch, which is a NEW pause, the ORDINARY flow of
   QUOTA §4/§5 — a package generation and a `quota-paused` status, plus the single U2 timer where
   that window's reset is known, within 5 h and an authorized route exists, and U3's recorded
   no-timer disposition where it is not.
4. A same-account successor session samples immediately after a prior pause: expected transition
   = still capped if the fresh sample shows LOW, `resume` only on genuinely new capacity evidence;
   expected artifacts = the successor's own observation record, no inherited `resume` status.
5. A child holds a lock, live or unknown, at the moment `quota-paused` triggers: expected
   transition = `quota-paused` proceeds unaffected; expected artifacts = the lock left untouched
   (never released as a side effect of pausing), the child left classified per checklist A.4/A.7.
6. A cancellation control message arrives while `prepare` is active: expected transition =
   the cancelled unit recorded and not revived, `prepare` continues independently; expected
   artifacts = the cancelled/tombstone state and any unresolved child or effect record KEPT (never
   erased from recovery), no package entry for the cancelled unit, and a reply only where that
   control message's own type/contract requires one — an INFORMATIONAL cancellation notice gets no
   automatic acknowledgment (SKILL §5).
7. Partial package publication followed by a duplicate preparation attempt in the same PAUSE
   GENERATION: expected transition = no second `prepare` transition for that pause generation
   (QUOTA §4, "one preparation per pause generation"); expected artifacts = exactly ONE accepted
   complete package generation, named by the pointer — immutable earlier generations, a staged
   partial successor and the committed pointer may coexist on disk, so the test is one selected
   complete generation with no duplicate logical application, the partial bytes rejected or
   reconciled, not "exactly one directory".
8. Compaction of the session versus an actual replacement instance: expected transition =
   compaction keeps the SAME alias/instance (checklist A.2), a replacement gets a NEW alias
   inheriting no token authority (QUOTA §5); expected artifacts = the package pointer resolved
   correctly for whichever identity actually resumes.
9. `quota-paused` holds across several turn boundaries with no capacity change: expected
   transition = no state change, no cue; expected artifacts = no repeated cueing of the paused
   task (QUOTA §6, "no cue loop while paused").
10. A 5-hour-window pause (QUOTA §4/§8, U2) with its resume timer firing while a fresh sample
    shows UNCHANGED capacity: expected transition = re-package once, stay `quota-paused`;
    expected artifacts = no second timer armed off the same evidence ("no timer loop").
11. A binding weekly-window pause with more than 5 h to reset (QUOTA §4/§8, U3): expected
    transition = `quota-paused` with `resets-at`, no timer, turn ends; expected artifacts = NO
    resume timer registry entry at all.
12. Two blocking windows both reset within 5 h, at different times: expected transition =
    `quota-paused` with one resume check; expected artifacts = the timer armed at the LATEST of
    the two reset times plus margin, one registry entry (intent → handle), never the earliest.
13. A blocking window's reset is unknown WHILE another blocking window's reset is known and near:
    expected transition = no aggregate resume timer is scheduled at all (QUOTA §8, the whole
    blocker set is tested); expected artifacts = no guessed timer entry, and no partial timer armed
    off the known reset alone.
14. The user cancels an armed resume timer: expected transition = the pause continues under the
    user's own choice (fresh account/session), never auto-retried, and a later CHANGED quota
    observation does not by itself authorize a replacement timer for that pause generation;
    expected artifacts = the registry entry retired with its actual stop result (an uncertain stop
    stays `stop-pending`), a late callback arriving after cancellation recorded and not acted on,
    and any genuinely new user-authorized scope recorded as distinct from the cancelled one.
15. A child session runs under a model-specific window while its parent runs a different model:
    expected transition = the child's own model-specific window binds ITS work only, the parent's
    window governs the parent; expected artifacts = separate observation records per QUOTA §7,
    neither state contaminating the other. 
16. A new reset epoch is observed for the deciding window while the WEEKLY window is still at or
    below LOW (> 5 h to reset): expected transition = NO `resume` (admission evaluates every
    current binding blocker); expected artifacts = the pause generation stays open, no timer
    re-armed off the same evidence.
17. An in-epoch `resume` (horizon again exceeds the deferred unit) is followed later in the SAME
    reset epoch by a LOW sample: expected transition = a NEW pause generation (`prepare` →
    `quota-paused`); expected artifacts = a second package generation, a second `quota-paused`
    status, one live timer at most.
18. A forecast-driven pause from `observe` (horizon shorter than the next unit) on a window whose
    reset lies within 5 h: expected transition = `quota-paused` recorded as forecast-driven and
    treated as entering LOW for §8; expected artifacts = package, status, ONE timer at the latest
    blocking reset + margin (U2).
19. Two samples that are not comparable — 80 % under one `pool`, then 40 % under another ten
    minutes later, and the same pair run again as a changed `source`: expected transition = the
    trend is INVALID (QUOTA §3), so no horizon exists to compare with any unit's duration and none
    may be fabricated from the pair, while 40 % alone is above WARN, so the state stays `observe`;
    expected artifacts = none at all — no forecast record, no preparation, no package, no
    `quota-paused` status, no timer.
20. An active U2 pause (short window 9 %, reset in 4 h, weekly 80 % resetting in 7 days) whose
    timer is armed, and then the weekly window samples 9 %: expected transition = the weekly window
    JOINS the blocking-window set and the pause continues in the SAME generation — no second
    `prepare` or `quota-paused` transition is recorded; expected artifacts = timer disposition
    RECOMPUTED with the set, so the now-ineligible timer (a blocking weekly reset more than 5 h
    away is U3, not U2) is retired with its actual stop result — an uncertain stop staying
    `stop-pending` — and no replacement timer is armed.
21. In that same pause, a weekly window falling 80 % → 40 % over ten minutes, a ten-minute horizon
    against the sixty-minute unit already deferred: expected transition = the newly valid FORECAST
    blocker is evaluated WHILE PAUSED, not ignored because the pause began elsewhere, and joins the
    blocking-window set with its own recorded resume condition, still in the same generation;
    expected artifacts = the pause record's blocking-window set and resume condition updated, timer
    disposition recomputed as in case 20, and no duplicate pause transition.
22. A U2 pause (short window LOW, reset in 2 h) decided with the context record at 90 % of the
    window, a known cache anchor and a stated 1-hour cache TTL: expected transition = `prepare`
    records `pause-disposition: compact-first` (`resume_risk` cache-expired by age at resume,
    `tokens_used` ≥ CTX), then `quota-paused`; expected artifacts = package, the status carrying
    the disposition, ONE compaction-request record with outcome `unknown` carrying the anchor,
    the ADVISORY `compact-by` = anchor + TTL, and the route named or `unavailable` (a modeled
    notification, never a modeled compaction), the U2 timer armed at reset + margin exactly as
    without the disposition, and no keep-warm entry.
23. The same pause with the reset 40 min away (shorter than the TTL): expected transition =
    `same-session` (`resume_risk` cache-may-hold — no hit assumed); expected artifacts = no
    request, timer unchanged.
23b. The same pause with a known cache anchor 40 min before the pause, a 60-min TTL and the
    reset 30 min away: expected transition = `prepare` records `pause-disposition:
    compact-first` (`resume_risk` cache-expired — age at resume 70 min ≥ the 60-min TTL,
    computed from the anchor, never from the remaining 30-min pause alone); expected artifacts =
    as case 22, keyed to this anchor and TTL.
24. The same pause with the context record at 20 % of the window: expected transition =
    `same-session`; expected artifacts = none beyond revision 7's.
25. Case 22's timer fires with fresh samples showing capacity and NO compaction observed:
    expected transition = `resume` (the aggregate test decides, the disposition never does);
    expected artifacts = the request outcome `not observed`, the resumed turn's input volume
    `unmeasured` (no predicted cost written as an observation), no second timer, no second
    request, no delayed resumed turn.
26. A U3 pause (weekly window LOW, > 5 h to reset) with the context record at 90 % and a stated
    1-hour cache TTL: expected transition = the resume estimate is computed from the known
    weekly reset plus the §8 margin EVEN THOUGH U3 arms no timer, giving `resume_risk`
    cache-expired, so `compact-first` is recorded at `prepare`, then `quota-paused` with no
    timer (U3 unchanged); expected artifacts = the request record made on that estimate, no
    timer, the turn ends; `successor` appears only with a user decision record.
27. Case 22 with the cache TTL `unknown`: expected transition = `resume_risk` unknown →
    `same-session`, nothing requested (no fabricated classification); expected artifacts = none
    beyond revision 7's.
28. Case 22 where a compaction is observed AFTER the timer was armed, then re-entry (RECOVERY A.7)
    finds the timer handle (a) verified lost, (b) unverifiable, (c) verified lost with the
    original firing time ELAPSED by the time the arming step (A.13) runs, (d) verified lost with a
    user cancellation for this generation, (e) verified lost with the aggregate admission test now
    PASSING: expected transition = the pause generation continues, no new pause transition, EXCEPT
    (e) where it closes to `resume`; expected artifacts = (a) A.7 RECORDS the registry entry
    retired with the stop result `lost at compaction` and PLANS ONE replacement, EXECUTED at A.13
    only because the route, the target lifecycle, the pause and work generation and the failing
    admission test all still hold and the firing time is still future; (b) the entry marked
    `unknown`, no duplicate armed, the wake routes of SKILL §7 recorded as the resume path; (c)
    A.13 takes the ordinary fresh-admission path instead — new samples, §4, U2/U3 re-decided —
    never a re-arm at the elapsed timestamp; (d) A.13 arms no replacement at all, the cancellation
    standing; (e) A.13 arms no replacement, the pause closes to `resume` on the passing test; in
    every branch the request outcome is recorded `observed` with before/after volumes, survival
    never assumed, and `unknown` is never duplicated.
29. A user decision record selecting `successor` arrives during a pause: expected transition =
    disposition `successor` published in a new status; expected artifacts = no launch, no
    alias/token/lock inheritance (the successor is a NEW alias under the ordinary SKILL §5
    handoff gates), quota state and the blocking-window set unchanged, timer disposition
    unchanged.
30. While paused: (i) a turn whose only purpose is cache retention: expected transition = none;
    expected artifacts = flagged FORBIDDEN, no timer or admission change; (ii) a cancellation, a
    receipt and a recovery-information notice: expected transition = none; expected artifacts =
    delivered, NOT flagged.
31. The context record at 20 % of the window at `prepare`/pause, then a 90 % measurement while
    still paused: expected transition = the disposition first becomes `compact-first` LATE, at
    that later aggregate update; expected artifacts = an updated checkpoint and package, a NEW
    status (the next `status-seq`) carrying the disposition and preceding ONE compaction-request
    record, no new pause transition, the timer untouched, and the earlier `same-session` status
    unchanged.
32. After an observed compaction 235930 → 60000 tokens (§1), a later `resume` closes that
    generation, then a NEW LOW pause generation opens with no further context measurement:
    expected transition = the second generation decides its disposition on the post-compaction
    volume (60000), giving `same-session`; expected artifacts = no compaction-request record for
    the second generation; the 235930 before-volume remains present only in the first
    generation's request outcome, never as the latest eligible context.

Wording rule: every case above is a simulated trace check — it verifies neither native hard-stop
activation nor an external supervisor; no real quota is exhausted. Its "expected artifacts" are the
MODELED records such a trace is entitled to assert — the package, lock, cue, timer and
compaction-request flags the model itself writes — and never a validated durable artifact or a
native gate: a modeled package
flag is not QUOTA §5's durable verification of a published generation, a modeled cue flag is not
observed native idleness on a verified route, and a passing case establishes neither of those, nor
hard-stop survival. State a case's claim no wider than that, or add the corresponding modeled-record
check WITH its negative case (the record absent, or present but unverified) and claim only what that
check covers. A mismatch between two implementations of a case is INVESTIGATED, never attributed in
advance: it may be a runner, an oracle or a rule-text defect. Freeze runner, checker, fixtures and
expected outcomes by hash before any review or replay; a runner's own PASS string, or expected
fields copied into "produced" artifacts, is not independent validation. Required companions,
unchanged from revision 6: the real bounded handoff cycle (checklist C) and the controlled joint
recovery drill (checklist D), both before any §9 agreement sentence.

## K. Continuation-snapshot drill (isolated scratch root; after this revision's text and its exact plan are frozen, after checklist C's real handoff cycle, checklist D's controlled joint recovery drill and the FULL checklist J regression, and before the §9 agreement gate)
Isolated scratch root `/private/tmp/agents_bus_scratch_rev9-20260918`, with `bus/` and a
disposable `work/`. This is a PROPOSED LOCATION, not a registration and not a route activation;
the project's primary legacy bus is left untouched, and nothing in K writes to it.
DIVISION OF LABOUR: Claude exercises its ACTUAL watcher, its own harmless, finite, owned fake
worker, and the cue DUTY of H7 (SKILL §7) on the scratch bus, recording real running and terminal
observations; Codex exercises the cue-only / no-watcher branch, its native worker observations
(`list_agents`, child messages, bounded waits, shell session handles), the TARGET side of the cue
case, and independent evidence checks. BOTH sides check the state table independently and compare
outputs.
CASES:
1. a JUSTIFIED timer, decided against the three-justification ADMISSION PREDICATE of SKILL §7 and
   `references/QUOTA.md` §8 as the oracle: expected outcome = the entry names exactly one of
   `cap-near`, `resume-after-pause` or `poll-external` with its evidence, its owner, target,
   verified route and its work and pause generations, and the independent gates (no self-wakeup
   over owned work; route authorization) are checked separately. `cap-near` is decided
   DIRECTIONALLY against QUOTA §4, which is expressed in REMAINING capacity: a fresh
   binding-window observation of 20 % remaining against the default 25 % WARN threshold ADMITS,
   and so does a valid §3 forecast blocker on that window; 80 % remaining with NO valid forecast DOES
   NOT — above WARN it is `observe`, and an entry claiming `cap-near` on it is INADMISSIBLE. Oracle:
   20 % / no forecast → numeric purpose satisfied; 80 % / no forecast → not satisfied; 80 % / valid
   forecast → forecast purpose satisfied (purpose-predicate results only; every separate arming gate
   is retained). Silence authorizes no
   retry, no takeover and no lock release.
2. an UNJUSTIFIED timer — a routine fallback, keep-alive or 'in case' wakeup: expected outcome =
   INADMISSIBLE under the same predicate, planned for retirement at A.7 and performed as an
   authorized stop in the effect phase, a failed stop staying `stop-pending` with its handle
   preserved. The case uses an explicitly LABELLED INVALID SNAPSHOT FIXTURE plus a DRY-RUN stop
   plan; no purposeless real timer is ever armed into live work. Silence authorizes no retry, no
   takeover and no lock release.
3. a stale-but-running worker: expected outcome = an old transcript and an exceeded expected
   window are `unknown`, a bounded investigation is PLANNED, and nothing is retired or retried.
   Silence authorizes no retry, no takeover and no lock release.
4. an unavailable handle (`not found`, no completion record): expected outcome = `unknown` with
   its source and scope recorded, never a cessation record. Silence authorizes no retry, no
   takeover and no lock release.
5. a terminal worker with unresolved descendants or effects: expected outcome = protected owned
   work for the no-self-wakeup rule, its descendants and effects reconciled before any eligible
   arming. Silence authorizes no retry, no takeover and no lock release.
6. a completed candidate needing VALIDATION, not relaunch: expected outcome = `candidate_ready`
   reconciled by hash under the SKILL §10/§11 gates, no fresh attempt. Silence authorizes no
   retry, no takeover and no lock release.
7. duplicate or unknown arming: expected outcome = the `unknown` or `stop-pending` handle is
   RECONCILED, never duplicated by a fresh arming. Silence authorizes no retry, no takeover and no
   lock release.
8. a user cancellation plus a superseded generation: expected outcome = no replacement armed, the
   cancellation standing for that pause generation and the superseded generation never revived by
   a late callback. Silence authorizes no retry, no takeover and no lock release.
9. an early wake followed by a new worker launch: expected outcome = the earlier idle timer is
   reconciled and CANCELLED before the protected work resumes. Silence authorizes no retry, no
   takeover and no lock release.
10. a pause with draining workers: expected outcome = a `quota-paused` record legitimately
    retaining draining, unknown, interrupted or completed worker entries, recorded explicitly; no
    worker killed and no entry erased to make the snapshot look healthy. Silence authorizes no
    retry, no takeover and no lock release.
11. a new control arriving between preflight and arming: expected outcome = the timer is
    RECONCILED and the sequence returns to the appropriate earlier step instead of arming. Silence
    authorizes no retry, no takeover and no lock release.
12. a REQUEST TO A CUE-ONLY PEER: a reply-required request published to a target whose registered
    activation is cue-only, exercising the DUTY to EVALUATE SKILL §7's eligible-cue procedure, the
    ONE coalesced cue with its intent / actual-result / observed-drain / retirement records, the
    outstanding-attempt limit scoped per caller and target instance, and the
    bus-only-inquiry-is-not-a-cue rule (SKILL §6), with these branches: (12a) a historical
    heartbeat or a finished bounded wait while the native target is STILL ACTIVE or its lifecycle
    is UNKNOWN — duty recorded as pending with its deferral reason, NO dispatch; (12b) a newly
    supplied REPLY OR RESULT that unblocks already-accepted work — one coalesced cue under the
    exact unit/attempt/request/input generation binding; (12c) a CONFIRMED dispatch without an
    observed drain versus a GENUINELY UNKNOWN dispatch — different facts, different dispositions,
    neither retired by silence; (12d) a generic receipt or `task_started` versus BOUND DRAIN
    evidence — only the latter retires the cue; (12e) an old attempt RETIRED while a NEW UNCOVERED
    id arrives — the uncovered id is rechecked and not stranded; (12f) a CANCELLED or SUPERSEDED
    accepted-work generation — no cue, and no late callback revives it; (12g) a recovery-status
    cue OWED before its permitted effect phase — recorded at A.7, or, where A.7 had NONE, first
    recorded by the A.10 status — dispatched in either case only at A.11(c-bis), never by
    publishing A.10 and never inside A.13; (12h) a route EXPERIMENT not yet registered as
    `verified` — no duty, no cue, user-relay instead; plus no verified route → no duty,
    user-relay; and exit 0 with no target-origin evidence → a CONFIRMED DISPATCH AWAITING DRAIN,
    which stays confirmed and unobserved until bound target-origin drain evidence arrives, a
    SEPARATE OUTCOME from a GENUINELY UNKNOWN dispatch (`dispatch_unknown`), which is reconciled
    before any repeat — the absence of target-origin evidence never reclassifies a recorded
    dispatch, and neither outcome is retried or retired from silence. The case ASSERTS THE EXACT
    CUE BYTES against SKILL §7's template and the no-extra-path rule. These are BOUNDED simulated
    cases for existing obligations, not permission for live cue experiments, and none of them
    authorizes a retry, a takeover or a lock release from silence.
INTERRUPT CASE: an interruption marker injected into a COPIED transcript tests the RECOVERY
DECISION only — it is not evidence of native interruption delivery and not evidence of child
survival. The verdict text must preserve that distinction verbatim.
EVIDENCE: inputs, NATIVE results, the decisions taken, before/after registry snapshots, and
outcomes checked INDEPENDENTLY by the other side — never author-written booleans alone. Any
controlled stop stays inside its frozen ownership plan.
GATES: SKILL §9, RECOVERY C, RECOVERY D and RECOVERY J are RETAINED unchanged; K supplements them
and replaces none.
