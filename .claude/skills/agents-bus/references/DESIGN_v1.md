# agents-bus skill design prototype, version 1

This is a design to exercise, not a skill. Do not create or install SKILL.md
until the release gate below is satisfied by the actual Codex and Claude sessions.
The scope is coordination of work already authorized by the user, including
compaction, connection loss and a peer that never replies. It does not authorize
commits, pushes, new research, live-session cloning, or permission changes.

## Existing foundation

Keep the immutable file bus, token-owned directory locks, evidence, explicit
handoff acceptance, and delivery/activation distinction of PROTOCOL.md v2.1.
For the tested design, pin a copy of that baseline and its hash in the manifest.
The following changes resolve gaps in v2.1 and specify recovery and skill release.
Version changes require a new manifest; old approvals never apply to new bytes.

## Publication, receipt and truthful status

- Every message has a unique id, from, to, sender-session, created-at, type and
  self-contained body. Correlated work also carries task, re, input/design hash,
  and whether a reply is required. Use UTC timestamps. Put the unique id in its
  final filename. Publish complete bytes atomically without overwriting an
  existing id. Same-id/same-content retries are idempotent; changed content with
  the same id is a conflict. An immutable message store plus inbox hardlinks is
  an acceptable implementation if interrupted delivery can be repaired safely.
- Match a reply by request/task id and expected sender. Accept an already-present
  unhandled matching reply: it may have beaten the waiter or arrived during
  compaction. An empty inbox does not mean no outstanding request. Keep handled
  ids durably; never execute an action twice merely because it was redelivered.
- Acknowledgment means receipt; acceptance means the work was accepted; done
  means its completion evidence exists. Informational status and acknowledgments
  do not require acknowledgments of their own. No ping-pong loops.
- Publish status on task acceptance, handoff, significant change, timeout,
  recovery, completion, and before a planned turn end or compaction. Include
  observed-at, pending outbound ids, accepted work, held locks, next action and
  current activation mechanism. A short status may link a durable checkpoint. Give each publisher status
  an increasing sequence and superseded-status id so a late old idle notice
  cannot overwrite a newer waiting status.
- If the relevant scope truly has no pending request, accepted work, or blocked
  obligation, explicitly say **nothing to wait for; nothing to do** and require
  no reply. Otherwise name exactly what is pending. Scope-specific idle notices
  must disclose unrelated outstanding tasks rather than silently closing them.
- Forced compaction, power loss or connection failure may prevent a final notice.
  Status is a last observation, never an availability guarantee or a lock lease.
  Do not claim an always-current inbox can be guaranteed during a crash.

## Bounded silence and recovery

1. Before a request or an effect, persist the logical task/request ids, input
   hashes, intended effect, completed-effect evidence, locks owned, what response
   is expected, and the next safe action. This is a checkpoint in the bus's tmp
   workspace, not either agent's private transcript or memory.
2. Requests specify receipt deadline, any work deadline, and the authorized
   timeout default. Suggested ordinary receipt budget is 120 seconds with one
   availability inquiry at 60 seconds; the sender may state a different budget.
   Each blocking tool call remains within its harness limits. An acknowledged
   long-running task uses its agreed work deadline/status, not the receipt timer.
3. At most one availability inquiry and one unreachable-status notice per silent
   episode. Retries keep the logical request id; new transport ids, if needed,
   explicitly supersede the earlier delivery. Never silently duplicate effects.
4. On budget exhaustion, mark **peer-unreachable / availability unknown** and
   checkpoint the dependency. This is not cancellation or rejection. Release
   only locks you own after stopping your own relevant work. Do not touch the
   peer's locks or files. Continue independent authorized work or prepare an
   isolated proposal; stop polling this episode indefinitely. If progress needs
   the peer, report the exact blocked dependency and recovery path to the user.
5. The user asking to await agreement means the agreement remains pending,
   even when active waiting is suspended. No response can never satisfy the
   skill-release gate. A native scheduler may revisit a pending checkpoint when
   the user has requested one; a shell process alone does not restart an ended
   Codex turn. Do not create background services or retry storms implicitly.
6. On startup or after compaction/error, first read the active design/protocol,
   own inbox and handled-id record, checkpoint, and actual lock directories.
   Publish a recovery status before resuming effects. Reconcile completed
   artifacts and hashes; validate any queued/late reply against the still-pending
   generation. A matching late reply may finish that request exactly once.
   Replies for cancelled, superseded or changed-hash work are recorded but do
   not revive it. Ask for current evidence if the reply is insufficient.
7. A different session id is a replacement participant, not automatically the
   former owner's lock holder. An OWNER-less directory remains occupied. Age,
   missing status and a peer's silence never prove its work stopped. Reclaiming
   its resources requires explicit release or verified cessation and authorized
   recovery. Do not run a second process on a live transcript to get a response.

## Exclusion and the shared board

The lock directory is authoritative for exclusion. STATE.md is informational.
Every read-modify-write of the whole STATE.md, even an edit only to one's own
section, takes the brief state lock and rereads the current file before writing.
Acquire multiple resource keys in fixed order; release acquired keys on failure.
Do not hold a shared resource lock while waiting for a peer that might need it.
All users of the same build outputs follow the same build-writer exclusion.

## Actual peer exercise before signoff

Use a named drill and its own directory under tmp/agents_bus/prototype/runs/.
No live process is killed and no real project/resource lock is broken.

1. The actual peer accepts the drill and both read its self-contained packet.
2. The peer deliberately withholds a response to one clearly labeled drill
   request. The sender's short, explicitly agreed drill budget expires. The
   sender records unreachable status, keeps the request pending, and confirms
   a sentinel representing a peer-owned lock is untouched. No skill approval.
3. The sender publishes a recovery packet containing all required context.
   The actual peer reconciles that packet, replies to the original logical
   request and reports one harmless effect in the isolated drill directory.
4. Redeliver the same request id; demonstrate that the completed effect is not
   repeated. A stale-hash approval fixture is rejected by the local gate check.
   Fixtures never impersonate actual peer consent.
5. Close the drill with final status in both inboxes. Record any remaining real
   work separately. Unit checks cover publication races and replies that precede
   the waiter; the peer round trip supplies the activation/recovery observation.

These observations test the protocol under controlled silence. They do not claim
to prove behavior of a real forced compaction, outage, or machine power loss.

## Exact bilateral release gate

Freeze a manifest with the baseline protocol hash, this design hash, helper/test
hashes, successful local checks and the actual peer drill evidence. Both
participants review the same manifest and each publishes an authored agreement:

    yes I agree with the design of this skill

Each agreement identifies its author/session, manifest hash, design hash and
test-run id. Codex must receive Claude's agreement and Claude must receive
Codex's agreement before either authors or installs any SKILL.md. A receipt,
quoted example, simulated peer, old-version approval, or uncorrelated phrase
does not count. A changed design/helper invalidates the release gate until the
changed version is checked and both participants explicitly agree again.

After the gate, choose one skill author and reviewer. Package one concise
canonical agents-bus skill plus only useful tested helpers/references. Keep
project paths/session ids in project-local state, not hardcoded into a global
skill. Respect existing coordination registries instead of overriding their
claims. Review the package against the agreed design, validate it, and mirror
identical content for Codex and Claude. Final packaging handoff says what is
installed, what remains pending, and whether anything needs a reply. No silent
handoff or implied future watcher.
