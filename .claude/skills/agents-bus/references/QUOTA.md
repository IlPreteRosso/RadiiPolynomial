# references/QUOTA.md — quota and context-pressure observations (revision 7)

## 0. What this is / is not
A local observation record and default policy for account-quota and context-pressure signals, read
at checkpoints. It installs nothing (no service, scheduler or helper script) and is never a hard
limit, a capacity guarantee or a completion claim. It does not replace the durable
task/attempt/publication state that is the actual recovery guarantee (RECOVERY A, I.1); it feeds a
best-effort recovery package (§5) while execution is still available. A fresh session never
replenishes a shared account's exhausted quota.

## 1. Observation record
One record per sample: `{source, pool, observed_at, window_id, window_duration, remaining_percent |
"unavailable", resets_at | null, availability note}`. `pool` is a STABLE, NON-SENSITIVE label for
the allowance sampled — never an account identifier or credential; samples are only ever compared
within one source/pool/window (§3). `observed_at` is the ORIGINAL sample time, never the checkpoint
time it is later copied into. A source may expose several named windows at once (short rolling,
all-models weekly, model-specific weekly): record each under its own `window_id`, never collapsed
into one number. UNAVAILABLE ≠ zero ≠ unlimited: a missing window is reported as unavailable, not
assumed exhausted or absent. Context pressure is a SEPARATE record, `{tokens_used, context_window,
compact_threshold | "unknown", cache_ttl | "unknown", cache_anchor | "unknown", resume_risk}`;
totals are never divided by the window to fake a percentage. `cache_ttl` is the harness's STATED
cache lifetime (§7); `cache_anchor` is `{at, kind, source}` — the most recent event the harness
STATES refreshes its prompt cache, a dated observation: Claude Code, the session's last request (a
harness statement); Codex, unavailable. `resume_risk` is computed from the AGE AT RESUME = the
EXPECTED RESUME TIME minus the anchor time, never from the remaining pause alone: `cache-expired`
when that age is at least the TTL, `cache-may-hold` when shorter (no hit guaranteed: key and
eviction stay unobserved), `unknown` when the anchor, the TTL or the resume estimate is unavailable
— a checkpoint time is never substituted for an anchor. `resume_risk` is a LABEL, never rounded or a
predicted cost. The EXPECTED RESUME TIME is the latest blocking reset (§8) plus the §8 margin,
whether or not a timer may be armed (U2 or U3 alike); `unknown` only when no blocking window's reset
is known; a user-selected earlier resume (a successor decision) is a decision record, never an
estimate. `compact-by` = anchor plus TTL on the same basis, ADVISORY only — never a deadline this
policy enforces. An observed compaction with an after-volume REPLACES the latest context measurement
(kind `post-compaction, harness-reported`, with its time); without an after-volume the prior
occupancy is `unavailable` until refreshed, and the before-volume stays in the request outcome as
history only, never the latest eligible context. `tokens_used` is an input VOLUME, never a quota,
cache or monetary cost. Account identifiers, credentials and credit/billing details never appear in
either record.

## 2. Sampling
Record the latest known sample at every checkpoint and turn boundary; this is free (no new fetch).
FETCH a new sample only when the refresh deadline is due, or before starting a consequential long or
uninterruptible unit. Refresh deadline: 10 min default with no reliable trend yet; tighten toward 5
min under pressure (inside a warning band, §4); relax to 30 min only with ample headroom AND stable,
comparable prior samples. These are local policy defaults, not a proven optimal schedule. Per
harness: Codex samples at its own active-turn boundaries only, no timer or background task. Claude
Code samples only through its own already-authorized wake or monitor route (SKILL §7).

## 3. Forecast
Per window, from two samples of the SAME source, `pool` and window in the SAME reset epoch: burn `b
= (r_prev − r_cur) / elapsed_min`; horizon `T = r / b`, computed only for positive, valid `b`. A
changed `pool` label (a switched account, provider or source) INVALIDATES the earlier trend. Use the
shortest valid horizon across windows; never mix one window's remaining percent with another
window's burn rate. Two coarse samples on a shared account yield a WARNING forecast only, never a
bound. Missing data, a stale sample, or zero measured burn all mean "forecast unknown" — not "safe".
A negative delta, or a delta spanning a reset, invalidates the trend for that pair. A `resets_at`
timestamp merely passing restores nothing by itself; capacity is only what the next actual sample
shows.

## 4. Bands and states
| state | trigger | actions | recorded |
|---|---|---|---|
| `observe` | remaining above WARN and no valid forecast blocker (below) | normal sampling (§2) | latest sample |
| `prepare` | WARN band reached: default 25 % of the tightest BINDING window (§8) whose sample is available, or transitionally the forecast branch below | write/refresh the recovery package (§5); reduce speculative concurrency; stop starting NEW delegation; decide the context-aware disposition (below) | transition reason, triggering sample, pause disposition |
| `quota-paused` | LOW band reached: default 10 % of the tightest BINDING window (§8) whose sample is available, or the forecast branch below | accepted actionable work MAY be deferred (explicit SKILL §5/§10 amendment); never a hard limit or a fabricated completion; controls (cancellations, receipts, recovery info) keep being delivered | transition reason, blocking-window set, resume condition |
| `resume` | the aggregate admission test below passes over every currently binding window | resume ordinary work, same alias/instance (RECOVERY A for a resumed turn) | the resuming samples; the pause generation closed |

**Aggregate admission and pause generations.** Admission is decided over ALL currently binding
windows (§8), never the deciding one alone: `quota-paused` records its BLOCKING-WINDOW SET, and each
blocker clears ONLY on its own valid fresh evidence — a same-window sample in the same reset epoch
back above LOW, or one from a NEWLY OBSERVED reset epoch (taken after that window's `resets_at`,
whose passing alone restores nothing, §3), which RESOLVES that blocker: correlate it to the pause
record and close or supersede that record explicitly. "Capacity" is the recorded band/forecast
admission condition, not any positive percent; an UNAVAILABLE sample never clears an established
blocker; a window the source never exposed is never invented as one; a newly blocking window
recomputes the aggregate and keeps the pause; timer placement (§8) never substitutes for this test
at firing. EVERY aggregate update recomputes two things, while already paused exactly as at entry:
BLOCKER MEMBERSHIP — a window newly blocking by band, or by a newly valid forecast (§3) against the
unit already DEFERRED, joins the set and records its own resume condition, and a blocker resolved as
above leaves it — and TIMER DISPOSITION (§8) — a live timer the new set makes ineligible (U2 giving
way to U3) is retired with its actual stop result, and a set that newly qualifies may arm one
unless the user's cancellation stands for this generation (§8).
Neither recomputation records a second `prepare` or `quota-paused` transition for the generation
already open. A PAUSE GENERATION is one `prepare` → `quota-paused` → `resume` cycle, a RESET EPOCH
one window's reset period: one `prepare` and one `quota-paused` per PAUSE GENERATION (a later sample
reproducing an active pause's evidence re-triggers nothing), and a `resume` CLOSES the generation —
a later band or forecast trigger, even inside the same reset epoch, opens a NEW generation and may
transition again.

Context pressure is not a quota band: it goes to a checkpoint, then the harness's own supported
compaction/continuation path (RECOVERY I) — a replacement session is not the default response. Band
defaults live in this file and in SKILL text; a bus may override them only through a designated
VERSIONED policy record (immutable generations; explicit adoption recording path, hash and adopted
values in each participant's checkpoint). `STATE.md` "Shared" records that decision and its pointer
and stays informational — never the configuration itself, and no new mutable authority.

**Context-aware disposition.** Decided at `prepare` from the §1 context record, and re-decided at
every later aggregate update that keeps the pause: with `resume_risk` `cache-expired` AND
`tokens_used` at or above CTX (default 40 % of `context_window`, a configurable heuristic; a bus
overrides it only through the versioned policy record above) the disposition is `compact-first`;
with `cache-may-hold`, `unknown` or a smaller context it is `same-session`. A disposition is a
REQUEST, never evidence that a compaction or a succession happened. `compact-first` adds ONE bounded
action, made at `prepare` when eligible there, otherwise ONCE — when the disposition first becomes
`compact-first` during the pause, preceded by an updated checkpoint and package and a NEW status
(the next `status-seq`) carrying the disposition, never a new pause transition and never a delay to
the pause or the §8 timer; earlier statuses stay immutable. Publish the §5 status carrying
`pause-disposition: compact-first`, then REQUEST a planned compaction FROM THE USER through the
harness's own notification route where one exists (RECOVERY I.3 — a push notification and a sidebar
flag on the harness that offers them; the turn-end report line otherwise and in every case), naming
its ADVISORY `compact-by` (§1). A compaction before it MAY reuse cached prefix; after it the
summarization itself is a large read; the request stays worth honouring because a compacted context
CAN reduce every later turn's input volume — none of which is a measured hit, cost or quota saving;
observed cache use and before/after volumes are recorded separately (§1). Automatic compaction at
the harness's own threshold is never relied on. A peer with no notification route may ask the
WATCHING side (SKILL §7) to relay the request to the user by info message; the relay names the peer,
its session and the deadline, and is never a cue or a command to compact. The checkpoint records
three things SEPARATELY: the request (when, how), its observed outcome (a compaction observed with
before/after volumes, `not observed`, or `unknown`), and cache usage only where the harness measures
it. Affordability of the summarization turn is not guaranteed; an unanswered or declined request
never delays the pause or the §8 timer. The request changes nothing else: the timer is armed exactly
as without it — the policy intention; its survival across a compaction is a per-harness observation
(RECOVERY I.3, §8), never assumed — and a turn resumed after a compaction re-enters per RECOVERY A
with the same alias and instance. Turns whose only purpose is cache retention are FORBIDDEN during a
pause; controls, receipts, recovery information and safety reconciliation are not keep-warm traffic.
`successor` (a new alias re-entering from the §5 package under the ordinary SKILL §5 handoff gates)
is the USER's decision, recorded when they make it: no launcher route exists, it never replenishes
an account's quota, and it is never a default.

**Forecast-driven early pause.** Independent of the bands, a valid forecast (§3) whose shortest
horizon is shorter than the next consequential unit's expected duration transitions to
`quota-paused` from ANY runnable state — from `observe` as well as from `prepare`, since a shared
pool can drain fast at a high remaining percent — passing through `prepare` only to write the
package (§5). Recorded as forecast-driven, not band-triggered (DESIGN_v2 §16.2). A window forecast
to exhaust before its reset COUNTS AS ENTERING LOW for §8 and joins the blocking-window set, so the
pause follows U2 or U3 by that window's reset. Its RECORDED resume condition replaces the `resume`
row's band test for that window — the horizon again exceeds the deferred unit, or capacity is
observed after the reset — the aggregate test still applying to every other window.

**U2 — a binding window blocks (band or forecast) and EVERY currently blocking window has a KNOWN
reset within 5 h.** (1) recovery package (§5) and a `quota-paused` status; (2) arm exactly ONE
resume timer per §8, registered and user-cancellable (§8); (3) on firing: the aggregate admission
test passing ⇒ `resume` (same alias, same instance); still blocked ⇒ re-package once, and do not arm
a second timer without a genuinely new observation (§8, "no timer loop").

**U3 — a binding WEEKLY window is exhausted for admission — at or below the LOW band, or forecast to
exhaust before its reset — with MORE than 5 h until that reset.** "Exhausted" is that admission
condition, never "0 %". No timer: write the recovery package, publish a `quota-paused` status
carrying `resets-at` (body notes the weekly window and that no timer is armed), and end the turn;
the user chooses a fresh account/session or waits out the reset. The same durable no-timer
disposition is recorded when a blocking window's reset is UNKNOWN, or when no authorized timer route
exists (§8).

## 5. Recovery package
Location: `<bus>/checkpoints/<alias>/handoff/<generation>/`, pointed to atomically from the
participant's checkpoint and from its status. Contents: the same instance/task/attempt state
`references/RECOVERY.md` I.1 already tracks, plus (i) the triggering quota sample and (ii) this
package's own pointer. It is NOT a work handoff: reassignment still needs the ordinary SKILL §5
handoff gates. A successor session is a NEW alias and inherits no token authority; a same-instance
resume keeps the existing alias. A project's own ledger — `<R>/HANDOFF.md` in particular — is bound
to this package only when explicitly named, and is never invented or overwritten by default.

Preparation finishes only a bounded safe-stop action: checkpoint the current unit rather than
insisting it finish. Pausing changes no ownership: unknown launches or effects and locks a child may
still use are preserved as recorded; only reconciled locks the participant itself owns are released
(RECOVERY A.9, A.11(b)). A failed status or package publication leaves the last complete durable
checkpoint and the last complete package generation usable. A generation counts as COMPLETE only on
its own durable verification — the committed pointer resolving to the bytes actually written; a
simulated trace's completion flag (RECOVERY J) records the model of that, never the verification.
Quota state lives in the status and the checkpoint, never in the heartbeat's first line;
`idle-with-queue:` still names only the journal's accepted-unstarted units, never a paused in-flight
one.

## 6. Peer relay
Consistent with SKILL §7/§8's provenance rules: an authorized peer may relay an ACTUAL target-origin
(or correctly mapped target-pool) observation, with its source and sample time intact — never its
own quota relabelled as the target's. Dedupe by target/pool/window/reset epoch (§4). A quota warning
never cancels remote work, kills a child, takes a lock, repeatedly cues a paused task, switches
account/provider/model, spends reset credits, or creates a new task. "Send nothing new" (§4
`prepare`) means no new ORDINARY jobs — cancellations, supersessions, results/receipts and recovery
information keep flowing.

## 7. Per-harness sources
| harness | window(s) observed | context signal | dated observation | provenance |
|---|---|---|---|---|
| Claude Code | a short rolling window (5 h) + an all-models weekly window + a model-specific weekly window, from the desktop app's usage reader | a live token/context meter with a compaction-threshold percent | 2026-09-18T05:49:00Z: rolling window 33 % remaining (resets 2026-09-18T07:50:00Z); weekly-all-models 84 % remaining; model-specific weekly 81 % remaining (both reset 2026-09-24T16:00:00Z) | Claude-observed, `checks/rev7/claude/OBSERVATIONS.json`, this session, for that task/runtime — not a permanent limit of every Claude Code client |
| Codex | one weekly window from the app's `get_usage_limits`; no matching short window exposed | last-request input-token occupancy against the model's context window only (no live remaining-context meter) | 2026-09-18T05:37:54Z: weekly window 97 % remaining (resets 2026-09-25T05:11:24Z); short window UNAVAILABLE (not zero, not unlimited); last-request occupancy ≈ 24.8 % of context | Codex-observed, `checks/rev7/codex/OBSERVATIONS.json`, for that task/runtime — not a permanent limit of every Codex client |

**Context continuity (dated observations).** Claude Code, 2026-09-18T15:4xZ–16:2xZ
(`checks/rev8/claude/OBSERVATIONS.json`): a 1-hour prompt-cache TTL stated by the harness; planned
compaction is user-triggered or automatic at the harness threshold, no agent-triggerable route
observed; one planned compaction 895198 → 100554 of 1 000 000 tokens with status and package
published first and the same alias/instance re-entered per RECOVERY A; a persistent inbox watcher
survived it; a session-scoped resume timer surviving one NOT observed either way; user-notification
routes for the request tested once — a push notification ("Mobile push requested"; desktop notice,
phone when Remote Control is connected, skipped as redundant when the user is at the terminal) and
the sidebar unread flag — neither compacting anything. Codex, 2026-09-18T16:06:28Z (`checks/rev8/codex/OBSERVATIONS.json`,
sha256 7b387f74271479c95ff1a6c9e4a9670f67c921fc4fe713ae4e106b4c224037ff): TTL unavailable, a cache-hit counter with
no retention guarantee, one compaction (trigger unknown), no verified route, timer survival unavailable.

## 8. Resume timer and binding windows

**Binding windows (model-neutral).** Two windows always bind: the short rolling window and the
all-models weekly window. A model-specific weekly window binds ONLY that model's work, including a
child running that model under a parent running a different one; other models ignore it.
Provider-to-window mappings are dated observations (§7), never invented.

**Resume timer.** One-shot; armed only on a verified, authorized native route the arming session
actually has (SKILL §7; no new route is created here). Bound to the target instance, the specific
PAUSE GENERATION (§4), and the work generation being paused. Registered before arming (intent),
given its handle right after (actual) and retired with its stop result when superseded, cancelled or
fired (SKILL §7). User-cancellable at any time in favour of a fresh account/session; that
cancellation is the user's and no later quota observation overrides it FOR THAT PAUSE GENERATION
(§4) — a newly eligible generation is a fresh decision, never a revival of the cancelled timer. On
firing, before any work: recheck cancellation, supersession, session lifecycle, and take FRESH
samples for §4's aggregate admission test — elapsed time alone never clears a pause. Unchanged
capacity/reset evidence at firing re-packages once (U2) and never arms a second timer off the same evidence ("no timer loop"). The
§4 disposition never touches the timer; its absence at firing is an observation only, decided by the aggregate test alone, with
the resumed input volume recorded only where measured (`unmeasured` otherwise) and no second timer or request armed off it.
Re-entry (RECOVERY A.7) RECORDS the handle: live → kept; lost → retired with that stop result and PLANNED for ONE
replacement, EXECUTED only at the terminal yield phase RECOVERY A.13, after A.11(d)'s queue and admission disposition is
settled, and only if the route is still authorized, the target lifecycle is unchanged, no user cancellation stands for this
pause generation, the same pause and work generation hold, the aggregate admission test still fails, and the original firing
time is still in the FUTURE — an ELAPSED firing time instead takes the ordinary fresh-admission path (samples, §4, U2/U3
re-decided), never a re-arm at that elapsed timestamp; unverifiable → `unknown`, NEVER duplicated, ordinary wake routes
remain the resume path.

**For a CUED target** (the watching side arms the timer on the target's behalf): on firing it
samples only a target-origin or correctly mapped target-pool source (§6 — never its own quota
relabelled). With such a sample showing capacity, or with no target-side source at all, it publishes
an info relay and MAY cue the target ONCE under SKILL §7's gates — a CONTROL request that the target
take its own sample, distinct from re-cueing the blocked project unit and never a `quota-state:
resume` on its behalf; the native-idle, pause-generation and no-repeat gates apply. With a
target-side sample showing NO capacity it does nothing at all: no cue, no relay, no re-arm — the
target stays paused until its own ordinary wake or its user. The target's own fresh sample, `resume`
or one re-package (U2) happens at its own wake through its own intake (SKILL §10). Wording: "Codex
arms none BY POLICY" — timer-arming is assigned to the WATCHING side (SKILL §7), which cues Codex
after the reset; dispatch never by itself proves the resume (DESIGN_v2 §16.2).

**When the timer is armed.** Only if EVERY currently blocking binding window (§4's blocking-window
set, in or entering the LOW band) has a KNOWN reset within 5 h: arm the resume check at the LATEST
of those reset times plus a margin (default 2 min), not the earliest. If ANY blocking window's reset
is UNKNOWN, NO timer is armed at all — a partial timer over only the known resets is never a
substitute; the pause keeps U3's no-timer disposition. A binding weekly window blocking admission
with MORE than 5 h to its reset overrides the timer branch entirely: that is U3, not U2 — no timer
at all, whatever other windows show. A "NEW OBSERVATION" — U2's condition for re-arming — means
changed relevant evidence: a different remaining percent, a different and still FUTURE reset time,
or a newly eligible pause generation, never a re-read reproducing the same values already used to
decide not to arm again. Changed evidence alone never arms: U2's precondition must hold at that
moment too, so a different remaining percent over a `resets_at` already elapsed, with no future
reset for a timer to sit at, is a new observation and still no timer.

**Self-wakeup admission.** Warning bands are §4; §7 only records per-harness sources. Routine sampling happens at
active-turn checkpoints and requires no wakeup timer. A self-wakeup timer is admissible only on one of three justifications
recorded with its evidence — `cap-near` (a fresh binding-window observation satisfying §4's WARN/LOW or valid-forecast
condition — §4 is in REMAINING capacity, so remaining at or BELOW WARN; 80 % remaining ALONE does not qualify, while a valid §4 forecast still can), `resume-after-pause`
(this section's timer, bound to its pause generation) or `poll-external` (a named external state the harness cannot notify
about, with its expected change rate) — never on a routine fallback, a keep-alive or an 'in case' wakeup; a non-quota
justification records its pause generation `not-applicable`; and a justification authorizes nothing by itself. No
self-wakeup timer is armed over a potentially active owned worker or in-flight tool call absent a verified non-interrupting
delivery route (SKILL §7); an earlier idle timer is reconciled and cancelled before protected work resumes.
