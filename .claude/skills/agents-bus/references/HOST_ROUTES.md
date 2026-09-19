# references/HOST_ROUTES.md — observed host routes for cross-harness activation

## 0. What this is / is not
Descriptive observations per host, dated, with evidence paths. The participant record stays the
per-target authority for eligibility: a catalogue entry here makes no route eligible by itself.
SKILL §7 requires the route VERIFIED and recorded in the target's participant record, the user's
authorization, and the caller's own native-idle evidence; a configured record, an unrecorded
route, or an entry here by itself, is not eligible. First use on a bus whose target record does
not yet say `verified` is a user-authorized EXPERIMENT, recorded with intent, result and
observation the way the RadiiPolynomial bus recorded
`checks/activation/QUEUE_ROUTE_EXPERIMENT.json`; it is not a §7 activation, no rule here makes it
one, and the target registers `verified` only after that experiment's observed wake. Nothing here
authenticates a sender. This package never edits instruction files.

## 1. Table of observed host routes

| host | harness | route | executable | argv | versions observed | evidence | not the route |
|---|---|---|---|---|---|---|---|
| macOS with the ChatGPT desktop app (Codex app) | Codex | `cli-queue` | `/Applications/ChatGPT.app/Contents/Resources/codex` | `queue --thread <thread id> --message "<cue>"` (cue body: SKILL §7 format, pointers only) | 0.154.0-alpha.6.2 (2026-09-13…17), 0.155.0-alpha.2.6 (2026-09-18) — the app updates itself; the path has been stable across these observed versions — an observation, not a guarantee across future installations | RadiiPolynomial bus `checks/activation/QUEUE_ROUTE_EXPERIMENT.json` (2026-09-13T21:50:39Z, exit 0, observed wake). Dispatch only, wake NOT observed: Grading bus `checks/cues/20260917T201500Z-claude2-cue2.json` (2026-09-17T20:15:10Z, exit 0, `result.status: dispatched`, `observed: null`) | `/opt/homebrew/bin/codex` (Homebrew `codex-cli` 0.136.0, no `queue` subcommand; observed 2026-09-18); `codex agents` needs a TTY (fails with 'stdin is not a terminal' from a tool call; observed 2026-09-17, not re-run 2026-09-18) |
| Claude Code target | Claude Code | none | — | — | — | — | none known or verified as of 2026-09-18; concurrent resume of a live transcript is forbidden (SKILL §7); a Claude Code session is the WATCHING side and cue dispatcher (SKILL §7 default activation pattern): it arms its own inbox watcher and needs no cue; a Codex task cannot cue it and falls back to `user-relay` only while that watcher is not running |

## 2. Procedure for a fresh session
1. Check the app bundle path exists and `… queue --help` prints
   `Usage: codex queue [OPTIONS] --thread <THREAD> --message <TEXT>`; exit status 0 proves
   nothing by itself — the PATH binary (Homebrew `codex-cli`) also exits 0 and prints its own
   top-level help (observed 2026-09-18). Run `which -a codex` and `--version` on each candidate —
   record which binary you tested.
2. The target thread id is the `instance_id` in the target's participant record (Codex registers
   `CODEX_THREAD_ID`). That alias → instance binding holds regardless of the record's age: a stale
   `last_seen` is an uninformative observation, never a change of identity (SKILL §6), and a fresh
   one is not liveness. If no record exists (a new bus, or a target that has not registered), the
   caller may only ENUMERATE candidates: `~/.codex/session_index.jsonl` newest-first (`id`,
   `updated_at`; the index has no `cwd` field) and each id's rollout file
   `~/.codex/sessions/YYYY/MM/DD/rollout-<ts>-<id>.jsonl`, whose first line (`session_meta`) carries
   `cwd` and `originator`. Several live Codex tasks can share one cwd, so a cwd match narrows the
   list and never resolves it: only the target's own registration (`hello`) or the user's direct
   mapping says which thread is the peer. Record the source as `thread_provenance`.
3. Native-idle evidence = the rollout's LAST line is an `event_msg` of type `task_complete` with no
   later `task_started` (an observation of the harness itself, SKILL §7 condition (a)), or the
   user's direct report. This shows only that the thread's last recorded turn finished, not that the
   thread is still open in the app — a closed thread ends identically, and a queue to a closed
   thread still returns 0 (§1 above). Rollout completion is a dated observation of a completed turn;
   neither a participant record's `last_seen` nor the index's `updated_at` proves the current
   lifecycle state — use a native status observation or the user's direct report for the lifecycle
   gate. Corroborate with the app's own thread list, a fresh `updated_at` in `session_index.jsonl`,
   or the user's report. A heartbeat is never that evidence. (All `~/.codex` layout facts in steps
   2-3 — `session_index.jsonl` keys, the rollout filename pattern, `session_meta` fields,
   `event_msg` types — observed 2026-09-18, codex-cli 0.155.0-alpha.2.6; Homebrew `codex-cli`
   0.136.0.)
4. Publish the bus message FIRST.
5. Record the cue intent under `<bus>/checks/cues/<id>.json` (fields: `intent_at`, `caller`,
   `caller_instance`, `target`, `route`, `executable`, `thread`, `thread_provenance`,
   `native_idle_evidence`, `covered_ids`); dispatch with stdin from `/dev/null`; record the
   result (exit code, stdout, `dispatched_at`) — exit 0 with "Queued message …" is DISPATCH, not
   observation: a stale or wrong thread also returns 0 (observed 2026-09-17, cue1 to a
   predecessor thread).
6. `observed` only on target-origin evidence bound to the covered ids (SKILL §7).
7. A target whose cwd is not under the coordination root cannot find the bus by the marker walk from
   where it runs; it must already hold the bus location from its own durable route context (its
   participant record, checkpoint or the project's own configuration). If it does not, discovery is
   UNRESOLVED and needs an initial location handoff from the user — the cue is never broadened to
   carry paths, and no session scans unrelated buses as a workaround. The bus message body still
   names absolute paths for a peer that can read them.

## 3. Registering the route for a target
The TARGET runs `hello` with a keepalive marking this route — for example
`--keepalive cli-queue:verified` (or `configured`), in whatever free-text form that bus's §7
convention uses — after a real wake was observed on that bus. The executable path, argv and host
of the verified route are recorded in the project's own configuration as well (RECOVERY I.3); the
keepalive value alone records none of them. The caller never writes the target's record.

## 4. Adding a host
Append a dated row with evidence paths. This file is part of the package (MANIFEST), so an
addition is a revision under SKILL §9.
