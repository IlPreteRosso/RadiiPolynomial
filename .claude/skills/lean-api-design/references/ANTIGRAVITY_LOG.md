# Antigravity Log

Dated Antigravity (`agy`) evidence moved VERBATIM out of `lean-api-design/SKILL.md` by the
SKILL-COMPACT-20260922 packet (2026-09-22). Line ranges are those of the base SKILL.md
(sha256 9c38835b3b8e4b62…, 308 lines). The standing rules these logs support stay in
SKILL.md, section "Peer Harnesses → Antigravity CLI"; this file is evidence, not an
instruction source, and a block quoted here that disagrees with SKILL.md loses.

## Model slugs from `agy models`, 2026-09-19 — base lines 99–100 (LAD-12)

```text
   `--dangerously-skip-permissions`. Slugs come from `agy models` (2026-09-19: Gemini 3.8 /
   3.7 / 3.6 Flash, Gemini 3.1 Pro high/low, Claude Sonnet 4.6 / Opus 4.6, GPT-OSS 120B).
```

## Cost samples of the first review-worker runs, 2026-09-20 — base lines 121–125 (LAD-11)

```text
   `--conversation <id>` and the missing rule. Cost sample: a review of
   ~1000 new lines inside a 4252-line module took 332 s, 14 probes, 654k tokens (596k in,
   58k out incl. 47k thinking); an 844-line module 164 s / 269k; a 1137-line module 269 s /
   528k. Verdicts are non-final: file them under `ledger/bus/claude_units/<unit>/agy/` and
   record the coordinator's disposition per finding.
```

## First prose-consult A/B, 2026-09-20 — base lines 166–169 (LAD-10)

```text
   First A/B (2026-09-20, Liouville route): Pro and Flash gave the same route and quality,
   Flash faster and more detailed; both reported a Mathlib lemma as missing that exists
   (`SymplecticGroup.det_eq_one`), so grep/#check every "missing in Mathlib" claim
   from a prose consult before it enters a brief.
```

## Friction log, 2026-09-20 (16 headless runs) — base lines 170–184 (LAD-11)

```text
   Friction log (2026-09-20, 16 headless runs): (3) on inputs above ~1500 lines the final
   text can degenerate into one repeated word and Google's safety filter returns
   `status: ERROR`, yet `structured_output` is still delivered and usable — treat it as a
   lower-trust verdict and review blocks, not whole modules (scope the prompt to a line range
   and let the rest of the file be context); (4) a DNS/network failure (`AGY_ERROR … no such
   host`, `retryable: true`) dies before the first model call — just relaunch; (5) trap (1)
   recurs even with the foreground rule in the prompt (2 of 16 runs): keep the rule, and on
   the kill resume with `--conversation <id>` restating it — the resumed run keeps its probes;
   (6) `--effort` takes only low|medium|high (high is the ceiling); (7) a wrong line count in
   the prompt is harmless, the worker counts for itself. Verdict profile: strong on hypothesis
   strength, unused binders, probe-verified Mathlib duplicates and docstring honesty; weak on
   judging against the item MARKER (it judges against the prompt's framing) and prone to
   'vacuous when the domain is empty' padding; it never found a mathematical error (Lean
   already checks), so its value is the second reading, not a verdict. Typical cost 160–370 s
   and 250k–860k tokens per review.
```

## Probe narrative, 2026-09-19 (`probe_geom_tail`) — base lines 208–217 (LAD-11)

```text
7. Probe 2026-09-19, `probe_geom_tail` (Mathlib-only geometric tail, statement from the
   Aristotle probe), both runs compiled on v4.33.0 with `[propext, Classical.choice,
   Quot.sound]` and a byte-identical statement.
   Gemini 3.1 Pro high: two headless calls (the first ended by a denied ad-hoc `lean` call
   before the checker took a file argument, resumed with `--conversation`), ~5 min wall,
   137k tokens on the second call, nested `calc` with manual `mul_inv` shuffling and
   `clear`: golf-stage material.
   Gemini 3.8 Flash high: one call, 62 s wall, 153k tokens, six lines
   (`div_lt_one`, `simp_rw [pow_succ']`, `tsum_mul_left`, `tsum_geometric_of_lt_one`,
   `field_simp`): committable after the trust gate as is. Hence the default above.
```

## First production reviews, 2026-09-20 — base lines 219–226 (LAD-11)

```text
   First production reviews 2026-09-20 (Gemini 3.8 Flash high, comment-stripped modules):
   S-333b (Ch03/Sec3, 12 new private lemmas) PASS, confirmed no Mathlib duplicates for the
   three reusable lemmas, six name/style findings; F-102a (Ch10/Sec2) CONCERNS, one real
   docstring overclaim (fixed) plus API-shape notes; F-085 (Ch08/Sec5Taylor) CONCERNS, three
   identity faces mis-judged against the prompt's "recurrence" wording plus three verified
   API-reuse notes. The worker is reliable on hypothesis satisfiability, unused hypotheses
   and `#check`-verified duplicates; it takes the prompt's framing literally, so describe
   each face by what its marker says, not by a collective label.
```
