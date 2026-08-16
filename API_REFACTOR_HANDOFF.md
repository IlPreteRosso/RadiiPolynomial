# RadiiPolynomial API Refactor Handoff

Date: 2026-06-22

> **Historical snapshot — refreshed 2026-07-10.** The staged-refactor state
> described below was superseded when the refactor landed on `main` as
> `dc5d550`. Do not follow the instructions below to preserve or commit a
> staged refactor baseline. For current project context, start with this
> checkout's `AGENTS.md`, Codex's project-memory import, and the current
> inner-repository `git status`. The current module layout and dependency rules
> are documented in `ARCHITECTURE.md`; module paths below are historical. The
> detailed migrated corpus remains at
> `/Users/ilpreterosso/.claude/projects/-Users-ilpreterosso-VSCode-Lean-RadiiPolynomial/memory/MEMORY.md`.

## Goal

Refactor the API while preserving the mathematical layering:

- Keep the abstract radii-polynomial theorem as the anchor.
- Keep the `CompPoly` + `MvPolynomial` split: computable certificates on the AST side, algebraic proofs through `MvPolynomial`/`aeval`.
- Keep `evalBanach` as the user-facing evaluator; keep `evalAlg` as an internal bridge to `aeval`.
- Keep the IVP layers separated: data, algebra, certificate, analytic.
- Trim development leftovers and unnecessary API plumbing.
- End state: all production examples compile with `lake build`.

## Current Repository State

The refactor has been moved back into the main local repository:

- Active tree: `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial`
- Active branch: `main`, tracking `origin/main`
- The former `RadiiPolynomial-api-refactor` linked worktree was removed.
- The local `codex/api-refactor` branch was deleted.
- The refactor diff is staged on `main`; no commit has been made yet.
- The pre-swap original tree was archived at `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial-backup-20260622-164709.tar.gz`.

The LeanCert dependency is still a local path dependency for now:

- Path: `/Users/ilpreterosso/VSCode/Lean/LeanCert/leancert`
- Branch used locally: `local/mathlib-v4.31.0`
- Reproducible remote pinning is intentionally deferred.

## New Session Startup

Use this exact starting sequence in a new Codex session:

```bash
cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial
sed -n '1,260p' API_REFACTOR_HANDOFF.md
git status --short --branch
lake build
```

Then read the design/memory files listed below before making API changes. The current invariant is: work directly on `main`, keep the refactor staged/uncommitted until the user explicitly asks to commit, and do not change the local LeanCert path dependency unless explicitly requested.

Important diff boundary:

- The staged diff on `main` contains both the user's pre-existing in-progress project state and the intentional refactor slices documented below.
- Do not assume every staged line was introduced by the refactor session.
- Before a final upstream-quality PR, separate or document the mirrored baseline from intentional refactor changes.

## Current Verification State

In the active tree:

```bash
cd /Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial
lake build
```

Status: succeeds, 2986 jobs, after updating the project and local LeanCert path dependency to Lean/mathlib `v4.31.0`.

The default build currently emits no warnings. Project-owned deprecations were updated to the v4.31.0 names, and the local LeanCert dependency branch was also cleaned of the deprecations that appeared in the default import graph.

## Removed / Excluded Inventory

Brief rationale for cleanup already performed:

- `abar_Q` / `habar` parameters were removed from `IVP.ivp_hDF_block` and `IVP.ivp_hDF_block_nat` because the proofs never used the approximate-solution array directly; the needed computable bridge is already supplied by `hDφ_Q` and the finite-block match `hDF`.
- `hφ_diff` and `hK` were removed from `IVP.ivp_Dφ_norm_le` because neither was used. Differentiability is not needed for this norm estimate, and multiplying `hDφ_le` by `‖h‖ ≥ 0` does not require a separate `0 ≤ K` hypothesis.
- Extra implicit `[NeZero L]` / `[Fact (1 ≤ ν)]` contexts were removed with `omit` where Lean reported they were unused. This shrinks theorem contexts without changing conclusions.
- `RadiiPolynomial/source/MvPolyBridge/POC.lean` was deleted because it was a proof-of-concept scratch file, not imported by the root module, and its useful ideas have moved into `MvPolyBridge.Basic`, `MvPolyBridge.CompPoly`, tactics, and production examples.
- `RadiiPolynomial/source/Chebyshev/PerformanceDemo.lean` was deleted because it was a performance note/demo, not library API, not root-imported, and contained demonstration `sorry`s.
- Copied untracked `RadiiPolynomial/examples/Numina_Example77/` was deleted because it was scratch/eval material with unresolved `sorry`s and no root imports.
- `RadiiPolynomial/examples/Example1421/*` was excluded from the default root import graph, not deleted, because it is a tracked Chebyshev scaffold waiting for Julia-exported numerical data and a certificate.
- `examples/tests/*` remains excluded from the default build because those files are intentional autoformalization skeletons with `sorry`s.

## Completed Slices

### 1. IVP DF API Simplification

Files changed in this refactor after mirroring the current dirty state:

- `RadiiPolynomial/source/IVP/DFBlock.lean`
- `RadiiPolynomial/source/IVP/StandardIVP.lean`

What changed:

- Removed unused `abar_Q` / `habar` parameters from `IVP.ivp_hDF_block`.
- Removed unused `abar_Q` / `habar` parameters from `IVP.ivp_hDF_block_nat`.
- Updated `StdIVPData.composedApprox_eq_fderiv_G_fin` to call the simpler `ivp_hDF_block_nat`.
- Removed unused `hφ_diff` and `hK` parameters from `IVP.ivp_Dφ_norm_le`.
- Added `omit [NeZero L] in` before theorem/docstrings where `[NeZero L]` was being pulled into declarations that do not use it.

Focused checks passed:

```bash
lake env lean RadiiPolynomial/source/IVP/DFBlock.lean
lake build RadiiPolynomial.source.IVP.DFBlock
lake env lean RadiiPolynomial/source/IVP/StandardIVP.lean
lake build
```

### 2. Scratch/Demo Surface Removal

Scratch/demo surfaces removed:

- Deleted tracked `RadiiPolynomial/source/MvPolyBridge/POC.lean`.
- Deleted tracked `RadiiPolynomial/source/Chebyshev/PerformanceDemo.lean`.
- Deleted copied untracked `RadiiPolynomial/examples/Numina_Example77/`.

Verification:

```bash
rg -n "MvPolyBridge\\.POC|Chebyshev\\.PerformanceDemo|Numina_Example77" RadiiPolynomial.lean RadiiPolynomial/source RadiiPolynomial/examples
lake build
```

The `rg` command finds no references. `lake build` succeeds.

### 3. Project-Owned Warning Cleanup

Project-owned warning cleanup:

- `RadiiPolynomial/source/Chebyshev/ChebyshevIVP.lean`: added `omit` for unused `[Fact (1 ≤ (ν : ℝ))]` / `[NeZero L]`; removed unused simp arguments.
- `RadiiPolynomial/source/Chebyshev/ChebyshevBlockDiag.lean`: added `omit [NeZero L]`; removed an unused simp argument.
- `RadiiPolynomial/examples/Example81/Certificate.lean`: replaced the unnecessary `<;>` sequence-focus proof shape with a direct case split.
- `RadiiPolynomial/source/lpSpace/CauchyProduct.lean`: replaced project-local `push_neg` uses with `push Not`.
- `RadiiPolynomial/source/lpSpace/OperatorNorm.lean`: replaced project-local `push_neg` with `push Not`.

Focused checks passed:

```bash
lake env lean RadiiPolynomial/source/Chebyshev/ChebyshevIVP.lean
lake env lean RadiiPolynomial/source/Chebyshev/ChebyshevBlockDiag.lean
lake env lean RadiiPolynomial/examples/Example81/Certificate.lean
lake env lean RadiiPolynomial/source/lpSpace/CauchyProduct.lean
lake build
```

### 4. Root Import Cleanup

Root import cleanup in `RadiiPolynomial.lean`:

- Reordered imports to mirror the intended layering: lp/Banach infrastructure, core theorem, MvPolyBridge, evaluation/tactics, BlockDiag, IVP, Chebyshev, production examples.
- Added an explicit root import of `RadiiPolynomial.source.MvPolyBridge.CompPoly`.
- Moved analytic example imports into the examples section rather than mixing them with IVP infrastructure.
- Kept the `FinMatrixBound` direct root import commented as before.

Verification:

```bash
lake env lean RadiiPolynomial.lean
lake build
```

### 5. Example1421 Default-Build Exclusion

Excluded the tracked `Example1421` Chebyshev scaffold from the default root import graph:

- `RadiiPolynomial/examples/Example1421/Numbers.lean` and `Algebra.lean` remain in the tree.
- They are now commented out in `RadiiPolynomial.lean` with a note that Julia-exported numerical data and a certificate are still missing.
- This keeps the default build focused on production examples rather than TODO-only scaffolding.

Verification:

```bash
lake env lean RadiiPolynomial.lean
lake build
```

### 6. CompPoly Usage Documentation

Updated the public `CompPoly` usage documentation:

- Replaced stale `φ_cpoly` / `φ_spec` / `Dφ_Q` example names with `f_cpoly` / `f_spec` / `Df_Q`.
- Changed the user-facing evaluator in the usage block from `evalAlg` to `evalBanach`.
- This is documentation-only; `evalAlg` remains part of the internal bridge to `aeval`.

Verification:

```bash
lake env lean RadiiPolynomial/source/MvPolyBridge/CompPoly.lean
lake build
```

### 7. Lean/mathlib v4.31.0 Compatibility

Updated the project to Lean/mathlib `v4.31.0`.

Dependency state:

- `lean-toolchain`: `leanprover/lean4:v4.31.0`
- `lakefile.toml`: Mathlib `rev = "v4.31.0"`
- `lake-manifest.json`: Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Local LeanCert path dependency points to `/Users/ilpreterosso/VSCode/Lean/LeanCert/leancert`.
- LeanCert branch used by the path dependency: `local/mathlib-v4.31.0`.

Main compatibility friction and fixes:

- Edited imported files require `lake build`, not just `lake env lean`/stdin tests; cached `.olean` files can hide new simp/bridge lemmas until the dependency module is rebuilt.
- `lpSpace/NormHelpers.lean`: `sum4_swap_pairs` needed a more explicit `simpa` over equivalence combinators after Mathlib changed normal forms.
- `lpSpace/OperatorNorm.lean`: inverse proof now uses `(u⁻¹).val` explicitly where coercion inference changed.
- `lpSpace/Eval.lean`: derivative proof now exposes summability and derivative equality explicitly rather than relying on brittle simplification.
- `BlockDiag/Base.lean`, `BlockDiag/Concrete.lean`, `IVP/DFBlock.lean`: replaced brittle `convert` proofs with explicit `change`/`calc`/`simpa` steps.
- `IVP/Bridge.lean`: added the needed ODE existence/uniqueness import under the new Mathlib layout.
- `MvPolyBridge/CompPoly.lean`: added reusable structural bridges for the examples:
  `differentiable_evalBanach_l1Weighted`,
  `pderiv_pderiv_toMvPoly`,
  simp support for generated `pderiv`/`toMvPoly` equations and operation notation,
  and general `MvPolynomial.C_natCast_eq` / `C_ofNat_eq` / `C_intCast_eq` constant bridges.
- `Example81/Certificate.lean`: after the generic `CompPoly` Hessian bridge, the remaining `C 2` normalization is handled locally with `rw [MvPolynomial.C_ofNat_eq]` and `norm_num`; do not promote a global `C_two_eq` API lemma for this.
- `Example83/Certificate.lean`: rewrote `D₂_lorenz` from pattern matching to decidable `Fin` equalities so `simp (config := { decide := true })` reduces the Lorenz Hessian table and row sums reliably.

Anti-ad-hoc API rule from this slice:

- Do not add source/API lemmas that only solve one certificate's concrete numeral or finite case.
- General structural bridge lemmas belong in `source/`; incidental numeric or finite cleanup belongs in the certificate proof or a private local lemma.

Verification:

```bash
lake build LeanCert
lake build leancert
lake build LeanCert.CheckCompat
lake exe check-compat
lake build RadiiPolynomial.source.MvPolyBridge.CompPoly
lake build RadiiPolynomial.examples.Example81.Certificate
lake build RadiiPolynomial.examples.Example83.Certificate
lake build
```

## Important Memories / Design Constraints

Read these before further edits:

- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/MEMORY.md`
- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/project_comppoly_api.md`
- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/project_blockdiag.md`
- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/project_refactor_changelog.md`
- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/feedback_lake_build.md`
- `/Users/ilpreterosso/.codex/memories/claude_memory_radii_polynomial/feedback_api_over_unfolding.md`

Use the `radii-poly-api-design` skill.

Anti-goals unless explicitly requested:

- Do not refactor `F` from raw `ℕ → ℝ` into an omega-space codomain.
- Do not bundle the deferred two-weight `BlockDiag` refactor into this pass.
- Do not delete `evalAlg`; it is an internal bridge for the categorical story and proofs.
- Do not make tests with intentional sorries part of the default build.

## Current Audit Findings

Development leftovers / scratch surfaces:

- `RadiiPolynomial/examples/tests/easy/*` and `examples/tests/hard/*`: skeletons with sorries, intentionally commented out in `RadiiPolynomial.lean`.

TODOs:

- `RadiiPolynomial/source/BlockDiag/Concrete.lean`: TODO about unifying with `IVP.ivp_Z₀_le`; this is the deferred two-weight BlockDiag Phase A/Phase B topic.
- `RadiiPolynomial/source/IVP/Theorem.lean`: same Z0-unification TODO.
- `RadiiPolynomial/examples/Example1421/*`: Chebyshev example scaffold with Julia-export TODOs; tracked but excluded from the default root import graph until numerical data/certificate are present.

Warning cleanup state:

- `lake build` in the active project tree emits no warnings.
- `lake build LeanCert` in `/Users/ilpreterosso/VSCode/Lean/LeanCert/leancert` emits no warnings.
- Source scans for the targeted deprecated identifiers are clean in both trees:
  `fderiv_id'`, `fderiv_comp'`, `totalDegree_finset_sum`, deprecated `ContinuousLinearMap.*_apply` names, `push_neg`, `continuous_mul_right`, and `ENat.one_le_iff_ne_zero`.
- While checking touched non-default LeanCert modules, `LeanCert.Engine.TaylorModel.Log1p` needed a small v4.31.0 port: import `Mathlib.RingTheory.Polynomial.Tower`, use `Polynomial.aeval_map_algebraMap`, and unfold `Function.comp_def` in the `log(1 - x)` derivative proof.

## Recommended Next Slices

1. Reconfirm the active tree and staged baseline:

```bash
pwd
git branch --show-current
git status --short --branch
git diff --cached --stat
git diff --cached -- RadiiPolynomial/source/IVP/DFBlock.lean RadiiPolynomial/source/IVP/StandardIVP.lean
```

2. Create a baseline checkpoint strategy before larger cleanup:

- Option A: make a local WIP commit on `main` that represents the currently staged refactor state, then continue with smaller commits.
- Option B: keep everything staged/uncommitted, but maintain this handoff file and record each slice precisely.
- Prefer Option A before any further broad deletion/move work; it makes rollback and review practical.

3. Continue API cleanup by removing unused parameters or stale names only when:

- The theorem statement becomes mathematically cleaner.
- All callers are updated through wrapper APIs when possible.
- The proof still follows the intended layer: `CompPoly` for computation, `MvPolynomial` for algebra, `general_radii_polynomial_theorem` for existence.

4. Verification loop per slice:

```bash
lake env lean <changed-file>
lake build <changed-module>
lake build
```

Do not trust `lake env lean` alone after editing dependencies; cached oleans can mislead. Use `lake build` for the final check.

## Stop / Escalate Conditions

- If a cleanup wants to change the mathematical shape of `F`, stop; the current plan keeps `F : ℕ → ℝ` raw.
- If a cleanup requires the two-weight BlockDiag design, stop and make a separate plan; that is explicitly deferred.
- If deleting a file breaks a production example, either restore the file or turn the useful content into a properly imported API lemma.
- If `lake build` fails after a slice, fix the slice before starting the next one.

## Suggested New-Session Prompt

Paste this into a fresh Codex session if memory is tight:

```text
Continue the RadiiPolynomial API refactor in the active main worktree:
/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/RadiiPolynomial

The refactor diff is staged on main but not committed. First read API_REFACTOR_HANDOFF.md, then the listed Codex/Claude memory files and the radii-poly-api-design skill. Preserve the math layering: general radii theorem anchor, CompPoly/MvPolynomial split, evalBanach public with evalAlg internal, IVP data/algebra/certificate/analytic layers. Goal: trim development leftovers and unnecessary API plumbing while keeping all production examples compiling with lake build.
```
