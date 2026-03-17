# Refactoring Log: BlockDiag Witness Layer + Namespace Rename

**Date**: 2026-03-17
**Build**: 2958 jobs, all passing

## Motivation

Example83 (Lorenz IVP, L=3, N=30) had a 727-line `Certificate.lean` that manually
reasoned about operator norm bounds term-by-term. The Z₂ bound alone was 280 lines of
manual fderiv decomposition, auxiliary element construction, and per-component threading.
The goal was to exploit the equation-independent structure of IVP problems (Chapter 8.2
of the reference book) to reduce certificates to only equation-specific hypotheses.

## Key Discovery

`IVP/Setup.lean` (506 lines) already contained three structural lemmas:
- `IVP.ivp_Z₁_le` — generic Z₁ bound from `hfin` + `htail` + `hDφ`
- `IVP.ivp_Y₀_le` — generic Y₀ bound from support + per-component sums
- `IVP.ivp_Z₂_le` — generic Z₂ bound from `hDφ_diff` + active set + block norms

Certificate.lean was not using them — it re-derived everything manually.

## Changes

### 1. Library: `CauchyProduct.ratCast` (`source/lpSpace/CauchyProduct.lean`)

Added `ℚ → ℝ` cast lemma for Cauchy products, used by ℚ bridge proofs.
Required `import Mathlib.Data.Real.Basic` and wrapping existing `variable {R : Type*}`
in `section Generic` to prevent universe-polymorphic `R` from capturing `ℝ`.

### 2. Library: Dead code deletion (`source/BlockDiag/Base.lean`)

Deleted `ComponentwiseMatrixOp` and `ComponentwiseBlockDiagOp` (~75 lines).
These modeled an "Architecture A" (L×L matrix of CLMs / diagonal of CLMs)
that was never used. The actual pipeline uses "Architecture B":
coefficient-level `SystemBlockDiagData.action` → single `toCLM` lift.
The Z₂ sparsity optimization uses `norm_toCLM_component_le_restricted`
with active sets, not CLM-level type abstractions.

### 3. Namespace rename: `SystemTaylorODE` → `RadiiPolynomial`

All 15 source files renamed. Additionally:
- `NormHelpers` → `RadiiPolynomial.NormHelpers`
- `FiniteWeightedNorm` → `RadiiPolynomial.FiniteWeightedNorm`
- `DiscreteConvolution` left standalone (pure Mathlib-level, no project deps)
- Created root `RadiiPolynomial.lean` import file

### 4. TBC integration

12 files from `exterior/TBC/` copied into project:
- `source/IVP/Setup.lean`, `source/IVP/Test.lean` — generic IVP infrastructure
- `source/Tactic/AutoPolyFDeriv.lean`, `source/Tactic/FinMatrixBound.lean` — tactics
- `source/MvPolyBridge/Basic.lean` — multivariate polynomial bridge
- `examples/Example83/`, `examples/Example77/`, `examples/Example245/` — examples

All imports updated from old paths (`RadiiPolynomial.SystemTaylorODE.*`) to new paths
(`RadiiPolynomial.source.*`, `RadiiPolynomial.examples.*`).

### 5. IVP bridge lemmas (`examples/Example83/Algebra.lean`)

Added bridge lemmas connecting equation-specific `F_coeffs`/`G_lorenz` to
the generic `IVP.ivpCoeffs`/`IVP.ivpMap` API:

```lean
lemma F_coeffs_eq_ivpCoeffs (a l n) :
    F_coeffs a l n = IVP.ivpCoeffs φ_lorenz x₀ a l n := by rfl

lemma G_lorenz_coeff_ivp (a l n) :
    l1Weighted.toSeq (G_lorenz a l) n =
      approxInverse.action (IVP.ivpCoeffs φ_lorenz x₀ a) l n
```

Also fixed: `YOmega` type alias (deleted earlier, inlined), `mem_deriv_shift_sub`
rename, `lpWeightedDeriv` import, `PosReal` coercion proofs.

### 6. Certificate.lean rewrite: 727 → 293 lines (60% reduction)

| Section | Before | After | Method |
|---------|--------|-------|--------|
| Z₀ + ‖A‖ | 81 | 81 | Already clean (`finmatrix_bound`) |
| Y₀ | 208 | 42 | ℚ bridges moved to Algebra |
| ābar norms | 27 | 0 | Moved to Algebra |
| Z₁ | 104 | 79 | `IVP.ivp_Z₁_le` |
| Z₂ | 280 | 55 | `IVP.ivp_Z₂_le` |
| Radii + main | 27 | 27 | Unchanged |

**Z₂ was the biggest win** (280 → 55 lines): the generic `IVP.ivp_Z₂_le` absorbs
the entire manual proof — constructing the auxiliary `w : XL1`, proving the
factorization `fderiv_diff(G)(h) = A.toCLM(w)`, bounding `‖w‖`, and threading
through `norm_toCLM_component_le_restricted` with active sets. The certificate
now just provides the equation-specific `Dφ_diff_norm_le` (D²φ bound) and
the block norm evaluation via `native_decide`.

### 7. ℚ bridges moved to Algebra.lean

Moved from Certificate to Algebra (equation-specific but reusable):
- `σ_q`, `ρ_q_val`, `β_q`, `x₀_q` — ℚ parameter aliases
- `φ_lorenz_Q`, `F_coeffs_Q` — ℚ nonlinearity/coefficient mirrors
- `φ_lorenz_bridge`, `F_coeffs_bridge`, `abar_toSeq_eq` — cast bridges
- `φ_lorenz_abar_support`, `F_coeffs_abar_support`, `F_coeffs_abar_mem` — support bounds
- `abar_norm_0_le`, `abar_norm_1_le`, `abar_norm_2_le` — ābar component norms

## Architecture After Refactoring

```
source/
  lpSpace/           — weighted ℓ¹ spaces, norms, Cauchy product, Banach algebra
  BlockDiag/         — block-diagonal operators: Base (algebra), Concrete (CLM), Scalar (L=1)
  IVP/Setup.lean     — equation-independent IVP infrastructure (ivpCoeffs, ivpMap, Z₁/Y₀/Z₂)
  Tactic/            — custom tactics (AutoPolyFDeriv, FinMatrixBound)
  MvPolyBridge/      — multivariate polynomial bridge
  Core.lean          — canonical bounds (Y₀_norm, Z₀_norm, Z₁_norm, Z₂_norm)
  RadiiPolyGeneral   — Neumann series, Newton operator, fixed point theorems
  WitnessSpec.lean   — equation-independent bound reductions
  LeanCertEval.lean  — ℚ evaluators + correctness bridges

examples/
  Example83/         — Lorenz IVP (Algebra: equation defs + ℚ bridges; Certificate: bound proofs)
  Example77/         — scalar IVP
  Example245/        — algebraic example
```

## Certificate Structure After Refactoring

A certificate for a new IVP system needs to provide:

1. **Z₀** (~8 lines): `finmatrix_bound` on the defect block columns
2. **‖A‖** (~5 lines): `finmatrix_bound` on A's block columns
3. **Y₀** (~40 lines): evaluator wiring + `finsum_bound` per component
4. **Z₁** (~15 lines structural + ~50 lines Dφ bound):
   - `IVP.ivp_Z₁_le` with `hfin`/`htail` from Algebra
   - Equation-specific `Dφ_norm_le` (triangle + submultiplicativity)
5. **Z₂** (~15 lines structural + ~35 lines D²φ bound):
   - `IVP.ivp_Z₂_le` with active set + `hDφ_diff` + `native_decide`
   - Equation-specific `Dφ_diff_norm_le` (bilinear structure)
6. **Radii polynomial** (~5 lines): `fast_bound`
7. **Main theorem** (~10 lines): `existsUnique` call

The equation-specific parts (Dφ bound, D²φ bound) are irreducible — they depend
on the polynomial structure of the specific nonlinearity. Everything else is generic.

### 8. Dead code cleanup

After wiring Certificate to `IVP.ivp_Z₁_le`, the `Z₁_le` wrapper in Algebra.lean
became dead (Certificate calls `IVP.ivp_Z₁_le` directly). Deleted.

Also confirmed `Example77/Algebra.lean` had a stale reference to
`l1Weighted.finWeightedMatrixNorm` → fixed to `FiniteWeightedNorm.finWeightedMatrixNorm`.

## Remaining Issues

- The `sorry` at `source/BlockDiag/Concrete.lean:994`
  (`finite_block_injective_of_defect_norm_lt_one`) is pre-existing.
- Namespace rename should eventually be followed by removing the `source/` path prefix
  (restructuring the folder hierarchy to match the namespace hierarchy directly).
- The ℚ bridge boilerplate in Algebra.lean (~100 lines of `φ_lorenz_Q`, `F_coeffs_Q`,
  `φ_lorenz_bridge`, `F_coeffs_bridge`) is equation-specific but follows a mechanical
  pattern. A future `ivpCoeffsQ` + generic bridge lemma could reduce this further.
