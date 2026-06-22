import RadiiPolynomial.source.BlockDiag.Base

/-!
# Block-Diagonal Lift Typeclass

Abstracts the bridge between a concrete system Banach space `X` and the
ℕ-indexed coefficient space `SystemCoeff L`, enabling generic construction
of the composed approximate derivative CLM and Z₀ bound.

Both Taylor (`XL1 = Fin L → l1Weighted ν`) and Chebyshev (`XCheb = Fin L → l1Chebyshev ν`)
share the same `SystemBlockDiagData` structure operating on `SystemCoeff L`. They differ only
in how coefficients are extracted from `X` and how finite-rank results are embedded back.

## Main definitions

- `BlockDiagLift`: typeclass providing `extractCoeff` and `liftDefect`
- `BlockDiagLift.composedApproxCLM`: generic composed approximate derivative (id - defect)
- `BlockDiagLift.composedApprox_Z₀`: generic Z₀ bound

## Architecture

The typeclass does NOT require a ring/algebra structure on `X`. It only needs:
1. Coefficient extraction: `X → SystemCoeff L`
2. Finite block defect lift: `SystemBlockDiagData L N → X → X` (linear, norm-bounded)

The `N` parameter is NOT part of the typeclass — the same space supports any truncation level.
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal} {L : ℕ}

/-- Typeclass for Banach spaces that support lifting `SystemBlockDiagData`
finite block actions via coefficient extraction and re-embedding.

An instance provides:
- `extractCoeff`: project elements of `X` to ℕ-indexed `SystemCoeff L`
- `liftDefect`: apply `actionFinite` to extracted coefficients and embed result back into `X`
- Linearity and norm bound for `liftDefect`

From these, generic `composedApproxCLM` and `composedApprox_Z₀` are derived. -/
class BlockDiagLift (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : ℕ) [NeZero L] (ν : PosReal) where
  /-- Extract ℕ-indexed coefficient representation from system space element. -/
  extractCoeff : X → SystemCoeff L
  /-- Lift finite block action to X: apply `D.actionFinite` to extracted coefficients,
  re-embed result into X. The result is zero on tail modes (n > N). -/
  liftDefect : {N : ℕ} → SystemBlockDiagData L N → X → X
  /-- Additivity of lifted defect. -/
  liftDefect_add : ∀ {N : ℕ} (D : SystemBlockDiagData L N) (x y : X),
    liftDefect D (x + y) = liftDefect D x + liftDefect D y
  /-- Scalar homogeneity of lifted defect. -/
  liftDefect_smul : ∀ {N : ℕ} (D : SystemBlockDiagData L N) (r : ℝ) (x : X),
    liftDefect D (r • x) = r • liftDefect D x
  /-- Norm bound: `‖liftDefect D x‖ ≤ finiteBlockMatrixNorm(D.finBlock) * ‖x‖`. -/
  liftDefect_norm_le : ∀ {N : ℕ} (D : SystemBlockDiagData L N) (x : X),
    ‖liftDefect D x‖ ≤ finiteBlockMatrixNorm ν D.finBlock * ‖x‖

namespace BlockDiagLift

variable {N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NeZero L] [BlockDiagLift X L ν]

/-! ## Generic Constructions -/

private def composedApprox_lm (D : SystemBlockDiagData L N) :
    X →ₗ[ℝ] X where
  toFun h := h - liftDefect (ν := ν) D h
  map_add' h₁ h₂ := by rw [liftDefect_add (ν := ν)]; abel
  map_smul' r h := by rw [liftDefect_smul (ν := ν)]; simp [smul_sub]

private lemma composedApprox_bound (D : SystemBlockDiagData L N) (h : X) :
    ‖composedApprox_lm (ν := ν) D h‖ ≤
      (1 + finiteBlockMatrixNorm ν D.finBlock) * ‖h‖ := by
  refine (norm_sub_le h _).trans ?_
  rw [add_mul, one_mul]
  exact add_le_add le_rfl (liftDefect_norm_le (ν := ν) D h)

/-- The composed approximate derivative as a CLM on X: `h ↦ h - liftDefect D h`.

Built directly via `LinearMap.mkContinuous` (not `id - defectCLM`) to avoid
elaboration timeouts on deeply-nested `lpOneAlg` types. -/
def composedApproxCLM (D : SystemBlockDiagData L N) : X →L[ℝ] X :=
  LinearMap.mkContinuous (composedApprox_lm (ν := ν) D)
    (1 + finiteBlockMatrixNorm ν D.finBlock) (composedApprox_bound (ν := ν) D)

@[simp] lemma composedApproxCLM_apply (D : SystemBlockDiagData L N) (h : X) :
    composedApproxCLM (ν := ν) D h = h - liftDefect (ν := ν) D h := rfl

/-- Z₀ bound: `‖id - composedApproxCLM D‖ ≤ Z₀`.

Since `(id - composedApprox)(h) = h - (h - defect(h)) = defect(h)`,
the operator norm equals `‖defect‖ ≤ finiteBlockMatrixNorm(D.finBlock)`. -/
lemma composedApprox_Z₀ (D : SystemBlockDiagData L N)
    {Z₀ : ℝ} (hZ₀ : finiteBlockMatrixNorm ν D.finBlock ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ X - composedApproxCLM (ν := ν) D‖ ≤ Z₀ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (le_trans (finiteBlockMatrixNorm_nonneg (ν := ν) _) hZ₀) fun x => ?_
  rw [sub_apply, ContinuousLinearMap.id_apply,
    composedApproxCLM_apply, sub_sub_cancel]
  exact (liftDefect_norm_le (ν := ν) D x).trans
    (mul_le_mul_of_nonneg_right hZ₀ (norm_nonneg x))

end BlockDiagLift

end RadiiPolynomial

end
