import RadiiPolynomial.Operators.BlockDiagonal.Basic

/-!
# Block-Diagonal Lift Typeclass

Abstract interface for the composed approximate derivative `id - defect` on a real normed
space `X` (no completeness is assumed): `X` carries, for every `D : SystemBlockDiagData L N`,
a linear defect action `liftDefect D : X → X` bounded by `finiteBlockMatrixNorm ν D.finBlock`.
From these data alone one gets the CLM `composedApproxCLM D` and its Z₀ bound.

The class does not enforce a coefficient representation: nothing ties `liftDefect D` to
`D.actionFinite`, and the zero lift (`liftDefect D x = 0`) satisfies every field. The
coefficient meaning lives in the instances: Taylor (`XL1 = Fin L → l1Weighted ν`,
`instBlockDiagLiftXL1`) applies `D.actionFinite` to `toCoeff x` and re-embeds the result;
Chebyshev (`XCheb = Fin L → l1Chebyshev ν`, `instBlockDiagLiftXCheb`) does the same on the
ℕ-coefficients of a ℤ-indexed sequence. On `XL1` the equality bridge
`SystemBlockDiagData.composedApprox_toCLM_eq_lift` identifies the generic construction with the
concrete `composedApprox`.

## Main definitions

- `BlockDiagLift`: typeclass providing `liftDefect` with linearity and the norm bound
- `BlockDiagLift.composedApproxCLM`: generic composed approximate derivative (id - defect)
- `BlockDiagLift.composedApprox_Z₀`: generic Z₀ bound

The typeclass does not require a ring/algebra structure on `X`, and the truncation level `N`
is not a class parameter: the same space supports every truncation level.
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal} {L : ℕ}

/-- A norm-bounded linear defect action of `SystemBlockDiagData L N` on a real normed space
`X` (no completeness is assumed), for every truncation level `N`.

The fields are the action `liftDefect`, its additivity and homogeneity, and the bound
`‖liftDefect D x‖ ≤ finiteBlockMatrixNorm ν D.finBlock * ‖x‖`. They do not relate
`liftDefect D` to `D.actionFinite` or to any coefficient map, and the zero action satisfies them;
the coefficient meaning is supplied by each instance (see the module docstring).

From these, generic `composedApproxCLM` and `composedApprox_Z₀` are derived. -/
class BlockDiagLift (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : ℕ) [NeZero L] (ν : PosReal) where
  /-- The defect action of `D` on `X`. In the Taylor and Chebyshev instances: `D.actionFinite`
  applied to the coefficients of the argument and re-embedded into `X` (zero on tail modes
  `n > N`); the class itself imposes only linearity and the norm bound. -/
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

Built directly via `LinearMap.mkContinuous` from the unbundled `liftDefect`, without a bundled
defect CLM, to avoid elaboration timeouts on deeply-nested `lpOneAlg` types. -/
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

/-- The zero action satisfies the `BlockDiagLift` axioms: the class imposes no coefficient law. -/
example (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NeZero L] :
    BlockDiagLift X L ν where
  liftDefect _ _ := 0
  liftDefect_add _ _ _ := (add_zero 0).symm
  liftDefect_smul _ r _ := (smul_zero r).symm
  liftDefect_norm_le _ x := by
    rw [norm_zero]; exact mul_nonneg (finiteBlockMatrixNorm_nonneg _) (norm_nonneg x)

end RadiiPolynomial

end
