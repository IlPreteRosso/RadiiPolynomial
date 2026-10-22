import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic

/-!
# Evaluation and determination on the geometric weighted ℓ¹ algebra

For a normed scalar field `𝕜` and `ν > 0`, `geomFiber 𝕜 ν` gives the weights `νⁿ`.
In a complete normed `𝕜`-algebra `B`, a power-growth bound
`∀ n, ‖x ^ n‖ ≤ C * νⁿ` defines the continuous algebra homomorphism
`lpOneAlg.geomAeval 𝕜 ν x C hx`. Its series formula is `geomAeval_apply`; its
single and generator computations are `geomAeval_single` and `geomAeval_gen`.
The application bound comes from the generic `norm_liftAlgHom_apply_le`.

`geomAlgHom_ext` determines a continuous algebra homomorphism from its value on
the generator. Over a nontrivially normed field, `norm_gen_pow_le` supplies the
power-growth bound at the map's operator norm, and `eq_geomAeval_gen` recovers
the map as the corresponding evaluation.

When the target has `NormOneClass`, `‖x‖ ≤ ν` suffices at `C = 1`:
`geomAeval_of_norm_le` and `norm_geomAeval_of_norm_le_apply_le` give this
specialization. The real-coefficient faces are `l1Weighted.aeval_of_norm_le`
and `l1Weighted.algHom_ext`. General targets are covered by `geomAeval`;
the tests in `Examples/tests/WL/GeneralTargetAeval` exercise the
`C = max 1 ‖1‖` construction without a norm-one hypothesis.

`Geometric/Evaluation` identifies the real evaluation arrow with the coordinate power series.
-/

noncomputable section

namespace RadiiPolynomial

/-- The geometric fiber over a normed field `𝕜`: `𝕜` with norm `‖x‖ νⁿ` at
index `n`. `ScaledReal ν = geomFiber ℝ ν` definitionally. -/
abbrev geomFiber (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal) :=
  WeightedScalar 𝕜 (fun n : ℕ => (ν : ℝ) ^ n)

section Fiber

variable {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal)

/-- The weight of the geometric fiber at `n` is `νⁿ`. -/
theorem geomFiber_weight (n : ℕ) :
    FiberTrivialization.weight (E := geomFiber 𝕜 ν) n = (ν : ℝ) ^ n :=
  WeightedScalar.fiberTrivialization_weight n

example : ScaledReal ν = geomFiber ℝ ν := rfl

example : l1Weighted ν = lpOneAlg ℕ (geomFiber ℝ ν) := rfl

end Fiber

namespace lpOneAlg

/-! ### Introduction: evaluation at an element of power growth -/

section Aeval

variable (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

omit [NormedAlgebra 𝕜 B] [CompleteSpace B] in
/-- Power growth `‖xⁿ‖ ≤ C νⁿ` is domination by the geometric weight. -/
theorem pow_le_geomFiber_weight (x : B) (C : ℝ)
    (hx : ∀ n, ‖x ^ n‖ ≤ C * (ν : ℝ) ^ n) (n : ℕ) :
    ‖x ^ n‖ ≤ C * FiberTrivialization.weight (E := geomFiber 𝕜 ν) n := by
  rw [geomFiber_weight]
  exact hx n

/-- **Evaluation at an element of power growth** (introduction face): for
`x : B` with `‖xⁿ‖ ≤ C νⁿ`, the continuous algebra homomorphism
`a ↦ ∑' n, aₙ • xⁿ` out of the geometric ℓ¹ algebra. -/
def geomAeval (x : B) (C : ℝ) (hx : ∀ n, ‖x ^ n‖ ≤ C * (ν : ℝ) ^ n) :
    lpOneAlg ℕ (geomFiber 𝕜 ν) →A[𝕜] B :=
  liftAlgHom (fun n => x ^ n) C (pow_le_geomFiber_weight 𝕜 ν x C hx) (pow_zero x)
    (pow_add x)

variable (x : B) (C : ℝ) (hx : ∀ n, ‖x ^ n‖ ≤ C * (ν : ℝ) ^ n)

theorem geomAeval_apply (a : lpOneAlg ℕ (geomFiber 𝕜 ν)) :
    geomAeval 𝕜 ν x C hx a = ∑' n, toRealSeq a n • x ^ n := rfl



/-- Computation face on every single: `eₙ ↦ xⁿ`. -/
@[simp] theorem geomAeval_single (n : ℕ) :
    geomAeval 𝕜 ν x C hx (single n 1) = x ^ n :=
  liftAlgHom_single _ _ _ _ _ n

/-- Computation face on the generator: `e₁ ↦ x`. -/
@[simp] theorem geomAeval_gen : geomAeval 𝕜 ν x C hx (single 1 1) = x := by
  rw [geomAeval_single, pow_one]

omit [NormedAlgebra 𝕜 B] [CompleteSpace B] in
/-- In a `NormOneClass` target, `‖x‖ ≤ ν` gives power growth at `C = 1`. -/
theorem pow_le_of_norm_le [NormOneClass B] {x : B} (hx : ‖x‖ ≤ (ν : ℝ)) (n : ℕ) :
    ‖x ^ n‖ ≤ 1 * (ν : ℝ) ^ n := by
  rw [one_mul]
  exact (norm_pow_le x n).trans (pow_le_pow_left₀ (norm_nonneg x) hx n)

/-- Evaluation at an element of norm at most `ν` (the `C = 1` case; the
`NormOneClass` hypothesis is what makes `n = 0` work). -/
def geomAeval_of_norm_le [NormOneClass B] (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) :
    lpOneAlg ℕ (geomFiber 𝕜 ν) →A[𝕜] B :=
  geomAeval 𝕜 ν x 1 (pow_le_of_norm_le ν hx)

@[simp] theorem geomAeval_of_norm_le_gen [NormOneClass B] (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) :
    geomAeval_of_norm_le 𝕜 ν x hx (single 1 1) = x :=
  geomAeval_gen 𝕜 ν x 1 _

/-- Contractivity of evaluation at a point of norm at most `ν`. -/
theorem norm_geomAeval_of_norm_le_apply_le [NormOneClass B] (x : B) (hx : ‖x‖ ≤ (ν : ℝ))
    (a : lpOneAlg ℕ (geomFiber 𝕜 ν)) :
    ‖geomAeval_of_norm_le 𝕜 ν x hx a‖ ≤ ‖a‖ := by
  have h := norm_liftAlgHom_apply_le (fun n => x ^ n) 1
    (pow_le_geomFiber_weight 𝕜 ν x 1 (pow_le_of_norm_le ν hx)) (pow_zero x) (pow_add x) a
  rwa [one_mul] at h





end Aeval

/-! ### Uniqueness: determination on the generator -/

section Ext

variable {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal)

/-- Powers of the generator are the singles: `e₁ⁿ = eₙ`. -/
theorem gen_pow_eq_single (n : ℕ) :
    (single (E := geomFiber 𝕜 ν) 1 (1 : 𝕜)) ^ n = single n 1 := by
  rw [single_pow, smul_eq_mul, mul_one]


variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- **Determination on the generator** (uniqueness face): two continuous
algebra homomorphisms out of the geometric ℓ¹ algebra agreeing on `e₁` are
equal. -/
theorem geomAlgHom_ext ⦃φ ψ : lpOneAlg ℕ (geomFiber 𝕜 ν) →A[𝕜] B⦄
    (h : φ (single 1 1) = ψ (single 1 1)) : φ = ψ :=
  continuousAlgHom_ext fun n => by rw [← gen_pow_eq_single, map_pow, map_pow, h]

end Ext

/-! ### Completeness: every continuous algebra homomorphism is an evaluation -/

section Complete

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- The image of the generator under a continuous algebra homomorphism has
power growth at the operator norm: `‖(φ e₁)ⁿ‖ ≤ ‖φ‖ νⁿ`. -/
theorem norm_gen_pow_le (φ : lpOneAlg ℕ (geomFiber 𝕜 ν) →A[𝕜] B) (n : ℕ) :
    ‖φ (single 1 1) ^ n‖ ≤ ‖φ.toContinuousLinearMap‖ * (ν : ℝ) ^ n := by
  rw [← map_pow, gen_pow_eq_single]
  have h := φ.toContinuousLinearMap.le_opNorm (single n 1)
  rwa [norm_single, norm_one, one_mul, geomFiber_weight] at h

variable [CompleteSpace B]

/-- **Every continuous algebra homomorphism is evaluation at the image of the
generator** (completeness face), at the growth constant
`‖φ.toContinuousLinearMap‖` (`ContinuousAlgHom` carries no norm of its own). -/
theorem eq_geomAeval_gen (φ : lpOneAlg ℕ (geomFiber 𝕜 ν) →A[𝕜] B) :
    φ = geomAeval 𝕜 ν (φ (single 1 1)) ‖φ.toContinuousLinearMap‖ (norm_gen_pow_le ν φ) :=
  geomAlgHom_ext ν (by rw [geomAeval_gen])


end Complete

/-! ### The gate: the generator value lies in the closed disc of radius `ν` -/

section Gate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra 𝕜 B]


end Gate

end lpOneAlg

/-! ### The real carrier instance `l1Weighted ν` -/

namespace l1Weighted

section Aeval

variable (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]


variable (x : B) (C : ℝ) (hx : ∀ n, ‖x ^ n‖ ≤ C * (ν : ℝ) ^ n)





/-- Evaluation at an element of norm at most `ν` (`C = 1`). -/
def aeval_of_norm_le [NormOneClass B] (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) :
    l1Weighted ν →A[ℝ] B :=
  lpOneAlg.geomAeval_of_norm_le ℝ ν x hx

@[simp] theorem aeval_of_norm_le_gen [NormOneClass B] (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) :
    aeval_of_norm_le ν x hx (lpOneAlg.single 1 1) = x :=
  lpOneAlg.geomAeval_of_norm_le_gen ℝ ν x hx





end Aeval

section Ext

variable (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- Determination on the generator for `l1Weighted ν`. -/
theorem algHom_ext ⦃φ ψ : l1Weighted ν →A[ℝ] B⦄
    (h : φ (lpOneAlg.single 1 1) = ψ (lpOneAlg.single 1 1)) : φ = ψ :=
  lpOneAlg.geomAlgHom_ext ν h

variable [CompleteSpace B]


end Ext

section Gate

variable (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra ℝ B]


end Gate


end l1Weighted



end RadiiPolynomial

end
