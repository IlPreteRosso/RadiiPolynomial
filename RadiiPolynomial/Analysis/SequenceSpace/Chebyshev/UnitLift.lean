import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Symmetrize
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The bilateral weighted algebra is free on a weight-dominated unit

For a unit `u : Bˣ` whose integer powers satisfy `‖uᵏ‖ ≤ C ν^|k|`,
`lpOneAlg.geomUnitLift` is the continuous algebra homomorphism from the bilateral geometric
carrier. `geomUnitLift_apply`, `geomUnitLift_single`, `geomUnitLift_gen` and
`norm_geomUnitLift_apply_le` specify its series, atom computation and bound.
`bilateralAlgHom_ext` gives uniqueness from the generator, and `eq_geomUnitLift_gen`
identifies every such homomorphism with the lift of its unit `genUnit`, using
`norm_genUnit_zpow_le`.

The shipped complex evaluation of the real carrier is `l1Chebyshev.evalLaurentC`, with
`evalLaurentC_apply`, `evalLaurentC_single` and `norm_evalLaurentC_apply_le`.
`evalLaurentC_circle` places the unit circle in the annulus when `1 ≤ ν`.
The additional annulus classification inequalities, general Laurent evaluator and symmetry/
reality laws belong to the recovery module `B5RecordLaurentSpectrum`. They are not the
shipped universal-property surface. The retained domination lemmas `unit_zpow_le_weight`
and `norm_unit_zpow_le` do not impose `Fact (1 ≤ ν)`.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

/-! ### Domination: integer powers of a unit against the bilateral weight -/

section Domination

variable {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal)
variable {B : Type*} [NormedRing B]

/-- The growth hypothesis `‖uᵏ‖ ≤ C ν^|k|` on the integer powers of a unit,
rewritten against the fiber weights of `geomFiberZ 𝕜 ν` — the form the
algebra lift consumes. -/
theorem unit_zpow_le_weight (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs) (k : ℤ) :
    ‖((u ^ k : Bˣ) : B)‖ ≤ C * FiberTrivialization.weight (E := geomFiberZ 𝕜 ν) k := by
  rw [geomFiberZ_weight]
  exact hu k

variable [NormOneClass B]

/-- A unit bounded by `ν` on both sides has integer powers dominated by the
bilateral weight with constant `1`: `‖uᵏ‖ ≤ ν^|k|`. No `ν ≥ 1` is needed. -/
theorem norm_unit_zpow_le (u : Bˣ)
    (hu : ‖(u : B)‖ ≤ (ν : ℝ)) (hu' : ‖((u⁻¹ : Bˣ) : B)‖ ≤ (ν : ℝ)) (k : ℤ) :
    ‖((u ^ k : Bˣ) : B)‖ ≤ 1 * (ν : ℝ) ^ k.natAbs := by
  rw [one_mul]
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.natAbs_natCast, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact (norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) hu n)
  | negSucc n =>
    rw [Int.natAbs_negSucc, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    exact (norm_pow_le _ (n + 1)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hu' (n + 1))

end Domination

/-! ### Introduction: the lift of a weight-dominated unit -/

section UnitLift

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- **The bilateral algebra is free on a weight-dominated unit** (introduction
face). A unit `u : Bˣ` with `‖uᵏ‖ ≤ C ν^|k|` for all `k : ℤ` induces the
continuous algebra homomorphism `a ↦ ∑' k, aₖ • uᵏ` out of the bilateral
carrier, sending `e₁ ↦ u` and `e₋₁ ↦ u⁻¹`. -/
def geomUnitLift (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B :=
  liftAlgHom (fun k : ℤ => ((u ^ k : Bˣ) : B)) C (unit_zpow_le_weight ν u C hu)
    (by rw [zpow_zero, Units.val_one])
    (fun m n => by rw [zpow_add, Units.val_mul])

variable (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs)

theorem geomUnitLift_apply (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    geomUnitLift (𝕜 := 𝕜) ν u C hu a = ∑' k : ℤ, toRealSeq a k • ((u ^ k : Bˣ) : B) := rfl


/-- Computation face: the unit single at mode `k` goes to `uᵏ`. -/
@[simp] theorem geomUnitLift_single (k : ℤ) :
    geomUnitLift (𝕜 := 𝕜) ν u C hu (single k 1) = ((u ^ k : Bˣ) : B) :=
  liftAlgHom_single _ _ _ _ _ k

/-- The generator `e₁` goes to `u`. -/
theorem geomUnitLift_gen : geomUnitLift (𝕜 := 𝕜) ν u C hu (single 1 1) = (u : B) := by
  rw [geomUnitLift_single, zpow_one]


/-- Pointwise bound: `‖geomUnitLift (𝕜 := 𝕜) ν u C hu a‖ ≤ C ‖a‖`. -/
theorem norm_geomUnitLift_apply_le (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖geomUnitLift (𝕜 := 𝕜) ν u C hu a‖ ≤ C * ‖a‖ :=
  norm_liftAlgHom_apply_le _ _ _ _ _ a

end UnitLift

/-! ### Uniqueness on the generator alone -/

section Uniqueness

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- The generator value of a continuous algebra homomorphism out of the
bilateral carrier, as a unit: value `φ e₁`, inverse `φ e₋₁`
(forced by `e₁ * e₋₁ = 1 = e₋₁ * e₁`). -/
def genUnit (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) : Bˣ where
  val := φ (single 1 1)
  inv := φ (single (-1) 1)
  val_inv := by
    rw [← map_mul, single_mul_single, add_neg_cancel, mul_one, ← one_eq_single_zero,
      map_one]
  inv_val := by
    rw [← map_mul, single_mul_single, neg_add_cancel, mul_one, ← one_eq_single_zero,
      map_one]

@[simp] theorem genUnit_val (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    ((genUnit ν φ : Bˣ) : B) = φ (single 1 1) := rfl

@[simp] theorem genUnit_inv_val (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    (((genUnit ν φ)⁻¹ : Bˣ) : B) = φ (single (-1) 1) := rfl

/-- Every unit single is an integer power of the generator value: the atom
family of `φ` is `k ↦ (genUnit φ)ᵏ`. -/
theorem continuousAlgHom_single_zpow (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) (k : ℤ) :
    φ (single k 1) = ((genUnit ν φ ^ k : Bˣ) : B) := by
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, genUnit_val,
      ← map_pow, single_pow, nsmul_eq_mul, mul_one]
  | negSucc n =>
    have hns : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hns, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, genUnit_inv_val,
      ← map_pow, single_pow, nsmul_eq_mul, mul_neg_one]

/-- **Determination on the generator** (uniqueness face): two continuous
algebra homomorphisms out of the bilateral carrier agreeing on `e₁` are
equal. The value at `e₋₁` is forced (it is the inverse of the value at `e₁`),
and every other single is a power of `e₁` or of `e₋₁`. -/
theorem bilateralAlgHom_ext ⦃φ ψ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B⦄
    (h : φ (single 1 1) = ψ (single 1 1)) : φ = ψ := by
  have hu : genUnit ν φ = genUnit ν ψ := Units.ext h
  refine continuousAlgHom_ext fun k => ?_
  rw [continuousAlgHom_single_zpow ν φ k, continuousAlgHom_single_zpow ν ψ k, hu]

end Uniqueness

/-! ### Completeness: every continuous algebra homomorphism is a unit lift -/

section Completeness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal)
  [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- The generator value of a continuous algebra homomorphism is weight-dominated
at the operator norm: `‖(φ e₁)ᵏ‖ ≤ ‖φ‖ ν^|k|` for every `k : ℤ`, both signs. -/
theorem norm_genUnit_zpow_le (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) (k : ℤ) :
    ‖((genUnit ν φ ^ k : Bˣ) : B)‖
      ≤ ‖φ.toContinuousLinearMap‖ * (ν : ℝ) ^ k.natAbs := by
  rw [← continuousAlgHom_single_zpow]
  have h := φ.toContinuousLinearMap.le_opNorm (single k 1)
  rwa [lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul] at h

variable [CompleteSpace B]

/-- **Every continuous algebra homomorphism out of the bilateral carrier is
the lift of its generator value** (completeness face): `φ = geomUnitLift ν
(genUnit φ) ‖φ‖ _`. This is "characters are Laurent evaluations" (as the series
`a ↦ ∑' k, aₖ (φ e₁)ᵏ`; the annulus bound on `φ e₁` is the gate section) for every
complete normed algebra `B` over every complete nontrivially normed field. -/
theorem eq_geomUnitLift_gen (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    φ = geomUnitLift ν (genUnit ν φ) ‖φ.toContinuousLinearMap‖ (norm_genUnit_zpow_le ν φ) :=
  bilateralAlgHom_ext ν (by rw [geomUnitLift_gen, genUnit_val])


end Completeness

/-! ### The gate: the generator value lies in the closed annulus `[ν⁻¹, ν]` -/

section Gate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal)
  [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra 𝕜 B]



end Gate

/-! ### Evaluation on the closed annulus -/

section Annulus

variable {K : Type*} [NormedField K] (ν : PosReal)

/-- A point of the closed annulus `ν⁻¹ ≤ ‖z‖ ≤ ν` is nonzero. -/
theorem ne_zero_of_annulus {z : K} (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) : z ≠ 0 :=
  norm_pos_iff.mp ((inv_pos.mpr ν.coe_pos).trans_le hz.1)

/-- The inverse of a point of the closed annulus is bounded by `ν`. -/
theorem norm_annulus_inv_le {z : K} (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    ‖(((Units.mk0 z (ne_zero_of_annulus ν hz))⁻¹ : Kˣ) : K)‖ ≤ (ν : ℝ) := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv]
  exact inv_le_of_inv_le₀ ν.coe_pos hz.1

/-- The annulus point as a unit of `K`, with the `C = 1` growth bound
`‖zᵏ‖ ≤ ν^|k|` on all its integer powers. -/
theorem norm_annulus_zpow_le {z : K} (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) (k : ℤ) :
    ‖((Units.mk0 z (ne_zero_of_annulus ν hz) ^ k : Kˣ) : K)‖ ≤ 1 * (ν : ℝ) ^ k.natAbs :=
  norm_unit_zpow_le ν _ (by rw [Units.val_mk0]; exact hz.2) (norm_annulus_inv_le ν hz) k

end Annulus

section EvalLaurent

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]


variable (z : 𝕜) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ))





end EvalLaurent

end lpOneAlg

/-! ### The real instance: `l1Chebyshev ν` -/

namespace l1Chebyshev

section RealInstance

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]


variable (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs)





end RealInstance

section RealGate

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra ℝ B]



end RealGate

/-! ### The real carrier evaluated into `ℂ`: Laurent evaluation and the circle

`evalLaurentC` is `geomUnitLift` at `𝕜 = ℝ`, `B = ℂ` — complex evaluation of
the REAL Chebyshev carrier, the consumer face of the analytic bridge. -/

section ComplexEvaluation

open Complex ComplexConjugate

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- **Complex Laurent evaluation of the real Chebyshev carrier** at a point
`z` of the closed annulus `ν⁻¹ ≤ ‖z‖ ≤ ν`: `a ↦ ∑' k, aₖ zᵏ`, a continuous
`ℝ`-algebra homomorphism `l1Chebyshev ν →A[ℝ] ℂ`. -/
def evalLaurentC (z : ℂ) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    l1Chebyshev ν →A[ℝ] ℂ :=
  lpOneAlg.geomUnitLift (𝕜 := ℝ) ν (Units.mk0 z (lpOneAlg.ne_zero_of_annulus ν hz)) 1
    (lpOneAlg.norm_annulus_zpow_le ν hz)

variable (z : ℂ) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ))

theorem evalLaurentC_apply (a : l1Chebyshev ν) :
    evalLaurentC ν z hz a = ∑' k : ℤ, ((lpOneAlg.toRealSeq a k : ℝ) : ℂ) * z ^ k := by
  rw [evalLaurentC, lpOneAlg.geomUnitLift_apply]
  exact tsum_congr fun k => by
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Complex.real_smul]

@[simp] theorem evalLaurentC_single (k : ℤ) :
    evalLaurentC ν z hz (single k 1) = z ^ k := by
  rw [evalLaurentC, lpOneAlg.geomUnitLift_single, Units.val_zpow_eq_zpow_val, Units.val_mk0]


/-- Contractivity: `‖∑ₖ aₖ zᵏ‖ ≤ ‖a‖` on the annulus. -/
theorem norm_evalLaurentC_apply_le (a : l1Chebyshev ν) :
    ‖evalLaurentC ν z hz a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_geomUnitLift_apply_le ν _ _ (lpOneAlg.norm_annulus_zpow_le ν hz) a
  rwa [one_mul] at h

/-- The unit circle lies in the closed annulus `[ν⁻¹, ν]`, using `1 ≤ ν`.
The additional conjugation and symmetry laws are in `B5RecordLaurentSpectrum`. -/
theorem evalLaurentC_circle (θ : ℝ) :
    (ν : ℝ)⁻¹ ≤ ‖exp (θ * I)‖ ∧ ‖exp (θ * I)‖ ≤ (ν : ℝ) := by
  rw [norm_exp_ofReal_mul_I]
  exact ⟨inv_le_one_of_one_le₀ Fact.out, Fact.out⟩






end ComplexEvaluation

end l1Chebyshev

end RadiiPolynomial

end
