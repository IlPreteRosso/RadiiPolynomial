import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The bilateral weighted algebra is free on a weight-dominated unit

`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` — the bilateral geometric carrier over any normed
field `𝕜`, whose `𝕜 = ℝ` instance is `l1Chebyshev ν` — receives exactly one
continuous algebra homomorphism into a Banach algebra `B` for every unit
`u : Bˣ` whose integer powers are dominated by the weight, `‖uᵏ‖ ≤ C ν^|k|`.
The three faces of this universal property, with the doctrine erased at proof
time (no exists-unique statements, no category theory):

* introduction `lpOneAlg.geomUnitLift ν u C hu : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B`,
  the algebra lift of the family `k ↦ uᵏ`, with `geomUnitLift_gen : e₁ ↦ u`,
  `geomUnitLift_gen_inv : e₋₁ ↦ u⁻¹` and `norm_geomUnitLift_apply_le`;
* uniqueness `lpOneAlg.bilateralAlgHom_ext` on the single generator `e₁`: the
  value at `e₋₁` is forced, being the two-sided inverse of the value at `e₁`
  (`e₁ * e₋₁ = 1`), and every other single is a power of one of the two;
* completeness `lpOneAlg.eq_geomUnitLift_gen`: every continuous algebra
  homomorphism out of the carrier is the lift of its generator value, read as
  the unit `lpOneAlg.genUnit φ` (value `φ e₁`, inverse `φ e₋₁`), at the operator
  norm of its underlying continuous linear map.

Gate: `lpOneAlg.norm_genUnit_le` and `lpOneAlg.inv_le_norm_genUnit` pin the
generator value of any continuous algebra homomorphism into a target with
multiplicative norm to the closed annulus `ν⁻¹ ≤ ‖φ e₁‖ ≤ ν` — the half of
the character classification the completeness face does not supply.

Evaluation faces: `lpOneAlg.evalLaurent ν z hz` is the bilateral power
evaluation `a ↦ ∑' k, aₖ zᵏ` at a point of the closed annulus
`ν⁻¹ ≤ ‖z‖ ≤ ν`, and `l1Chebyshev.evalLaurentC ν z hz` is the same map out of
the REAL carrier into `ℂ` (`𝕜 = ℝ`, `B = ℂ`; no complex carrier is built). On
the unit circle `z = exp(iθ)`, symmetric coefficient sequences evaluate to
real numbers (`l1Chebyshev.evalLaurentC_eq_re_of_isSymmetric`,
`evalLaurentC_symmetrize_eq_re`) — reality is exactly what is proved here, and
nothing more. Rewriting that real value as the cosine series
`a₀ + 2∑ₖ aₖ cos kθ` is G3.5 item 1, not in this file: it needs the ℤ→ℕ tsum
split. NOTE the plan's earlier identity
`evalLaurent z (symmetrize a) = re (evalLaurent z a)` is FALSE, because
`symmetrize` is the `|k|`-fold (`Bordered.lean:620`), not `(a + reflect a) / 2`.

Hygiene: `[Fact (1 ≤ (ν : ℝ))]` is exactly where the ring structure of the
bilateral carrier demands it (the bilateral weight `ν^|k|` is submultiplicative
iff `ν ≥ 1`), plus the one place it is mathematically needed — the unit circle
lies in the annulus `[ν⁻¹, ν]` (`evalLaurentC_circle`). The domination lemmas
`unit_zpow_le_weight` / `norm_unit_zpow_le` carry no `Fact`.

The exists-unique forms of these statements live in `tmp/ground_floor` (frozen).
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

/-! ### The bilateral geometric fiber over any normed field -/

/-- The bilateral geometric fiber over a normed field `𝕜`: `𝕜` with norm
`‖x‖ ν^|k|` at mode `k : ℤ`. Its real instance is `ScaledRealZ ν`
(definitionally), so `l1Chebyshev ν = lpOneAlg ℤ (geomFiberZ ℝ ν)`. -/
abbrev geomFiberZ (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal) :=
  WeightedScalar 𝕜 (fun k : ℤ => (ν : ℝ) ^ k.natAbs)

example (ν : PosReal) : ScaledRealZ ν = geomFiberZ ℝ ν := rfl

/-- The fiber weight of `geomFiberZ 𝕜 ν` at `k` is `ν^|k|`. -/
theorem geomFiberZ_weight {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal) (k : ℤ) :
    ‖lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)‖ = (ν : ℝ) ^ k.natAbs := by
  rw [show lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)
      = WeightedScalar.ofReal 1 from rfl, WeightedScalar.norm_ofReal,
    norm_one, one_mul]

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
    ‖((u ^ k : Bˣ) : B)‖ ≤ C * ‖lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)‖ := by
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

theorem geomUnitLift_toContinuousLinearMap :
    (geomUnitLift (𝕜 := 𝕜) ν u C hu).toContinuousLinearMap
      = liftCLM (fun k : ℤ => ((u ^ k : Bˣ) : B)) C (unit_zpow_le_weight ν u C hu) := rfl

/-- Computation face: the unit single at mode `k` goes to `uᵏ`. -/
@[simp] theorem geomUnitLift_single (k : ℤ) :
    geomUnitLift (𝕜 := 𝕜) ν u C hu (single k 1) = ((u ^ k : Bˣ) : B) :=
  liftAlgHom_single _ _ _ _ _ k

/-- The generator `e₁` goes to `u`. -/
@[simp] theorem geomUnitLift_gen : geomUnitLift (𝕜 := 𝕜) ν u C hu (single 1 1) = (u : B) := by
  rw [geomUnitLift_single, zpow_one]

/-- The co-generator `e₋₁` goes to `u⁻¹`. -/
theorem geomUnitLift_gen_inv :
    geomUnitLift (𝕜 := 𝕜) ν u C hu (single (-1) 1) = ((u⁻¹ : Bˣ) : B) := by
  rw [geomUnitLift_single, zpow_neg_one]

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
  rwa [norm_single, norm_one, one_mul, geomFiberZ_weight] at h

variable [CompleteSpace B]

/-- **Every continuous algebra homomorphism out of the bilateral carrier is
the lift of its generator value** (completeness face): `φ = geomUnitLift ν
(genUnit φ) ‖φ‖ _`. This is "characters are Laurent evaluations" for every
complete Banach algebra `B` over every nontrivially normed field. -/
theorem eq_geomUnitLift_gen (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    φ = geomUnitLift ν (genUnit ν φ) ‖φ.toContinuousLinearMap‖ (norm_genUnit_zpow_le ν φ) :=
  bilateralAlgHom_ext ν (by rw [geomUnitLift_gen, genUnit_val])

/-- Existential form of `eq_geomUnitLift_gen`. -/
theorem exists_eq_geomUnitLift (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    ∃ (u : Bˣ) (C : ℝ) (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs),
      φ = geomUnitLift ν u C hu :=
  ⟨_, _, _, eq_geomUnitLift_gen ν φ⟩

end Completeness

/-! ### The gate: the generator value lies in the closed annulus `[ν⁻¹, ν]` -/

section Gate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (ν : PosReal)
  [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra 𝕜 B]

/-- **Outer gate.** When the norm of the target is multiplicative, the image of
the generator under any continuous algebra homomorphism out of the bilateral
carrier satisfies `‖φ e₁‖ ≤ ν`: the nonnegative half of the weight domination
`‖(φ e₁)ᵏ‖ ≤ ‖φ‖ ν^|k|` (`norm_genUnit_zpow_le`), read through the archimedean
gate `le_of_forall_pow_le_mul_pow`. -/
theorem norm_genUnit_le (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    ‖φ (single 1 1)‖ ≤ (ν : ℝ) :=
  le_of_forall_pow_le_mul_pow ν.coe_pos fun n => by
    have h := norm_genUnit_zpow_le ν φ (n : ℤ)
    rwa [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow, Int.natAbs_natCast,
      genUnit_val] at h

/-- **Inner gate.** Dually, `ν⁻¹ ≤ ‖φ e₁‖`: the negative half of the weight
domination bounds the inverse `‖φ e₋₁‖ ≤ ν`, and `‖φ e₋₁‖ ‖φ e₁‖ = ‖1‖ = 1`
inverts it. Together with `norm_genUnit_le` this pins the generator value to
the closed annulus `ν⁻¹ ≤ ‖φ e₁‖ ≤ ν` — the half of the character
classification that `eq_geomUnitLift_gen` does not give. -/
theorem inv_le_norm_genUnit (φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] B) :
    (ν : ℝ)⁻¹ ≤ ‖φ (single 1 1)‖ := by
  have hlow : ‖(((genUnit ν φ)⁻¹ : Bˣ) : B)‖ ≤ (ν : ℝ) :=
    le_of_forall_pow_le_mul_pow ν.coe_pos fun n => by
      have h := norm_genUnit_zpow_le ν φ (-(n : ℤ))
      rwa [zpow_neg, ← inv_zpow, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow,
        Int.natAbs_neg, Int.natAbs_natCast] at h
  have hone : ‖(((genUnit ν φ)⁻¹ : Bˣ) : B)‖ * ‖φ (single 1 1)‖ = 1 := by
    rw [← genUnit_val ν φ, ← norm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      norm_one]
  refine le_of_mul_le_mul_left ?_ ν.coe_pos
  rw [mul_inv_cancel₀ ν.coe_pos.ne', ← hone]
  exact mul_le_mul_of_nonneg_right hlow (norm_nonneg _)

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

/-- **Bilateral power evaluation** at a point `z` of the closed annulus
`ν⁻¹ ≤ ‖z‖ ≤ ν`: the character `a ↦ ∑' k, aₖ zᵏ` of the bilateral carrier,
`geomUnitLift` at the unit `z` with constant `1`. -/
def evalLaurent (z : 𝕜) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →A[𝕜] 𝕜 :=
  geomUnitLift ν (Units.mk0 z (ne_zero_of_annulus ν hz)) 1 (norm_annulus_zpow_le ν hz)

variable (z : 𝕜) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ))

theorem evalLaurent_apply (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    evalLaurent ν z hz a = ∑' k : ℤ, toRealSeq a k * z ^ k := by
  rw [evalLaurent, geomUnitLift_apply]
  exact tsum_congr fun k => by
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, smul_eq_mul]

@[simp] theorem evalLaurent_single (k : ℤ) : evalLaurent ν z hz (single k 1) = z ^ k := by
  rw [evalLaurent, geomUnitLift_single, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- The generator `e₁` evaluates to `z`. -/
@[simp] theorem evalLaurent_gen : evalLaurent ν z hz (single 1 1) = z := by
  rw [evalLaurent_single, zpow_one]

/-- Contractivity of the Laurent evaluation on the annulus: `‖∑ₖ aₖ zᵏ‖ ≤ ‖a‖`. -/
theorem norm_evalLaurent_apply_le (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖evalLaurent ν z hz a‖ ≤ ‖a‖ := by
  have h := norm_geomUnitLift_apply_le ν _ _ (norm_annulus_zpow_le ν hz) a
  rwa [one_mul] at h

end EvalLaurent

end lpOneAlg

/-! ### The real instance: `l1Chebyshev ν` -/

namespace l1Chebyshev

section RealInstance

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- The Chebyshev bilateral algebra is free on a weight-dominated unit:
`lpOneAlg.geomUnitLift` at `𝕜 = ℝ`. -/
abbrev unitLift (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs) :
    l1Chebyshev ν →A[ℝ] B :=
  lpOneAlg.geomUnitLift (𝕜 := ℝ) ν u C hu

variable (u : Bˣ) (C : ℝ)
    (hu : ∀ k : ℤ, ‖((u ^ k : Bˣ) : B)‖ ≤ C * (ν : ℝ) ^ k.natAbs)

theorem unitLift_gen : unitLift ν u C hu (single 1 1) = (u : B) :=
  lpOneAlg.geomUnitLift_gen ν u C hu

theorem unitLift_gen_inv : unitLift ν u C hu (single (-1) 1) = ((u⁻¹ : Bˣ) : B) :=
  lpOneAlg.geomUnitLift_gen_inv ν u C hu

theorem norm_unitLift_apply_le (a : l1Chebyshev ν) : ‖unitLift ν u C hu a‖ ≤ C * ‖a‖ :=
  lpOneAlg.norm_geomUnitLift_apply_le ν u C hu a

omit [CompleteSpace B] in
/-- Uniqueness on `e₁` for the Chebyshev bilateral algebra. -/
theorem algHom_ext ⦃φ ψ : l1Chebyshev ν →A[ℝ] B⦄
    (h : φ (single 1 1) = ψ (single 1 1)) : φ = ψ :=
  lpOneAlg.bilateralAlgHom_ext ν h

/-- Completeness for the Chebyshev bilateral algebra: every continuous
algebra homomorphism is the unit lift of its generator value. -/
theorem eq_unitLift_gen (φ : l1Chebyshev ν →A[ℝ] B) :
    φ = unitLift ν (lpOneAlg.genUnit ν φ) ‖φ.toContinuousLinearMap‖
      (lpOneAlg.norm_genUnit_zpow_le ν φ) :=
  lpOneAlg.eq_geomUnitLift_gen ν φ

end RealInstance

section RealGate

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
variable {B : Type*} [NormedRing B] [NormOneClass B] [NormMulClass B] [NormedAlgebra ℝ B]

/-- Outer gate for the Chebyshev bilateral algebra: `‖φ e₁‖ ≤ ν`. -/
theorem norm_genUnit_le (φ : l1Chebyshev ν →A[ℝ] B) : ‖φ (single 1 1)‖ ≤ (ν : ℝ) :=
  lpOneAlg.norm_genUnit_le ν φ

/-- Inner gate for the Chebyshev bilateral algebra: `ν⁻¹ ≤ ‖φ e₁‖`. -/
theorem inv_le_norm_genUnit (φ : l1Chebyshev ν →A[ℝ] B) : (ν : ℝ)⁻¹ ≤ ‖φ (single 1 1)‖ :=
  lpOneAlg.inv_le_norm_genUnit ν φ

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

@[simp] theorem evalLaurentC_gen : evalLaurentC ν z hz (single 1 1) = z := by
  rw [evalLaurentC_single, zpow_one]

/-- Contractivity: `‖∑ₖ aₖ zᵏ‖ ≤ ‖a‖` on the annulus. -/
theorem norm_evalLaurentC_apply_le (a : l1Chebyshev ν) :
    ‖evalLaurentC ν z hz a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_geomUnitLift_apply_le ν _ _ (lpOneAlg.norm_annulus_zpow_le ν hz) a
  rwa [one_mul] at h

/-- The unit circle lies in the closed annulus `[ν⁻¹, ν]` — the one place
`1 ≤ ν` is used mathematically in this file. -/
theorem evalLaurentC_circle (θ : ℝ) :
    (ν : ℝ)⁻¹ ≤ ‖exp (θ * I)‖ ∧ ‖exp (θ * I)‖ ≤ (ν : ℝ) := by
  rw [norm_exp_ofReal_mul_I]
  exact ⟨inv_le_one_of_one_le₀ Fact.out, Fact.out⟩

/-- Real coefficients: conjugation passes through the evaluation to the point. -/
theorem conj_evalLaurentC (hz' : (ν : ℝ)⁻¹ ≤ ‖conj z‖ ∧ ‖conj z‖ ≤ (ν : ℝ))
    (a : l1Chebyshev ν) :
    conj (evalLaurentC ν z hz a) = evalLaurentC ν (conj z) hz' a := by
  rw [evalLaurentC_apply, evalLaurentC_apply, Complex.conj_tsum]
  exact tsum_congr fun k => by rw [map_mul, Complex.conj_ofReal, map_zpow₀]

/-- On a symmetric sequence (`a₋ₖ = aₖ`) the evaluation at `z⁻¹` equals the
evaluation at `z`: reindex `k ↦ -k`. -/
theorem evalLaurentC_inv_of_isSymmetric
    (hz' : (ν : ℝ)⁻¹ ≤ ‖z⁻¹‖ ∧ ‖z⁻¹‖ ≤ (ν : ℝ)) (a : l1Chebyshev ν) (ha : a.IsSymmetric) :
    evalLaurentC ν z⁻¹ hz' a = evalLaurentC ν z hz a := by
  rw [evalLaurentC_apply, evalLaurentC_apply]
  have hre : (∑' k : ℤ, ((lpOneAlg.toRealSeq a (-k) : ℝ) : ℂ) * z ^ (-k))
      = ∑' k : ℤ, ((lpOneAlg.toRealSeq a k : ℝ) : ℂ) * z ^ k :=
    (Equiv.neg ℤ).tsum_eq (fun k => ((lpOneAlg.toRealSeq a k : ℝ) : ℂ) * z ^ k)
  rw [← hre]
  exact tsum_congr fun k => by rw [ha k, zpow_neg, inv_zpow]

/-- On the unit circle, a symmetric sequence evaluates to a real number:
`conj (∑ₖ aₖ zᵏ) = ∑ₖ aₖ zᵏ` when `‖z‖ = 1` and `a₋ₖ = aₖ`. -/
theorem conj_evalLaurentC_of_isSymmetric (hz1 : ‖z‖ = 1) (a : l1Chebyshev ν)
    (ha : a.IsSymmetric) :
    conj (evalLaurentC ν z hz a) = evalLaurentC ν z hz a := by
  have hzinv : conj z = z⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz1, one_pow, inv_one,
      Complex.ofReal_one, mul_one]
  have hz' : (ν : ℝ)⁻¹ ≤ ‖z⁻¹‖ ∧ ‖z⁻¹‖ ≤ (ν : ℝ) := by
    rw [norm_inv, hz1, inv_one]; exact ⟨inv_le_one_of_one_le₀ Fact.out, Fact.out⟩
  have hc : (ν : ℝ)⁻¹ ≤ ‖conj z‖ ∧ ‖conj z‖ ≤ (ν : ℝ) := by
    rw [Complex.norm_conj]; exact hz
  rw [conj_evalLaurentC ν z hz hc a]
  have hcongr : ∀ (w₁ w₂ : ℂ) (h : w₁ = w₂) (h₁ : (ν : ℝ)⁻¹ ≤ ‖w₁‖ ∧ ‖w₁‖ ≤ (ν : ℝ))
      (h₂ : (ν : ℝ)⁻¹ ≤ ‖w₂‖ ∧ ‖w₂‖ ≤ (ν : ℝ)),
      evalLaurentC ν w₁ h₁ a = evalLaurentC ν w₂ h₂ a := by
    intro w₁ w₂ h h₁ h₂; subst h; rfl
  rw [hcongr (conj z) z⁻¹ hzinv hc hz']
  exact evalLaurentC_inv_of_isSymmetric ν z hz hz' a ha

/-- On the unit circle a symmetric sequence evaluates to (the complex cast of)
its real part. -/
theorem evalLaurentC_eq_re_of_isSymmetric (hz1 : ‖z‖ = 1) (a : l1Chebyshev ν)
    (ha : a.IsSymmetric) :
    evalLaurentC ν z hz a = ((evalLaurentC ν z hz a).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (conj_evalLaurentC_of_isSymmetric ν z hz hz1 a ha)).symm

/-- **The symmetrize bridge**: on the circle `z = exp(iθ)`, the evaluation of
`symmetrize a` (coefficients `a_{|k|}`) is a real number — that, and only that,
is what this lemma proves: the value equals the complex cast of its own real
part.

The cosine-series identity is G3.5 item 1 (needs the ℤ→ℕ tsum split); NOTE the
plan's earlier identity `evalLaurent z (symmetrize a) = re (evalLaurent z a)`
is FALSE because `symmetrize` is the `|k|`-fold (`Bordered.lean:620`), not
`(a + reflect a) / 2`. -/
theorem evalLaurentC_symmetrize_eq_re (θ : ℝ) (a : l1Chebyshev ν) :
    evalLaurentC ν (exp (θ * I)) (evalLaurentC_circle ν θ) (symmetrize a)
      = ((evalLaurentC ν (exp (θ * I)) (evalLaurentC_circle ν θ) (symmetrize a)).re : ℂ) :=
  evalLaurentC_eq_re_of_isSymmetric ν _ _ (norm_exp_ofReal_mul_I θ) _
    (symmetrize_isSymmetric a)

end ComplexEvaluation

end l1Chebyshev

end RadiiPolynomial

end
