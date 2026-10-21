import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Carrier
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Complex.Norm

/-! Bounded convolution X₂×X₂→Y at ν≥1. Absolute convergence uses complete scalars; operator-norm packaging uses nontrivially normed scalars. No product X₂×X₂→X₂ or convolution ring on X₂ is asserted. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

section RawAndMagnitudes

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- The raw product coefficient `∑' j, coeff x j * coeff y (k - j)` of `x, y ∈ X₂ 𝕜 ν` at `k`
(a `tsum`: `0` when the series is not summable). -/
def convCoeff (x y : X₂ 𝕜 ν) (k : ℤ) : 𝕜 := ∑' j : ℤ, coeff x j * coeff y (k - j)

/-- The raw product coefficient is symmetric (reindexing by the reflection `j ↦ k - j`). -/
theorem convCoeff_comm (x y : X₂ 𝕜 ν) (k : ℤ) : convCoeff x y k = convCoeff y x k :=
  ((Equiv.subLeft k).tsum_eq fun j => coeff x j * coeff y (k - j)).symm.trans <|
    tsum_congr fun j => by
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      exact mul_comm _ _

/-- The raw product coefficient is homogeneous in the left factor. -/
theorem convCoeff_smul_left (c : 𝕜) (x y : X₂ 𝕜 ν) (k : ℤ) :
    convCoeff (c • x) y k = c * convCoeff x y k := by
  simp only [convCoeff, coeff_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

/-- The raw product coefficient is homogeneous in the right factor. -/
theorem convCoeff_smul_right (c : 𝕜) (x y : X₂ 𝕜 ν) (k : ℤ) :
    convCoeff x (c • y) k = c * convCoeff x y k := by
  simp only [convCoeff, coeff_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => mul_left_comm _ _ _

/-- **Cauchy–Schwarz on the normalized magnitudes**: the products
`(‖coeff x j‖ * ν ^ |j|) * (‖coeff y (k - j)‖ * ν ^ |k - j|)` are summable with sum at most
`‖x‖ * ‖y‖` (Hölder at `(2, 2)` on the fibre-norm families, the second one reindexed by
`j ↦ k - j`). -/
theorem summable_and_tsum_normMag_mul_le (x y : X₂ 𝕜 ν) (k : ℤ) :
    (Summable fun j : ℤ => (‖coeff x j‖ * (ν : ℝ) ^ j.natAbs) *
        (‖coeff y (k - j)‖ * (ν : ℝ) ^ (k - j).natAbs)) ∧
      ∑' j : ℤ, (‖coeff x j‖ * (ν : ℝ) ^ j.natAbs) *
        (‖coeff y (k - j)‖ * (ν : ℝ) ^ (k - j).natAbs) ≤ ‖x‖ * ‖y‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_ofNat]
    exact .two_two
  simp only [← norm_apply_X₂]
  obtain ⟨C, -, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg x)
    (norm_nonneg y) (f := fun j => ‖x j‖) (g := fun j => ‖y (k - j)‖)
    (fun j => norm_nonneg _) (fun j => norm_nonneg _)
    (lp.hasSum_norm hpq.pos x) ((Equiv.subLeft k).hasSum_iff.2 (lp.hasSum_norm hpq.symm.pos y))
  exact ⟨hs.summable, hs.tsum_eq.trans_le hC⟩

/-- The products of normalized magnitudes along the reflection `j ↦ k - j` are summable. -/
theorem summable_normMag_mul (x y : X₂ 𝕜 ν) (k : ℤ) :
    Summable fun j : ℤ => (‖coeff x j‖ * (ν : ℝ) ^ j.natAbs) *
      (‖coeff y (k - j)‖ * (ν : ℝ) ^ (k - j).natAbs) :=
  (summable_and_tsum_normMag_mul_le x y k).1

/-- `∑' j, (‖coeff x j‖ * ν ^ |j|) * (‖coeff y (k - j)‖ * ν ^ |k - j|) ≤ ‖x‖ * ‖y‖`. -/
theorem tsum_normMag_mul_le (x y : X₂ 𝕜 ν) (k : ℤ) :
    ∑' j : ℤ, (‖coeff x j‖ * (ν : ℝ) ^ j.natAbs) *
      (‖coeff y (k - j)‖ * (ν : ℝ) ^ (k - j).natAbs) ≤ ‖x‖ * ‖y‖ :=
  (summable_and_tsum_normMag_mul_le x y k).2

end RawAndMagnitudes

section WeightBound

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))]

/-- **The weight triangle inequality on one product term** (`ν ≥ 1`):
`‖coeff x j * coeff y (k - j)‖ * ν ^ |k|` is at most the product of the normalized magnitudes
`(‖coeff x j‖ * ν ^ |j|) * (‖coeff y (k - j)‖ * ν ^ |k - j|)`. -/
theorem norm_conv_term_mul_le (x y : X₂ 𝕜 ν) (k j : ℤ) :
    ‖coeff x j * coeff y (k - j)‖ * (ν : ℝ) ^ k.natAbs ≤
      (‖coeff x j‖ * (ν : ℝ) ^ j.natAbs) * (‖coeff y (k - j)‖ * (ν : ℝ) ^ (k - j).natAbs) := by
  have h := ScaledRealZ.pow_natAbs_add_le ν Fact.out j (k - j)
  rw [add_sub_cancel] at h
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

end WeightBound

section ConvergentProduct

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))]

/-- The raw product series converges absolutely (`ν ≥ 1`). -/
theorem summable_conv_term (x y : X₂ 𝕜 ν) (k : ℤ) :
    Summable fun j : ℤ => coeff x j * coeff y (k - j) :=
  (summable_normMag_mul x y k).of_norm_bounded fun j =>
    (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ Fact.out)).trans
      (norm_conv_term_mul_le x y k j)

omit [CompleteSpace 𝕜] in
/-- **The uniform bound on the normalized magnitudes of the product** (`ν ≥ 1`):
`‖convCoeff x y k‖ * ν ^ |k| ≤ ‖x‖ * ‖y‖`. -/
theorem normMag_convCoeff_le (x y : X₂ 𝕜 ν) (k : ℤ) :
    ‖convCoeff x y k‖ * (ν : ℝ) ^ k.natAbs ≤ ‖x‖ * ‖y‖ := by
  have hw : 0 < (ν : ℝ) ^ k.natAbs := pow_pos ν.coe_pos _
  have h := tsum_of_norm_bounded (f := fun j => coeff x j * coeff y (k - j))
    ((summable_normMag_mul x y k).hasSum.div_const _) fun j =>
      (le_div_iff₀ hw).2 (norm_conv_term_mul_le x y k j)
  exact ((le_div_iff₀ hw).1 h).trans (tsum_normMag_mul_le x y k)

omit [CompleteSpace 𝕜] in
/-- The raw product coefficients define an element of `Y 𝕜 ν` (`ν ≥ 1`). -/
theorem memℓp_top_convCoeff (x y : X₂ 𝕜 ν) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (convCoeff x y k)) ∞ :=
  memℓp_top_of_bdd _ (normMag_convCoeff_le x y)

/-- The raw product coefficient is additive in the left factor. -/
theorem convCoeff_add_left (x₁ x₂ y : X₂ 𝕜 ν) (k : ℤ) :
    convCoeff (x₁ + x₂) y k = convCoeff x₁ y k + convCoeff x₂ y k := by
  simp only [convCoeff, coeff_add, Pi.add_apply, add_mul]
  exact (summable_conv_term x₁ y k).tsum_add (summable_conv_term x₂ y k)

/-- The raw product coefficient is additive in the right factor. -/
theorem convCoeff_add_right (x y₁ y₂ : X₂ 𝕜 ν) (k : ℤ) :
    convCoeff x (y₁ + y₂) k = convCoeff x y₁ k + convCoeff x y₂ k := by
  simp only [convCoeff, coeff_add, Pi.add_apply, mul_add]
  exact (summable_conv_term x y₁ k).tsum_add (summable_conv_term x y₂ k)

/-- The product as a bilinear map `X₂ 𝕜 ν →ₗ[𝕜] X₂ 𝕜 ν →ₗ[𝕜] Y 𝕜 ν` (`ν ≥ 1`): the element of
`Y 𝕜 ν` with raw coefficients `convCoeff x y`, built by the carrier's `ofCoeff`, whose simp law
`coeff_ofCoeff` reduces each linearity field to the coefficient law. -/
def prodLM : X₂ 𝕜 ν →ₗ[𝕜] X₂ 𝕜 ν →ₗ[𝕜] Y 𝕜 ν :=
  LinearMap.mk₂ 𝕜 (fun x y => ofCoeff (convCoeff x y) (memℓp_top_convCoeff x y))
    (fun x₁ x₂ y => ext_coeff <| funext fun k => by simp [convCoeff_add_left])
    (fun c x y => ext_coeff <| funext fun k => by simp [convCoeff_smul_left])
    (fun x y₁ y₂ => ext_coeff <| funext fun k => by simp [convCoeff_add_right])
    (fun c x y => ext_coeff <| funext fun k => by simp [convCoeff_smul_right])

/-- The raw coefficients of `prodLM x y` are the raw product coefficients. -/
theorem coeff_prodLM (x y : X₂ 𝕜 ν) (k : ℤ) : coeff (prodLM x y) k = convCoeff x y k :=
  coeff_ofCoeff _ _ k

/-- `‖prodLM x y‖ ≤ ‖x‖ * ‖y‖` in the sup norm of `Y 𝕜 ν`. -/
theorem norm_prodLM_le (x y : X₂ 𝕜 ν) : ‖prodLM x y‖ ≤ ‖x‖ * ‖y‖ :=
  lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg x) (norm_nonneg y)) fun k => by
    rw [norm_apply_Y, coeff_prodLM]
    exact normMag_convCoeff_le x y k

end ConvergentProduct

section BoundedProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))]

/-- **The bounded bilinear product** `X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν →L[𝕜] Y 𝕜 ν` (`ν ≥ 1`), with raw
coefficients `∑' j, coeff x j * coeff y (k - j)` and norm at most `1` (exactly `1`,
`norm_prodCLM_eq`). -/
def prodCLM : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν →L[𝕜] Y 𝕜 ν :=
  prodLM.mkContinuous₂ 1 fun x y => by
    rw [one_mul]
    exact norm_prodLM_le x y

/-- The raw coefficients of the product: `coeff (prodCLM x y) k = convCoeff x y k`. -/
@[simp] theorem coeff_prodCLM (x y : X₂ 𝕜 ν) (k : ℤ) :
    coeff (prodCLM x y) k = convCoeff x y k :=
  coeff_prodLM x y k

/-- `‖prodCLM x y‖ ≤ ‖x‖ * ‖y‖`. -/
theorem norm_prodCLM_apply_le (x y : X₂ 𝕜 ν) : ‖prodCLM x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_prodLM_le x y

/-- `‖prodCLM‖ ≤ 1`. -/
theorem norm_prodCLM_le : ‖prodCLM (𝕜 := 𝕜) (ν := ν)‖ ≤ 1 :=
  (prodCLM (𝕜 := 𝕜) (ν := ν)).opNorm_le_bound₂ zero_le_one fun x y =>
    (norm_prodCLM_apply_le x y).trans_eq (by rw [one_mul])

/-- The product is commutative. -/
theorem prodCLM_comm (x y : X₂ 𝕜 ν) : prodCLM x y = prodCLM y x :=
  ext_coeff <| funext fun k => by rw [coeff_prodCLM, coeff_prodCLM, convCoeff_comm]

end BoundedProduct

end RadiiPolynomial.WeightedLp.Bilateral

end
