import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Carrier
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Complex.Norm

/-! Bounded convolution X_w×X_w→Y_w, `X_w = WeightedLp ℤ (WeightedScalar 𝕜 w) 2`, `Y_w = WeightedLp ℤ (WeightedScalar 𝕜 w) ∞`, for every positive submultiplicative weight `w` (`[PosWeight w]`, `Moderate w w 1`; no `w ≥ 1`; the geometric weight `ν ^ |k|` at `ν ≥ 1` through `geomSubmul`). Absolute convergence uses complete scalars; operator-norm packaging uses nontrivially normed scalars. No product X_w×X_w→X_w or convolution ring on X_w is asserted. The reflection `(refl a)ₙ = a₋ₙ` (any normed field, any positive ν) is an isometry of X₂ and commutes with the raw product. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

section RawAndMagnitudes

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]

/-- The raw product coefficient `∑' j, coeff x j * coeff y (k - j)` of
`x, y ∈ WeightedLp ℤ (WeightedScalar 𝕜 w) 2` at `k` (a `tsum`: `0` when the series is not
summable). -/
def convCoeff (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) : 𝕜 :=
  ∑' j : ℤ, coeff x j * coeff y (k - j)

/-- The raw product coefficient is symmetric (reindexing by the reflection `j ↦ k - j`). -/
theorem convCoeff_comm (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    convCoeff x y k = convCoeff y x k :=
  ((Equiv.subLeft k).tsum_eq fun j => coeff x j * coeff y (k - j)).symm.trans <|
    tsum_congr fun j => by
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      exact mul_comm _ _

/-- The raw product coefficient is homogeneous in the left factor. -/
theorem convCoeff_smul_left (c : 𝕜) (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    convCoeff (c • x) y k = c * convCoeff x y k := by
  simp only [convCoeff, coeff_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

/-- The raw product coefficient is homogeneous in the right factor. -/
theorem convCoeff_smul_right (c : 𝕜) (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    convCoeff x (c • y) k = c * convCoeff x y k := by
  simp only [convCoeff, coeff_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => mul_left_comm _ _ _

/-- **Cauchy–Schwarz on the normalized magnitudes**: the products
`(‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j))` are summable with sum at most
`‖x‖ * ‖y‖` (Hölder at `(2, 2)` on the fibre-norm families, the second one reindexed by
`j ↦ k - j`; no submultiplicativity). -/
theorem summable_and_tsum_normMag_mul_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    (Summable fun j : ℤ => (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j))) ∧
      ∑' j : ℤ, (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j)) ≤ ‖x‖ * ‖y‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_ofNat]
    exact .two_two
  have hn (z : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (j : ℤ) : ‖z j‖ = ‖coeff z j‖ * w j := by
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight]
  simp only [← hn]
  obtain ⟨C, -, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg x)
    (norm_nonneg y) (f := fun j => ‖x j‖) (g := fun j => ‖y (k - j)‖)
    (fun j => norm_nonneg _) (fun j => norm_nonneg _)
    (lp.hasSum_norm hpq.pos x) ((Equiv.subLeft k).hasSum_iff.2 (lp.hasSum_norm hpq.symm.pos y))
  exact ⟨hs.summable, hs.tsum_eq.trans_le hC⟩

/-- The products of normalized magnitudes along the reflection `j ↦ k - j` are summable. -/
theorem summable_normMag_mul (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    Summable fun j : ℤ => (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j)) :=
  (summable_and_tsum_normMag_mul_le x y k).1

/-- `∑' j, (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j)) ≤ ‖x‖ * ‖y‖`. -/
theorem tsum_normMag_mul_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    ∑' j : ℤ, (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j)) ≤ ‖x‖ * ‖y‖ :=
  (summable_and_tsum_normMag_mul_le x y k).2

end RawAndMagnitudes

section WeightBound

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w] (hsub : Moderate w w 1)
include hsub

/-- **The weight triangle inequality on one product term** (positive submultiplicative weight):
`‖coeff x j * coeff y (k - j)‖ * w k` is at most the product of the normalized magnitudes
`(‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j))`. -/
theorem norm_conv_term_mul_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k j : ℤ) :
    ‖coeff x j * coeff y (k - j)‖ * w k ≤
      (‖coeff x j‖ * w j) * (‖coeff y (k - j)‖ * w (k - j)) := by
  have h := hsub j (k - j)
  rw [add_sub_cancel, one_mul] at h
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

end WeightBound

section ConvergentProduct

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {w : ℤ → ℝ} [PosWeight w]
  (hsub : Moderate w w 1)
include hsub

/-- The raw product series converges absolutely (positive submultiplicative weight): the
majorant is divided by the fixed positive weight `w k`. -/
theorem summable_conv_term (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    Summable fun j : ℤ => coeff x j * coeff y (k - j) :=
  ((summable_normMag_mul x y k).div_const (w k)).of_norm_bounded fun j =>
    (le_div_iff₀ (PosWeight.weight_pos k)).2 (norm_conv_term_mul_le hsub x y k j)

omit [CompleteSpace 𝕜] in
/-- **The uniform bound on the normalized magnitudes of the product** (positive
submultiplicative weight): `‖convCoeff x y k‖ * w k ≤ ‖x‖ * ‖y‖`. -/
theorem normMag_convCoeff_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    ‖convCoeff x y k‖ * w k ≤ ‖x‖ * ‖y‖ := by
  have hw : 0 < w k := PosWeight.weight_pos k
  have h := tsum_of_norm_bounded (f := fun j => coeff x j * coeff y (k - j))
    ((summable_normMag_mul x y k).hasSum.div_const _) fun j =>
      (le_div_iff₀ hw).2 (norm_conv_term_mul_le hsub x y k j)
  exact ((le_div_iff₀ hw).1 h).trans (tsum_normMag_mul_le x y k)

omit [CompleteSpace 𝕜] in
/-- The raw product coefficients define an element of `WeightedLp ℤ (WeightedScalar 𝕜 w) ∞`
(positive submultiplicative weight). -/
theorem memℓp_top_convCoeff (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) :
    Memℓp (fun k => FiberTrivialization.equiv (E := WeightedScalar 𝕜 w) k (convCoeff x y k)) ∞ :=
  memℓp_infty ⟨‖x‖ * ‖y‖, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [FiberTrivialization.norm_equiv_apply, WeightedScalar.fiberTrivialization_weight]
    exact normMag_convCoeff_le hsub x y k⟩

/-- The raw product coefficient is additive in the left factor. -/
theorem convCoeff_add_left (x₁ x₂ y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    convCoeff (x₁ + x₂) y k = convCoeff x₁ y k + convCoeff x₂ y k := by
  simp only [convCoeff, coeff_add, Pi.add_apply, add_mul]
  exact (summable_conv_term hsub x₁ y k).tsum_add (summable_conv_term hsub x₂ y k)

/-- The raw product coefficient is additive in the right factor. -/
theorem convCoeff_add_right (x y₁ y₂ : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    convCoeff x (y₁ + y₂) k = convCoeff x y₁ k + convCoeff x y₂ k := by
  simp only [convCoeff, coeff_add, Pi.add_apply, mul_add]
  exact (summable_conv_term hsub x y₁ k).tsum_add (summable_conv_term hsub x y₂ k)

/-- The product as a bilinear map
`WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →ₗ[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →ₗ[𝕜]
WeightedLp ℤ (WeightedScalar 𝕜 w) ∞` (positive submultiplicative weight): the element with raw
coefficients `convCoeff x y`, whose coordinates `coeff_mk_equiv` reduce each linearity field to
the coefficient law. -/
def prodLM : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →ₗ[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →ₗ[𝕜]
    WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ :=
  LinearMap.mk₂ 𝕜 (fun x y => ⟨_, memℓp_top_convCoeff hsub x y⟩)
    (fun x₁ x₂ y => ext_coeff <| funext fun k => (coeff_mk_equiv _ _ k).trans <| by
      simp only [coeff_add, Pi.add_apply, coeff_mk_equiv, convCoeff_add_left hsub])
    (fun c x y => ext_coeff <| funext fun k => (coeff_mk_equiv _ _ k).trans <| by
      simp only [coeff_smul, Pi.smul_apply, smul_eq_mul, coeff_mk_equiv, convCoeff_smul_left])
    (fun x y₁ y₂ => ext_coeff <| funext fun k => (coeff_mk_equiv _ _ k).trans <| by
      simp only [coeff_add, Pi.add_apply, coeff_mk_equiv, convCoeff_add_right hsub])
    (fun c x y => ext_coeff <| funext fun k => (coeff_mk_equiv _ _ k).trans <| by
      simp only [coeff_smul, Pi.smul_apply, smul_eq_mul, coeff_mk_equiv, convCoeff_smul_right])

/-- The raw coefficients of `prodLM hsub x y` are the raw product coefficients. -/
theorem coeff_prodLM (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    coeff (prodLM hsub x y) k = convCoeff x y k :=
  coeff_mk_equiv _ _ k

/-- `‖prodLM hsub x y‖ ≤ ‖x‖ * ‖y‖` in the sup norm of `WeightedLp ℤ (WeightedScalar 𝕜 w) ∞`. -/
theorem norm_prodLM_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) :
    ‖prodLM hsub x y‖ ≤ ‖x‖ * ‖y‖ :=
  lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg x) (norm_nonneg y)) fun k => by
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight, coeff_prodLM]
    exact normMag_convCoeff_le hsub x y k

end ConvergentProduct

section BoundedProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {w : ℤ → ℝ} [PosWeight w]
  (hsub : Moderate w w 1)
include hsub

/-- **The bounded bilinear product**
`WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜]
WeightedLp ℤ (WeightedScalar 𝕜 w) ∞` for a positive submultiplicative weight `w`
(`Moderate w w 1`; the geometric weight passes `geomSubmul ν`), with raw coefficients
`∑' j, coeff x j * coeff y (k - j)` and norm at most `1` (`norm_prodCLM_le`). -/
def prodCLM : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜]
    WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ :=
  (prodLM hsub).mkContinuous₂ 1 fun x y => by
    rw [one_mul]
    exact norm_prodLM_le hsub x y

/-- The raw coefficients of the product: `coeff (prodCLM hsub x y) k = convCoeff x y k`. -/
@[simp] theorem coeff_prodCLM (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    coeff (prodCLM hsub x y) k = convCoeff x y k :=
  coeff_prodLM hsub x y k

/-- `‖prodCLM hsub x y‖ ≤ ‖x‖ * ‖y‖`. -/
theorem norm_prodCLM_apply_le (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) :
    ‖prodCLM hsub x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_prodLM_le hsub x y

/-- `‖prodCLM hsub‖ ≤ 1`. -/
theorem norm_prodCLM_le : ‖prodCLM (𝕜 := 𝕜) hsub‖ ≤ 1 :=
  (prodCLM (𝕜 := 𝕜) hsub).opNorm_le_bound₂ zero_le_one fun x y =>
    (norm_prodCLM_apply_le hsub x y).trans_eq (by rw [one_mul])

/-- The product is commutative. -/
theorem prodCLM_comm (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) :
    prodCLM hsub x y = prodCLM hsub y x :=
  ext_coeff <| funext fun k => by rw [coeff_prodCLM, coeff_prodCLM, convCoeff_comm]

end BoundedProduct

section Reflection

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- The reflected coefficient family `n ↦ a₋ₙ` of `a ∈ X₂ 𝕜 ν` lies in `X₂ 𝕜 ν` (the weight
`ν ^ |n|` is even). -/
theorem memℓp_refl (a : X₂ 𝕜 ν) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (coeff a (-k))) 2 :=
  memℓp_two_of_summable _ (((Equiv.neg ℤ).summable_iff.2 (summable_sq_X₂ a)).congr fun k => by
    simp only [Function.comp_apply, Equiv.neg_apply, Int.natAbs_neg])

/-- **The reflection** `(refl a)ₙ = a₋ₙ` of the bilateral carrier `X₂ 𝕜 ν` (any normed field,
any positive `ν`). -/
def refl (a : X₂ 𝕜 ν) : X₂ 𝕜 ν := ofCoeff (fun n => coeff a (-n)) (memℓp_refl a)

/-- The reflection in coordinates. -/
@[simp] theorem coeff_refl (a : X₂ 𝕜 ν) (n : ℤ) : coeff (refl a) n = coeff a (-n) :=
  coeff_ofCoeff _ _ n

private theorem norm_refl (a : X₂ 𝕜 ν) : ‖refl a‖ = ‖a‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_X₂, norm_sq_X₂, ← (Equiv.neg ℤ).tsum_eq]
  exact tsum_congr fun k => by simp only [coeff_refl, Equiv.neg_apply, neg_neg, Int.natAbs_neg]

private theorem refl_sub (a b : X₂ 𝕜 ν) : refl (a - b) = refl a - refl b :=
  ext_coeff <| funext fun n => by
    rw [coeff_refl, coeff_sub, coeff_sub, Pi.sub_apply, Pi.sub_apply, coeff_refl, coeff_refl]

/-- **The reflection is an isometry** of `X₂ 𝕜 ν`. -/
theorem isometry_refl : Isometry (refl : X₂ 𝕜 ν → X₂ 𝕜 ν) :=
  Isometry.of_dist_eq fun a b => by rw [dist_eq_norm, dist_eq_norm, ← refl_sub, norm_refl]

/-- The raw product commutes with the reflection: `(refl x ⋆ refl y)ₙ = (x ⋆ y)₋ₙ` (the reindex
`j ↦ −j`; no summability). -/
theorem convCoeff_refl (x y : X₂ 𝕜 ν) (n : ℤ) :
    convCoeff (refl x) (refl y) n = convCoeff x y (-n) := by
  rw [convCoeff, convCoeff]
  refine (tsum_congr fun j => ?_).trans
    ((Equiv.neg ℤ).tsum_eq fun j => coeff x j * coeff y (-n - j))
  rw [coeff_refl, coeff_refl, Equiv.neg_apply, show -(n - j) = -n - -j by ring]

end Reflection

end RadiiPolynomial.WeightedLp.Bilateral

end
