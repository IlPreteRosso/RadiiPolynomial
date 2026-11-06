import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Convolution
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal
import RadiiPolynomial.Analysis.Norm.InfiniteSum
import Mathlib.Analysis.PSeries

/-!
# Book §10.1 Helmholtz–Duffing on the polynomial carrier: weight and product

The polynomial amplitude `m_n = (1 + |n|)²` on `ℤ` (mass exponent `4 > 1`) is the concrete
producer of the services consumed by the second-carrier certificate:

* the row bound `polyRowBound` at `p = q = 2` with the coarse constant `K = 10`: the ratio rows
  satisfy `∑_k (m_n / (m_{n−k} m_k))² ≤ 2⁴ · 2 · ∑_k (1 + |k|)⁻⁴ ≤ 32 · 7/3 ≤ 10²`, so the
  carrier `X = ℓ²_m(ℤ; ℂ)` carries the bounded product `polyProd = convCLM polyRowBound`;
* the self-moderation `polyModerate` (`m` is submultiplicative, constant `1`), for the ℓ¹ symbol
  action of the derivative at the centre, and its raw-weight form `polyModerate_raw`, for the
  bounded product `X → X → ℓ^∞_m` of the curvature bound.

The reciprocal-mass embedding into unweighted ℓ¹ is not used. The convolution coordinates are
read in the convention `(f ⋆ g)_n = ∑_k f_k g_{n−k}` of the bilateral consumer (`conv_apply`).
-/

open scoped DiscreteConvolution

noncomputable section

namespace FourierDuffing.Polynomial

open RadiiPolynomial RadiiPolynomial.WeightedLp
open _root_.DiscreteConvolution (addFiber addRingConvolution_apply)
open RadiiPolynomial.DiscreteConvolution (addFiberEquiv)

/-! ### The convolution coordinates on `ℤ` -/

/-- The additive-index ring convolution on `ℤ` in the convention `∑_k f_k g_{n−k}`. -/
theorem conv_apply (f g : ℤ → ℂ) (n : ℤ) : (f ⋆ᵣ₊ g) n = ∑' k, f k * g (n - k) := by
  rw [addRingConvolution_apply, ← ((Equiv.subLeft n).trans (addFiberEquiv n)).tsum_eq]
  exact tsum_congr fun k => by
    show f (n - (n - k)) * g (n - k) = f k * g (n - k)
    rw [sub_sub_cancel]

/-! ### Polynomial weight estimates -/

section Estimates

open Real

/-- `pw n = 1 + |n|`. -/
private def pw (n : ℤ) : ℝ := 1 + |(n : ℝ)|

private theorem pw_pos (n : ℤ) : 0 < pw n :=
  lt_of_lt_of_le one_pos (le_add_of_nonneg_right (abs_nonneg _))

private theorem abs_le_abs_sub_add (n k : ℤ) : |(n : ℝ)| ≤ |((n - k : ℤ) : ℝ)| + |(k : ℝ)| := by
  have h : (n : ℝ) = ((n - k : ℤ) : ℝ) + (k : ℝ) := by push_cast; ring
  rw [h]
  exact abs_add_le _ _

/-- `1 + |n| ≤ (1 + |n − k|)(1 + |k|)`. -/
private theorem pw_le_mul (n k : ℤ) : pw n ≤ pw (n - k) * pw k := by
  have h := abs_le_abs_sub_add n k
  have h1 := abs_nonneg ((n - k : ℤ) : ℝ)
  have h2 := abs_nonneg (k : ℝ)
  simp only [pw]
  nlinarith [mul_nonneg h1 h2]

/-- `1 + |n| ≤ (1 + |n − k|) + (1 + |k|)`. -/
private theorem pw_le_add (n k : ℤ) : pw n ≤ pw (n - k) + pw k := by
  have h := abs_le_abs_sub_add n k
  simp only [pw]
  linarith

/-- `(x + y)^s ≤ 2^s (x^s + y^s)` for `x, y, s ≥ 0`. -/
private theorem add_rpow_le_two_rpow_mul {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 ≤ s) :
    (x + y) ^ s ≤ 2 ^ s * (x ^ s + y ^ s) := by
  rcases le_total x y with h | h
  · refine (rpow_le_rpow (by positivity) (by linarith : x + y ≤ 2 * y) hs).trans ?_
    rw [mul_rpow (by norm_num) hy]
    gcongr
    exact le_add_of_nonneg_left (rpow_nonneg hx s)
  · refine (rpow_le_rpow (by positivity) (by linarith : x + y ≤ 2 * x) hs).trans ?_
    rw [mul_rpow (by norm_num) hx]
    gcongr
    exact le_add_of_nonneg_right (rpow_nonneg hy s)

/-- The mass weight `(1 + |n|)^s`. -/
private def polyW (s : ℝ) (n : ℤ) : ℝ := pw n ^ s

private theorem polyW_pos (s : ℝ) (n : ℤ) : 0 < polyW s n := rpow_pos_of_pos (pw_pos n) s

/-- The ratio of the polynomial weight is bounded by `2^s (1/(1+|k|)^s + 1/(1+|n−k|)^s)`. -/
private theorem polyW_ratio_le {s : ℝ} (hs : 0 ≤ s) (n k : ℤ) :
    polyW s n / (polyW s (n - k) * polyW s k) ≤
      2 ^ s * (1 / pw k ^ s + 1 / pw (n - k) ^ s) := by
  have hp := pw_pos n
  have hq := pw_pos (n - k)
  have hr := pw_pos k
  have heq : polyW s n / (polyW s (n - k) * polyW s k) = (pw n / (pw (n - k) * pw k)) ^ s := by
    simp only [polyW]
    rw [div_rpow hp.le (mul_pos hq hr).le, mul_rpow hq.le hr.le]
  have hle : pw n / (pw (n - k) * pw k) ≤ 1 / pw k + 1 / pw (n - k) := by
    rw [div_le_iff₀ (mul_pos hq hr)]
    have e : (1 / pw k + 1 / pw (n - k)) * (pw (n - k) * pw k) = pw (n - k) + pw k := by
      field_simp
    rw [e]
    exact pw_le_add n k
  rw [heq]
  refine (rpow_le_rpow (by positivity) hle hs).trans ?_
  refine (add_rpow_le_two_rpow_mul (by positivity) (by positivity) hs).trans_eq ?_
  rw [div_rpow zero_le_one hr.le, div_rpow zero_le_one hq.le, one_rpow]

/-- The row estimate for the mass weight `(1 + |n|)^s`, `s > 1`. -/
private theorem polyW_row_bound {s : ℝ} (hs : 1 < s) (n : ℤ) :
    Summable (fun k => polyW s n / (polyW s (n - k) * polyW s k)) ∧
      ∑' k, polyW s n / (polyW s (n - k) * polyW s k) ≤
        2 ^ s * (2 * ∑' k : ℤ, 1 / pw k ^ s) := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hz : Summable fun k : ℤ => 1 / pw k ^ s := by
    simpa only [pw] using NormHelpers.summable_inv_one_add_abs_rpow hs
  have hz' : Summable fun k : ℤ => 1 / pw (n - k) ^ s :=
    ((Equiv.subLeft n).summable_iff (f := fun j : ℤ => 1 / pw j ^ s)).2 hz
  have hdom : Summable fun k : ℤ => 2 ^ s * (1 / pw k ^ s + 1 / pw (n - k) ^ s) :=
    (hz.add hz').mul_left _
  have h0 : ∀ k : ℤ, 0 ≤ polyW s n / (polyW s (n - k) * polyW s k) := fun k =>
    div_nonneg (polyW_pos s n).le (mul_pos (polyW_pos s _) (polyW_pos s _)).le
  have hle : ∀ k : ℤ, polyW s n / (polyW s (n - k) * polyW s k) ≤
      2 ^ s * (1 / pw k ^ s + 1 / pw (n - k) ^ s) := fun k => polyW_ratio_le hs0 n k
  have hsum : Summable fun k : ℤ => polyW s n / (polyW s (n - k) * polyW s k) :=
    Summable.of_nonneg_of_le h0 hle hdom
  refine ⟨hsum, (Summable.tsum_le_tsum hle hsum hdom).trans_eq ?_⟩
  have h1 : ∑' k : ℤ, 2 ^ s * (1 / pw k ^ s + 1 / pw (n - k) ^ s) =
      2 ^ s * ∑' k : ℤ, (1 / pw k ^ s + 1 / pw (n - k) ^ s) := tsum_mul_left
  have h2 : ∑' k : ℤ, (1 / pw k ^ s + 1 / pw (n - k) ^ s) =
      ∑' k : ℤ, 1 / pw k ^ s + ∑' k : ℤ, 1 / pw (n - k) ^ s := hz.tsum_add hz'
  have h3 : ∑' k : ℤ, 1 / pw (n - k) ^ s = ∑' k : ℤ, 1 / pw k ^ s :=
    (Equiv.subLeft n).tsum_eq fun j : ℤ => 1 / pw j ^ s
  rw [h1, h2, h3]
  ring

end Estimates

/-! ### The weight and its two services -/

/-- **The polynomial amplitude weight** `m_n = (1 + |n|)²`. -/
def polyWeight (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ 2

instance instPosWeightPolyWeight : PosWeight polyWeight where
  weight_pos _ := sq_pos_of_pos (by positivity)

/-- **The polynomial carrier** `X = ℓ²_m(ℤ; ℂ)`, `m_n = (1 + |n|)²`. -/
abbrev X := WeightedLp ℤ (WeightedScalar ℂ polyWeight) 2

private theorem polyW_four_eq (n : ℤ) : polyW 4 n = polyWeight n ^ 2 := by
  rw [polyW, polyWeight, pw, ← pow_mul, ← Real.rpow_natCast]
  norm_num

/-- The reciprocal mass sum `∑_k (1 + |k|)⁻⁴ ≤ 7/3`. -/
private theorem invPolyMass_le : ∑' n : ℤ, 1 / pw n ^ (4 : ℝ) ≤ (7 / 3 : ℝ) := by
  let f : ℤ → ℝ := fun n => 1 / pw n ^ (4 : ℝ)
  have hs : Summable f := by
    simpa only [f, pw] using NormHelpers.summable_inv_one_add_abs_rpow (s := 4) (by norm_num)
  have hn : Summable (fun n : ℕ => f n) := hs.comp_injective Nat.cast_injective
  have hm : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hs.comp_injective fun a b h =>
    Int.ofNat_inj.mp (add_right_cancel (neg_injective h))
  have he : (fun n : ℕ => f (-((n : ℤ) + 1))) = (fun n : ℕ => f ((n : ℤ) + 1)) := by
    funext n
    simp only [f, pw, Int.cast_neg, abs_neg]
  have hterm (n : ℕ) : f ((n : ℤ) + 1) ≤ 1 / (((n + 1 + 1 : ℕ) : ℝ)) ^ 2 := by
    simp only [f, pw, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    push_cast
    have h1 : 1 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hb : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤ psi1 1 :=
    Summable.tsum_le_tsum hterm (hm.congr fun n => congrFun he n) (summable_psi1_term 1)
  rw [tsum_of_nat_of_neg_add_one hn hm, hn.tsum_eq_zero_add, he]
  have hpsi := psi1_le 1
  have hf0 : f ((0 : ℕ) : ℤ) = 1 := by norm_num [f, pw]
  have hshift : (fun n : ℕ => f (↑(n + 1))) = fun n : ℕ => f ((n : ℤ) + 1) := by
    funext n
    simp
  rw [hf0, hshift]
  norm_num at hpsi
  linarith

/-- **The row bound** of the polynomial frame at `p = q = 2` with `K = 10`. -/
theorem polyRowBound :
    RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ polyWeight)) 2 10 := by
  rw [show FiberTrivialization.weight (E := WeightedScalar ℂ polyWeight) = polyWeight from
    funext WeightedScalar.fiberTrivialization_weight]
  have hrow := polyW_row_bound (s := 4) (by norm_num)
  have hratio (n k : ℤ) : polyW 4 n / (polyW 4 (n - k) * polyW 4 k) =
      (polyWeight n / (polyWeight (n - k) * polyWeight k)) ^ 2 := by
    rw [polyW_four_eq, polyW_four_eq, polyW_four_eq, div_pow, mul_pow]
  refine RowBound.of_tsum_rpow_le (by norm_num) PosWeight.weight_pos (by norm_num)
    (fun n => ?_) (fun n => ?_)
  · rw [ENNReal.toReal_ofNat]
    refine (addFiberEquiv n).summable_iff.mp (((hrow n).1).congr fun k => ?_)
    rw [hratio, Function.comp_apply, Real.rpow_two]
    rfl
  · rw [ENNReal.toReal_ofNat, ← (addFiberEquiv n).tsum_eq]
    refine le_trans (le_of_eq (tsum_congr fun k => ?_)) ((hrow n).2.trans ?_)
    · rw [hratio, Real.rpow_two]
      rfl
    · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left invPolyMass_le
        (by norm_num)) (by positivity)).trans ?_
      norm_num

/-- **Self-moderation at the raw weight** (`m` is submultiplicative, constant `1`): the positive
submultiplicativity `Moderate polyWeight polyWeight 1` consumed by the bounded product
`Bilateral.prodCLM`. -/
theorem polyModerate_raw : Moderate polyWeight polyWeight 1 := by
  intro j l
  rw [one_mul]
  have h := pw_le_mul (j + l) l
  rw [add_sub_cancel_right] at h
  simp only [polyWeight]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (pw_pos (j + l)).le (h.trans_eq (mul_comm _ _)) 2

/-- **Self-moderation** of the polynomial frame: `polyModerate_raw` in the frame form
(`Moderate.weightedScalar_iff`). -/
theorem polyModerate :
    Moderate (FiberTrivialization.weight (E := WeightedScalar ℂ polyWeight)) polyWeight 1 :=
  Moderate.weightedScalar_iff.mpr polyModerate_raw

/-- The polynomial weight is negation-invariant (the `hw` of `conjReflL`). -/
theorem polyWeight_neg : ∀ n : ℤ, polyWeight (-n) = polyWeight n := fun n => by
  unfold polyWeight
  rw [Int.cast_neg, abs_neg]

/-- The polynomial weight is at least `1` (the `h1` of `pairing`). -/
theorem one_le_polyWeight : ∀ n : ℤ, 1 ≤ polyWeight n := fun _ =>
  one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))

/-- **The product** of the polynomial carrier: `convCLM` at the row bound `K = 10`. -/
abbrev polyProd : X →L[ℂ] X →L[ℂ] X := convCLM polyRowBound

end FourierDuffing.Polynomial
