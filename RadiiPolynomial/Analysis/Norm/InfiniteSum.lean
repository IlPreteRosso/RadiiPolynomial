import RadiiPolynomial.Algebra.Convolution.Ring
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# Infinite sums: integer series and the norm bound of the ring convolution

Scalar series over the index `ℤ` and the weight-free norm summability of the ring convolution.
No sequence-space carrier is used.

* `NormHelpers.summable_inv_one_add_abs_rpow`: `∑_{n ∈ ℤ} 1 / (1 + |n|)^s < ∞` for real `s > 1`.
* `NormHelpers.summable_natAbs_pow_mul_geometric`: `∑_{n ∈ ℤ} |n|^j q^|n| < ∞` for `|q| < 1`.
* `NormHelpers.hasSum_geometric_natAbs`: `∑_{n ∈ ℤ} q^|n| = (1 + q) / (1 − q)` for `|q| < 1`.
* `DiscreteConvolution.summable_norm_ringConvolution` and its additive-index image
  `DiscreteConvolution.summable_norm_addRingConvolution`: on a monoid index with coefficients in a
  nonunital seminormed ring, norm-summable `f` and `g` give a norm-summable `f ⋆ᵣ g`. The statement
  concerns Mathlib's totalized `tsum` in each fiber; no completeness, unit or commutativity of the
  coefficients is used.
-/

open scoped DiscreteConvolution
open DiscreteConvolution (mulFiber ringConvolution_apply)

namespace RadiiPolynomial.NormHelpers

/-- `∑_{n ∈ ℤ} 1 / (1 + |n|)^s < ∞` for `s > 1`. -/
theorem summable_inv_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ s := by
  have hN := (Real.summable_one_div_nat_add_rpow 1 s).2 hs
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun n => ?_
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1), add_comm]
  · refine hN.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1), add_comm]

/-- The bilateral moments of a geometric sequence are summable: `∑ |n|^j q^|n| < ∞`
(`|q| < 1`). -/
theorem summable_natAbs_pow_mul_geometric (j : ℕ) {q : ℝ} (hq : |q| < 1) :
    Summable fun n : ℤ => (n.natAbs : ℝ) ^ j * q ^ n.natAbs := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ j * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one j (by rwa [Real.norm_eq_abs])
  refine Summable.of_nat_of_neg_add_one (by simpa only [Int.natAbs_natCast] using h) ?_
  have hn : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  simpa only [hn, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

/-- The bilateral geometric series: `∑_{n ∈ ℤ} q^|n| = (1 + q) / (1 − q)` (`|q| < 1`). -/
theorem hasSum_geometric_natAbs {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℤ => q ^ n.natAbs) ((1 + q) / (1 - q)) := by
  have h : HasSum (fun n : ℕ => q ^ (n + 1)) (q * (1 - q)⁻¹) := by
    simpa only [pow_succ'] using (hasSum_geometric_of_abs_lt_one hq).mul_left q
  have hp : HasSum (fun n : ℕ => q ^ ((n : ℤ) + 1).natAbs) (q * (1 - q)⁻¹) := by
    simpa only [show ∀ n : ℕ, ((n : ℤ) + 1).natAbs = n + 1 from fun n => by omega] using h
  have hm : HasSum (fun n : ℕ => q ^ (-((n : ℤ) + 1)).natAbs) (q * (1 - q)⁻¹) := by
    simpa only [show ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 from fun n => by omega] using h
  convert HasSum.of_add_one_of_neg_add_one (f := fun n : ℤ => q ^ n.natAbs) hp hm using 1
  have h1 : 1 - q ≠ 0 := (sub_pos.2 (abs_lt.1 hq).2).ne'
  rw [Int.natAbs_zero, pow_zero]
  field_simp
  ring

end RadiiPolynomial.NormHelpers

namespace RadiiPolynomial.DiscreteConvolution

/-- **Norm summability of the ring convolution**: on a monoid index, with coefficients in a
nonunital seminormed ring, `∑ ‖f m‖ < ∞` and `∑ ‖g m‖ < ∞` give `∑ ‖(f ⋆ᵣ g) m‖ < ∞`. Each fiber
value is Mathlib's totalized `tsum`, bounded by the fiber sum of the real majorant
`‖f a‖ * ‖g b‖`. -/
@[to_additive (dont_translate := R) summable_norm_addRingConvolution
  /-- **Norm summability of the additive-index ring convolution**: on an additive monoid index,
  with coefficients in a nonunital seminormed ring, `∑ ‖f m‖ < ∞` and `∑ ‖g m‖ < ∞` give
  `∑ ‖(f ⋆ᵣ₊ g) m‖ < ∞`. -/]
theorem summable_norm_ringConvolution
    {M R : Type*} [Monoid M] [NonUnitalSeminormedRing R]
    {f g : M → R}
    (hf : Summable fun m => ‖f m‖)
    (hg : Summable fun m => ‖g m‖) :
    Summable fun m => ‖(_root_.DiscreteConvolution.ringConvolution f g) m‖ := by
  have hsig := (summable_sigma_of_nonneg
    (f := fun x : Σ k : M, mulFiber k => ‖f x.2.1.1‖ * ‖g x.2.1.2‖)
    fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)).1
    ((sigmaMulFiberEquiv.summable_iff (f := fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖)).2
      (hf.mul_of_nonneg hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _))
  refine hsig.2.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  rw [ringConvolution_apply]
  exact tsum_of_norm_bounded (hsig.1 k).hasSum fun _ => norm_mul_le _ _

end RadiiPolynomial.DiscreteConvolution
