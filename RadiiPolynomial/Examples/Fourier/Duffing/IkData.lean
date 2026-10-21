import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal

/-!
# Reciprocal Fourier tail comparison for the Duffing certificate

The symbol `ik k = I * k` supplies a square-summable reciprocal tail comparison.
Its squared tail sum is `2 * psi1 N`, where `psi1 N = ∑_{k > N} k⁻²`.
The Duffing symbol comparison in `Algebra.lean` consumes this service.

Statements and proofs are selected from the accepted CF3 `FourierIkData.lean`,
sha256 `fbbcfb2a5c941578809e855d11754364953e63cee976011b9946398596cf34e9`.
The original source and header, obsolete first-order defect bridge, and unused
head-membership controls are retained in the source-preparation archive.
-/

open scoped ENNReal
open RadiiPolynomial RadiiPolynomial.WeightedLp

namespace FourierDuffing.IkData

/-! ### The symbol `μ = ik` and the head `|k| ≤ N` (CF-2 Probe lines 49–78) -/

section IK

/-- The head `S_N = {k : |k| ≤ N}`. -/
abbrev headZ (N : ℕ) : Set ℤ := {k : ℤ | |k| ≤ (N : ℤ)}

/-- The first-order symbol `μ k = i k`. -/
def ik (k : ℤ) : ℂ := Complex.I * k

theorem norm_ik (k : ℤ) : ‖ik k‖ = ((|k| : ℤ) : ℝ) := by
  rw [ik, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Int.cast_abs]





/-! ### The squared tail entries and their sum `2 · psi1 N` (CF-2 Probe lines 117–168) -/

/-- The squared tail entries of `ik` on `ℕ`: `0` on the head, `1/(n)²` on the tail. -/
theorem sq_norm_tailSymbol_ik_nat (N n : ℕ) :
    ‖tailSymbol (headZ N) ik (n : ℤ)‖ ^ 2 = if n ≤ N then 0 else (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2 := by
  rw [norm_tailSymbol]
  by_cases h : n ≤ N
  · rw [ite_eq_left (show (n : ℤ) ∈ headZ N by
      simp only [headZ, Set.mem_ofPred_eq, abs_of_nonneg (Int.natCast_nonneg n)]; exact_mod_cast h),
      ite_eq_left h, sq, mul_zero]
  · rw [ite_eq_right (show (n : ℤ) ∉ headZ N by
      simp only [headZ, Set.mem_ofPred_eq, abs_of_nonneg (Int.natCast_nonneg n), not_le]
      exact_mod_cast not_le.1 h), ite_eq_right h, norm_ik, abs_of_nonneg (Int.natCast_nonneg n),
      inv_pow, one_div]
    norm_cast

/-- The negative ray mirrors the positive one. -/
theorem norm_tailSymbol_ik_neg (N : ℕ) (k : ℤ) :
    ‖tailSymbol (headZ N) ik (-k)‖ = ‖tailSymbol (headZ N) ik k‖ := by
  rw [norm_tailSymbol, norm_tailSymbol]
  simp only [headZ, Set.mem_ofPred_eq, abs_neg, norm_ik]

/-- The positive ray sums to `psi1 N`. -/
theorem hasSum_pos_ray (N : ℕ) :
    HasSum (fun n : ℕ => ‖tailSymbol (headZ N) ik (n : ℤ)‖ ^ 2) (RadiiPolynomial.WeightedLp.psi1 N) := by
  rw [← hasSum_nat_add_iff' (N + 1)]
  have h0 : ∑ i ∈ Finset.range (N + 1), ‖tailSymbol (headZ N) ik (i : ℤ)‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [sq_norm_tailSymbol_ik_nat, ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rw [h0, sub_zero]
  refine (RadiiPolynomial.WeightedLp.summable_psi1_term N).hasSum.congr_fun fun k => ?_
  rw [sq_norm_tailSymbol_ik_nat, ite_eq_right (by omega)]
  push_cast
  ring_nf

/-- **The `psi1` indexing, settled**: `∑' k : ℤ, ‖d_N(k)‖² = 2 · psi1 N` with
`psi1 N = ∑_{k > N} k⁻²` (CB-3's `psi1`; the paper quantity is `ψ₁(N + 1)`). -/
theorem hasSum_sq_tailSymbol_ik (N : ℕ) :
    HasSum (fun k : ℤ => ‖tailSymbol (headZ N) ik k‖ ^ 2) (2 * RadiiPolynomial.WeightedLp.psi1 N) := by
  have hpos := hasSum_pos_ray N
  have hneg : HasSum (fun n : ℕ => ‖tailSymbol (headZ N) ik (-((n : ℤ) + 1))‖ ^ 2)
      (RadiiPolynomial.WeightedLp.psi1 N) := by
    have h1 := (hasSum_nat_add_iff' 1).2 hpos
    rw [Finset.sum_range_one, sq_norm_tailSymbol_ik_nat, ite_eq_left (Nat.zero_le N), sub_zero] at h1
    refine h1.congr_fun fun n => ?_
    rw [norm_tailSymbol_ik_neg]
    push_cast
    rfl
  rw [two_mul]
  exact hpos.of_nat_of_neg_add_one hneg

theorem summable_sq_tailSymbol_ik (N : ℕ) :
    Summable fun k : ℤ => ‖tailSymbol (headZ N) ik k‖ ^ 2 :=
  (hasSum_sq_tailSymbol_ik N).summable

end IK

end FourierDuffing.IkData

