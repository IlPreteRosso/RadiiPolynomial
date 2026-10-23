import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal

/-!
# Reciprocal Fourier tail comparison: the first-order symbol `i k`

The fixed complex symbol `ik k = I * k` on `ℤ` supplies a square-summable reciprocal tail
comparison on the head `headZ N = {k : |k| ≤ N}`. Its squared tail sum is `2 * psi1 N`, where
`psi1 N = ∑_{k > N} k⁻²`. This is symbol data of the Fourier family (no state carrier, weight,
candidate or certificate), shared by the Duffing symbol comparison
(`Examples/Fourier/Duffing/Algebra.lean`) and the Riccati certificate
(`Examples/Fourier/Riccati/Certificate.lean`).
-/

open scoped ENNReal
open RadiiPolynomial RadiiPolynomial.WeightedLp

namespace RadiiPolynomial.Fourier.IkData

/-! ### The symbol `μ = ik` and the head `|k| ≤ N` -/

section IK

/-- The head `S_N = {k : |k| ≤ N}`. -/
abbrev headZ (N : ℕ) : Set ℤ := {k : ℤ | |k| ≤ (N : ℤ)}

/-- The first-order symbol `μ k = i k`. -/
def ik (k : ℤ) : ℂ := Complex.I * k

theorem norm_ik (k : ℤ) : ‖ik k‖ = ((|k| : ℤ) : ℝ) := by
  rw [ik, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Int.cast_abs]





/-! ### The squared tail entries and their sum `2 · psi1 N` -/

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

end RadiiPolynomial.Fourier.IkData

