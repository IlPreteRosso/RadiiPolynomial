import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation

/-!
# Sharper bounds for Chebyshev evaluation

For the production one-sided-in-bilateral storage convention, evaluation on
`[-1, 1]` is contractive once the geometric weight is at least `2`.  No
symmetry hypothesis is required.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

open Polynomial.Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- At weights `ν ≥ 2`, evaluation on `[-1, 1]` is contractive on the
production storage carrier. -/
theorem abs_eval_le_norm_of_two_le (hν : (2 : ℝ) ≤ (ν : ℝ))
    (a : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    |eval a t| ≤ ‖a‖ := by
  let term : ℕ → ℝ := fun k =>
    toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t
  have hnorm : Summable (fun k : ℕ => ‖a ((k + 1 : ℕ) : ℤ)‖) :=
    (summable_norm_natCast a).comp_injective (add_left_injective 1)
  have hcol : ∀ k : ℕ, 2 * ‖term k‖ ≤ ‖a ((k + 1 : ℕ) : ℤ)‖ := by
    intro k
    rw [norm_fiber_natCast, Real.norm_eq_abs, abs_mul]
    have hT := abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) ht
    have hpow : (2 : ℝ) ≤ (ν : ℝ) ^ (k + 1) := by
      refine hν.trans ?_
      have hp := pow_le_pow_right₀ (Fact.out : (1 : ℝ) ≤ (ν : ℝ))
        (show 1 ≤ k + 1 by omega)
      simpa using hp
    calc
      2 * (|toSeq a ((k + 1 : ℕ) : ℤ)| * |(T ℝ ((k + 1 : ℕ) : ℤ)).eval t|) =
          |toSeq a ((k + 1 : ℕ) : ℤ)| *
            (2 * |(T ℝ ((k + 1 : ℕ) : ℤ)).eval t|) := by ring
      _ ≤ |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hnormterm : Summable (fun k : ℕ => ‖term k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      linarith [hcol k, norm_nonneg (term k)]) hnorm
  have htail : 2 * ‖∑' k : ℕ, term k‖ ≤
      ∑' k : ℕ, ‖a ((k + 1 : ℕ) : ℤ)‖ := by
    calc
      2 * ‖∑' k : ℕ, term k‖ ≤ 2 * ∑' k : ℕ, ‖term k‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnormterm) (by norm_num)
      _ = ∑' k : ℕ, 2 * ‖term k‖ := by rw [tsum_mul_left]
      _ ≤ ∑' k : ℕ, ‖a ((k + 1 : ℕ) : ℤ)‖ :=
        Summable.tsum_le_tsum hcol (hnormterm.mul_left 2) hnorm
  have hnat_le : (∑' n : ℕ, ‖a (n : ℤ)‖) ≤ ‖a‖ := by
    rw [lpOneAlg.norm_eq_tsum]
    exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm a)
      (fun _ => norm_nonneg _) fun n m h => by simpa using h
  have hsplit := (summable_norm_natCast a).tsum_eq_zero_add
  have hzero : ‖a ((0 : ℕ) : ℤ)‖ = |toSeq a 0| := by
    rw [norm_fiber_natCast]
    simp
  have htri : |eval a t| ≤ |toSeq a 0| + 2 * ‖∑' k : ℕ, term k‖ := by
    rw [eval]
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_two, Real.norm_eq_abs])
  rw [hzero] at hsplit
  linarith

end l1Chebyshev

end RadiiPolynomial

