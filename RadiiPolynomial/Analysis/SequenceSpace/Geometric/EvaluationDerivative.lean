import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Term-by-Term Differentiation of Weighted Sequence Evaluation

Differentiates `l1Weighted.eval` strictly inside its disk of convergence. This analytic
layer uses the coordinate presentation of the universal geometric evaluation;
`Geometric/Evaluation.lean` identifies it with `aeval_of_norm_le` on its admissible disc.
-/

open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

namespace l1Weighted

private abbrev seq (a : l1Weighted ν) := l1Weighted.toSeq a


/-- Term-by-term differentiation of `eval` strictly inside the disk of convergence. -/
theorem hasDerivAt_eval (a : l1Weighted ν) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (l1Weighted.eval a) (l1Omega.eval (derivShift a) t) t := by
  obtain ⟨ν', hν'_lt_t, hν'_lt_ν⟩ : ∃ ν' : ℝ, |t| < ν' ∧ ν' < (ν : ℝ) :=
    ⟨(|t| + (ν : ℝ)) / 2, by linarith [abs_nonneg t], by linarith [ν.2]⟩
  have hν'_pos : (0 : ℝ) < ν' := lt_of_le_of_lt (abs_nonneg t) hν'_lt_t
  rw [abs_lt] at hν'_lt_t
  have h_t_mem : t ∈ Set.Ioo (-ν') ν' := ⟨hν'_lt_t.1, hν'_lt_t.2⟩
  have h_zero_mem : (0 : ℝ) ∈ Set.Ioo (-ν') ν' := ⟨by linarith, hν'_pos⟩
  have h_g_hasDeriv : ∀ n : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => seq a n * y^n) (seq a n * (n : ℝ) * y^(n - 1)) y := by
    intro n y
    have h := (hasDerivAt_pow n y).const_mul (seq a n)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_g_bound : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-ν') ν',
      ‖seq a n * (n : ℝ) * y^(n - 1)‖ ≤ |seq a n| * (n : ℝ) * ν'^(n - 1) := by
    intro n y hy
    have hy_abs : |y| ≤ ν' := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        show |((n : ℝ))| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    exact pow_le_pow_left₀ (abs_nonneg _) hy_abs _
  have h_g_summable_zero : Summable fun n : ℕ => seq a n * (0 : ℝ)^n := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := fun h => hn (by simp [h])
    simp [zero_pow this]
  have h_main := hasDerivAt_tsum_of_isPreconnected
    (l1Weighted.summable_abs_mul_pow_pred a hν'_pos.le hν'_lt_ν)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y _ => h_g_hasDeriv n y)
    h_g_bound h_zero_mem h_g_summable_zero h_t_mem
  have h_summable : Summable fun n : ℕ => seq a n * (n : ℝ) * t^(n - 1) := by
    refine Summable.of_norm_bounded
      (g := fun n => |seq a n| * (n : ℝ) * ν'^(n - 1))
      (l1Weighted.summable_abs_mul_pow_pred a hν'_pos.le hν'_lt_ν)
      (fun n => h_g_bound n t h_t_mem)
  have h_deriv_eq :
      (∑' n, seq a n * (n : ℝ) * t^(n - 1)) =
        l1Omega.eval (derivShift a) t := by
    rw [l1Omega.eval, h_summable.tsum_eq_zero_add]
    simp only [Nat.zero_sub, pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_add]
    refine tsum_congr fun m => ?_
    rw [derivShift_apply]
    push_cast
    ring
  change HasDerivAt (fun z => ∑' n, seq a n * z ^ n) (l1Omega.eval (derivShift a) t) t
  rw [← h_deriv_eq]
  exact h_main

end l1Weighted

end RadiiPolynomial
