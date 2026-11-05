import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Finite Norm Inequality Helpers

Reusable finite-sum inequalities used across norm proofs, and the norm bound of a family
restricted to a finite set (`bddAbove_norm_indicator_finset`).
-/

open scoped BigOperators

namespace RadiiPolynomial.NormHelpers

/-- Weighted triangle inequality with a finite component index:
`∑ₙ |∑ⱼ fⱼₙ| wₙ ≤ ∑ⱼ ∑ₙ |fⱼₙ| wₙ` for nonnegative weights. -/
lemma weighted_sum_abs_sum_le
    {L N : ℕ}
    (w : Fin (N + 1) → ℝ)
    (hw : ∀ n : Fin (N + 1), 0 ≤ w n)
    (f : Fin L → Fin (N + 1) → ℝ) :
    ∑ n : Fin (N + 1), |∑ j : Fin L, f j n| * w n ≤
      ∑ j : Fin L, ∑ n : Fin (N + 1), |f j n| * w n :=
  (Finset.sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (hw n)).trans_eq
    (by simp_rw [Finset.sum_mul]; exact Finset.sum_comm)

/-- Pull out a uniform right factor from a weighted finite sum:
if `b j ≤ C` and `a j ≥ 0`, then `∑ a j * b j ≤ (∑ a j) * C`. -/
lemma sum_mul_le_sum_mul_const
    {L : ℕ}
    (a b : Fin L → ℝ) (C : ℝ)
    (ha : ∀ j : Fin L, 0 ≤ a j)
    (hb : ∀ j : Fin L, b j ≤ C) :
    ∑ j : Fin L, a j * b j ≤ (∑ j : Fin L, a j) * C :=
  (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (ha j)).trans_eq
    (by rw [Finset.sum_mul])

section SumMul

variable {A ι : Type*} [NonUnitalSeminormedRing A] [Fintype ι]

/-- For a direction `h : ι → A` with the sup norm, `‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖`:
the triangle inequality, submultiplicativity of the norm, and `‖h i‖ ≤ ‖h‖`. -/
theorem norm_sum_mul_pi_le (f h : ι → A) :
    ‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖ := by
  refine ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => norm_mul_le _ _)).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _)

end SumMul

section Indicator

variable {M E : Type*} [SeminormedAddGroup E]

/-- The restriction `(F : Set M).indicator μ` of a family to a finite set `F` has bounded norm,
with bound `∑ j ∈ F, ‖μ j‖`: on `F` the norm is one summand, off `F` it is zero. -/
theorem bddAbove_norm_indicator_finset (F : Finset M) (μ : M → E) :
    BddAbove (Set.range fun n => ‖(F : Set M).indicator μ n‖) := by
  refine ⟨∑ j ∈ F, ‖μ j‖, Set.forall_mem_range.2 fun n => ?_⟩
  by_cases h : n ∈ F
  · rw [Set.indicator_of_mem (Finset.mem_coe.2 h)]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (μ j)) h
  · rw [Set.indicator_of_notMem (mt Finset.mem_coe.1 h), norm_zero]
    exact Finset.sum_nonneg fun j _ => norm_nonneg (μ j)

end Indicator

end RadiiPolynomial.NormHelpers
