import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Data.Matrix.Basic

/-!
# Matrices over a normed real algebra acting on `R^n` (sup norm)

A matrix `M` with entries in a normed real algebra `R` acts on `R^n = Fin n → R` (sup norm) by
left multiplication, `matCLM M h i = Σₖ M i k * h k`, as an `ℝ`-linear map. Any continuous linear
map with this row form has operator norm at most the largest row sum `Σₖ ‖M i k‖`
(`opNorm_le_of_rowSum`); the row form is stable under composition with `matCLM A`, subtraction,
and `id - matCLM A ∘ T`.

## Main results

- `matCLM`, `matCLM_apply`
- `opNorm_le_of_rowSum`: `‖T‖ ≤ C` from row sums `Σₖ ‖M i k‖ ≤ C`
- `matCLM_comp_apply`, `sub_apply_rowSum`, `id_sub_matCLM_comp_apply`: row forms of composites
-/

open scoped BigOperators
open ContinuousLinearMap

namespace RadiiPolynomial

section Matrix

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {n : ℕ}

/-- Left multiplication by `M` on `R^n`, as an `ℝ`-linear map. -/
noncomputable def matCLM (M : Matrix (Fin n) (Fin n) R) : (Fin n → R) →L[ℝ] (Fin n → R) :=
  ContinuousLinearMap.pi fun i =>
    ∑ k : Fin n, M i k • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => R) k)

theorem matCLM_apply (M : Matrix (Fin n) (Fin n) R) (h : Fin n → R) (i : Fin n) :
    matCLM M h i = ∑ k, M i k * h k := by
  simp [matCLM]

/-- Row-sum bound for the sup-norm operator norm on `R^n`. -/
theorem opNorm_le_of_rowSum (T : (Fin n → R) →L[ℝ] (Fin n → R))
    (M : Matrix (Fin n) (Fin n) R) (hT : ∀ h i, T h i = ∑ k, M i k * h k) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ∑ k, ‖M i k‖ ≤ C) : ‖T‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun h => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))]
  intro i
  rw [hT]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm h k) (norm_nonneg _))).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)

theorem matCLM_comp_apply {T : (Fin n → R) →L[ℝ] (Fin n → R)} {M : Matrix (Fin n) (Fin n) R}
    (hT : ∀ h i, T h i = ∑ k, M i k * h k) (A : Matrix (Fin n) (Fin n) R) (h : Fin n → R)
    (i : Fin n) : (matCLM A ∘L T) h i = ∑ k, (A * M) i k * h k := by
  simp only [ContinuousLinearMap.comp_apply, matCLM_apply, hT, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem sub_apply_rowSum {T S : (Fin n → R) →L[ℝ] (Fin n → R)} {M N : Matrix (Fin n) (Fin n) R}
    (hT : ∀ h i, T h i = ∑ k, M i k * h k) (hS : ∀ h i, S h i = ∑ k, N i k * h k)
    (h : Fin n → R) (i : Fin n) : (T - S) h i = ∑ k, (M - N) i k * h k := by
  simp only [sub_apply, Pi.sub_apply, hT, hS, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem id_sub_matCLM_comp_apply {T : (Fin n → R) →L[ℝ] (Fin n → R)}
    {M : Matrix (Fin n) (Fin n) R} (hT : ∀ h i, T h i = ∑ k, M i k * h k)
    (A : Matrix (Fin n) (Fin n) R) (h : Fin n → R) (i : Fin n) :
    (ContinuousLinearMap.id ℝ (Fin n → R) - matCLM A ∘L T) h i = ∑ k, (1 - A * M) i k * h k := by
  rw [sub_apply, Pi.sub_apply, matCLM_comp_apply hT]
  simp only [ContinuousLinearMap.id_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Matrix

end RadiiPolynomial
