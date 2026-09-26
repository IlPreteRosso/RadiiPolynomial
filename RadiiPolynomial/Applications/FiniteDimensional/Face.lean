import RadiiPolynomial.Core.Theorem
import RadiiPolynomial.Operators.Matrix.SupNorm

/-!
# Finite-dimensional face in row-sum form

For `f : R^n → R^n` over a finite-dimensional normed real algebra `R` (sup norm on
`R^n = Fin n → R`), with derivative data `D x` given on the closed ball `B̄(x̄, r₀)` in row form
`D x h i = Σₖ J x i k * h k` and an approximate inverse given by a matrix `A`, `Y₀` bounds every
entry of the vector `A f(x̄)`, `Z₀` every row sum `Σₖ ‖(1 - A J(x̄)) i k‖`, and `Z₂ r₀` every row sum
`Σₖ ‖(A (J c - J x̄)) i k‖` for `c` in the ball.
`enclosure_of_rowSum` turns them into an `Enclosure` through the local engine
`enclosure_of_radii`; no global differentiability is assumed.
-/

open scoped BigOperators
open Metric

namespace RadiiPolynomial

section RowSumFace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]
  {n : ℕ} [NeZero n] {f : (Fin n → R) → (Fin n → R)}
  {D : (Fin n → R) → ((Fin n → R) →L[ℝ] (Fin n → R))}
  {J : (Fin n → R) → Matrix (Fin n) (Fin n) R} {A : Matrix (Fin n) (Fin n) R}
  {xBar : Fin n → R} {r₀ Y₀ Z₀ Z₂ : ℝ}

/-- **Row-sum face, local form.** The derivative data `hf`, `hD` are required on the closed ball
only. Output: the full `Enclosure` (`A` invertible, `D c` invertible on the ball, a unique zero
in the closed ball, lying in the open ball). -/
theorem enclosure_of_rowSum
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (D x) (closedBall xBar r₀) x)
    (hD : ∀ x ∈ closedBall xBar r₀, ∀ h i, D x h i = ∑ k, J x i k * h k) (hr₀ : 0 < r₀)
    (hY : ∀ i, ‖∑ j, A i j * f xBar j‖ ≤ Y₀)
    (hZ₀ : ∀ i, ∑ k, ‖(1 - A * J xBar) i k‖ ≤ Z₀)
    (hZ₂ : ∀ c ∈ closedBall xBar r₀, ∀ i, ∑ k, ‖(A * (J c - J xBar)) i k‖ ≤ Z₂ * r₀)
    (hp : radiiPolynomial Y₀ Z₀ (fun _ => Z₂) r₀ < 0) :
    Enclosure f D (matCLM A) xBar r₀ := by
  have hx : xBar ∈ closedBall xBar r₀ := mem_closedBall_self hr₀.le
  have i0 : Fin n := 0
  refine enclosure_of_radii (Z₂ := fun _ => Z₂) hr₀ ?_ ?_ (fun c hc => ?_) hf hp
  · rw [pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hY i0))]
    intro i
    rw [matCLM_apply]
    exact hY i
  · exact opNorm_le_of_rowSum _ _ (id_sub_matCLM_comp_apply (hD xBar hx) A)
      ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hZ₀ i0)) hZ₀
  · exact opNorm_le_of_rowSum _ _
      (matCLM_comp_apply (sub_apply_rowSum (hD c hc) (hD xBar hx)) A)
      ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hZ₂ c hc i0)) (hZ₂ c hc)

end RowSumFace

end RadiiPolynomial
