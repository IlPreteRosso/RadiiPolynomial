import RadiiPolynomial.Examples.FiniteDimensional.Example245.Algebra
import RadiiPolynomial.Certification.LeanCertAdapter

/-!
# Example 2.4.5 — Certificate

Numerical verification of f(x) = x² - 2 near x̄ = 13/10.
All bound proofs use `leancert` (dyadic interval arithmetic), with `abs_le`
to split two-sided bounds.

Bound lemma statements use canonical norms (`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`)
from `RadiiPolynomial.Core`; `main_theorem` calls `general_radii_polynomial_theorem`
directly.
-/

open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap
open RadiiPolynomial Example245

namespace Example245.Cert

/-! ## Parameter definitions -/

noncomputable abbrev f     : ℝ → ℝ := fun x => x ^ 2 - 2
noncomputable abbrev xBar  : ℝ := 13 / 10
noncomputable abbrev A     : ℝ →L[ℝ] ℝ := smulCLM (19 / 50)
noncomputable abbrev A_dag : ℝ →L[ℝ] ℝ := smulCLM (13 / 5)
noncomputable abbrev Y₀_bound : ℝ := 1 / 8
noncomputable abbrev Z₀_bound : ℝ := 1 / 80
noncomputable abbrev Z₂_bound : ℝ → ℝ := fun _ => 19 / 25
noncomputable abbrev r₀    : ℝ := 3 / 20

/-! ## Bound proofs — all via leancert -/

private lemma Y₀_le : Y₀_norm f xBar A ≤ Y₀_bound := by
  unfold Y₀_norm
  simp only [A, f, xBar, Y₀_bound, smulCLM_apply, Real.norm_eq_abs]
  rw [abs_le]
  exact ⟨by leancert, by leancert⟩

private lemma Z₀_le : Z₀_norm A A_dag ≤ Z₀_bound := by
  unfold Z₀_norm
  rw [smulCLM_comp, id_sub_smulCLM, norm_smulCLM]
  simp only [Z₀_bound]
  rw [abs_le]
  exact ⟨by leancert, by leancert⟩

private lemma Z₁_le : Z₁_norm f xBar A A_dag ≤ 0 := by
  unfold Z₁_norm
  rw [fderiv_sq_sub_const, smulCLM_sub, smulCLM_comp, norm_smulCLM, xBar]
  rw [abs_le]
  exact ⟨by leancert, by leancert⟩

private lemma Z₂_le (c : ℝ) (hc : c ∈ closedBall xBar r₀) :
    Z₂_norm f xBar A c ≤ Z₂_bound r₀ * r₀ :=
  (Z₂_bound_sq_sub_const _ xBar 2 hc).trans
    (by simp only [Z₂_bound, r₀]
        exact (by leancert))

private lemma radii_neg : generalRadiiPolynomial Y₀_bound Z₀_bound 0 Z₂_bound r₀ < 0 := by
  unfold generalRadiiPolynomial Y₀_bound Z₀_bound Z₂_bound r₀
  exact (by leancert)

private lemma r₀_pos : 0 < r₀ := by
  unfold r₀; exact (by leancert)

private lemma A_inj : Function.Injective A :=
  smulCLM_injective (ne_of_gt ((by leancert)))

/-! ## Main Theorem -/

theorem main_theorem :
    ∃! xTilde ∈ closedBall xBar r₀, f xTilde = 0 :=
  general_radii_polynomial_theorem r₀_pos Y₀_le Z₀_le Z₁_le (fun c hc => Z₂_le c hc)
    (differentiable_sq_sub_const 2) radii_neg A_inj

theorem sqrt2 :
    ∃! xTilde ∈ closedBall (xBar : ℝ) r₀, xTilde ^ 2 = 2 := by
  obtain ⟨xTilde, ⟨hMem, hZero⟩, hUniq⟩ := main_theorem
  refine ⟨xTilde, ⟨hMem, ?_⟩, ?_⟩
  · simp only [f] at hZero; linarith
  · intro y ⟨hyMem, hySq⟩
    exact hUniq y ⟨hyMem, by simp only [f]; linarith⟩

end Example245.Cert
