import RadiiPolynomial.Core.Theorem

/-!
# Periodic points from the open-set face

A period-`p` point of `g : E → E` on a finite-dimensional real normed space is a zero of
`z ↦ g^[p] z - z`. `periodicPoint_of_differentiableOn` applies the open-set face
`enclosure_of_differentiableOn` to this map and adds a minimality hypothesis on the ball, giving a
unique period-`p` point in the ball whose minimal period is exactly `p`.
-/

open Metric

namespace RadiiPolynomial

/-- A point fixed by `g^[p]` and by no `g^[q]` with `0 < q < p` has minimal period `p`. -/
theorem minimalPeriod_eq_of_no_smaller {α : Type*} {g : α → α} {x : α} {p : ℕ}
    (hppos : 0 < p) (hfix : g^[p] x = x)
    (hsmall : ∀ q, 0 < q → q < p → g^[q] x ≠ x) :
    Function.minimalPeriod g x = p := by
  have hper : Function.IsPeriodicPt g p x := hfix
  have hmpos : 0 < Function.minimalPeriod g x :=
    Function.minimalPeriod_pos_of_mem_periodicPts ⟨p, hppos, hper⟩
  rcases eq_or_lt_of_le (hper.minimalPeriod_le hppos) with h | h
  · exact h
  · exact absurd (Function.isPeriodicPt_minimalPeriod g x) (hsmall _ hmpos h)

/-- **Period-`p` points, open-set face.** `enclosure_of_differentiableOn` applied to
`z ↦ g^[p] z - z` (single radius `r₀`, the `Z₂` bound at `r₀`, the `radiiPolynomial` sign
condition), plus the minimality hypothesis on the ball: a unique period-`p` point in the closed
ball, with minimal period `p`. -/
theorem periodicPoint_of_differentiableOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} {p : ℕ} (hppos : 0 < p) {U : Set E} (hU : IsOpen U)
    {xBar : E} {A : E →L[ℝ] E} {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (g^[p] xBar - xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖ContinuousLinearMap.id ℝ E -
        A.comp (fderiv ℝ (fun z : E => g^[p] z - z) xBar)‖ ≤ Z₀)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀,
      ‖A.comp (fderiv ℝ (fun z : E => g^[p] z - z) c -
        fderiv ℝ (fun z : E => g^[p] z - z) xBar)‖ ≤ Z₂ r₀ * r₀)
    (hballU : closedBall xBar r₀ ⊆ U)
    (hf_diff : DifferentiableOn ℝ (fun z : E => g^[p] z - z) U)
    (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0)
    (h_minimal : ∀ q, 0 < q → q < p → ∀ y ∈ closedBall xBar r₀, g^[q] y ≠ y) :
    ∃ xTilde ∈ closedBall xBar r₀,
      Function.minimalPeriod g xTilde = p ∧
        ∀ y ∈ closedBall xBar r₀, g^[p] y = y → y = xTilde := by
  obtain ⟨xTilde, ⟨hmem, hzero⟩, huniq⟩ :=
    (enclosure_of_differentiableOn (f := fun z : E => g^[p] z - z) hU hr₀ h_Y₀ h_Z₀ h_Z₂
      hballU hf_diff h_radii).existsUnique
  exact ⟨xTilde, hmem,
    minimalPeriod_eq_of_no_smaller hppos (sub_eq_zero.mp hzero)
      (fun q hq hqp => h_minimal q hq hqp xTilde hmem),
    fun y hy hyfix => huniq y ⟨hy, sub_eq_zero.mpr hyfix⟩⟩

end RadiiPolynomial
