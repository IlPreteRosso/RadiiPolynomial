import RadiiPolynomial.Core.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Univariate
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds

/-!
# Degree-general `Z₂` engine on a normed commutative algebra

`Z₂_ball_bound_of_mul_lipschitzOn`: if, on the closed ball `B̄_{r₀}(x̄)` of a normed commutative
real algebra `𝔸`, the derivative of `f` is left multiplication by an element `g x` plus a constant
operator `K`, and `g` is `L`-Lipschitz towards the centre, then
`Z₂_norm f x̄ T c ≤ L · ‖T‖ · r₀` for every `c` in the ball. No degree, algebra or operator is
fixed; polynomial faces specialize `g` to a polynomial evaluation.

Polynomial faces (any degree):
* `Z₂_ball_bound_of_compPoly` — the derivative is left multiplication by a univariate
  polynomial `Q(x)`; the constant is the syntactic Lipschitz constant of `Q` at a radius
  `R ≥ ‖x̄‖ + r₀`;
* `Z₂_ball_bound_of_polyMap` — for `f = P(·) - b` the constant is
  `derivativeLipschitzBound P` at that radius.
-/

open Metric MvPolyBridge

namespace RadiiPolynomial

section Z2

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **Degree-general `Z₂` engine.** If on the ball the derivative is left multiplication by an
element `g x` (plus a constant operator `K`) and `g` is `L`-Lipschitz towards the centre, then
`Z₂_norm ≤ L · ‖T‖ · r₀`. General in `𝔸`, `f`, `g`, `K`, `T`, `L`, `r₀`. -/
theorem Z₂_ball_bound_of_mul_lipschitzOn {f g : 𝔸 → 𝔸} {K : 𝔸 →L[ℝ] 𝔸} {xBar : 𝔸}
    {r₀ L : ℝ}
    (hf : ∀ x ∈ Metric.closedBall xBar r₀,
      fderiv ℝ f x = ContinuousLinearMap.mul ℝ 𝔸 (g x) + K)
    (hg : ∀ x ∈ Metric.closedBall xBar r₀, ‖g x - g xBar‖ ≤ L * ‖x - xBar‖) (hL : 0 ≤ L)
    (T : 𝔸 →L[ℝ] 𝔸) (c : 𝔸) (hc : c ∈ Metric.closedBall xBar r₀) :
    Z₂_norm f xBar T c ≤ L * ‖T‖ * r₀ := by
  have hr : 0 ≤ r₀ := Metric.nonempty_closedBall.mp ⟨c, hc⟩
  have hcx : ‖c - xBar‖ ≤ r₀ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hc
  unfold Z₂_norm
  rw [hf c hc, hf xBar (Metric.mem_closedBall_self hr), add_sub_add_right_eq_sub, ← map_sub]
  have h1 : ‖ContinuousLinearMap.mul ℝ 𝔸 (g c - g xBar)‖ ≤ L * r₀ :=
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ 𝔸 _).trans
      ((hg c hc).trans (mul_le_mul_of_nonneg_left hcx hL))
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg T)).trans (le_of_eq ?_)
  ring

/-- **`CompPoly` face of the `Z₂` engine.** The derivative is left multiplication by a
polynomial `Q(x)` (any degree); the constant is the syntactic Lipschitz constant of `Q` at a
radius `R ≥ ‖x̄‖ + r₀`. General in `𝔸`, `f`, `Q`, `K`, `T`, `R`, `r₀`. -/
theorem Z₂_ball_bound_of_compPoly [NormOneClass 𝔸] {f : 𝔸 → 𝔸} (Q : CompPoly 1)
    {K : 𝔸 →L[ℝ] 𝔸} {xBar : 𝔸} {r₀ R : ℝ}
    (hf : ∀ x ∈ Metric.closedBall xBar r₀,
      fderiv ℝ f x = ContinuousLinearMap.mul ℝ 𝔸 (Q.evalBanach (fun _ => x)) + K)
    (hR : ‖xBar‖ + r₀ ≤ R) (T : 𝔸 →L[ℝ] 𝔸) (c : 𝔸) (hc : c ∈ Metric.closedBall xBar r₀) :
    Z₂_norm f xBar T c ≤ Q.lipschitzBound (fun _ => R) * ‖T‖ * r₀ := by
  have hr : 0 ≤ r₀ := Metric.nonempty_closedBall.mp ⟨c, hc⟩
  have hxR : ‖xBar‖ ≤ R := by linarith
  refine Z₂_ball_bound_of_mul_lipschitzOn hf (fun x hx => ?_)
    (CompPoly.lipschitzBound_nonneg Q _ fun _ => (norm_nonneg xBar).trans hxR) T c hc
  have hx' : ‖x - xBar‖ ≤ r₀ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hx
  have hxn : ‖x‖ ≤ R := by linarith [norm_sub_norm_le x xBar]
  exact CompPoly.norm_evalBanach_one_sub_le Q x xBar R hxn hxR

/-- **Polynomial-map face.** For `f = P(·) - b` the constant is
`derivativeLipschitzBound P` at a radius `R ≥ ‖x̄‖ + r₀`. General in `𝔸`, `P`, `b`, `T`,
`R`, `r₀`. -/
theorem Z₂_ball_bound_of_polyMap [NormOneClass 𝔸] (P : CompPoly 1) (b : 𝔸) {xBar : 𝔸}
    {r₀ R : ℝ} (hR : ‖xBar‖ + r₀ ≤ R) (T : 𝔸 →L[ℝ] 𝔸) (c : 𝔸)
    (hc : c ∈ Metric.closedBall xBar r₀) :
    Z₂_norm (CompPoly.polyMap P b) xBar T c ≤
      P.derivativeLipschitzBound (fun _ => R) * ‖T‖ * r₀ := by
  rw [CompPoly.derivativeLipschitzBound_one]
  exact Z₂_ball_bound_of_compPoly (P.pderiv 0) (K := 0)
    (fun x _ => by rw [CompPoly.fderiv_polyMap, add_zero]) hR T c hc

end Z2

end RadiiPolynomial
