import RadiiPolynomial.Core.AlgebraZ2
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic

/-!
# Z₂ Bounds for Affine-Fderiv Maps on `l1Weighted ν`

`Z₂` bound for maps on `l1Weighted ν` whose Fréchet derivative is affine in `leftMul`:
  `fderiv ℝ f x = α • leftMul x + K`
where `α : ℝ` is a scalar and `K` is a constant CLM. It is the power-series case of the
degree-general `Z₂` engine `Z₂_ball_bound_of_mul_lipschitzOn` (`Core/AlgebraZ2`); polynomial
maps of any degree use `Z₂_ball_bound_of_polyMap` directly.

## Main result

- `Z₂_ball_bound_of_affine_leftMul`: Z₂ ball bound `|α| * ‖A‖ * r₀`, a corollary of the engine
  with `g x = α • x`
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial MvPolyBridge

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}



/-- Z₂ ball bound for affine-fderiv maps: for `c ∈ closedBall(xBar, r₀)`,
`Z₂_norm f xBar A c ≤ |α| * ‖A‖ * r₀`.

Plugs directly into `general_radii_polynomial_theorem`. -/
lemma Z₂_ball_bound_of_affine_leftMul
    {f : l1Weighted ν → l1Weighted ν} {α : ℝ}
    {K : l1Weighted ν →L[ℝ] l1Weighted ν}
    (hf : ∀ x, fderiv ℝ f x = α • l1Weighted.leftMul x + K)
    (A : l1Weighted ν →L[ℝ] l1Weighted ν) (xBar : l1Weighted ν)
    {r₀ : ℝ} (c : l1Weighted ν) (hc : c ∈ Metric.closedBall xBar r₀) :
    Z₂_norm f xBar A c ≤ |α| * ‖A‖ * r₀ :=
  Z₂_ball_bound_of_mul_lipschitzOn (g := fun x => α • x)
    (fun x _ => by rw [hf x, map_smul])
    (fun x _ => by rw [← smul_sub, norm_smul, Real.norm_eq_abs])
    (abs_nonneg α) A c hc


end RadiiPolynomial
