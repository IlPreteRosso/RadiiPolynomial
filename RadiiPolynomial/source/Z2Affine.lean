import RadiiPolynomial.source.Core
import RadiiPolynomial.source.lpSpace.LpOneBanachAlgebra

/-!
# Z₂ Bounds for Affine-Fderiv Maps on `l1Weighted ν`

Generic Z₂ infrastructure for maps whose Fréchet derivative is affine in `leftMul`:
  `fderiv ℝ f x = α • leftMul x + K`
where `α : ℝ` is a scalar and `K` is a constant CLM.

This captures the algebraic structure of any polynomial map of degree ≤ 2 on `l1Weighted ν`
(e.g., `f(x) = x² - c` has `fderiv f x = 2 • leftMul x`, i.e. `α = 2, K = 0`).

## Main results

- `fderiv_diff_of_affine_leftMul`: fderiv difference factors through `leftMul`
- `norm_fderiv_diff_of_affine_leftMul`: norm bound `|α| * ‖c - a‖`
- `Z₂_ball_bound_of_affine_leftMul`: Z₂ ball bound `|α| * ‖A‖ * r₀`
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

/-- Fderiv difference factors through `leftMul` for affine-fderiv maps.
If `fderiv ℝ f x = α • leftMul x + K` for all `x`, then
`fderiv ℝ f c - fderiv ℝ f a = α • leftMul (c - a)`. -/
lemma fderiv_diff_of_affine_leftMul
    {f : l1Weighted ν → l1Weighted ν} {α : ℝ}
    {K : l1Weighted ν →L[ℝ] l1Weighted ν}
    (hf : ∀ x, fderiv ℝ f x = α • l1Weighted.leftMul x + K)
    (c a : l1Weighted ν) :
    fderiv ℝ f c - fderiv ℝ f a = α • l1Weighted.leftMul (c - a) := by
  rw [hf c, hf a]
  simp [smul_sub, l1Weighted.leftMul_sub]

/-- Norm bound on fderiv difference for affine-fderiv maps.
`‖fderiv ℝ f c - fderiv ℝ f a‖ ≤ |α| * ‖c - a‖`. -/
lemma norm_fderiv_diff_of_affine_leftMul
    {f : l1Weighted ν → l1Weighted ν} {α : ℝ}
    {K : l1Weighted ν →L[ℝ] l1Weighted ν}
    (hf : ∀ x, fderiv ℝ f x = α • l1Weighted.leftMul x + K)
    (c a : l1Weighted ν) :
    ‖fderiv ℝ f c - fderiv ℝ f a‖ ≤ |α| * ‖c - a‖ := by
  rw [fderiv_diff_of_affine_leftMul hf]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (l1Weighted.norm_leftMul_le _) (abs_nonneg _)

/-- Z₂ ball bound for affine-fderiv maps: for `c ∈ closedBall(xBar, r₀)`,
`Z₂_norm f xBar A c ≤ |α| * ‖A‖ * r₀`.

Plugs directly into `general_radii_polynomial_theorem`. -/
lemma Z₂_ball_bound_of_affine_leftMul
    {f : l1Weighted ν → l1Weighted ν} {α : ℝ}
    {K : l1Weighted ν →L[ℝ] l1Weighted ν}
    (hf : ∀ x, fderiv ℝ f x = α • l1Weighted.leftMul x + K)
    (A : l1Weighted ν →L[ℝ] l1Weighted ν) (xBar : l1Weighted ν)
    {r₀ : ℝ} (c : l1Weighted ν) (hc : c ∈ Metric.closedBall xBar r₀) :
    Z₂_norm f xBar A c ≤ |α| * ‖A‖ * r₀ := by
  unfold Z₂_norm
  rw [fderiv_diff_of_affine_leftMul hf]
  calc ‖A.comp (α • l1Weighted.leftMul (c - xBar))‖
      ≤ ‖A‖ * ‖α • l1Weighted.leftMul (c - xBar)‖ := opNorm_comp_le _ _
    _ ≤ ‖A‖ * (|α| * ‖c - xBar‖) := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (l1Weighted.norm_leftMul_le _) (abs_nonneg _)
    _ = |α| * ‖A‖ * ‖c - xBar‖ := by ring
    _ ≤ |α| * ‖A‖ * r₀ := by
        rw [mem_closedBall, dist_eq_norm] at hc
        gcongr

end RadiiPolynomial
