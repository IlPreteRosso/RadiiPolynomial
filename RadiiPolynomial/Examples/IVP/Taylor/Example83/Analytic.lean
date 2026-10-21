import RadiiPolynomial.Examples.IVP.Taylor.Example83.Certificate
import RadiiPolynomial.Applications.IVP.Taylor.Analytic

/-!
# Example 8.3 — Analytic uniqueness corollary (function-space side)

Function-space lift of `Certificate.lean`'s `main_theorem` for the Lorenz IVP.
Mirrors `Example81/Analytic.lean`: nothing structural is stated. The
`IVP.StdIVPData.analytic_*_of_compPoly_of_radii` faces read the coefficient
nonlinearity off `f_cpoly` and the contraction `Z₀ < 1` off the same five facts
`main_theorem` consumed. The zero is named (`xTilde := main_theorem.exists.choose`)
because `Analyticity.lean` and `ComplexTime.lean` consume the canonical solution
`x_analytic` and the zero itself.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example83.Cert

open Example83

abbrev R_traj : ℝ := ‖(data.abar : XL1 ν_val L)‖ + (r_minus : ℝ)

/-- Canonical sequence-space zero from `main_theorem`. -/
def xTilde : XL1 ν_val L := main_theorem.exists.choose

private lemma xTilde_spec :
    xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ) ∧
    data.G f x₀ xTilde = 0 :=
  main_theorem.exists.choose_spec

lemma xTilde_ball : xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ) :=
  xTilde_spec.1

lemma xTilde_G_zero : data.G f x₀ xTilde = 0 := xTilde_spec.2

/-- Canonical analytic solution `t ↦ (eval(xTilde l, t))_l`. -/
def x_analytic : ℝ → Fin L → ℝ := IVP.x_analytic xTilde

/-- **Existence**: `x_analytic` is a ball solution (`IsBallSolution`). -/
theorem x_analytic_isBallSolution :
    IVP.IsBallSolution (ν := ν_val) f_cpoly x₀ R_traj x_analytic :=
  data.x_analytic_isBallSolution_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg
    xTilde xTilde_ball xTilde_G_zero

/-- **Pinning**: any ball solution equals `x_analytic` on `(-ν, ν)`. -/
theorem analytic_eq_canonical
    (g : ℝ → Fin L → ℝ)
    (hg : IVP.IsBallSolution (ν := ν_val) f_cpoly x₀ R_traj g) :
    Set.EqOn g x_analytic (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_eq_canonical_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg
    xTilde xTilde_ball xTilde_G_zero g hg


/-- **Existence + uniqueness for the Lorenz IVP** on `(-ν, ν)`. -/
theorem analytic_existsUnique :
    ∃ u : ℝ → Fin L → ℝ,
      IVP.IsBallSolution (ν := ν_val) f_cpoly x₀ R_traj u ∧
      ∀ v : ℝ → Fin L → ℝ,
        IVP.IsBallSolution (ν := ν_val) f_cpoly x₀ R_traj v →
        Set.EqOn v u (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_existsUnique_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg

/-! ## Per-component enclosure

`IsBallSolution` charges every component the uniform radius `R_traj = ‖ā‖ + r₀`, and
`‖ā‖ = max_l ‖ā_l‖` is set by the `y`-component (certified bounds `20, 26, 11` for
`x, y, z`). The box face `IVP.eval_traj_in_box_of_mem_closedBall` keeps each component's
own centre norm: for `z` the certified radius drops from `26 + r₀` to `11 + r₀`. Both
numbers are upper enclosures (certified bounds on `‖ā_l‖`, not exact trajectory extrema). The
uniqueness statements above are unchanged; the box lies inside the ball. -/

/-- **Per-component enclosure** of the canonical Lorenz solution: on `[-ν, ν]` its `l`-th
component stays within `‖ā_l‖ + r₀` of `0`. -/
theorem x_analytic_mem_box {t : ℝ} (ht : |t| ≤ (ν_val : ℝ)) :
    x_analytic t ∈ Set.pi Set.univ fun l =>
      Metric.closedBall (0 : ℝ) (‖(data.abar : XL1 ν_val L) l‖ + (r_minus : ℝ)) :=
  IVP.eval_traj_in_box_of_mem_closedBall xTilde_ball ht

/-- **The `z`-component enclosure**: `|z(t)| ≤ 11 + r₀` on `[-ν, ν]`, against the uniform
trajectory radius `R_traj = ‖ā‖ + r₀ ≤ 26 + r₀` of `IsBallSolution`; both are upper enclosures,
not exact extrema. -/
theorem abs_x_analytic_two_le {t : ℝ} (ht : |t| ≤ (ν_val : ℝ)) :
    |x_analytic t 2| ≤ 11 + (r_minus : ℝ) := by
  have h := Set.mem_univ_pi.mp (x_analytic_mem_box ht) 2
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
  exact h.trans (add_le_add abar_norm_2_le le_rfl)

end Example83.Cert
