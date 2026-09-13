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

/-- **Existence**: `x_analytic` is an analytic solution. -/
theorem x_analytic_isAnalyticSolution :
    IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj x_analytic :=
  data.x_analytic_isAnalyticSolution_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg
    xTilde xTilde_ball xTilde_G_zero

/-- **Pinning**: any analytic candidate equals `x_analytic` on `(-ν, ν)`. -/
theorem analytic_eq_canonical
    (g : ℝ → Fin L → ℝ)
    (hg : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g) :
    Set.EqOn g x_analytic (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_eq_canonical_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg
    xTilde xTilde_ball xTilde_G_zero g hg

/-- **Function-space uniqueness**: any two analytic candidates agree. -/
theorem analytic_unique
    (g₁ g₂ : ℝ → Fin L → ℝ)
    (h₁ : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g₁)
    (h₂ : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g₂) :
    Set.EqOn g₁ g₂ (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_unique_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg
    g₁ g₂ h₁ h₂

/-- **Existence + uniqueness for the Lorenz IVP** on `(-ν, ν)`. -/
theorem analytic_existsUnique :
    ∃ u : ℝ → Fin L → ℝ,
      IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj u ∧
      ∀ v : ℝ → Fin L → ℝ,
        IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj v →
        Set.EqOn v u (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_existsUnique_of_compPoly_of_radii f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg

end Example83.Cert
