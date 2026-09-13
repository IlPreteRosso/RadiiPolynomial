import RadiiPolynomial.Examples.IVP.Taylor.Example83.Analytic
import RadiiPolynomial.Applications.IVP.Taylor.Analyticity

/-!
# Example 8.3 — actual analyticity of the certified canonical solution

Additive strengthening of `Analytic.lean`: the canonical Lorenz solution
`Example83.Cert.x_analytic` is not merely a power series centred at zero, it is
`AnalyticOnNhd ℝ` on the whole interval `(-ν, ν)`, and that analyticity is
attached to the existing existence/uniqueness statement.

Mirrors `Example81/Analyticity.lean`; both are one-line consumers of the generic
`IVP.analyticOnNhd_x_analytic`. The complex-time statements stay in
`Example83/ComplexTime.lean`. The certificate, the competitor class
`IVP.IsAnalyticSolution`, and the public surface of `Analytic.lean` are
untouched; the axiom set of these theorems is exactly that of
`Example83.Cert.main_theorem`.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example83.Cert

open Example83

/-- The Lorenz certificate now has an actual analytic canonical solution. -/
theorem lorenz_analyticOnNhd :
    AnalyticOnNhd ℝ Example83.Cert.x_analytic
      (Set.Ioo (-(Example83.ν_val : ℝ)) Example83.ν_val) :=
  IVP.analyticOnNhd_x_analytic Example83.Cert.xTilde

/-- Analyticity is attached to the selected Lorenz solution, while uniqueness
still compares it against every differentiable in-ball solution. -/
theorem lorenz_analytic_existsUnique :
    ∃ u : ℝ → Fin Example83.L → ℝ,
      AnalyticOnNhd ℝ u (Set.Ioo (-(Example83.ν_val : ℝ)) Example83.ν_val) ∧
      IsAnalyticSolution (ν := Example83.ν_val) Example83.f_cpoly Example83.x₀
        Example83.Cert.R_traj u ∧
      ∀ v : ℝ → Fin Example83.L → ℝ,
        IsAnalyticSolution (ν := Example83.ν_val) Example83.f_cpoly Example83.x₀
          Example83.Cert.R_traj v →
        Set.EqOn v u (Set.Ioo (-(Example83.ν_val : ℝ)) Example83.ν_val) :=
  ⟨Example83.Cert.x_analytic, lorenz_analyticOnNhd,
    Example83.Cert.x_analytic_isAnalyticSolution, Example83.Cert.analytic_eq_canonical⟩

end Example83.Cert
