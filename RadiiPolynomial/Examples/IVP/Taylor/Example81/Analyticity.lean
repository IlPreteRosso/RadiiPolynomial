import RadiiPolynomial.Examples.IVP.Taylor.Example81.Analytic
import RadiiPolynomial.Applications.IVP.Taylor.Analyticity

/-!
# Example 8.1 — actual analyticity of the certified canonical solution

Additive strengthening of `Analytic.lean`: the canonical solution
`Example81.Cert.x_analytic` is not merely a power series centred at zero, it is
`AnalyticOnNhd ℝ` on the whole interval `(-ν, ν)`. It is a one-line consumer of
the generic `IVP.analyticOnNhd_x_analytic`.

The certificate, the competitor class `IVP.IsAnalyticSolution`, and the public
surface of `Analytic.lean` are untouched; the axiom set of this theorem is
exactly that of `Example81.Cert.main_theorem`. No complex-time statement is
given for the scalar logistic example.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example81.Cert

open Example81

/-- The scalar logistic certificate now has an actual analytic canonical solution. -/
theorem logistic_analyticOnNhd :
    AnalyticOnNhd ℝ Example81.Cert.x_analytic
      (Set.Ioo (-(Example81.ν_val : ℝ)) Example81.ν_val) :=
  IVP.analyticOnNhd_x_analytic Example81.Cert.xTilde

end Example81.Cert
