import RadiiPolynomial.Examples.IVP.Taylor.Example81.Analytic
import RadiiPolynomial.Applications.IVP.Taylor.Analyticity

/-!
# Example 8.1 — actual analyticity of the certified canonical solution

`logistic_analyticOnNhd`: the canonical solution `Example81.Cert.x_analytic` of
`Analytic.lean` is not merely a power series centred at zero, it is `AnalyticOnNhd ℝ`
on the whole interval `(-ν, ν)`. It is a one-line consumer of the generic
`IVP.analyticOnNhd_x_analytic`, and its axiom set is exactly that of
`Example81.Cert.main_theorem`. No complex-time statement is given for the scalar
logistic example.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example81.Cert

open Example81

/-- The canonical solution of the scalar logistic certificate is real analytic on
`(-ν, ν)`. -/
theorem logistic_analyticOnNhd :
    AnalyticOnNhd ℝ Example81.Cert.x_analytic
      (Set.Ioo (-(Example81.ν_val : ℝ)) Example81.ν_val) :=
  IVP.analyticOnNhd_x_analytic Example81.Cert.xTilde

end Example81.Cert
