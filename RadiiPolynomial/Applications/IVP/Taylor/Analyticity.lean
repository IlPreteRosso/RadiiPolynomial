import RadiiPolynomial.Applications.IVP.Taylor.Analytic
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Analytic

/-!
# Real analyticity of the canonical Taylor trajectory

The canonical Taylor trajectory `IVP.x_analytic` of a coefficient vector is
`AnalyticOnNhd ℝ` on the whole open interval `(-ν, ν)`, not merely a power series
centred at zero.

This is the real-variable half of what used to live in
`Applications/IVP/Taylor/ComplexTime.lean`; it is separated so that an example
asking only for real analyticity (`Example81/Analyticity.lean`,
`Example83/Analyticity.lean`) does not have to import the complex-time layer.
`ComplexTime.lean` imports this module and adds the holomorphic trajectory on the
complex disc.
-/

open scoped NNReal ENNReal Topology
open RadiiPolynomial MvPolyBridge

noncomputable section

namespace IVP

variable {ν : PosReal} {L : ℕ}

/-- Every canonical Taylor trajectory is analytic on its full open real interval. -/
theorem analyticOnNhd_x_analytic (a : XL1 ν L) :
    AnalyticOnNhd ℝ (IVP.x_analytic a) (Set.Ioo (-(ν : ℝ)) ν) := by
  -- `convert!` rather than `simpa`: the `NormedSpace ℝ ℝ` instance on the target is the
  -- `RCLike` one, which `simpa` does not identify with `NormedField.toNormedSpace`.
  convert! AnalyticOnNhd.pi (fun l => l1Weighted.analyticOnNhd_eval (a l)) using 1
  simp only [Real.ball_eq_Ioo, zero_sub, zero_add]

end IVP

end
