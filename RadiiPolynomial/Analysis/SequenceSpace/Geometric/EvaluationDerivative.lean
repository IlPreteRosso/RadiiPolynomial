import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import RadiiPolynomial.Analysis.Calculus.ScalarSeries

/-!
# Term-by-Term Differentiation of Weighted Sequence Evaluation

Differentiates `l1Weighted.eval` strictly inside its disk of convergence. This analytic
layer uses the coordinate presentation of the universal geometric evaluation;
`Geometric/Evaluation.lean` identifies it with `aeval_of_norm_le` on its admissible disc.
The derivative is `ScalarSeries.hasDerivAt_ofScalars` at the power series
`hasFPowerSeriesOnBall_eval`.
-/

open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

namespace l1Weighted

/-- Term-by-term differentiation of `eval` strictly inside the disk of convergence. -/
theorem hasDerivAt_eval (a : l1Weighted ν) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (l1Weighted.eval a) (l1Omega.eval (derivShift a) t) t := by
  have hm : t ∈ Metric.eball (0 : ℝ) (ν : ℝ≥0) := by
    simpa only [Metric.eball_coe, mem_ball_zero_iff, Real.norm_eq_abs,
      PosReal.coe_toNNReal] using ht
  convert ScalarSeries.hasDerivAt_ofScalars (hasFPowerSeriesOnBall_eval a) hm using 1
  exact tsum_congr fun n => by rw [derivShift_apply]

end l1Weighted

end RadiiPolynomial
