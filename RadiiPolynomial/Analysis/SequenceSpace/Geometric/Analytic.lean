import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import RadiiPolynomial.Analysis.Calculus.ScalarSeries

/-!
# Full-disc analyticity of Taylor coefficient realizations

Sequence-space layer, Taylor (geometric) carrier, above `Geometric/AnalyticExt.lean`:
the realization of an element of `l1Weighted ν` is analytic on the *whole* weight
ball (`analyticOnNhd_eval`, from `hasFPowerSeriesOnBall_eval`), and the same
coefficient estimate gives its complex counterpart `l1Weighted.complexEval` on the
open complex disc together with a termwise derivative identity through `derivShift`.

The coefficient carrier stays real: complex evaluation changes the target of the algebra
homomorphism, not the coefficients or any certificate. The polynomial-substitution identity
for `complexEval` lives with its consumer in `Applications/IVP/Taylor/ComplexTime.lean`.
-/

open scoped ENNReal NNReal Topology

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

variable {ν : PosReal}

/-- The Taylor realization is real-analytic on the whole open interval
`(-ν, ν)`. -/
theorem analyticOnNhd_eval (a : l1Weighted ν) :
    AnalyticOnNhd ℝ (l1Weighted.eval a) (Metric.ball 0 (ν : ℝ)) := by
  simpa only [Metric.eball_coe, PosReal.coe_toNNReal]
    using (hasFPowerSeriesOnBall_eval a).analyticOnNhd

/-- The total complex series function whose restriction to the closed disc is `evalC`. -/
def complexEval (a : l1Weighted ν) (z : ℂ) : ℂ :=
  ∑' n, (l1Weighted.toSeq a n : ℂ) * z ^ n

/-- Complex synthesis for the derivative-weighted coefficient space. -/
def complexOmegaEval (b : l1Omega ν) (z : ℂ) : ℂ :=
  ∑' n, (l1Omega.toSeq b n : ℂ) * z ^ n

/-- The same coefficient sequence read over `ℂ` is a power series of `complexEval a` on the
open complex disc of radius `ν`, as in the real case. -/
theorem hasFPowerSeriesOnBall_complexEval (a : l1Weighted ν) :
    HasFPowerSeriesOnBall (complexEval a)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (l1Weighted.toSeq a n : ℂ)))
      0 (ν : ℝ≥0) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (l1Weighted.toSeq a n : ℂ))
  have hradius : ((ν : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, PosReal.coe_toNNReal,
      Complex.norm_real, Real.norm_eq_abs] using l1Weighted.summable_weighted a
  have hpos : 0 < ((ν : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast ν.2
  have hp := (p.hasFPowerSeriesOnBall (hpos.trans_le hradius)).mono hpos hradius
  convert hp using 1
  funext z
  simp only [complexEval, FormalMultilinearSeries.sum, p,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

/-- Holomorphy holds on the whole open disc of the coefficient weight. -/
theorem analyticOnNhd_complexEval (a : l1Weighted ν) :
    AnalyticOnNhd ℂ (complexEval a) (Metric.ball 0 (ν : ℝ)) := by
  simpa only [Metric.eball_coe, PosReal.coe_toNNReal]
    using (hasFPowerSeriesOnBall_complexEval a).analyticOnNhd

/-- The series is the existing algebra-hom evaluation on its closed domain. -/
theorem complexEval_eq_evalC (a : l1Weighted ν) (z : ℂ) (hz : ‖z‖ ≤ (ν : ℝ)) :
    complexEval a z = l1Weighted.evalC ν z hz a :=
  (l1Weighted.evalC_apply ν z hz a).symm

/-- The complex derivative is synthesis of the same coefficient derivative shift. -/
theorem hasDerivAt_complexEval (a : l1Weighted ν) {z : ℂ} (hz : ‖z‖ < (ν : ℝ)) :
    HasDerivAt (complexEval a) (complexOmegaEval (derivShift a) z) z := by
  have hm : z ∈ Metric.eball (0 : ℂ) (ν : ℝ≥0) := by
    simpa only [Metric.eball_coe, mem_ball_zero_iff, PosReal.coe_toNNReal] using hz
  convert ScalarSeries.hasDerivAt_ofScalars (hasFPowerSeriesOnBall_complexEval a) hm using 1
  refine tsum_congr fun n => ?_
  rw [derivShift_apply]
  push_cast
  ring

end l1Weighted

end RadiiPolynomial
