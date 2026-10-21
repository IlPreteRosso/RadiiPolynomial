import Mathlib.Analysis.Analytic.Uniqueness
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation

/-!
# Analytic extensionality for Taylor coefficient sequences

An element of `l1Weighted ν` is determined by its analytic realization near the
expansion centre.  This is the elementwise counterpart to the generator
extensionality used for morphisms out of the Taylor coefficient algebra.

The converse representation of a real function analytic at `0` is recovered in
`B5RecordTaylorAnalytic`: such a function is,
near `0`, the realization of a coefficient sequence at some positive radius. The radius is
existential; no maximal radius is prescribed and no algorithm computes one.
-/

open Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

variable {ν : PosReal}

/-- The real power series of a coefficient sequence converges on the full weight ball
(radius `ν`): the weighted-ℓ¹ domination is the only input. -/
theorem hasFPowerSeriesOnBall_eval (a : l1Weighted ν) :
    HasFPowerSeriesOnBall (l1Weighted.eval a)
      (FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a)) 0 (ν : ℝ≥0) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a)
  have hradius : ((ν : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, PosReal.coe_toNNReal,
      Real.norm_eq_abs] using l1Weighted.summable_weighted a
  refine { r_le := hradius, r_pos := by exact_mod_cast ν.2, hasSum := ?_ }
  intro y hy
  have hyν : |y| ≤ (ν : ℝ) := by
    rw [Metric.eball_coe, mem_ball_zero_iff] at hy
    simpa only [Real.norm_eq_abs, PosReal.coe_toNNReal] using hy.le
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  exact (l1Weighted.summable_eval a hyν).hasSum




end l1Weighted

end RadiiPolynomial
