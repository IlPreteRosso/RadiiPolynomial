import Mathlib.Analysis.Analytic.Uniqueness
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation

/-!
# Analytic extensionality for Taylor coefficient sequences

An element of `l1Weighted ν` is determined by its analytic realization near the
expansion centre.  This is the elementwise counterpart to the generator
extensionality used for morphisms out of the Taylor coefficient algebra.
-/

open Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

variable {ν : PosReal}

/-- The Taylor realization of a weighted coefficient sequence has its coefficient
sequence as a formal multilinear power series at the expansion centre. -/
theorem hasFPowerSeriesAt_eval (a : l1Weighted ν) :
    HasFPowerSeriesAt (l1Weighted.eval a)
      (FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a)) 0 := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a)
  have hradius : ((ν : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, PosReal.coe_toNNReal,
      Real.norm_eq_abs] using l1Weighted.summable_weighted a
  refine ⟨(ν : ℝ≥0), ?_⟩
  refine
    { r_le := hradius
      r_pos := by exact_mod_cast ν.2
      hasSum := ?_ }
  intro y hy
  have hyν : |y| ≤ (ν : ℝ) := by
    rw [Metric.eball_coe, mem_ball_zero_iff] at hy
    simpa only [Real.norm_eq_abs, PosReal.coe_toNNReal] using hy.le
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]
  exact (l1Weighted.summable_eval a hyν).hasSum

/-- Two Taylor coefficient sequences are equal when their analytic realizations
agree in a neighbourhood of the expansion centre. -/
theorem ext_of_eventuallyEq_eval {a b : l1Weighted ν}
    (h : l1Weighted.eval a =ᶠ[nhds 0] l1Weighted.eval b) : a = b := by
  apply l1Weighted.ext
  have hp :
      FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a) =
        FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq b) :=
    (hasFPowerSeriesAt_eval a).eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesAt_eval b) h
  exact congrFun (FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hp)

end l1Weighted

end RadiiPolynomial
