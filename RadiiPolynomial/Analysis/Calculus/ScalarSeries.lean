import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Derivatives of scalar power series

Carrier-neutral facts about a scalar power series `∑ cₙ zⁿ`, written as Mathlib's
`FormalMultilinearSeries.ofScalars 𝕜 c`, over a nontrivially normed field `𝕜`.

* `apply_one_comp_derivSeries_ofScalars`: evaluating the derivative series at `1` gives the
  scalar series of the shifted coefficients `(n + 1) c_(n+1)` (an identity of formal series;
  no completeness or convergence).
* `hasDerivAt_ofScalars`: if `f` has the power series `ofScalars 𝕜 c` on the ball `B(0, r)`,
  then at every `z ∈ B(0, r)` the derivative of `f` is `∑ₙ (n + 1) c_(n+1) zⁿ`
  (`CompleteSpace 𝕜`, used by Mathlib's analytic differentiation).

Consumed by the real and complex Taylor evaluation derivatives `l1Weighted.hasDerivAt_eval` and
`l1Weighted.hasDerivAt_complexEval`.
-/

open scoped ENNReal

namespace RadiiPolynomial.ScalarSeries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Evaluation at `1` turns the derivative series of `∑ cₙ zⁿ` into the scalar series of the
shifted coefficients `(n + 1) c_(n+1)`. -/
theorem apply_one_comp_derivSeries_ofScalars (c : ℕ → 𝕜) :
    (ContinuousLinearMap.apply 𝕜 𝕜 1).compFormalMultilinearSeries
      (FormalMultilinearSeries.ofScalars 𝕜 c).derivSeries =
    FormalMultilinearSeries.ofScalars 𝕜 (fun n => (n + 1 : 𝕜) * c (n + 1)) := by
  ext n
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  congr 1
  change (FormalMultilinearSeries.ofScalars 𝕜 c).derivSeries.coeff n 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, FormalMultilinearSeries.coeff_ofScalars]
  simp [nsmul_eq_mul]

/-- **Termwise derivative of a scalar power series.** If `f` has the power series `∑ cₙ zⁿ` on
the ball `B(0, r)`, then at every point of that ball `f' (z) = ∑ₙ (n + 1) c_(n+1) zⁿ`. -/
theorem hasDerivAt_ofScalars [CompleteSpace 𝕜] {c : ℕ → 𝕜} {f : 𝕜 → 𝕜} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 c) 0 r)
    {z : 𝕜} (hz : z ∈ Metric.eball (0 : 𝕜) r) :
    HasDerivAt f (∑' n : ℕ, ((n + 1 : 𝕜) * c (n + 1)) * z ^ n) z := by
  have hd := (h.analyticAt_of_mem hz).differentiableAt.hasFDerivAt.hasDerivAt
  have he := ((ContinuousLinearMap.apply 𝕜 𝕜 1).comp_hasFPowerSeriesOnBall h.fderiv).sum hz
  rw [apply_one_comp_derivSeries_ofScalars] at he
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, zero_add,
    FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at he
  exact he ▸ hd

end RadiiPolynomial.ScalarSeries
