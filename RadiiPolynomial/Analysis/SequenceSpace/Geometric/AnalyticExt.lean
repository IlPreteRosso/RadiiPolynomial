import Mathlib.Analysis.Analytic.Uniqueness
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation

/-!
# Analytic extensionality for Taylor coefficient sequences

An element of `l1Weighted ν` is determined by its analytic realization near the
expansion centre.  This is the elementwise counterpart to the generator
extensionality used for morphisms out of the Taylor coefficient algebra.

Conversely, `exists_eval_eq_of_analyticAt`: a real function that is analytic at `0` is,
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

/-- The Taylor realization of a weighted coefficient sequence has its coefficient
sequence as a formal multilinear power series at the expansion centre (the
centred corollary of `hasFPowerSeriesOnBall_eval`). -/
theorem hasFPowerSeriesAt_eval (a : l1Weighted ν) :
    HasFPowerSeriesAt (l1Weighted.eval a)
      (FormalMultilinearSeries.ofScalars ℝ (l1Weighted.toSeq a)) 0 :=
  (hasFPowerSeriesOnBall_eval a).hasFPowerSeriesAt

/-- **Local converse of `hasFPowerSeriesOnBall_eval`, at zero.** A real function
`f : ℝ → ℝ` that is analytic at `0` agrees on the open interval `|t| < μ` with the
realization `l1Weighted.eval q` of a coefficient sequence `q : l1Weighted μ`, for some
positive weight radius `μ`.

Scope: the hypothesis is real scalar analyticity at the single point `0`. The radius `μ` and
the sequence `q` are existential: the statement prescribes no maximal radius and provides no
algorithm computing a radius. -/
theorem exists_eval_eq_of_analyticAt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ μ : PosReal, ∃ q : l1Weighted μ,
      ∀ t : ℝ, |t| < (μ : ℝ) → l1Weighted.eval q t = f t := by
  obtain ⟨p, r, hr⟩ := hf
  obtain ⟨m, hm0, hmr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
  have hm0' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hsum : Summable fun n : ℕ => ‖p n‖ * (m : ℝ) ^ n :=
    p.summable_norm_mul_pow (lt_of_lt_of_le hmr hr.r_le)
  refine ⟨⟨(m : ℝ), hm0'⟩, l1Weighted.mk p.coeff ?_, fun t ht => ?_⟩
  · rw [l1Weighted.mem_iff]
    refine hsum.congr fun n => ?_
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, Real.norm_eq_abs]
    rfl
  · have htm : ‖t‖₊ < m := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs]
      exact ht
    have hball : t ∈ Metric.eball (0 : ℝ) r :=
      mem_eball_zero_iff.mpr
        (lt_of_lt_of_le (by rw [enorm_eq_nnnorm]; exact ENNReal.coe_lt_coe.mpr htm) hmr.le)
    have hs := hr.hasSum hball
    simp only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at hs
    have hs' : HasSum (fun n : ℕ => p.coeff n * t ^ n) (f t) := by
      have heq : (fun n : ℕ => p.coeff n * t ^ n) = fun n : ℕ => t ^ n * p.coeff n :=
        funext fun n => mul_comm _ _
      rw [heq]
      exact hs
    unfold l1Weighted.eval
    exact hs'.tsum_eq

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
