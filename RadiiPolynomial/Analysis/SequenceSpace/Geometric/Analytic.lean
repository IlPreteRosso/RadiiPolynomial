import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Full-disc analyticity of Taylor coefficient realizations

Sequence-space layer, Taylor (geometric) carrier, above `Geometric/AnalyticExt.lean`:
the realization of an element of `l1Weighted ν` is analytic on the *whole* weight
ball (`analyticOnNhd_eval`, from `hasFPowerSeriesOnBall_eval`), and the same
coefficient estimate gives its complex counterpart `l1Weighted.complexEval` on the
open complex disc together with a termwise derivative identity through `derivShift`.

Before this module production carried only the power series centred at zero and a
real derivative identity on `(-ν, ν)`. The coefficient carrier stays real: complex
evaluation changes the target of the algebra homomorphism, not the coefficients or
any certificate. The polynomial-substitution identity for `complexEval` lives with
its consumer in `Applications/IVP/Taylor/ComplexTime.lean`.
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

/-- The same coefficient sequence read over `ℂ` has the same radius. -/
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

private theorem summable_derivative_bound (a : l1Weighted ν) {r : ℝ}
    (hr : 0 < r) (hrν : r < (ν : ℝ)) :
    Summable (fun n : ℕ => |l1Weighted.toSeq a n| * (n : ℝ) * r ^ (n - 1)) := by
  have hs := l1Omega.summable_abs_eval (derivShift a)
    (show |r| < (ν : ℝ) by simpa only [abs_of_pos hr] using hrν)
  have ht : Summable (fun n : ℕ =>
      |l1Weighted.toSeq a (n + 1)| * ((n : ℝ) + 1) * r ^ n) := by
    refine hs.congr fun n => ?_
    rw [derivShift_apply, abs_mul, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
      abs_of_pos hr]
    ring
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] using ht)

/-- The complex derivative is synthesis of the same coefficient derivative shift. -/
theorem hasDerivAt_complexEval (a : l1Weighted ν) {z : ℂ} (hz : ‖z‖ < (ν : ℝ)) :
    HasDerivAt (complexEval a) (complexOmegaEval (derivShift a) z) z := by
  obtain ⟨r, hzr, hrν⟩ := exists_between hz
  have hr := (norm_nonneg z).trans_lt hzr
  have hbound : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖(l1Weighted.toSeq a n : ℂ) * (n : ℂ) * y ^ (n - 1)‖ ≤
        |l1Weighted.toSeq a n| * (n : ℝ) * r ^ (n - 1) := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hy.le _)
      (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hsum0 : Summable (fun n : ℕ => (l1Weighted.toSeq a n : ℂ) * (0 : ℂ) ^ n) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
    simp only [zero_pow hn0, mul_zero]
  have hmain : HasDerivAt (complexEval a)
      (∑' n : ℕ, (l1Weighted.toSeq a n : ℂ) * (n : ℂ) * z ^ (n - 1)) z := by
    exact hasDerivAt_tsum_of_isPreconnected (𝕜 := ℂ)
      (g := fun n y => (l1Weighted.toSeq a n : ℂ) * y ^ n)
      (g' := fun n y => (l1Weighted.toSeq a n : ℂ) * (n : ℂ) * y ^ (n - 1))
      (summable_derivative_bound a hr hrν)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
      (fun n y _ => by simpa only [mul_assoc] using
        (hasDerivAt_pow n y).const_mul (l1Weighted.toSeq a n : ℂ))
      hbound (Metric.mem_ball_self hr) hsum0
      (show z ∈ Metric.ball (0 : ℂ) r by
        simpa only [Metric.mem_ball, dist_zero_right] using hzr)
  have hs : Summable (fun n : ℕ =>
      (l1Weighted.toSeq a n : ℂ) * (n : ℂ) * z ^ (n - 1)) :=
    Summable.of_norm_bounded (summable_derivative_bound a hr hrν)
      (fun n => hbound n z (by simpa only [Metric.mem_ball, dist_zero_right] using hzr))
  have heq : (∑' n : ℕ, (l1Weighted.toSeq a n : ℂ) * (n : ℂ) * z ^ (n - 1)) =
      complexOmegaEval (derivShift a) z := by
    rw [complexOmegaEval, hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
    refine tsum_congr fun n => ?_
    rw [derivShift_apply]
    push_cast
    ring
  exact heq ▸ hmain

end l1Weighted

end RadiiPolynomial
