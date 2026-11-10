import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Certificate
import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Realization
import RadiiPolynomial.Analysis.Norm.InfiniteSum

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: the closed-strip enclosure

On `X = ℓ²_m`, `m_n = (6/5)^{|n|} (1 + |n|)²`, the polynomial factor of the weight supplies the
reciprocal summability and the geometric factor supplies the strip. With
`C = √(∑' n, 1 / (1 + |n|)⁴)` (a supplied majorant, not an evaluation norm), for every `x y : X`
and every `z` with `|Im z| ≤ log (6/5)`, both boundary lines included:

* the Fourier series of `x` at `z` converges absolutely and has sum `complexRealization (coeff x) z`
  (`summable_norm_series`, `hasSum_series`);
* `‖complexRealization (coeff x) z − complexRealization (coeff y) z‖ ≤ C ‖x − y‖`
  (`closed_strip_lipschitz`).

The estimate is the quantitative coordinate bound
`WeightedLp.summable_norm_coeff_mul_and_tsum_le` with majorant `geoW`, whose squared ratio to the
frame weight is `1 / (1 + |n|)⁴` (`ratio_sq`). For the certified zero `xC` and its centre `ā`
(`Combined/Certificate.lean`, radius `3/10000`) this gives the uniform error
`certified_closed_strip_error`. No geometric certified zero is used.
-/

noncomputable section

namespace FourierDuffing.Combined.Enclosure

open RadiiPolynomial RadiiPolynomial.WeightedLp
open Complex (I)

/-- The strip half-width `log (6/5)`. -/
def stripRadius : ℝ := Real.log (6 / 5 : ℝ)

/-- The closed-strip constant `C = √(∑' n, 1 / (1 + |n|)⁴)`. -/
def stripConstant : ℝ := Real.sqrt (∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ (4 : ℕ))

theorem stripConstant_nonneg : 0 ≤ stripConstant := Real.sqrt_nonneg _

theorem summable_reciprocal_fourth :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ (4 : ℕ)) := by
  have h := NormHelpers.summable_inv_one_add_abs_rpow (s := 4) (by norm_num)
  exact h.congr fun n => by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast]

/-- The geometric amplitude cancels: `(geoW n / m_n)² = 1 / (1 + |n|)⁴`. -/
theorem ratio_sq (n : ℤ) : (geoW n / combWeight n) ^ 2 =
    1 / (1 + |(n : ℝ)|) ^ (4 : ℕ) := by
  have hg : geoW n ≠ 0 := (geoW_pos n).ne'
  change (geoW n / (geoW n * (1 + |(n : ℝ)|) ^ (2 : ℕ))) ^ 2 = _
  rw [div_mul_cancel_left₀ hg]
  simp only [← inv_pow, ← pow_mul, one_div]

theorem geoW_eq_exp (n : ℤ) : geoW n = Real.exp (stripRadius * |(n : ℝ)|) := by
  have h := Real.exp_nat_mul (Real.log (6 / 5 : ℝ)) n.natAbs
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)] at h
  simpa only [Nat.cast_natAbs, Int.cast_abs, mul_comm, stripRadius, geoW] using h.symm

/-- The quantitative coordinate estimate on the combined carrier with majorant `geoW`. -/
theorem weighted_sum_bound (x : X) :
    Summable (fun n => ‖coeff x n‖ * geoW n) ∧
    ∑' n, ‖coeff x n‖ * geoW n ≤ stripConstant * ‖x‖ := by
  have hr : Summable (fun n : ℤ =>
      (geoW n / FiberTrivialization.weight (E := WeightedScalar ℂ combWeight) n) ^ 2) := by
    simpa only [WeightedScalar.fiberTrivialization_weight, ratio_sq] using
      summable_reciprocal_fourth
  have h := RadiiPolynomial.WeightedLp.summable_norm_coeff_mul_and_tsum_le geoW hr x
  simpa only [WeightedScalar.fiberTrivialization_weight, ratio_sq, stripConstant] using h

/-- On the closed strip the Fourier character is dominated by the geometric amplitude. -/
theorem norm_exp_le_geoW {z : ℂ} (hz : |z.im| ≤ stripRadius) (n : ℤ) :
    ‖Complex.exp ((n : ℂ) * z * I)‖ ≤ geoW n := by
  rw [geoW_eq_exp, Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hre : ((n : ℂ) * z * I).re = -((n : ℝ) * z.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  calc -((n : ℝ) * z.im) ≤ |(n : ℝ) * z.im| := neg_le_abs _
    _ = |(n : ℝ)| * |z.im| := abs_mul _ _
    _ ≤ |(n : ℝ)| * stripRadius := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = stripRadius * |(n : ℝ)| := mul_comm _ _

/-- Absolute convergence holds at every point of the closed strip. -/
theorem summable_norm_series (x : X) {z : ℂ} (hz : |z.im| ≤ stripRadius) :
    Summable (fun n : ℤ => ‖coeff x n * Complex.exp ((n : ℂ) * z * I)‖) := by
  refine (weighted_sum_bound x).1.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_exp_le_geoW hz n) (norm_nonneg _)

/-- The Fourier series has sum `complexRealization (coeff x) z` on the closed strip. -/
theorem hasSum_series (x : X) {z : ℂ} (hz : |z.im| ≤ stripRadius) :
    HasSum (fun n : ℤ => coeff x n * Complex.exp ((n : ℂ) * z * I))
      (Fourier.complexRealization (coeff x) z) :=
  (summable_norm_series x hz).of_norm.hasSum

theorem norm_realization_le (x : X) {z : ℂ} (hz : |z.im| ≤ stripRadius) :
    ‖Fourier.complexRealization (coeff x) z‖ ≤ stripConstant * ‖x‖ := by
  refine (norm_tsum_le_tsum_norm (summable_norm_series x hz)).trans ?_
  refine (Summable.tsum_le_tsum (fun n => ?_) (summable_norm_series x hz)
    (weighted_sum_bound x).1).trans (weighted_sum_bound x).2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_exp_le_geoW hz n) (norm_nonneg _)

theorem realization_sub (x y : X) {z : ℂ} (hz : |z.im| ≤ stripRadius) :
    Fourier.complexRealization (coeff (x - y)) z =
      Fourier.complexRealization (coeff x) z - Fourier.complexRealization (coeff y) z := by
  unfold Fourier.complexRealization
  simp only [coeff_sub, Pi.sub_apply, sub_mul]
  exact ((summable_norm_series x hz).of_norm).tsum_sub ((summable_norm_series y hz).of_norm)

/-- All-pairs estimate on the combined carrier, uniformly up to both boundary lines. -/
theorem closed_strip_lipschitz (x y : X) {z : ℂ} (hz : |z.im| ≤ stripRadius) :
    ‖Fourier.complexRealization (coeff x) z - Fourier.complexRealization (coeff y) z‖ ≤
      stripConstant * ‖x - y‖ := by
  rw [← realization_sub x y hz]
  exact norm_realization_le (x - y) hz

section Certified

open FourierDuffing.Combined.Certificate (xC abar xC_ball)

/-- **The closed-strip error of the certified zero**: on `|Im z| ≤ log (6/5)` the complex
realizations of `xC` and of the centre `ā` differ by at most `C · 3/10000`. -/
theorem certified_closed_strip_error {z : ℂ} (hz : |z.im| ≤ Real.log (6 / 5 : ℝ)) :
    ‖Fourier.complexRealization (coeff xC) z - Fourier.complexRealization (coeff abar) z‖ ≤
      Real.sqrt (∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ (4 : ℕ)) * (3 / 10000 : ℝ) := by
  refine (closed_strip_lipschitz xC abar hz).trans ?_
  apply mul_le_mul_of_nonneg_left _ stripConstant_nonneg
  have hb := Metric.mem_closedBall.mp xC_ball
  simpa only [dist_eq_norm, Numbers.radiusQ, Rat.cast_div, Rat.cast_ofNat] using hb

/-- The Fourier series of `xC` has sum its complex realization on the closed strip. -/
theorem certified_hasSum {z : ℂ} (hz : |z.im| ≤ Real.log (6 / 5 : ℝ)) :
    HasSum (fun n : ℤ => coeff xC n * Complex.exp ((n : ℂ) * z * Complex.I))
      (Fourier.complexRealization (coeff xC) z) := hasSum_series xC hz

/-- The error series `∑ (xC_n − ā_n) e^{inz}` has sum the realization difference on the closed
strip. -/
theorem certified_error_hasSum {z : ℂ} (hz : |z.im| ≤ Real.log (6 / 5 : ℝ)) :
    HasSum (fun n : ℤ => (coeff xC n - coeff abar n) *
      Complex.exp ((n : ℂ) * z * Complex.I))
      (Fourier.complexRealization (coeff xC) z - Fourier.complexRealization (coeff abar) z) := by
  have h := (hasSum_series xC hz).sub (hasSum_series abar hz)
  simpa only [sub_mul] using h

end Certified

end FourierDuffing.Combined.Enclosure
