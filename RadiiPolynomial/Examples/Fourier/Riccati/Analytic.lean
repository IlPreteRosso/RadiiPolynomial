import RadiiPolynomial.Examples.Fourier.Riccati.Certificate
import RadiiPolynomial.Applications.Fourier.Transfer

/-!
# Forced Riccati: the real-analytic periodic solution of `u′ + u − u² = cos (2t) / 100`

Function-space reading of `Certificate.lean`'s `raw_existsUnique_real`, in the shape of
`Examples/Fourier/Duffing/Analytic.lean`. The certified coefficient zero `a ∈ ℓ²_{6/5}` of the raw
Fourier map `rawF μ g a = (1 + i n) aₙ − (a ⋆ a)ₙ − gₙ` (`g_{±2} = 1/200`), unique in the closed
ball of radius `1/100` around `ā` and conjugate-symmetric, is realized as
`solution t = ∑ aₙ e^{int}`: a real-analytic `2π`-periodic solution of
`u′ + u − u² = cos (2t) / 100` on `ℝ`, with the holomorphic extension `extension z = ∑ aₙ e^{inz}`
on the full strip `|Im z| < log (6/5)`.

The analysis and the equation transfer are the generic faces of
`Analysis/SequenceSpace/Fourier/Realization.lean` and `Applications/Fourier/Transfer.lean`
(`realRealization_firstOrder` at `c₀ = c₁ = 1`, `b = g`);
only the forcing identity `u_g(t) = cos (2t) / 100` is proved here.
-/

open scoped ComplexConjugate

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic

noncomputable section

namespace FourierRiccati

/-- **The real solution** `u(t) = ∑ aₙ e^{int}`. -/
def solution : ℝ → ℝ := Fourier.realRealization (coeff a)

/-- **The holomorphic extension** `U(z) = ∑ aₙ e^{inz}`. -/
def extension : ℂ → ℂ := Fourier.complexRealization (coeff a)

private theorem one_lt_ν : 1 < (ν : ℝ) := by
  rw [coe_ν]
  norm_num

private theorem coeff_incl_a : coeff (incl a) = coeff a := funext (coeff_incl a)

private theorem solution_analytic : AnalyticOnNhd ℝ solution Set.univ := by
  have h := Fourier.analyticOnNhd_realRealization (incl a) one_lt_ν
  rw [coeff_incl_a] at h
  exact h

private theorem extension_analytic :
    AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} := by
  have h := Fourier.analyticOnNhd_complexRealization (incl a)
  rw [coeff_incl_a] at h
  exact h

private theorem solution_ofReal (t : ℝ) :
    (solution t : ℂ) = Fourier.realization (coeff a) t :=
  Fourier.ofReal_realRealization ((conjReflL_eq_self_iff_coeff _ a).1 coefficient_reality) t

/-- The raw zero in the coefficient form of the first-order family (`c₀ = c₁ = 1`, `b = g`). -/
private theorem coeff_equation (n : ℤ) :
    (((1 : ℝ) : ℂ) + Complex.I * ((1 : ℝ) : ℂ) * n) * coeff a n - convCoeff a a n -
      coeff g n = 0 := by
  rw [Complex.ofReal_one, mul_one]
  exact congrFun coefficient_zero n

/-- The forcing: `u_g(t) = cos (2t) / 100`. -/
private theorem realization_coeff_g (t : ℝ) :
    Fourier.realization (coeff g) t = (Real.cos (2 * t) / 100 : ℝ) := by
  rw [Fourier.realization, tsum_eq_sum (s := {2, -2}) fun n hn => by
    rw [coeff_g, gc,
      ite_eq_right (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hn), zero_mul],
    Finset.sum_pair (by decide), coeff_g, coeff_g, gc, ite_eq_left (Or.inl rfl), gc,
    ite_eq_left (Or.inr rfl), Complex.ofReal_div, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The real forcing: `Re u_g(t) = cos (2t) / 100`. -/
private theorem realRealization_coeff_g (t : ℝ) :
    Fourier.realRealization (coeff g) t = Real.cos (2 * t) / 100 :=
  (congrArg Complex.re (realization_coeff_g t)).trans (Complex.ofReal_re _)

/-- **THE ANALYTIC ENDPOINT** of the forced Riccati equation: the certified zero `a` of the raw
Fourier map, with the ball statement of `raw_existsUnique_real`, realizes the real-analytic
`2π`-periodic solution `u = solution` of `u′ + u − u² = cos (2t) / 100` on `ℝ`, the sum of its
Fourier series `∑ aₙ e^{int}` at every `t`, with the holomorphic extension `extension` on the
strip `|Im z| < log (6/5)`. -/
theorem riccati_analytic_solution :
    a ∈ Metric.closedBall abar (1 / 100 : ℝ) ∧ rawF μ g a = 0 ∧ conjRefl a = a ∧
      (∀ z ∈ Metric.closedBall abar (1 / 100 : ℝ), rawF μ g z = 0 → z = a) ∧
      (∀ t : ℝ, HasSum (fun n : ℤ => coeff a n * Complex.exp (n * t * Complex.I))
        (solution t)) ∧
      AnalyticOnNhd ℝ solution Set.univ ∧
      Function.Periodic solution (2 * Real.pi) ∧
      AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} ∧
      (∀ t : ℝ, extension t = solution t) ∧
      ∀ t : ℝ, deriv solution t + solution t - solution t ^ 2 = Real.cos (2 * t) / 100 := by
  obtain ⟨-, -, -, huniq⟩ := raw_existsUnique_real.choose_spec
  refine ⟨coefficient_ball, coefficient_zero, coefficient_reality, huniq, fun t => ?_,
    solution_analytic, Fourier.realRealization_periodic _, extension_analytic,
    fun t => (Fourier.complexRealization_ofReal _ t).trans (solution_ofReal t).symm, fun t => ?_⟩
  · rw [solution_ofReal]
    exact Fourier.hasSum_realization
      ((Bilateral.summable_moment_Y (incl a) zero_le_one one_lt_ν 0).congr fun n => by
        rw [coeff_incl, pow_zero, one_mul, one_pow, mul_one]) t
  · have h := Fourier.realRealization_firstOrder one_lt_ν a
      ((conjReflL_eq_self_iff_coeff _ a).1 coefficient_reality) coeff_equation t
    rw [one_mul, one_mul, realRealization_coeff_g] at h
    exact h

end FourierRiccati

end
