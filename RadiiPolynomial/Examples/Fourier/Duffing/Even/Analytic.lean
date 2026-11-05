import RadiiPolynomial.Examples.Fourier.Duffing.Even.Certificate
import RadiiPolynomial.Applications.Fourier.Realization

/-!
# The even Duffing instance: the real-analytic even solution of `u'' − u + u² = (4/5) cos t`

Function-space reading of `Certificate.lean`'s `even_l2_even`. The certified coefficient zero
`aTilde ∈ ℓ²_{6/5}` of the raw Fourier map `F_n(a) = (−n² − 1) aₙ − (a ⋆ a)ₙ + (4/5) bₙ`
(`b_{±1} = 1/2`; the Duffing family at `(c₁, c₂, c₃) = (0, −1, −4/5)`), unique in the closed ball of
radius `1/500000` around `ā`, conjugate-symmetric and even, realizes `v(t) = ∑ ãₙ e^{int}`, a
solution of `v'' − v − v² = −(4/5) cos t`; PlasmaLean's unknown is `u = −v`
(`exterior/tmp/external_repos/PlasmaLean/PlasmaLean/Design/ValidatedBVP.lean`, Apache-2.0).
The endpoint states, for `u = solution = −v`: the Fourier sum `u(t) = ∑ (−ãₙ) e^{int}` at every `t`,
real analyticity on `ℝ`, `2π`-periodicity, the holomorphic extension
`extension z = −∑ ãₙ e^{inz}` on the full strip `|Im z| < log (6/5)`, evenness `u(−t) = u(t)`, and
`u'' − u + u² = (4/5) cos t` on `ℝ`.

As in `Examples/Fourier/Duffing/Analytic.lean`, the analysis and the equation transfer are the
parameter-generic faces of `Applications/Fourier/Realization.lean`, instantiated at
`c₁ = 0`, `c₂ = −1`, `c₃ = −4/5`, `ν = 6/5`; the evenness of the realization of an even family is
`Fourier.realization_neg_of_even`, and the sign change `u = −v` is proved here. The uniqueness is
among coefficient zeros in the `ℓ²_{6/5}` ball, as in `even_l2_even`.
-/

open scoped ComplexConjugate

noncomputable section

namespace FourierDuffing.Even

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic RadiiPolynomial.Fourier.Duffing

/-- The certified coefficient zero of `even_l2_even` (the Duffing unknown `v`). -/
def aTilde : X₂ ℂ ν₆₅ := even_l2_even.choose

/-- **The real solution** `u = −v`, `v(t) = ∑ ãₙ e^{int}`. -/
def solution (t : ℝ) : ℝ := -Fourier.realRealization (coeff aTilde) t

/-- **The holomorphic extension** `U(z) = −∑ ãₙ e^{inz}`. -/
def extension (z : ℂ) : ℂ := -Fourier.complexRealization (coeff aTilde) z

private theorem one_lt_ν₆₅ : 1 < (ν₆₅ : ℝ) := by
  rw [coe_ν₆₅]
  norm_num

private theorem aTilde_spec :
    aTilde ∈ Metric.closedBall abar (1 / 500000) ∧
      (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) aTilde n = 0) ∧ conjRefl aTilde = aTilde ∧
      refl aTilde = aTilde ∧
      ∀ z ∈ Metric.closedBall abar (1 / 500000),
        (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) z n = 0) → z = aTilde :=
  even_l2_even.choose_spec

private theorem coeff_aTilde_even (n : ℤ) : coeff aTilde (-n) = coeff aTilde n := by
  have h := congrArg (fun x : X₂ ℂ ν₆₅ => coeff x n) aTilde_spec.2.2.2.1
  rwa [coeff_refl] at h

private theorem coeff_incl_aTilde : coeff (incl aTilde) = coeff aTilde := funext (coeff_incl aTilde)

private theorem realSolution_analytic :
    AnalyticOnNhd ℝ (Fourier.realRealization (coeff aTilde)) Set.univ := by
  have h := Fourier.analyticOnNhd_realRealization (incl aTilde) one_lt_ν₆₅
  rw [coeff_incl_aTilde] at h
  exact h

private theorem complexSolution_analytic :
    AnalyticOnNhd ℂ (Fourier.complexRealization (coeff aTilde))
      {z : ℂ | |z.im| < Real.log (6 / 5)} := by
  have h := Fourier.analyticOnNhd_complexRealization (incl aTilde)
  rw [coeff_incl_aTilde] at h
  exact h

private theorem realSolution_ofReal (t : ℝ) :
    (Fourier.realRealization (coeff aTilde) t : ℂ) = Fourier.realization (coeff aTilde) t :=
  Fourier.ofReal_realRealization ((conjReflL_eq_self_iff_coeff _ aTilde).1 aTilde_spec.2.2.1) t

/-- **THE ANALYTIC ENDPOINT** (PlasmaLean's periodic problem in our convention): the certified
zero `aTilde` of the raw Fourier map at `(c₁, c₂, c₃) = (0, −1, −4/5)`, with the ball statement of
`even_l2_real`, realizes `u = solution`, the real-analytic even `2π`-periodic solution of
`u'' − u + u² = (4/5) cos t` on `ℝ`, the sum of its Fourier series `∑ (−ãₙ) e^{int}` at every `t`,
with the holomorphic extension `extension` on the strip `|Im z| < log (6/5)`. -/
theorem even_analytic_solution :
    aTilde ∈ Metric.closedBall abar (1 / 500000) ∧
      (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) aTilde n = 0) ∧ conjRefl aTilde = aTilde ∧
      (∀ z ∈ Metric.closedBall abar (1 / 500000),
        (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) z n = 0) → z = aTilde) ∧
      (∀ t : ℝ, HasSum (fun n : ℤ => -coeff aTilde n * Complex.exp (n * t * Complex.I))
        (solution t)) ∧
      AnalyticOnNhd ℝ solution Set.univ ∧
      Function.Periodic solution (2 * Real.pi) ∧
      AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} ∧
      (∀ t : ℝ, extension t = solution t) ∧
      (∀ t : ℝ, solution (-t) = solution t) ∧
      ∀ t : ℝ, deriv (deriv solution) t - solution t + solution t ^ 2 = 4 / 5 * Real.cos t := by
  obtain ⟨hball, hzero, hreal, -, huniq⟩ := aTilde_spec
  have hcoeff : ∀ n : ℤ, (-(n : ℂ) ^ 2 + Complex.I * ((0 : ℝ) : ℂ) * n + ((-1 : ℝ) : ℂ)) *
      coeff aTilde n - convCoeff aTilde aTilde n - ((-4 / 5 : ℝ) : ℂ) * Fourier.cosCoeff n = 0 :=
    fun n => (rawF_duffing aTilde n).symm.trans (hzero n)
  refine ⟨hball, hzero, hreal, huniq, fun t => ?_, realSolution_analytic.neg,
    fun t => congrArg Neg.neg (Fourier.realRealization_periodic _ t), complexSolution_analytic.neg,
    fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [solution, Complex.ofReal_neg, realSolution_ofReal]
    simpa only [neg_mul] using (Fourier.hasSum_realization
      ((Fourier.summable_moment_Y (incl aTilde) zero_le_one one_lt_ν₆₅ 0).congr fun n => by
        rw [coeff_incl, pow_zero, one_mul, one_pow, mul_one]) t).neg
  · rw [extension, solution, Complex.ofReal_neg, Fourier.complexRealization_ofReal,
      realSolution_ofReal]
  · rw [solution, solution, Fourier.realRealization, Fourier.realRealization,
      Fourier.realization_neg_of_even coeff_aTilde_even]
  · have h := Fourier.realRealization_duffing one_lt_ν₆₅ aTilde
      ((conjReflL_eq_self_iff_coeff _ aTilde).1 hreal) hcoeff t
    have hd : deriv (deriv solution) t =
        -deriv (deriv (Fourier.realRealization (coeff aTilde))) t := by
      rw [show solution = fun s => -Fourier.realRealization (coeff aTilde) s from rfl,
        deriv.fun_neg', deriv.fun_neg]
    rw [hd, solution]
    linear_combination (-1 : ℝ) * h

end FourierDuffing.Even

end
