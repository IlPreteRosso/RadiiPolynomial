import RadiiPolynomial.Examples.Fourier.Duffing.Certificate
import RadiiPolynomial.Applications.Fourier.Realization

/-!
# Book §10.1 Helmholtz–Duffing: the real-analytic periodic solution

Function-space reading of `Certificate.lean`'s `duffing_l2_real`. The certified coefficient zero
`aTilde ∈ ℓ²_{6/5}` of the raw Fourier map `F_n(a) = (−n² + i n/10 + 4) aₙ − (a ⋆ a)ₙ − bₙ`
(`b_{±1} = 1/2`), unique in the closed ball of radius `1/200000` around `ā` and
conjugate-symmetric, is realized as `solution t = ∑ ãₙ e^{int}`: a real-analytic `2π`-periodic
solution of `u'' + u'/10 + 4u − u² = cos t` on `ℝ`, with the holomorphic extension
`extension z = ∑ ãₙ e^{inz}` on the full strip `|Im z| < log (6/5)`.

Nothing structural is stated here: the analysis and the equation transfer are the
parameter-generic faces of `Applications/Fourier/Realization.lean`, instantiated at
`c₁ = 1/10`, `c₂ = 4`, `c₃ = 1`, `ν = 6/5`. The uniqueness is among coefficient zeros in the
`ℓ²_{6/5}` ball, as in `duffing_l2_real`.
-/

open scoped ComplexConjugate

noncomputable section

namespace FourierDuffing.Certificate

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic FourierDuffing

/-- The certified coefficient zero of `duffing_l2_real`. -/
def aTilde : X₂ ℂ ν₆₅ := duffing_l2_real.choose

/-- **The real solution** `u(t) = ∑ ãₙ e^{int}`. -/
def solution : ℝ → ℝ := Fourier.realRealization (coeff aTilde)

/-- **The holomorphic extension** `U(z) = ∑ ãₙ e^{inz}`. -/
def extension : ℂ → ℂ := Fourier.complexRealization (coeff aTilde)

private theorem one_lt_ν₆₅ : 1 < (ν₆₅ : ℝ) := by
  rw [coe_ν₆₅]
  norm_num

private theorem aTilde_spec :
    aTilde ∈ Metric.closedBall abar (1 / 200000) ∧
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) aTilde n = 0) ∧ conjRefl aTilde = aTilde ∧
      ∀ z ∈ Metric.closedBall abar (1 / 200000),
        (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = aTilde :=
  duffing_l2_real.choose_spec

private theorem coeff_aTilde_neg (n : ℤ) : coeff aTilde (-n) = conj (coeff aTilde n) := by
  have h := congrArg (fun x : X₂ ℂ ν₆₅ => coeff x n) aTilde_spec.2.2.1
  rw [coeff_conjRefl] at h
  rw [← h, Complex.conj_conj]

private theorem coeff_incl_aTilde : coeff (incl aTilde) = coeff aTilde := funext (coeff_incl aTilde)

private theorem solution_analytic : AnalyticOnNhd ℝ solution Set.univ := by
  have h := Fourier.analyticOnNhd_realRealization (incl aTilde) one_lt_ν₆₅
  rw [coeff_incl_aTilde] at h
  exact h

private theorem extension_analytic :
    AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} := by
  have h := Fourier.analyticOnNhd_complexRealization (incl aTilde)
  rw [coeff_incl_aTilde] at h
  exact h

private theorem solution_ofReal (t : ℝ) :
    (solution t : ℂ) = Fourier.realization (coeff aTilde) t :=
  Fourier.ofReal_realRealization coeff_aTilde_neg t

/-- **THE ANALYTIC ENDPOINT** (book §10.1 at its data): the certified zero `aTilde` of the raw
Fourier map, with the ball statement of `duffing_l2_real`, realizes the real-analytic
`2π`-periodic solution `u = solution` of `u'' + u'/10 + 4u − u² = cos t` on `ℝ`, the sum of its
Fourier series `∑ ãₙ e^{int}` at every `t`, with the holomorphic extension `extension` on the
strip `|Im z| < log (6/5)`. -/
theorem duffing_analytic_solution :
    aTilde ∈ Metric.closedBall abar (1 / 200000) ∧
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) aTilde n = 0) ∧ conjRefl aTilde = aTilde ∧
      (∀ z ∈ Metric.closedBall abar (1 / 200000),
        (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = aTilde) ∧
      (∀ t : ℝ, HasSum (fun n : ℤ => coeff aTilde n * Complex.exp (n * t * Complex.I))
        (solution t)) ∧
      AnalyticOnNhd ℝ solution Set.univ ∧
      Function.Periodic solution (2 * Real.pi) ∧
      AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} ∧
      (∀ t : ℝ, extension t = solution t) ∧
      ∀ t : ℝ, deriv (deriv solution) t + 1 / 10 * deriv solution t + 4 * solution t -
        solution t ^ 2 = Real.cos t := by
  obtain ⟨hball, hzero, hreal, huniq⟩ := aTilde_spec
  have hcoeff : ∀ n : ℤ, (-(n : ℂ) ^ 2 + Complex.I * ((1 / 10 : ℝ) : ℂ) * n + ((4 : ℝ) : ℂ)) *
      coeff aTilde n - convCoeff aTilde aTilde n - ((1 : ℝ) : ℂ) * Fourier.cosCoeff n = 0 :=
    fun n => (rawF_duffing aTilde n).symm.trans (hzero n)
  refine ⟨hball, hzero, hreal, huniq, fun t => ?_, solution_analytic,
    Fourier.realRealization_periodic _, extension_analytic,
    fun t => (Fourier.complexRealization_ofReal _ t).trans (solution_ofReal t).symm, fun t => ?_⟩
  · rw [solution_ofReal]
    exact Fourier.hasSum_realization
      ((Fourier.summable_moment_Y (incl aTilde) zero_le_one one_lt_ν₆₅ 0).congr fun n => by
        rw [coeff_incl, pow_zero, one_mul, one_pow, mul_one]) t
  · have h := Fourier.realRealization_duffing one_lt_ν₆₅ aTilde coeff_aTilde_neg hcoeff t
    rw [one_mul] at h
    exact h

end FourierDuffing.Certificate

end
