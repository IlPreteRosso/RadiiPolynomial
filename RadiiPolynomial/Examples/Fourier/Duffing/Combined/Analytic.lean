import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Reality
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reweight
import RadiiPolynomial.Applications.Fourier.Transfer

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: the analytic endpoint

The combined-carrier zero `xC` (`Combined/Certificate.lean`, unique in the closed ball of radius
`3/10000` of `X = ℓ²_m`, `m_n = (6/5)^{|n|} (1 + |n|)²`, real by `Combined/Reality.lean`) is read
as a function through its own decay, with no geometric certified zero and no identification with
the polynomial-carrier or geometric zeros:

* the weights compare as `(6/5)^{|n|} ≤ 1 · m_n` (`geom_le_combWeight`), so the
  coefficient-preserving reweighting `toX₂ = reweightCLM … : X →L[ℂ] ℓ²_{6/5}` keeps every
  coefficient (`coeff_toX₂`); only the geometric carrier `ℓ²_{6/5}` and its analysis are reused;
* the coefficients of `xC` are read through `X →toX₂→ ℓ²_{6/5} →incl→ ℓ^∞_{6/5}` by the
  parameter-generic realization faces of `Analysis/SequenceSpace/Fourier/Realization.lean` and the
  equation transfer `Applications/Fourier/Transfer.lean`.

The clauses that read the real realization as the complex one (the Fourier sum, the agreement on
`ℝ`, the equation) use the conjugate symmetry `Certificate.coeff_xC_neg`; the helper theorems take
it as the hypothesis `hsym`, the end theorem `certified_analytic_solution` discharges it. The
uniqueness is among raw coefficient zeros in the combined ball; the holomorphic extension lives on
the strip `|Im z| < log (6/5)`.
-/

open scoped DiscreteConvolution ComplexConjugate

noncomputable section

namespace FourierDuffing.Combined

open RadiiPolynomial RadiiPolynomial.WeightedLp FourierDuffing.Polynomial

/-- The comparison `ν₆₅^{|n|} ≤ 1 · m_n` of the geometric frame with the combined frame. -/
theorem geom_le_combWeight (n : ℤ) :
    FiberTrivialization.weight (E := geomFiberZ ℂ FourierDuffing.Certificate.ν₆₅) n ≤
      1 * FiberTrivialization.weight (E := WeightedScalar ℂ combWeight) n := by
  rw [geomFiberZ_weight, WeightedScalar.fiberTrivialization_weight, one_mul, combWeight,
    FourierDuffing.Certificate.coe_ν₆₅]
  exact le_mul_of_one_le_right (by positivity) (one_le_polyWeight n)

/-- **The coefficient-preserving map** `X → X₂ ℂ (6/5)`: `reweightCLM` at the comparison
constant `1` of `geom_le_combWeight`. -/
def toX₂ : X →L[ℂ] Bilateral.X₂ ℂ FourierDuffing.Certificate.ν₆₅ :=
  reweightCLM zero_le_one geom_le_combWeight

@[simp] theorem coeff_toX₂ (x : X) (n : ℤ) : coeff (toX₂ x) n = coeff x n :=
  coeff_reweightCLM _ _ x n

end FourierDuffing.Combined

namespace FourierDuffing.Combined.Analytic

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
open RadiiPolynomial.Fourier.Duffing (duffing forcing rawF_duffing)
open FourierDuffing.Certificate (ν₆₅ coe_ν₆₅)
open FourierDuffing.Polynomial (conv_apply)
open FourierDuffing.Combined.Certificate (xC abar rawF xC_ball xC_zero unique_eq_xC)

theorem one_lt_ν₆₅ : 1 < (ν₆₅ : ℝ) := by
  rw [coe_ν₆₅]
  norm_num

/-- The image of `xC` in `ℓ^∞_{6/5}`. -/
def yC : Y ℂ ν₆₅ := incl (toX₂ xC)

theorem coeff_yC : coeff yC = coeff xC :=
  funext fun n => by rw [yC, coeff_incl, coeff_toX₂]

theorem coeff_toX₂_xC : coeff (toX₂ xC) = coeff xC := funext fun n => coeff_toX₂ xC n

/-- The combined raw map at `x` is the generic Duffing raw map at `toX₂ x`. -/
theorem rawF_eq_toX₂ (x : X) (n : ℤ) :
    rawF x n = Fourier.Quadratic.rawF (duffing (1 / 10) 4) (forcing 1) (toX₂ x) n := by
  have hconv : (coeff x ⋆ᵣ₊ coeff x) n = convCoeff (toX₂ x) (toX₂ x) n := by
    simp only [conv_apply, convCoeff, coeff_toX₂]
  rw [rawF, Fourier.Quadratic.rawF, hconv, Certificate.coeff_g_eq_forcing, coeff_toX₂]

/-- **The real solution** `u(t) = ∑ xCₙ e^{int}`. -/
def solution : ℝ → ℝ := Fourier.realRealization (coeff xC)

/-- **The holomorphic extension** `U(z) = ∑ xCₙ e^{inz}`. -/
def extension : ℂ → ℂ := Fourier.complexRealization (coeff xC)

theorem solution_analytic : AnalyticOnNhd ℝ solution Set.univ := by
  have h := Fourier.analyticOnNhd_realRealization yC one_lt_ν₆₅
  rwa [coeff_yC] at h

theorem solution_periodic : Function.Periodic solution (2 * Real.pi) :=
  Fourier.realRealization_periodic _

theorem extension_analytic :
    AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5 : ℝ)} := by
  have h := Fourier.analyticOnNhd_complexRealization yC
  rwa [coeff_yC] at h

section Symmetric

variable (hsym : ∀ n, coeff xC (-n) = conj (coeff xC n))
include hsym

theorem solution_ofReal (t : ℝ) : (solution t : ℂ) = Fourier.realization (coeff xC) t :=
  Fourier.ofReal_realRealization hsym t

theorem extension_agree (t : ℝ) : extension (t : ℂ) = (solution t : ℂ) :=
  (Fourier.complexRealization_ofReal _ t).trans (solution_ofReal hsym t).symm

theorem solution_ode (t : ℝ) :
    deriv (deriv solution) t + (1 / 10 : ℝ) * deriv solution t +
      4 * solution t - (solution t) ^ 2 = Real.cos t := by
  have hcoeff : ∀ n : ℤ, (-(n : ℂ) ^ 2 + Complex.I * ((1 / 10 : ℝ) : ℂ) * n + ((4 : ℝ) : ℂ)) *
      coeff (toX₂ xC) n - convCoeff (toX₂ xC) (toX₂ xC) n -
        ((1 : ℝ) : ℂ) * Fourier.cosCoeff n = 0 :=
    fun n => (rawF_duffing (toX₂ xC) n).symm.trans
      ((rawF_eq_toX₂ xC n).symm.trans (congrFun xC_zero n))
  have h := Fourier.realRealization_duffing one_lt_ν₆₅ (toX₂ xC)
    (by rw [coeff_toX₂_xC]; exact hsym) hcoeff t
  rw [coeff_toX₂_xC, one_mul] at h
  exact h
end Symmetric

/-- **THE COMBINED-CARRIER ENDPOINT** (book §10.1 at its data, combined carrier): the raw Fourier
map has a unique zero `xC` in the closed ball of radius `3/10000` around `ā` in `ℓ²_m`,
`m_n = (6/5)^{|n|} (1 + |n|)²`; its coefficients are conjugate symmetric (`coeff_xC_neg`, proved
by equivariance and ball uniqueness), so the coefficient tuple realizes the real-analytic `2π`-periodic solution `u = solution` of
`u'' + u'/10 + 4u − u² = cos t` on `ℝ`, the sum of its complex Fourier series, with the
holomorphic extension `extension` on the strip `|Im z| < log (6/5)`. No geometric certified
zero is used. -/
theorem certified_analytic_solution :
    xC ∈ Metric.closedBall abar (3 / 10000 : ℝ) ∧
    rawF xC = 0 ∧
    (∀ x ∈ Metric.closedBall abar (3 / 10000 : ℝ), rawF x = 0 → x = xC) ∧
    AnalyticOnNhd ℝ solution Set.univ ∧
    Function.Periodic solution (2 * Real.pi) ∧
    (∀ t, (solution t : ℂ) = Fourier.realization (coeff xC) t) ∧
    AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5 : ℝ)} ∧
    (∀ t : ℝ, extension (t : ℂ) = (solution t : ℂ)) ∧
    (∀ t, deriv (deriv solution) t + (1 / 10 : ℝ) * deriv solution t +
      4 * solution t - (solution t) ^ 2 = Real.cos t) := by
  have hr : ((Numbers.radiusQ : ℚ) : ℝ) = 3 / 10000 := by norm_num [Numbers.radiusQ]
  exact ⟨hr ▸ xC_ball, xC_zero, fun x hx hF => unique_eq_xC x (hr ▸ hx) hF,
    solution_analytic, solution_periodic, solution_ofReal Certificate.coeff_xC_neg, extension_analytic,
    extension_agree Certificate.coeff_xC_neg, solution_ode Certificate.coeff_xC_neg⟩

end FourierDuffing.Combined.Analytic
