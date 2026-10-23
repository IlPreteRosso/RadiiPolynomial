import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Certificate
import RadiiPolynomial.Examples.Fourier.Duffing.Analytic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reweight
import Mathlib.Tactic.IntervalCases

/-!
# Book §10.1 Helmholtz–Duffing on the polynomial carrier: identification and analytic endpoint

The polynomial-carrier zero `xPoly` (`Polynomial/Certificate.lean`, unique in the closed ball of
radius `1/10000` of `X = ℓ²_m`, `m_n = (1 + |n|)²`) is identified with the shipped geometric zero
`aTilde` of `duffing_l2_real` (unique in the ball of radius `1/200000` of `ℓ²_{6/5}`):

* the weights compare as `(1 + |n|)² ≤ 20 (6/5)^|n|`, so the coefficient-preserving reweighting
  `embed = reweightCLM … : ℓ²_{6/5} →L[ℂ] X` has `‖embed‖ ≤ 20`;
* `embed` keeps the centre and the raw Fourier map, and `20 · (1/200000) = 1/10000` puts
  `embed aTilde` in the polynomial ball, so polynomial uniqueness gives the identification
  companion `embed_aTilde_eq_xPoly`.

The analytic endpoint `certified_analytic_solution` reads the coefficients of `xPoly` as a
function. By the identification they are the coefficients of `aTilde`, so the realization
`solution t = ∑ xPolyₙ e^{int}` is the shipped `FourierDuffing.Certificate.solution`, and its
analysis is the shipped endpoint `duffing_analytic_solution` of the canonical realization bridge
`Applications/Fourier/Realization.lean` (no second derivation). The uniqueness is among raw
coefficient zeros in the polynomial ball.
-/

open scoped DiscreteConvolution

noncomputable section

namespace FourierDuffing.Polynomial

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
open FourierDuffing.Certificate (ν₆₅ coe_ν₆₅ aTilde duffing_analytic_solution coeff_forcing_eq)

/-! ### The weight comparison and the embedding -/

private theorem polynomial_le_geometric_nat (n : ℕ) :
    (1 + (n : ℝ)) ^ 2 ≤ 20 * (6 / 5 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 10
    · interval_cases n <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hk : 10 ≤ (k : ℝ) := by exact_mod_cast (show 10 ≤ k by omega)
      have hstep : (1 + ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ (6 / 5 : ℝ) * (1 + (k : ℝ)) ^ 2 := by
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ (k : ℝ) + 2 by positivity)]
      refine hstep.trans ((mul_le_mul_of_nonneg_left (ih k (by omega)) (by norm_num)).trans_eq ?_)
      rw [pow_succ]
      ring

/-- The weight comparison `(1 + |n|)² ≤ 20 (6/5)^|n|`. -/
theorem weight_le_geometric (n : ℤ) :
    FiberTrivialization.weight (E := WeightedScalar ℂ polyWeight) n ≤
      20 * FiberTrivialization.weight (E := geomFiberZ ℂ ν₆₅) n := by
  rw [WeightedScalar.fiberTrivialization_weight, geomFiberZ_weight, coe_ν₆₅, polyWeight]
  simpa only [Nat.cast_natAbs, Int.cast_abs] using polynomial_le_geometric_nat n.natAbs

/-- **The embedding** `ℓ²_{6/5} → X`: the coefficient-preserving reweighting at `C = 20`. -/
def embed : X₂ ℂ ν₆₅ →L[ℂ] X := reweightCLM (by norm_num) weight_le_geometric

private theorem coeff_embed (x : X₂ ℂ ν₆₅) (n : ℤ) : coeff (embed x) n = coeff x n :=
  coeff_reweightCLM _ _ x n

private theorem embed_center : embed FourierDuffing.Certificate.abar = Certificate.abar :=
  ext_coeff <| funext fun n => by
    rw [coeff_embed, FourierDuffing.Certificate.coeff_abar, Certificate.coeff_abar]

private theorem raw_embed (x : X₂ ℂ ν₆₅) (n : ℤ) :
    Certificate.rawF (embed x) n = rawF (duffing (1 / 10) 4) (forcing 1) x n := by
  have hconv : (coeff (embed x) ⋆ᵣ₊ coeff (embed x)) n = convCoeff x x n := by
    simp only [conv_apply, convCoeff, coeff_embed]
  rw [Certificate.rawF, FourierDuffing.rawF, coeff_embed, hconv, Certificate.coeff_g,
    coeff_forcing_eq]

private theorem embed_aTilde_ball :
    embed aTilde ∈ Metric.closedBall Certificate.abar (Numbers.radiusQ : ℝ) := by
  rw [mem_closedBall_iff_norm, ← embed_center, ← map_sub]
  have hx : ‖aTilde - FourierDuffing.Certificate.abar‖ ≤ 1 / 200000 :=
    mem_closedBall_iff_norm.mp duffing_analytic_solution.1
  refine (embed.le_opNorm _).trans ((mul_le_mul (norm_reweightCLM_le _ _) hx (norm_nonneg _)
    (by norm_num)).trans_eq ?_)
  norm_num [Numbers.radiusQ]

/-- **The identification companion**: the embedding sends the shipped geometric zero `aTilde`
to the independently certified polynomial-carrier zero `xPoly`. -/
theorem embed_aTilde_eq_xPoly : embed aTilde = Certificate.xPoly :=
  Certificate.unique_eq_xPoly _ embed_aTilde_ball <| funext fun n =>
    (raw_embed aTilde n).trans (duffing_analytic_solution.2.1 n)

private theorem coeff_xPoly : coeff Certificate.xPoly = coeff aTilde := by
  rw [← embed_aTilde_eq_xPoly]
  exact funext (coeff_embed aTilde)

/-! ### The analytic endpoint -/

/-- **The real solution** `u(t) = ∑ xPolyₙ e^{int}`. -/
def solution : ℝ → ℝ := Fourier.realRealization (coeff Certificate.xPoly)

/-- **The holomorphic extension** `U(z) = ∑ xPolyₙ e^{inz}`. -/
def extension : ℂ → ℂ := Fourier.complexRealization (coeff Certificate.xPoly)

/-- **THE POLYNOMIAL-CARRIER ENDPOINT** (book §10.1 at its data, second carrier): the raw
Fourier map has a unique zero `xPoly` in the closed ball of radius `1/10000` around `ā` in
`ℓ²_m`, `m_n = (1 + |n|)²`, certified independently of the geometric certificate; its
coefficient tuple realizes the real-analytic `2π`-periodic solution `u = solution` of
`u'' + u'/10 + 4u − u² = cos t` on `ℝ`, the sum of its complex Fourier series, with the
holomorphic extension `extension` on the strip `|Im z| < log (6/5)`. Uniqueness is among raw
coefficient zeros in the polynomial ball. -/
theorem certified_analytic_solution :
    Certificate.xPoly ∈ Metric.closedBall Certificate.abar (1 / 10000 : ℝ) ∧
    Certificate.rawF Certificate.xPoly = 0 ∧
    (∀ x ∈ Metric.closedBall Certificate.abar (1 / 10000 : ℝ),
      Certificate.rawF x = 0 → x = Certificate.xPoly) ∧
    AnalyticOnNhd ℝ solution Set.univ ∧
    Function.Periodic solution (2 * Real.pi) ∧
    (∀ t, (solution t : ℂ) = Fourier.realization (coeff Certificate.xPoly) t) ∧
    AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5 : ℝ)} ∧
    (∀ t : ℝ, extension (t : ℂ) = (solution t : ℂ)) ∧
    (∀ t, deriv (deriv solution) t + (1 / 10 : ℝ) * deriv solution t +
      4 * solution t - (solution t) ^ 2 = Real.cos t) := by
  have hs : solution = FourierDuffing.Certificate.solution := by
    rw [solution, coeff_xPoly]
    rfl
  have he : extension = FourierDuffing.Certificate.extension := by
    rw [extension, coeff_xPoly]
    rfl
  have hr : ((Numbers.radiusQ : ℚ) : ℝ) = 1 / 10000 := by norm_num [Numbers.radiusQ]
  obtain ⟨-, -, -, -, hsum, han, hper, hext, hagree, hode⟩ := duffing_analytic_solution
  refine ⟨hr ▸ Certificate.xPoly_ball, Certificate.xPoly_zero,
    fun x hx hF => Certificate.unique_eq_xPoly x (hr ▸ hx) hF, hs ▸ han, hs ▸ hper,
    fun t => ?_, he ▸ hext, fun t => ?_, fun t => ?_⟩
  · rw [hs, coeff_xPoly]
    exact (hsum t).tsum_eq.symm
  · rw [he, hs]
    exact hagree t
  · rw [hs]
    exact hode t

end FourierDuffing.Polynomial
