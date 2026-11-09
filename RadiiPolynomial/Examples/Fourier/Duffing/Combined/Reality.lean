import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Certificate
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.RealityConvolution

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: reality of the zero

`R := conjReflL combWeight_neg` is the conjugate reflection on `X = ℓ²_m(ℤ; ℂ)`,
`m_n = (6/5)^{|n|} (1 + |n|)²`. It fixes `ā` (the leaf's reality clause), commutes with `rawF` up
to `n ↦ -n` and conjugation (product equivariance `conjReflL_convCLM` at the combined row bound,
the symbol and forcing symmetries `duffing_conj`, `coeff_forcing_conj`), and is an isometry; the
uniqueness of the raw zero in the closed ball of radius `3/10000` then gives `R xC = xC`, i.e.
`coeff xC (-n) = conj (coeff xC n)`. No geometric certified zero is used.
-/

open scoped DiscreteConvolution ComplexConjugate
open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.Fourier.Duffing (duffing forcing duffing_conj coeff_forcing_conj)
open RadiiPolynomial.Fourier.IkData (headF)
open FourierDuffing.Numbers (leaf)
open FourierDuffing.Certificate (ν₆₅)
open RadiiPolynomial.Certification.Fourier.Quadratic (toC toC_zero toC_cconj mem_idx idx)

noncomputable section

namespace FourierDuffing.Combined.Certificate

/-- The conjugate reflection `(R x)ₙ = conj x₋ₙ` on the combined carrier (`ℝ`-linear isometry). -/
abbrev R : X →L[ℝ] X := conjReflL combWeight_neg

/-- **Reality of the candidate**: `R ā = ā`, from the leaf reality clause. -/
theorem R_abar : R abar = abar :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_abar, coeff_abar]
    by_cases h : n ∈ idx 10
    · have hn : -n ∈ idx 10 := mem_idx.2 (by have := mem_idx.1 h; omega)
      have e := FourierDuffing.Numbers.checks.2.2.1 (-n) hn
      rw [neg_neg] at e
      rw [e, toC_cconj]
    · have hn : -n ∉ headF 10 := fun h' =>
        h (mem_idx.2 (by have := Finset.mem_Icc.1 h'; omega))
      rw [leaf.abarQ_eq_zero hn, leaf.abarQ_eq_zero fun h' => h (mem_idx.2 (Finset.mem_Icc.1 h')),
        toC_zero, map_zero]

/-- The forcing is real: `g₋ₙ = conj gₙ`. -/
theorem coeff_g_neg (n : ℤ) : coeff g (-n) = conj (coeff g n) := by
  rw [coeff_g_eq_forcing, coeff_g_eq_forcing, coeff_forcing_conj]

/-- **Equivariance of the raw map**: `rawF (R x) n = conj (rawF x (-n))`. -/
theorem rawF_R (x : X) (n : ℤ) : rawF (R x) n = conj (rawF x (-n)) := by
  have hconv : ∀ y : X, (coeff y ⋆ᵣ₊ coeff y) = coeff (convCLM combRowBound y y) :=
    fun y => (coeff_convCLM _ y y).symm
  rw [rawF, rawF, hconv, hconv, R, ← conjReflL_convCLM combWeight_neg combRowBound,
    coeff_conjReflL, coeff_conjReflL, coeff_g_neg, μ, duffing_conj, map_sub, map_sub, map_mul,
    Complex.conj_conj, Complex.conj_conj]

/-- **Ball uniqueness gives reality**: `R xC = xC`. -/
theorem R_xC : R xC = xC := by
  refine unique_eq_xC _ ?_ ?_
  · rw [← R_abar]; exact (isometry_conjReflL combWeight_neg).mapsTo_closedBall _ _ xC_ball
  · funext n; rw [rawF_R, xC_zero]; simp

/-- **The combined-carrier zero is real**: `xC₋ₙ = conj xCₙ` for every `n`. -/
theorem coeff_xC_neg : ∀ n : ℤ, coeff xC (-n) = starRingEnd ℂ (coeff xC n) :=
  (conjReflL_eq_self_iff_coeff combWeight_neg xC).1 R_xC

end FourierDuffing.Combined.Certificate
