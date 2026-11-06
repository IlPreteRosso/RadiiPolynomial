import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Eigenpair.Certificate
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Bootstrap
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.WeightedL1Iso

/-!
# The analytic eigenfunction of the certified Duffing eigenpair

The eigenvector `v` of `duffing_eigenpair` has geometric decay: (E1) reads
`duffing (1/10) (4 − λ) n · vₙ + (−2 u* ⋆ v)ₙ = 0` (`duff_E1_shifted`), the symbol grows along
`cofinite` for every real parameter (`tendsto_norm_duffing`), `u* ∈ ℓ¹_{11/10}` (`uStarL1`), so
`exists_toRealSeq_eq_of_growth` puts `v` in `ℓ¹_{11/10}` (`exists_toRealSeq_eq_of_E1`). Hence
`V = realRealization (coeff v)` is real-analytic on `ℝ`, `2π`-periodic, nonzero, and solves
`V″ + V′/10 + 4V − 2 u V = λ V` with `u = FourierDuffing.Polynomial.solution`
(`duffing_eigenfunction_analytic`, which also carries every conjunct of `duffing_eigenpair` and of
`duffing_eigenpair_enclosure`).
-/

open scoped ENNReal NNReal DiscreteConvolution ComplexConjugate

noncomputable section

namespace FourierDuffing.Polynomial.Eigenpair

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.Fourier.Eigenpair
open RadiiPolynomial.Fourier.Duffing RadiiPolynomial.Fourier.IkData

section Glue

/-- For every `n : ℤ`, `coeff Certificate.xPoly (-n) = conj (coeff Certificate.xPoly n)`. -/
theorem coeff_xPoly_neg (n : ℤ) :
    coeff Certificate.xPoly (-n) = conj (coeff Certificate.xPoly n) :=
  (mem_realSub_iff_coeff polyWeight_neg).1 xPoly_mem_realSub n

/-- The `PosReal` with value `11 / 10`. -/
def ρ₀ : PosReal := ⟨11 / 10, by norm_num⟩

/-- `(ρ₀ : ℝ) = 11 / 10`. -/
theorem coe_ρ₀ : (ρ₀ : ℝ) = 11 / 10 := rfl

/-- `1 < (ρ₀ : ℝ)`. -/
theorem one_lt_ρ₀ : 1 < (ρ₀ : ℝ) := by
  rw [coe_ρ₀]
  norm_num

/-- `Fact (1 ≤ (ρ₀ : ℝ))`, from `one_lt_ρ₀`. -/
instance fact_one_le_ρ₀ : Fact (1 ≤ (ρ₀ : ℝ)) := ⟨one_lt_ρ₀.le⟩

/-- `(ρ₀ : ℝ) < 6 / 5`. -/
theorem ρ₀_lt_six_fifths : (ρ₀ : ℝ) < 6 / 5 := by
  rw [coe_ρ₀]
  norm_num

/-- For `ρ : PosReal` with `(ρ : ℝ) < 6 / 5`, the element
`Bilateral.toL1 _ (Bilateral.incl FourierDuffing.Certificate.aTilde)` of
`lpOneAlg ℤ (geomFiberZ ℂ ρ)`. -/
def uStarL1 (ρ : PosReal) (hρ : (ρ : ℝ) < 6 / 5) : lpOneAlg ℤ (geomFiberZ ℂ ρ) :=
  Bilateral.toL1 (hρ.trans_eq FourierDuffing.Certificate.coe_ν₆₅.symm)
    (Bilateral.incl FourierDuffing.Certificate.aTilde)

/-- For `ρ : PosReal` with `(ρ : ℝ) < 6 / 5`,
`lpOneAlg.toRealSeq (uStarL1 ρ hρ) = coeff Certificate.xPoly`. -/
theorem toRealSeq_uStarL1 (ρ : PosReal) (hρ : (ρ : ℝ) < 6 / 5) :
    lpOneAlg.toRealSeq (uStarL1 ρ hρ) = coeff Certificate.xPoly := by
  rw [uStarL1, Bilateral.toRealSeq_toL1, coeff_xPoly_eq_coeff_aTilde]
  exact funext (Bilateral.coeff_incl FourierDuffing.Certificate.aTilde)

/-- For every `x : X`, `n ↦ ‖coeff x n‖` is summable. -/
theorem summable_norm_coeff_X (x : X) : Summable fun n => ‖coeff x n‖ :=
  summable_norm_coeff_weightedScalar (w := polyWeight)
    ((NormHelpers.summable_inv_one_add_abs_rpow (s := 4) (by norm_num)).congr fun n => by
      rw [polyWeight, inv_pow, ← pow_mul, one_div, show (4 : ℝ) = ((2 * 2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]) x

/-- For `c : ℂ`, `f v : ℤ → ℂ` and `n : ℤ`, `((c • f) ⋆ᵣ₊ v) n = c * (f ⋆ᵣ₊ v) n`. -/
private theorem smul_addRingConvolution_apply (c : ℂ) (f v : ℤ → ℂ) (n : ℤ) :
    ((c • f) ⋆ᵣ₊ v) n = c * (f ⋆ᵣ₊ v) n := by
  rw [DiscreteConvolution.addRingConvolution_apply, DiscreteConvolution.addRingConvolution_apply,
    ← tsum_mul_left]
  exact tsum_congr fun ab => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Let `v : ℤ → ℂ` and `lam : ℝ` satisfy
`duffing (1/10) 4 n * v n - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ v) n - (lam : ℂ) * v n = 0` for
every `n : ℤ`. Then for every `n : ℤ`,
`duffing (1/10) (4 - lam) n * v n +
(lpOneAlg.toRealSeq ((-2 : ℂ) • uStarL1 ρ₀ ρ₀_lt_six_fifths) ⋆ᵣ₊ v) n = 0`. -/
theorem duff_E1_shifted {v : ℤ → ℂ} {lam : ℝ}
    (hE1 : ∀ n : ℤ, duffing (1/10) 4 n * v n - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ v) n -
      (lam : ℂ) * v n = 0) (n : ℤ) :
    duffing (1/10) (4 - lam) n * v n +
      (lpOneAlg.toRealSeq ((-2 : ℂ) • uStarL1 ρ₀ ρ₀_lt_six_fifths) ⋆ᵣ₊ v) n = 0 := by
  rw [lpOneAlg.toRealSeq_smul, toRealSeq_uStarL1, smul_addRingConvolution_apply,
    ← duffing_sub_ofReal]
  linear_combination hE1 n

/-- For `v : ℤ → ℂ` with `n ↦ ‖v n‖` summable and `lam : ℝ` with
`duffing (1/10) 4 n * v n - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ v) n - (lam : ℂ) * v n = 0` for
every `n : ℤ`, some `a : lpOneAlg ℤ (geomFiberZ ℂ ρ₀)` has `lpOneAlg.toRealSeq a = v`. -/
theorem exists_toRealSeq_eq_of_E1 {v : ℤ → ℂ} {lam : ℝ} (hv : Summable fun n => ‖v n‖)
    (hE1 : ∀ n : ℤ, duffing (1/10) 4 n * v n - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ v) n -
      (lam : ℂ) * v n = 0) :
    ∃ a : lpOneAlg ℤ (geomFiberZ ℂ ρ₀), lpOneAlg.toRealSeq a = v :=
  Bootstrap.exists_toRealSeq_eq_of_growth (tendsto_norm_duffing (1/10) (4 - lam)) _ hv
    (duff_E1_shifted hE1)

end Glue

section EigenfunctionEnd

/-! ## The analytic end theorem -/

open FourierDuffing.Polynomial.Eigenpair.Numbers

/-- There is `y : ↥(realSub polyWeight_neg) × ℝ` in `Metric.ball ybar (1 / 20)` such that,
with `v = (y.1 : X)`, `λ = y.2` and `V = Fourier.realRealization (coeff v) : ℝ → ℝ`:
1. for every `n : ℤ`,
   `duffing (1/10) 4 n * coeff v n - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff v) n -
   (λ : ℂ) * coeff v n = 0`, and `pairing one_le_polyWeight v v = 1`;
2. the `ℝ`-restriction of
   `quadDeriv (LG polyWeight_neg one_le_polyWeight polyRowBound duffEigen)
   (BilG polyWeight_neg one_le_polyWeight duffEigen) y` is invertible;
3. every `z` in `Metric.closedBall ybar (1 / 20)` that satisfies the two equations of 1 (with
   `z` in place of `y`) equals `y`;
4. `|λ - (lbarQ : ℝ)| < 1 / 20`;
5. `4 < λ`;
6. `v ≠ 0`;
7. some `a : lpOneAlg ℤ (geomFiberZ ℂ ρ₀)` has `lpOneAlg.toRealSeq a = coeff v`;
8. `AnalyticOnNhd ℝ V Set.univ`;
9. `Function.Periodic V (2 * Real.pi)`;
10. for every `t : ℝ`, `(V t : ℂ) = Fourier.realization (coeff v) t`;
11. for every `t : ℝ`, `deriv (deriv V) t + 1 / 10 * deriv V t + 4 * V t -
    2 * (FourierDuffing.Polynomial.solution t * V t) = λ * V t`;
12. `V ≠ 0`. -/
theorem duffing_eigenfunction_analytic :
    ∃ y ∈ Metric.ball ybar (1 / 20 : ℝ),
      ((∀ n : ℤ, duffing (1/10) 4 n * coeff (y.1 : X) n
          - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (y.1 : X)) n - (y.2 : ℂ) * coeff (y.1 : X) n =
              0) ∧
        pairing one_le_polyWeight (y.1 : X) (y.1 : X) = 1) ∧
      (ContinuousLinearMap.restrictScalars ℝ
        (quadDeriv (LG polyWeight_neg one_le_polyWeight polyRowBound duffEigen)
          (BilG polyWeight_neg one_le_polyWeight duffEigen) y)).IsInvertible ∧
      (∀ z ∈ Metric.closedBall ybar (1 / 20 : ℝ),
        ((∀ n : ℤ, duffing (1/10) 4 n * coeff (z.1 : X) n
            - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (z.1 : X)) n - (z.2 : ℂ) * coeff (z.1 : X) n =
                0) ∧
          pairing one_le_polyWeight (z.1 : X) (z.1 : X) = 1) → z = y) ∧
      |y.2 - (lbarQ : ℝ)| < 1 / 20 ∧ 4 < y.2 ∧ (y.1 : X) ≠ 0 ∧
      (∃ a : lpOneAlg ℤ (geomFiberZ ℂ ρ₀), lpOneAlg.toRealSeq a = coeff (y.1 : X)) ∧
      AnalyticOnNhd ℝ (Fourier.realRealization (coeff (y.1 : X))) Set.univ ∧
      Function.Periodic (Fourier.realRealization (coeff (y.1 : X))) (2 * Real.pi) ∧
      (∀ t : ℝ, (Fourier.realRealization (coeff (y.1 : X)) t : ℂ) =
        Fourier.realization (coeff (y.1 : X)) t) ∧
      (∀ t : ℝ, deriv (deriv (Fourier.realRealization (coeff (y.1 : X)))) t +
          1 / 10 * deriv (Fourier.realRealization (coeff (y.1 : X))) t +
          4 * Fourier.realRealization (coeff (y.1 : X)) t -
          2 * (FourierDuffing.Polynomial.solution t * Fourier.realRealization (coeff (y.1 : X)) t) =
        y.2 * Fourier.realRealization (coeff (y.1 : X)) t) ∧
      Fourier.realRealization (coeff (y.1 : X)) ≠ 0 := by
  obtain ⟨y, hy, hE, hinv, huniq⟩ := duffing_eigenpair
  obtain ⟨y', hy', hE', hd, h4, hv0⟩ := duffing_eigenpair_enclosure
  have hyy := huniq y' (Metric.ball_subset_closedBall hy') hE'
  rw [hyy] at hd h4 hv0
  have hsym := (mem_realSub_iff_coeff polyWeight_neg).1 y.1.2
  have hv := summable_norm_coeff_X (y.1 : X)
  obtain ⟨a, ha⟩ := exists_toRealSeq_eq_of_E1 hv hE.1
  refine ⟨y, hy, hE, hinv, huniq, hd, h4, hv0, ⟨a, ha⟩, ?_, Fourier.realRealization_periodic _,
    Fourier.ofReal_realRealization hsym, fun t => ?_, fun hV => hv0 (ext_coeff ?_)⟩
  · have h := Fourier.analyticOnNhd_realRealization (lpOneAlg.toLinf (𝕜 := ℂ) a)
      one_lt_ρ₀
    rwa [lpOneAlg.coeff_toLinf, ha] at h
  · have key := Fourier.realRealization_linearSecondOrder (c₀ := 4) (c₁ := 1 / 10) (c₂ := 1)
      (κ := -2) (lam := y.2) (summable_norm_coeff_X Certificate.xPoly) hv
      coeff_xPoly_neg (fun n => by
        have h := hE.1 n
        simp only [duffing] at h
        push_cast at h ⊢
        linear_combination h) t
    rw [show Fourier.realRealization (coeff Certificate.xPoly) t =
      FourierDuffing.Polynomial.solution t from rfl] at key
    linear_combination key
  · rw [coeff_zero]
    exact Fourier.eq_zero_of_realRealization_eq_zero hv hsym hV

end EigenfunctionEnd

end FourierDuffing.Polynomial.Eigenpair

end
