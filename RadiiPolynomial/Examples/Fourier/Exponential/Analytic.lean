import RadiiPolynomial.Examples.Fourier.Exponential.Certificate
import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Realization
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.WeightedL1Iso

/-!
# The exponential Fourier consumer: the real-analytic even periodic solution of
`ψ'' + a (e^ψ − 1) = 0`

Function-space reading of `Certificate.lean`'s `exponential_l1_solution`. The certified
coefficient zero `uTilde ∈ ℓ¹_{6/5}(ℤ; ℂ)` of the symmetrized map
`F̃(u) = −u + Λ(P_e u + a (e^(P_e u) − 1))` (`a = 51/50`, `Λ = diag(1/(1+k²))`), in the open ball of
radius `10⁻⁵` around `ū`, unique among the zeros of `F̃` in the closed ball of radius `1/100`, even
and real, realizes `ψ(t) = ∑ ũₙ e^{int}`, the even `2π`-periodic solution of PlasmaLean's slab
equation `ψ'' + a (e^ψ − 1) = 0` (`exterior/tmp/external_repos/PlasmaLean/PlasmaLean/Design/
ValidatedSlabEquilibrium.lean`, Apache-2.0).

Nothing structural is stated here: the exponential is realized by `Fourier.realization_exp`
(`map_exp` through the algebra lift `circleLift`), the analysis by the inclusion
`lpOneAlg.toLinf : ℓ¹_ν →L Y ℂ ν` (`Compatibility/WeightedL1Iso`) and the faces of
`Analysis/SequenceSpace/Fourier/Realization.lean`: termwise derivatives from the moments of
`Y ℂ ν` (`WeightedLp.Bilateral.summable_moment_Y`), real analyticity, the strip holomorphy on
`|Im z| < log (6/5)` and the parity `realization_neg_of_even`.
-/

open scoped ComplexConjugate

noncomputable section

namespace FourierExponential

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral lpOneAlg
  Numbers

/-- The certified coefficient zero of `exponential_l1_solution`. -/
def uTilde : X := exponential_l1_solution.choose

/-- **The real solution** `ψ(t) = Re ∑ ũₙ e^{int}` (the sum is real). -/
def solution (t : ℝ) : ℝ := Fourier.realRealization (toRealSeq uTilde) t

/-- **The holomorphic extension** `Ψ(z) = ∑ ũₙ e^{inz}`. -/
def extension (z : ℂ) : ℂ := Fourier.complexRealization (toRealSeq uTilde) z

theorem one_lt_ν₆₅ : 1 < (ν₆₅ : ℝ) := by rw [coe_ν₆₅]; norm_num

private theorem uTilde_spec :
    uTilde ∈ Metric.ball ubar (r0 : ℝ) ∧ Ftil uTilde = 0 ∧ Family.R ν₆₅ uTilde = uTilde ∧
      coeffConj uTilde = uTilde ∧
      ∀ v ∈ Metric.closedBall ubar (r1 : ℝ), Ftil v = 0 → v = uTilde :=
  exponential_l1_solution.choose_spec

theorem coeff_uTilde_even (n : ℤ) : toRealSeq uTilde (-n) = toRealSeq uTilde n := by
  have h := congrArg (fun x : X => toRealSeq x n) uTilde_spec.2.2.1
  rwa [toRealSeq_refl] at h

theorem coeff_uTilde_real (n : ℤ) : conj (toRealSeq uTilde n) = toRealSeq uTilde n := by
  have h := congrArg (fun x : X => toRealSeq x n) uTilde_spec.2.2.2.1
  rwa [toRealSeq_coeffConj] at h

theorem coeff_uTilde_conj (n : ℤ) : toRealSeq uTilde (-n) = conj (toRealSeq uTilde n) := by
  rw [coeff_uTilde_even, coeff_uTilde_real]

/-- **The raw coefficient equation** `−n² ũₙ + a ((e^ũ)ₙ − δₙ₀) = 0` (from `F̃(ũ) = 0` and
`R ũ = ũ`). -/
theorem coeff_equation (n : ℤ) :
    -(n : ℂ) ^ 2 * toRealSeq uTilde n +
      51 / 50 * (toRealSeq (NormedSpace.exp uTilde) n - if n = 0 then 1 else 0) = 0 := by
  have h := Family.coeff_equation_of_zero ν₆₅ aC uTilde_spec.2.1 uTilde_spec.2.2.1 n
  have ha : aC = 51 / 50 := by rw [aC, aQ]; push_cast; ring
  rwa [ha] at h

private theorem moments (j : ℕ) :
    Summable fun n : ℤ => (n.natAbs : ℝ) ^ j * ‖toRealSeq uTilde n‖ :=
  (Bilateral.summable_moment_Y (lpOneAlg.toLinf (𝕜 := ℂ) uTilde) zero_le_one one_lt_ν₆₅ j).congr
    fun n => by rw [lpOneAlg.coeff_toLinf, one_pow, mul_one]

private theorem summable_deriv1 :
    Summable fun n => ‖Fourier.derivCoeff (toRealSeq uTilde) n‖ :=
  (moments 1).congr fun n => by rw [Fourier.norm_derivCoeff, pow_one]

private theorem summable_deriv2 :
    Summable fun n => ‖Fourier.derivCoeff (Fourier.derivCoeff (toRealSeq uTilde)) n‖ :=
  (moments 2).congr fun n => by
    rw [Fourier.norm_derivCoeff, Fourier.norm_derivCoeff, ← mul_assoc, ← sq]

private theorem solution_ofReal (t : ℝ) :
    (solution t : ℂ) = Fourier.realization (toRealSeq uTilde) t :=
  Fourier.ofReal_realRealization coeff_uTilde_conj t

private theorem deriv2_conj (n : ℤ) :
    Fourier.derivCoeff (Fourier.derivCoeff (toRealSeq uTilde)) (-n) =
      conj (Fourier.derivCoeff (Fourier.derivCoeff (toRealSeq uTilde)) n) := by
  simp only [Fourier.derivCoeff, map_mul, Complex.conj_I, map_intCast, coeff_uTilde_conj,
    Int.cast_neg]
  ring

/-- The equation in coefficient-series form: `u_(D²ũ)(t) + a (u_(e^ũ)(t) − 1) = 0`. -/
private theorem realization_equation (t : ℝ) :
    Fourier.realization (Fourier.derivCoeff (Fourier.derivCoeff (toRealSeq uTilde))) t +
      51 / 50 * (Fourier.realization (toRealSeq (NormedSpace.exp uTilde)) t - 1) = 0 := by
  have h2 := Fourier.hasSum_realization summable_deriv2 t
  have hE := Fourier.hasSum_realization
    (Bilateral.summable_norm_toRealSeq ν₆₅ (NormedSpace.exp uTilde)) t
  have h1 : HasSum (fun n : ℤ => (if n = 0 then (1 : ℂ) else 0) *
      Complex.exp (n * t * Complex.I)) 1 := by
    convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
    funext n
    split_ifs with hn
    · rw [hn]; simp
    · rw [zero_mul]
  have H := h2.add ((hE.sub h1).mul_left (51 / 50))
  refine H.unique ?_
  convert hasSum_zero using 1
  funext n
  have hc := coeff_equation n
  simp only [Fourier.derivCoeff]
  linear_combination Complex.exp (n * t * Complex.I) * hc +
    (n : ℂ) ^ 2 * toRealSeq uTilde n * Complex.exp (n * t * Complex.I) * (Complex.I_sq)

/-- **THE ANALYTIC ENDPOINT** (PlasmaLean's slab equation on the registered algebra): the certified
zero `uTilde` of the symmetrized map `F̃` on `ℓ¹_{6/5}`, in the ball of radius `10⁻⁵` around `ū`,
with its raw coefficient equation, conjugate symmetry and evenness, unique among the zeros of `F̃`
in the closed ball of radius `1/100`, realizes `ψ = solution`, the real-analytic even
`2π`-periodic solution of `ψ'' + (51/50) (e^ψ − 1) = 0` on `ℝ`, the sum of its Fourier series
`∑ ũₙ e^{int}` at every `t`, with the holomorphic extension `extension` on the strip
`|Im z| < log (6/5)`. -/
theorem exponential_analytic_solution :
    uTilde ∈ Metric.ball ubar (1 / 100000) ∧
      Ftil uTilde = 0 ∧
      (∀ n : ℤ, -(n : ℂ) ^ 2 * toRealSeq uTilde n +
        51 / 50 * (toRealSeq (NormedSpace.exp uTilde) n - if n = 0 then 1 else 0) = 0) ∧
      (∀ n : ℤ, toRealSeq uTilde (-n) = conj (toRealSeq uTilde n)) ∧
      (∀ n : ℤ, toRealSeq uTilde (-n) = toRealSeq uTilde n) ∧
      (∀ v ∈ Metric.closedBall ubar (1 / 100), Ftil v = 0 → v = uTilde) ∧
      (∀ t : ℝ, HasSum (fun n : ℤ => toRealSeq uTilde n * Complex.exp (n * t * Complex.I))
        (solution t)) ∧
      AnalyticOnNhd ℝ solution Set.univ ∧
      Function.Periodic solution (2 * Real.pi) ∧
      AnalyticOnNhd ℂ extension {z : ℂ | |z.im| < Real.log (6 / 5)} ∧
      (∀ t : ℝ, extension t = solution t) ∧
      (∀ t : ℝ, solution (-t) = solution t) ∧
      ∀ t : ℝ, deriv (deriv solution) t + 51 / 50 * (Real.exp (solution t) - 1) = 0 := by
  obtain ⟨hball, hF, -, -, huniq⟩ := uTilde_spec
  have hball' : uTilde ∈ Metric.ball ubar (1 / 100000) := by
    have h : ((r0 : ℚ) : ℝ) = 1 / 100000 := by rw [r0]; push_cast; ring
    rwa [h] at hball
  have huniq' : ∀ v ∈ Metric.closedBall ubar (1 / 100), Ftil v = 0 → v = uTilde := by
    have h : ((r1 : ℚ) : ℝ) = 1 / 100 := by rw [r1]; push_cast; ring
    rw [h] at huniq; exact huniq
  refine ⟨hball', hF, coeff_equation, coeff_uTilde_conj, coeff_uTilde_even, huniq',
    fun t => ?_, ?_, Fourier.realRealization_periodic _, ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩
  · rw [solution_ofReal]
    exact Fourier.hasSum_realization (Bilateral.summable_norm_toRealSeq ν₆₅ uTilde) t
  · have h := Fourier.analyticOnNhd_realRealization (lpOneAlg.toLinf (𝕜 := ℂ) uTilde) one_lt_ν₆₅
    rwa [lpOneAlg.coeff_toLinf] at h
  · have h := Fourier.analyticOnNhd_complexRealization (lpOneAlg.toLinf (𝕜 := ℂ) uTilde)
    rwa [lpOneAlg.coeff_toLinf] at h
  · rw [extension, Fourier.complexRealization_ofReal, solution_ofReal]
  · rw [solution, solution, Fourier.realRealization, Fourier.realRealization,
      Fourier.realization_neg_of_even coeff_uTilde_even]
  · have hd : deriv (deriv solution) t =
        Fourier.realRealization (Fourier.derivCoeff (Fourier.derivCoeff (toRealSeq uTilde))) t := by
      rw [show deriv solution = Fourier.realRealization (Fourier.derivCoeff (toRealSeq uTilde))
          from funext fun s => (Fourier.hasDerivAt_realRealization summable_deriv1 s).deriv]
      exact (Fourier.hasDerivAt_realRealization summable_deriv2 t).deriv
    have he : Fourier.realization (toRealSeq (NormedSpace.exp uTilde)) t =
        (Real.exp (solution t) : ℂ) := by
      rw [Fourier.realization_exp, ← solution_ofReal, Complex.ofReal_exp]
    have h := realization_equation t
    rw [he, ← Fourier.ofReal_realRealization deriv2_conj t] at h
    rw [hd]
    apply Complex.ofReal_injective
    push_cast at h ⊢
    linear_combination h

end FourierExponential

end
