import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Realization
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic

/-!
# Equation transfer for the Fourier realization

The equation faces of the Fourier realization (`Analysis/SequenceSpace/Fourier/Realization.lean`):
a coefficient zero is read back as a solution of the differential equation on `ℝ`.

* **The quadratic family.** For `a ∈ X₂ ℂ ν`, `ν > 1`, real `c₀, c₁, c₂`, any `b : ℤ → ℂ` and
  conjugate symmetry of `a`, the coefficient equation `(c₀ + i c₁ n − c₂ n²) aₙ − (a ⋆ a)ₙ − bₙ = 0`
  gives `c₂ u'' + c₁ u' + c₀ u − u² = Re u_b` on `ℝ` for the real realization
  `u = realRealization (coeff a)` (`realRealization_secondOrder`); at `c₂ = 0` this is the
  first-order family `c₁ u' + c₀ u − u² = Re u_b` (`realRealization_firstOrder`). The forcing
  carries no hypothesis: the equation makes `b` absolutely summable.
* **The Duffing family.** For `a ∈ X₂ ℂ ν`, `ν > 1`, under conjugate symmetry, the coefficient
  equation `(−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ = 0` with `b = cosCoeff` gives
  `u'' + c₁ u' + c₂ u − u² = c₃ cos t` on `ℝ` for `u = realRealization (coeff a)`
  (`realRealization_duffing`). The route is direct: termwise differentiation, linearity and
  multiplicativity of the lift; no Fourier-coefficient uniqueness theorem is used. The hypothesis
  is the raw-coefficient form of `rawF (duffing c₁ c₂) (forcing c₃) a n = 0`
  (`RadiiPolynomial.Fourier.Duffing.rawF_duffing`, `Applications/Fourier/Duffing.lean`); this
  module does not import the Duffing family and states it on raw coefficients.
* **The linear second-order family.** For absolutely summable `p, v : ℤ → ℂ`, `p` conjugate
  symmetric, the coefficient equation `(c₀ + i c₁ n − c₂ n²) vₙ + κ (p ⋆ v)ₙ − λ vₙ = 0` gives
  `c₂ V'' + c₁ V' + c₀ V + κ P V = λ V` for the real realizations
  (`realRealization_linearSecondOrder`).
-/

open scoped ComplexConjugate

noncomputable section

namespace RadiiPolynomial.Fourier

open WeightedLp WeightedLp.Bilateral lpOneAlg
open Complex (I)

/-! ### The quadratic family `c₂ u'' + c₁ u' + c₀ u − u² = u_b` and the Duffing family
`u'' + c₁ u' + c₂ u − u² = c₃ cos t` -/

section Duffing

variable {ν : PosReal}

/-- The moments of an `ℓ²_ν` coefficient family (`ν > 1`): the coefficients and their first two
derivative families are absolutely summable. -/
private theorem summable_norm_derivCoeff_X₂ (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) :
    (Summable fun n => ‖coeff a n‖) ∧ (Summable fun n => ‖derivCoeff (coeff a) n‖) ∧
      Summable fun n => ‖derivCoeff (derivCoeff (coeff a)) n‖ := by
  have hm (j : ℕ) : Summable fun n : ℤ => (n.natAbs : ℝ) ^ j * ‖coeff a n‖ :=
    (summable_moment_Y (incl a) zero_le_one hν j).congr fun n => by
      rw [coeff_incl, one_pow, mul_one]
  exact ⟨(hm 0).congr fun n => by rw [pow_zero, one_mul],
    (hm 1).congr fun n => by rw [norm_derivCoeff, pow_one],
    (hm 2).congr fun n => by rw [norm_derivCoeff, norm_derivCoeff, ← mul_assoc, ← sq]⟩

/-- The coefficient form of the equation transfer for the quadratic family: the realizations of
the coefficient families satisfy `c₂ u'' + c₁ u' + c₀ u − u² = u_b`. -/
private theorem realization_secondOrder_coeff (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) {c₀ c₁ c₂ : ℝ}
    {b : ℤ → ℂ}
    (h : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * coeff a n - convCoeff a a n - b n = 0)
    (t : ℝ) :
    c₂ * realization (derivCoeff (derivCoeff (coeff a))) t +
      c₁ * realization (derivCoeff (coeff a)) t + c₀ * realization (coeff a) t -
        realization (coeff a) t ^ 2 = realization b t := by
  obtain ⟨h0, h1, h2⟩ := summable_norm_derivCoeff_X₂ hν a
  -- the product through the circle lift at an intermediate weight `1 < ν' < ν`
  let ν' : PosReal := ⟨(1 + ν) / 2, by have := ν.coe_pos; positivity⟩
  have hν'1 : (1 : ℝ) ≤ ν' := by show (1 : ℝ) ≤ (1 + ν) / 2; linarith
  have hν' : (ν' : ℝ) < ν := by show (1 + (ν : ℝ)) / 2 < ν; linarith
  have : Fact (1 ≤ (ν' : ℝ)) := ⟨hν'1⟩
  have hLL : toRealSeq (toL1 hν' (incl a) * toL1 hν' (incl a)) = convCoeff a a :=
    funext fun n => (toRealSeq_mul_tsum _ _ n).trans (tsum_congr fun i => mul_comm _ _)
  have hq : Summable fun n => ‖convCoeff a a n‖ := hLL ▸ Bilateral.summable_norm_toRealSeq ν' _
  have hsq : realization (convCoeff a a) t = realization (coeff a) t ^ 2 := by
    rw [← hLL, realization_mul, sq]
    rfl
  -- the series of `b` is the combination of the four absolutely convergent series
  have H := ((((hasSum_realization h2 t).mul_left (c₂ : ℂ)).add
    ((hasSum_realization h1 t).mul_left (c₁ : ℂ))).add
    ((hasSum_realization h0 t).mul_left (c₀ : ℂ))).sub (hasSum_realization hq t)
  rw [← hsq]
  exact (H.congr_fun fun n => by
    simp only [derivCoeff]
    linear_combination (-Complex.exp (n * t * I)) * h n -
      c₂ * (n : ℂ) ^ 2 * coeff a n * Complex.exp (n * t * I) * Complex.I_sq).tsum_eq.symm

/-- **The real solution of the quadratic family** (`ν > 1`, conjugate symmetry
`a₋ₙ = conj aₙ`): the real realization solves `c₂ u'' + c₁ u' + c₀ u − u² = Re u_b` on `ℝ`. -/
theorem realRealization_secondOrder (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν)
    (hsym : ∀ n, coeff a (-n) = conj (coeff a n)) {c₀ c₁ c₂ : ℝ} {b : ℤ → ℂ}
    (h : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * coeff a n - convCoeff a a n - b n = 0)
    (t : ℝ) :
    c₂ * deriv (deriv (realRealization (coeff a))) t + c₁ * deriv (realRealization (coeff a)) t +
      c₀ * realRealization (coeff a) t - realRealization (coeff a) t ^ 2 =
        realRealization b t := by
  obtain ⟨-, h1, h2⟩ := summable_norm_derivCoeff_X₂ hν a
  rw [funext fun s => (hasDerivAt_realRealization h1 s).deriv,
    (hasDerivAt_realRealization h2 t).deriv]
  have key := realization_secondOrder_coeff hν a h t
  rw [← ofReal_realRealization hsym t, ← Complex.ofReal_pow] at key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  exact hre

/-- **The real solution of the first-order quadratic family** (`ν > 1`, conjugate symmetry
`a₋ₙ = conj aₙ`): the real realization solves `c₁ u' + c₀ u − u² = Re u_b` on `ℝ`. -/
theorem realRealization_firstOrder (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν)
    (hsym : ∀ n, coeff a (-n) = conj (coeff a n)) {c₀ c₁ : ℝ} {b : ℤ → ℂ}
    (h : ∀ n : ℤ, (c₀ + I * c₁ * n) * coeff a n - convCoeff a a n - b n = 0) (t : ℝ) :
    c₁ * deriv (realRealization (coeff a)) t + c₀ * realRealization (coeff a) t -
      realRealization (coeff a) t ^ 2 = realRealization b t := by
  have key := realRealization_secondOrder hν a hsym (c₀ := c₀) (c₁ := c₁) (c₂ := 0) (b := b)
    (fun n => by rw [Complex.ofReal_zero, zero_mul, sub_zero]; exact h n) t
  rwa [zero_mul, zero_add] at key

/-- The coefficient form of the equation transfer: the realizations of the coefficient families
satisfy the Duffing identity (the quadratic family at `c₀ = c₂`, `c₂ = 1`, `b = c₃ cosCoeff`). -/
private theorem realization_duffing_coeff (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) {c₁ c₂ c₃ : ℝ}
    (h : ∀ n : ℤ, (-(n : ℂ) ^ 2 + I * c₁ * n + c₂) * coeff a n - convCoeff a a n -
      c₃ * cosCoeff n = 0) (t : ℝ) :
    realization (derivCoeff (derivCoeff (coeff a))) t + c₁ * realization (derivCoeff (coeff a)) t +
      c₂ * realization (coeff a) t - realization (coeff a) t ^ 2 = c₃ * Real.cos t := by
  have key := realization_secondOrder_coeff hν a (c₀ := c₂) (c₁ := c₁) (c₂ := 1)
    (b := fun n => c₃ * cosCoeff n) (fun n => by push_cast; linear_combination h n) t
  rw [show realization (fun n => (c₃ : ℂ) * cosCoeff n) t = c₃ * realization cosCoeff t from
    (tsum_congr fun n => mul_assoc _ _ _).trans tsum_mul_left, realization_cosCoeff,
    Complex.ofReal_one, one_mul] at key
  exact key

/-- **The real Duffing solution** (`ν > 1`, conjugate symmetry `a₋ₙ = conj aₙ`): the real
realization solves `u'' + c₁ u' + c₂ u − u² = c₃ cos t` on `ℝ`. -/
theorem realRealization_duffing (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν)
    (hsym : ∀ n, coeff a (-n) = conj (coeff a n)) {c₁ c₂ c₃ : ℝ}
    (h : ∀ n : ℤ, (-(n : ℂ) ^ 2 + I * c₁ * n + c₂) * coeff a n - convCoeff a a n -
      c₃ * cosCoeff n = 0) (t : ℝ) :
    deriv (deriv (realRealization (coeff a))) t + c₁ * deriv (realRealization (coeff a)) t +
      c₂ * realRealization (coeff a) t - realRealization (coeff a) t ^ 2 = c₃ * Real.cos t := by
  obtain ⟨-, h1, h2⟩ := summable_norm_derivCoeff_X₂ hν a
  rw [funext fun s => (hasDerivAt_realRealization h1 s).deriv,
    (hasDerivAt_realRealization h2 t).deriv]
  have key := realization_duffing_coeff hν a h t
  rw [← ofReal_realRealization hsym t, ← Complex.ofReal_pow] at key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  exact hre

end Duffing

section LinearTransfer

open WeightedLp WeightedLp.Bilateral
open Complex (I)
open scoped _root_.DiscreteConvolution ComplexConjugate

/-! ### Linear transfer, complex form -/

/-- For real `c₁ c₂`, `n : ℤ` and `z : ℂ`, both `‖c₂ * (I * n * (I * n * z))‖` and
`‖c₁ * (I * n * z)‖` are at most `‖(I * c₁ * n - c₂ * n ^ 2) * z‖`. -/
private theorem norm_terms_le (c₁ c₂ : ℝ) (n : ℤ) (z : ℂ) :
    ‖(c₂ : ℂ) * (I * n * (I * n * z))‖ ≤ ‖(I * c₁ * n - c₂ * (n : ℂ) ^ 2) * z‖ ∧
      ‖(c₁ : ℂ) * (I * n * z)‖ ≤ ‖(I * c₁ * n - c₂ * (n : ℂ) ^ 2) * z‖ := by
  have e1 : (c₂ : ℂ) * (I * n * (I * n * z)) = ((-(c₂ * (n : ℝ) ^ 2) : ℝ) : ℂ) * z := by
    push_cast
    linear_combination ((c₂ : ℂ) * (n : ℂ) ^ 2 * z) * Complex.I_sq
  have e2 : (c₁ : ℂ) * (I * n * z) = (((c₁ * n : ℝ) : ℂ) * I) * z := by
    push_cast
    ring
  have e3 : I * c₁ * n - c₂ * (n : ℂ) ^ 2 =
      ((-(c₂ * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((c₁ * n : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e1, e2, e3]
  simp only [norm_mul, Complex.norm_add_mul_I, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]
  exact ⟨mul_le_mul_of_nonneg_right (Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _)))
    (norm_nonneg _), mul_le_mul_of_nonneg_right (by
      rw [← abs_mul]
      exact Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))) (norm_nonneg _)⟩

/-- If `n ↦ ‖p n‖` and `n ↦ ‖v n‖` are summable (`p v : ℤ → ℂ`) and, for every `n : ℤ`,
`(c₀ + I * c₁ * n - c₂ * n ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0` (real `c₀ c₁ c₂ κ`,
complex `lam`), then `n ↦ ‖c₂ * derivCoeff (derivCoeff v) n‖` and `n ↦ ‖c₁ * derivCoeff v n‖`
are summable. -/
private theorem summable_norm_terms {c₀ c₁ c₂ κ : ℝ} {lam : ℂ} {p v : ℤ → ℂ}
    (hp : Summable fun n => ‖p n‖) (hv : Summable fun n => ‖v n‖)
    (hE : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0) :
    (Summable fun n => ‖(c₂ : ℂ) * derivCoeff (derivCoeff v) n‖) ∧
      Summable fun n => ‖(c₁ : ℂ) * derivCoeff v n‖ := by
  have hw : Summable fun n : ℤ => ‖(I * c₁ * n - c₂ * (n : ℂ) ^ 2) * v n‖ := by
    refine ((hv.mul_left ‖lam - c₀‖).add
      ((DiscreteConvolution.summable_norm_addRingConvolution hp hv).mul_left
        ‖(κ : ℂ)‖)).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [show (I * c₁ * n - c₂ * (n : ℂ) ^ 2) * v n = (lam - c₀) * v n - κ * (p ⋆ᵣ₊ v) n by
      linear_combination hE n, ← norm_mul, ← norm_mul]
    exact norm_sub_le _ _
  exact ⟨hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => (norm_terms_le c₁ c₂ n (v n)).1,
    hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => (norm_terms_le c₁ c₂ n (v n)).2⟩

/-- For a real `c ≠ 0` and `f : ℤ → ℂ`, if `n ↦ ‖c * f n‖` is summable, then `n ↦ ‖f n‖` is
summable. -/
private theorem summable_of_mul {c : ℝ} (hc : c ≠ 0) {f : ℤ → ℂ}
    (hf : Summable fun n => ‖(c : ℂ) * f n‖) : Summable fun n => ‖f n‖ :=
  (hf.mul_left |c|⁻¹).congr fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc,
      inv_mul_cancel₀ (abs_ne_zero.2 hc), one_mul]

/-- For real `c`, `f : ℤ → ℂ` and `t : ℝ`,
`realization (fun n => c * f n) t = c * realization f t`. -/
private theorem realization_ofReal_mul (c : ℝ) (f : ℤ → ℂ) (t : ℝ) :
    realization (fun n => (c : ℂ) * f n) t = c * realization f t := by
  rw [realization, realization, ← tsum_mul_left]
  exact tsum_congr fun n => mul_assoc _ _ _

/-- If `n ↦ ‖p n‖` and `n ↦ ‖v n‖` are summable (`p v : ℤ → ℂ`) and, for every `n : ℤ`,
`(c₀ + I * c₁ * n - c₂ * n ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0` (real `c₀ c₁ c₂ κ`,
complex `lam`), then for every `t : ℝ`,
`realization (fun n => c₂ * derivCoeff (derivCoeff v) n) t +
realization (fun n => c₁ * derivCoeff v n) t + c₀ * realization v t +
κ * realization p t * realization v t = lam * realization v t`. -/
private theorem realization_linearSecondOrder_coeff {c₀ c₁ c₂ κ : ℝ} {lam : ℂ} {p v : ℤ → ℂ}
    (hp : Summable fun n => ‖p n‖) (hv : Summable fun n => ‖v n‖)
    (hE : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0)
    (t : ℝ) :
    realization (fun n => (c₂ : ℂ) * derivCoeff (derivCoeff v) n) t +
      realization (fun n => (c₁ : ℂ) * derivCoeff v n) t + c₀ * realization v t +
        κ * realization p t * realization v t = lam * realization v t := by
  obtain ⟨hA, hB⟩ := summable_norm_terms hp hv hE
  have H := (((hasSum_realization hA t).add (hasSum_realization hB t)).add
    ((hasSum_realization hv t).mul_left (c₀ : ℂ))).add
    ((hasSum_realization (DiscreteConvolution.summable_norm_addRingConvolution hp hv)
      t).mul_left (κ : ℂ))
  rw [mul_assoc (κ : ℂ), ← realization_addRingConvolution hp hv t]
  refine H.unique (((hasSum_realization hv t).mul_left lam).congr_fun fun n => ?_)
  simp only [derivCoeff]
  linear_combination (Complex.exp (n * t * I)) * hE n +
    c₂ * (n : ℂ) ^ 2 * v n * Complex.exp (n * t * I) * Complex.I_sq

/-! ### Linear transfer, real form -/

/-- For real `c₂` and `v : ℤ → ℂ`, if `n ↦ ‖c₂ * derivCoeff (derivCoeff v) n‖` is summable, then
for every `t : ℝ`, `c₂ * deriv (deriv (realRealization v)) t` equals
`(realization (fun n => c₂ * derivCoeff (derivCoeff v) n) t).re`. -/
private theorem mul_deriv_deriv_realRealization {c₂ : ℝ} {v : ℤ → ℂ}
    (hA : Summable fun n => ‖(c₂ : ℂ) * derivCoeff (derivCoeff v) n‖) (t : ℝ) :
    c₂ * deriv (deriv (realRealization v)) t =
      (realization (fun n => (c₂ : ℂ) * derivCoeff (derivCoeff v) n) t).re := by
  rcases eq_or_ne c₂ 0 with rfl | hc₂
  · simp [realization]
  · have h2 := summable_of_mul hc₂ hA
    have h1 := summable_norm_of_summable_norm_derivCoeff h2
    rw [funext fun s => (hasDerivAt_realRealization h1 s).deriv,
      (hasDerivAt_realRealization h2 t).deriv, realization_ofReal_mul, Complex.re_ofReal_mul]
    rfl

/-- For real `c₁` and `v : ℤ → ℂ`, if `n ↦ ‖c₁ * derivCoeff v n‖` is summable, then for every
`t : ℝ`, `c₁ * deriv (realRealization v) t = (realization (fun n => c₁ * derivCoeff v n) t).re`. -/
private theorem mul_deriv_realRealization {c₁ : ℝ} {v : ℤ → ℂ}
    (hB : Summable fun n => ‖(c₁ : ℂ) * derivCoeff v n‖) (t : ℝ) :
    c₁ * deriv (realRealization v) t = (realization (fun n => (c₁ : ℂ) * derivCoeff v n) t).re := by
  rcases eq_or_ne c₁ 0 with rfl | hc₁
  · simp [realization]
  · rw [(hasDerivAt_realRealization (summable_of_mul hc₁ hB) t).deriv,
      realization_ofReal_mul, Complex.re_ofReal_mul]
    rfl

/-- If `n ↦ ‖p n‖` and `n ↦ ‖v n‖` are summable (`p v : ℤ → ℂ`), `p (-n) = conj (p n)` for every
`n : ℤ`, and, for every `n : ℤ`,
`(c₀ + I * c₁ * n - c₂ * n ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0` (real `c₀ c₁ c₂ κ lam`),
then for every `t : ℝ`, with `V = realRealization v` and `P = realRealization p`,
`c₂ * deriv (deriv V) t + c₁ * deriv V t + c₀ * V t + κ * P t * V t = lam * V t`. -/
theorem realRealization_linearSecondOrder {c₀ c₁ c₂ κ lam : ℝ} {p v : ℤ → ℂ}
    (hp : Summable fun n => ‖p n‖) (hv : Summable fun n => ‖v n‖)
    (hps : ∀ n, p (-n) = conj (p n))
    (hE : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * v n + κ * (p ⋆ᵣ₊ v) n - lam * v n = 0)
    (t : ℝ) :
    c₂ * deriv (deriv (realRealization v)) t + c₁ * deriv (realRealization v) t +
      c₀ * realRealization v t + κ * realRealization p t * realRealization v t =
        lam * realRealization v t := by
  obtain ⟨hA, hB⟩ := summable_norm_terms hp hv hE
  rw [mul_deriv_deriv_realRealization hA, mul_deriv_realRealization hB]
  have key := realization_linearSecondOrder_coeff hp hv hE t
  rw [← ofReal_realRealization hps t, ← Complex.ofReal_mul] at key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.re_ofReal_mul] at hre
  exact hre

end LinearTransfer

end RadiiPolynomial.Fourier

end
