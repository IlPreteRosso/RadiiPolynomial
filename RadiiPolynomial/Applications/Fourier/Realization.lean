import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.Norm.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Fourier realization of bilateral coefficient sequences

The bilateral counterpart of the Taylor realization `l1Weighted.eval`
(`Geometric/Evaluation.lean`, `Applications/IVP/Taylor/Trajectory.lean`): a coefficient
family `c : ℤ → ℂ` is realized as the `2π`-periodic function
`realization c t = ∑' n, cₙ e^{int}` on `ℝ`, as `complexRealization c z = ∑' n, cₙ e^{inz}`
in complex time and as `realRealization c t = Re (realization c t)`.

## The faces

* **The algebra lift.** For `ν ≥ 1` the family `n ↦ fourier n` of Mathlib's exponential monomials
  on `AddCircle (2π)` is unital, multiplicative and dominated by the weight `ν^|n|` at `C = 1`, so
  `liftAlgHom` gives `circleLift ν : ℓ¹_ν →A[ℂ] C(AddCircle (2π), ℂ)`. Its series converges in
  the sup norm (`hasSum_circleLift`: uniform convergence), its coefficients are absolutely
  summable (`summable_norm_toRealSeq`), `‖circleLift ν a‖ ≤ ‖a‖`, and at `t : ℝ` it is
  `realization (toRealSeq a) t` (`circleLift_apply_coe`). Multiplicativity
  `realization_mul` is `map_mul` of the lift; no rearrangement of double series is proved here.
  The exponential: `realization_exp` (`u_(e^a)(t) = exp (u_a(t))` at every `t`, no evenness or
  reality hypothesis), since the lift and the evaluation at `t` are continuous ring homomorphisms
  (`NormHelpers.map_exp_of_continuous`).
* **Exponential decay.** The bounded-coefficient carrier `Y ℂ ν = ℓ^∞_{ν^|n|}` is the weakest
  carrier hypothesis: for `0 ≤ ρ < ν` the moments `|n|^j ‖aₙ‖ ρ^|n|` are summable
  (`summable_moment_Y`), and `toL1 : Y 𝕜 ν →L[𝕜] ℓ¹_{ν'}` (`0 < ν' < ν`) keeps the coefficients,
  with `‖toL1 a‖ ≤ (1 + q) / (1 − q) ‖a‖`, `q = ν'/ν`. With the inclusion `incl : X₂ → Y` this is
  the chain `ℓ²_ν → ℓ^∞_ν → ℓ¹_{ν'}` that feeds the lift from an `ℓ²` zero. An `ℓ¹_ν` element
  enters `Y 𝕜 ν` through the bounded inclusion `lpOneAlg.toLinf` (`lpOneAlg.coeff_toLinf`: the
  coefficients are kept; `Compatibility/WeightedL1Iso`).
* **Derivatives in moment form.** `derivCoeff c n = i n cₙ`. If `∑ |n| ‖cₙ‖ < ∞`, then
  `realization c` has derivative `realization (derivCoeff c)` at every `t`
  (`hasDerivAt_realization`); the summability of `‖cₙ‖` is derived, the zero mode handled
  explicitly. The derivative coefficients of `a ∈ ℓ¹_ν` need not lie in `ℓ¹_ν` without the
  same-weight moment hypothesis `∑ |n| ‖aₙ‖ ν^|n| < ∞`; for `a ∈ Y ℂ ν` they lie in `ℓ¹_ρ` for every
  `ρ < ν` (`summable_moment_Y` at `j = 1`).
* **Strip holomorphy.** For `a ∈ Y ℂ ν`, `complexRealization (coeff a)` is holomorphic on the full
  open strip `|Im z| < log ν` (`analyticOnNhd_complexRealization`) and restricts to
  `realization (coeff a)` on `ℝ` (`complexRealization_ofReal`); for `ν > 1` the real realization
  is real-analytic on `ℝ` (`analyticOnNhd_realRealization`).
* **Reality and parity.** Conjugate symmetry `c₋ₙ = conj cₙ` makes `realization c` real-valued
  (`ofReal_realRealization`); an even family `c₋ₙ = cₙ` has an even realization
  (`realization_neg_of_even`).
* **The quadratic family.** For `a ∈ X₂ ℂ ν`, `ν > 1`, real `c₀, c₁, c₂` and any `b : ℤ → ℂ`, the
  coefficient equation `(c₀ + i c₁ n − c₂ n²) aₙ − (a ⋆ a)ₙ − bₙ = 0` gives
  `c₂ u'' + c₁ u' + c₀ u − u² = u_b` on `ℝ` for `u = realization (coeff a)`, `u_b = realization b`
  (`realization_secondOrder`) and, under conjugate symmetry of `a`, for the real realizations
  (`realRealization_secondOrder`, right side `realRealization b`). At `c₂ = 0` this is the
  first-order family `c₁ u' + c₀ u − u² = u_b` (`realization_firstOrder`,
  `realRealization_firstOrder`). The forcing carries no hypothesis: the equation makes `b`
  absolutely summable, and the real part of `u_b` is `realRealization b` by definition.
* **The Duffing family.** For `a ∈ X₂ ℂ ν`, `ν > 1`, the coefficient equation
  `(−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ = 0` with `b = cosCoeff` (`b_{±1} = 1/2`) gives
  `u'' + c₁ u' + c₂ u − u² = c₃ cos t` on `ℝ` for `u = realization (coeff a)`
  (`realization_duffing`) and, under conjugate symmetry, for `u = realRealization (coeff a)`
  (`realRealization_duffing`). The route is direct: termwise differentiation, linearity and
  multiplicativity of the lift; no Fourier-coefficient uniqueness theorem is used. The hypothesis
  is the raw-coefficient form of `rawF (duffing c₁ c₂) (forcing c₃) a n = 0`
  (`RadiiPolynomial.Fourier.Duffing.rawF_duffing`, `Applications/Fourier/Duffing.lean`); this
  module does not import the Duffing family and states it on raw coefficients.
-/

open scoped ComplexConjugate

noncomputable section

namespace RadiiPolynomial.Fourier

open WeightedLp WeightedLp.Bilateral lpOneAlg
open Complex (I)

/-! ### A. The realization of a coefficient family -/

section Realization

/-- **The realization** `u_c(t) = ∑' n, cₙ e^{int}` of a bilateral coefficient family on the real
line (a `tsum`: `0` when the series is not summable). -/
def realization (c : ℤ → ℂ) (t : ℝ) : ℂ := ∑' n : ℤ, c n * Complex.exp (n * t * I)

/-- **The complex-time realization** `U_c(z) = ∑' n, cₙ e^{inz}`. -/
def complexRealization (c : ℤ → ℂ) (z : ℂ) : ℂ := ∑' n : ℤ, c n * Complex.exp (n * z * I)

/-- The real part of the realization. -/
def realRealization (c : ℤ → ℂ) (t : ℝ) : ℝ := (realization c t).re

/-- The complex-time realization restricts to the realization on the real line. -/
theorem complexRealization_ofReal (c : ℤ → ℂ) (t : ℝ) :
    complexRealization c t = realization c t := rfl

/-- Each phase has modulus one: `‖e^{int}‖ = 1`. -/
theorem norm_exp_mul_I (n : ℤ) (t : ℝ) : ‖Complex.exp (n * t * I)‖ = 1 := by
  rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

/-- An absolutely summable family is the sum of its realization series. -/
theorem hasSum_realization {c : ℤ → ℂ} (hc : Summable fun n => ‖c n‖) (t : ℝ) :
    HasSum (fun n : ℤ => c n * Complex.exp (n * t * I)) (realization c t) :=
  (Summable.of_norm (hc.congr fun n => by rw [norm_mul, norm_exp_mul_I, mul_one])).hasSum

/-- The realization is `2π`-periodic (every term is). -/
theorem realization_periodic (c : ℤ → ℂ) : Function.Periodic (realization c) (2 * Real.pi) :=
  fun t => tsum_congr fun n => by
    rw [show (n : ℂ) * ((t + 2 * Real.pi : ℝ) : ℂ) * I = n * t * I + n * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The real realization is `2π`-periodic. -/
theorem realRealization_periodic (c : ℤ → ℂ) :
    Function.Periodic (realRealization c) (2 * Real.pi) :=
  fun t => congrArg Complex.re (realization_periodic c t)

/-- **Conjugate symmetry makes the realization real**: `c₋ₙ = conj cₙ` gives
`conj (u_c t) = u_c t`. -/
theorem conj_realization {c : ℤ → ℂ} (hc : ∀ n, c (-n) = conj (c n)) (t : ℝ) :
    conj (realization c t) = realization c t := by
  rw [realization, Complex.conj_tsum]
  refine (tsum_congr fun n => ?_).trans
    ((Equiv.neg ℤ).tsum_eq fun n => c n * Complex.exp (n * t * I))
  rw [Equiv.neg_apply, hc, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I, Int.cast_neg]
  ring

/-- Under conjugate symmetry the realization is the real realization. -/
theorem ofReal_realRealization {c : ℤ → ℂ} (hc : ∀ n, c (-n) = conj (c n)) (t : ℝ) :
    (realRealization c t : ℂ) = realization c t :=
  Complex.conj_eq_iff_re.1 (conj_realization hc t)

/-- **The realization of an even family is even** (the reindex `n ↦ −n`). -/
theorem realization_neg_of_even {c : ℤ → ℂ} (hc : ∀ n, c (-n) = c n) (t : ℝ) :
    realization c (-t) = realization c t := by
  rw [realization, realization, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [Equiv.neg_apply, hc]
  congr 2
  push_cast
  ring

end Realization

/-! ### B. The realization as the algebra lift on the circle -/

/-- The period `2π` is positive (the compactness of `AddCircle (2π)`). -/
instance fact_zero_lt_two_pi : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

section CircleLift

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- The exponential monomials are dominated by the bilateral weight at `C = 1` (`ν ≥ 1`). -/
theorem norm_fourier_le_weight (n : ℤ) :
    ‖(fourier n : C(AddCircle (2 * Real.pi), ℂ))‖ ≤
      1 * FiberTrivialization.weight (E := geomFiberZ ℂ ν) n := by
  rw [fourier_norm, one_mul, geomFiberZ_weight]
  exact one_le_pow₀ Fact.out

/-- **The Fourier realization as the algebra lift** (`ν ≥ 1`): the continuous algebra homomorphism
`a ↦ ∑' n, aₙ • fourier n` from `ℓ¹_ν` into the continuous functions on the circle
`AddCircle (2π)`, the lift of the unital multiplicative family `n ↦ fourier n`. -/
def circleLift : lpOneAlg ℤ (geomFiberZ ℂ ν) →A[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  liftAlgHom (fun n => fourier n) 1 (norm_fourier_le_weight ν)
    (ContinuousMap.ext fun _ => fourier_zero) (fun _ _ => ContinuousMap.ext fun _ => fourier_add)

theorem circleLift_apply (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    circleLift ν a = ∑' n, toRealSeq a n • fourier n := rfl

/-- Computation face: the unit single at `n` goes to `fourier n`. -/
@[simp] theorem circleLift_single (n : ℤ) : circleLift ν (single n 1) = fourier n :=
  liftAlgHom_single _ _ _ _ _ n

/-- **Uniform convergence**: the realization series converges in the sup norm of
`C(AddCircle (2π), ℂ)`. -/
theorem hasSum_circleLift (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    HasSum (fun n => toRealSeq a n • (fourier n : C(AddCircle (2 * Real.pi), ℂ)))
      (circleLift ν a) :=
  (liftCLM_summable _ (norm_fourier_le_weight ν) a).hasSum

/-- The sup bound `‖u_a‖_∞ ≤ ‖a‖`. -/
theorem norm_circleLift_apply_le (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) : ‖circleLift ν a‖ ≤ ‖a‖ :=
  (norm_liftAlgHom_apply_le _ _ _ _ _ a).trans_eq (one_mul _)

/-- **Absolute convergence**: the coefficients of `a ∈ ℓ¹_ν` are absolutely summable (`ν ≥ 1`). -/
theorem summable_norm_toRealSeq (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    Summable fun n => ‖toRealSeq a n‖ :=
  (summable_norm a).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    rw [norm_eq_abs_toReal_mul_weight a n, geomFiberZ_weight]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ Fact.out)

/-- `fourier n` at the point `t` of the circle `AddCircle (2π)` is `e^{int}`. -/
private theorem fourier_coe_two_pi (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (2 * Real.pi)) = Complex.exp (n * t * I) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- **The lift on the real line is the realization**: `circleLift ν a t = u_{a}(t)`. -/
theorem circleLift_apply_coe (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) (t : ℝ) :
    circleLift ν a t = realization (toRealSeq a) t := by
  rw [circleLift_apply,
    ← ContinuousMap.tsum_apply (liftCLM_summable _ (norm_fourier_le_weight ν) a)]
  exact tsum_congr fun n => by rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_two_pi]

/-- **Multiplicativity** (`map_mul` of the lift): `u_{a ⋆ b} = u_a u_b`. -/
theorem realization_mul (a b : lpOneAlg ℤ (geomFiberZ ℂ ν)) (t : ℝ) :
    realization (toRealSeq (a * b)) t =
      realization (toRealSeq a) t * realization (toRealSeq b) t := by
  rw [← circleLift_apply_coe, ← circleLift_apply_coe, ← circleLift_apply_coe, map_mul,
    ContinuousMap.mul_apply]

/-- **The realization of `e^a` is the pointwise exponential**: `u_(e^a)(t) = exp (u_a(t))` at every
`t : ℝ` (no evenness or reality hypothesis; the lift `circleLift ν` and the evaluation at `t` are
continuous ring homomorphisms). -/
theorem realization_exp (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) (t : ℝ) :
    realization (toRealSeq (NormedSpace.exp a)) t =
      Complex.exp (realization (toRealSeq a) t) := by
  rw [← circleLift_apply_coe, ← circleLift_apply_coe,
    NormHelpers.map_exp_of_continuous (circleLift ν) (circleLift ν).continuous a,
    Complex.exp_eq_exp_ℂ]
  exact NormHelpers.map_exp_of_continuous
    (ContinuousMap.evalAlgHom ℂ ℂ (t : AddCircle (2 * Real.pi))) (continuous_eval_const _) _

end CircleLift

/-! ### C. Exponential decay: `ℓ^∞_ν → ℓ¹_{ν'}` -/

section Decay

/-- The bilateral moments of a geometric sequence are summable: `∑ |n|^j q^|n| < ∞`
(`|q| < 1`). -/
theorem summable_natAbs_pow_mul_geometric (j : ℕ) {q : ℝ} (hq : |q| < 1) :
    Summable fun n : ℤ => (n.natAbs : ℝ) ^ j * q ^ n.natAbs := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ j * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one j (by rwa [Real.norm_eq_abs])
  refine Summable.of_nat_of_neg_add_one (by simpa only [Int.natAbs_natCast] using h) ?_
  have hn : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  simpa only [hn, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

/-- The bilateral geometric series: `∑_{n ∈ ℤ} q^|n| = (1 + q) / (1 − q)` (`|q| < 1`). -/
theorem hasSum_geometric_natAbs {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℤ => q ^ n.natAbs) ((1 + q) / (1 - q)) := by
  have h : HasSum (fun n : ℕ => q ^ (n + 1)) (q * (1 - q)⁻¹) := by
    simpa only [pow_succ'] using (hasSum_geometric_of_abs_lt_one hq).mul_left q
  have hp : HasSum (fun n : ℕ => q ^ ((n : ℤ) + 1).natAbs) (q * (1 - q)⁻¹) := by
    simpa only [show ∀ n : ℕ, ((n : ℤ) + 1).natAbs = n + 1 from fun n => by omega] using h
  have hm : HasSum (fun n : ℕ => q ^ (-((n : ℤ) + 1)).natAbs) (q * (1 - q)⁻¹) := by
    simpa only [show ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 from fun n => by omega] using h
  convert HasSum.of_add_one_of_neg_add_one (f := fun n : ℤ => q ^ n.natAbs) hp hm using 1
  have h1 : 1 - q ≠ 0 := (sub_pos.2 (abs_lt.1 hq).2).ne'
  rw [Int.natAbs_zero, pow_zero]
  field_simp
  ring

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- **The decay estimate of `Y ℂ ν`**: `‖aₙ‖ ρ^|n| ≤ ‖a‖ (ρ/ν)^|n|`. -/
theorem norm_coeff_mul_pow_le_Y (a : Y 𝕜 ν) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (n : ℤ) :
    ‖coeff a n‖ * ρ ^ n.natAbs ≤ ‖a‖ * (ρ / ν) ^ n.natAbs := by
  have hν : (ν : ℝ) ^ n.natAbs ≠ 0 := pow_ne_zero _ ν.coe_pos.ne'
  rw [show ‖coeff a n‖ * ρ ^ n.natAbs =
      (‖coeff a n‖ * (ν : ℝ) ^ n.natAbs) * (ρ / ν) ^ n.natAbs by rw [div_pow]; field_simp]
  exact mul_le_mul_of_nonneg_right (normMag_le_norm_Y a n)
    (pow_nonneg (div_nonneg hρ0 ν.coe_pos.le) _)

/-- **The moments of `a ∈ Y ℂ ν` at every weight `ρ < ν`**: `∑ |n|^j ‖aₙ‖ ρ^|n| < ∞`. At `j = 0`
this is `a ∈ ℓ¹_ρ`; at `j = 1` it puts the derivative coefficients `i n aₙ` in `ℓ¹_ρ`. -/
theorem summable_moment_Y (a : Y 𝕜 ν) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < ν) (j : ℕ) :
    Summable fun n : ℤ => (n.natAbs : ℝ) ^ j * (‖coeff a n‖ * ρ ^ n.natAbs) :=
  ((summable_natAbs_pow_mul_geometric j ((abs_of_nonneg (div_nonneg hρ0 ν.coe_pos.le)).trans_lt
      ((div_lt_one ν.coe_pos).2 hρ))).mul_left ‖a‖).of_nonneg_of_le (fun _ => by positivity)
    fun n => (mul_le_mul_of_nonneg_left (norm_coeff_mul_pow_le_Y a hρ0 n)
      (by positivity)).trans_eq (mul_left_comm _ _ _)

variable {ν' : PosReal}

/-- The coefficients of `a ∈ Y 𝕜 ν` lie in `ℓ¹_{ν'}` for `ν' < ν`. -/
theorem memL1v_coeff_Y (h : (ν' : ℝ) < ν) (a : Y 𝕜 ν) :
    MemL1v (fun k : ℤ => (ν' : ℝ) ^ k.natAbs) (coeff a) :=
  (summable_moment_Y a ν'.coe_pos.le h 0).congr fun n => by rw [pow_zero, one_mul]

/-- The bound of `toL1` before bundling. -/
private theorem norm_ofRaw_coeff_le (h : (ν' : ℝ) < ν) (a : Y 𝕜 ν) :
    ‖ofRaw (coeff a) (memL1v_coeff_Y h a)‖ ≤ (1 + ν' / ν) / (1 - ν' / ν) * ‖a‖ := by
  have hq : |(ν' : ℝ) / ν| < 1 := (abs_of_nonneg (div_nonneg ν'.coe_pos.le ν.coe_pos.le)).trans_lt
    ((div_lt_one ν.coe_pos).2 h)
  rw [norm_symbol_eq]
  exact (hasSum_le (fun n => norm_coeff_mul_pow_le_Y a ν'.coe_pos.le n)
    (memL1v_coeff_Y h a).hasSum ((hasSum_geometric_natAbs hq).mul_left ‖a‖)).trans_eq
    (mul_comm _ _)

/-- **The map `Y_ν → ℓ¹_{ν'}`** (`0 < ν' < ν`), keeping the coefficients
(`toRealSeq_toL1`), with constant `(1 + q) / (1 − q)`, `q = ν'/ν` (`norm_toL1_apply_le`). -/
def toL1 (h : (ν' : ℝ) < ν) : Y 𝕜 ν →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν') :=
  LinearMap.mkContinuous
    { toFun := fun a => ofRaw (coeff a) (memL1v_coeff_Y h a)
      map_add' := fun a b => ext_toRealSeq ((coeff_add a b).trans
        (toRealSeq_add (ofRaw (coeff a) (memL1v_coeff_Y h a))
          (ofRaw (coeff b) (memL1v_coeff_Y h b))).symm)
      map_smul' := fun r a => ext_toRealSeq ((coeff_smul r a).trans
        (toRealSeq_smul r (ofRaw (coeff a) (memL1v_coeff_Y h a))).symm) }
    ((1 + ν' / ν) / (1 - ν' / ν)) (norm_ofRaw_coeff_le h)

/-- `toL1` keeps the coefficients. -/
@[simp] theorem toRealSeq_toL1 (h : (ν' : ℝ) < ν) (a : Y 𝕜 ν) :
    toRealSeq (toL1 h a) = coeff a := rfl

/-- The explicit constant: `‖toL1 a‖ ≤ (1 + q) / (1 − q) ‖a‖`, `q = ν'/ν`. -/
theorem norm_toL1_apply_le (h : (ν' : ℝ) < ν) (a : Y 𝕜 ν) :
    ‖toL1 h a‖ ≤ (1 + ν' / ν) / (1 - ν' / ν) * ‖a‖ :=
  norm_ofRaw_coeff_le h a

end Decay

/-! ### D. Derivatives in moment form -/

section Derivative

/-- The derivative coefficients `(D c)ₙ = i n cₙ`. -/
def derivCoeff (c : ℤ → ℂ) (n : ℤ) : ℂ := I * n * c n

theorem norm_derivCoeff (c : ℤ → ℂ) (n : ℤ) : ‖derivCoeff c n‖ = n.natAbs * ‖c n‖ := by
  rw [derivCoeff, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
    Nat.cast_natAbs, Int.cast_abs]

/-- The first moment controls the coefficients: `∑ |n| ‖cₙ‖ < ∞ ⇒ ∑ ‖cₙ‖ < ∞` (the zero mode is
a single term). -/
theorem summable_norm_of_summable_norm_derivCoeff {c : ℤ → ℂ}
    (h : Summable fun n => ‖derivCoeff c n‖) : Summable fun n => ‖c n‖ := by
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun n : ℤ => if n = 0 then ‖c 0‖ else 0) fun n hn => ?_)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  · rw [ite_eq_right (by simpa only [Finset.mem_singleton] using hn)]
  · rw [norm_derivCoeff]
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left rfl, Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_add]
    · rw [ite_eq_right hn, add_zero]
      exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast Int.natAbs_pos.2 hn)

private theorem hasDerivAt_exp_mul_I (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (n * s * I)) (I * n * Complex.exp (n * t * I)) t := by
  convert (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (n : ℂ)).mul_const I).cexp using 1
  · rfl
  change I * (n : ℂ) * Complex.exp ((n : ℂ) * (t : ℂ) * I) =
    Complex.exp ((n : ℂ) * (t : ℂ) * I) * ((n : ℂ) * 1 * I)
  ring

/-- **Termwise differentiation** (moment form): if `∑ |n| ‖cₙ‖ < ∞`, the realization has
derivative `realization (derivCoeff c)` at every `t`. -/
theorem hasDerivAt_realization {c : ℤ → ℂ} (h : Summable fun n => ‖derivCoeff c n‖) (t : ℝ) :
    HasDerivAt (realization c) (realization (derivCoeff c) t) t :=
  hasDerivAt_tsum (u := fun n => ‖derivCoeff c n‖)
    (g := fun n (s : ℝ) => c n * Complex.exp (n * s * I))
    (g' := fun n (s : ℝ) => derivCoeff c n * Complex.exp (n * s * I)) h
    (fun n s => by
      convert (hasDerivAt_exp_mul_I n s).const_mul (c n) using 1
      rw [derivCoeff]
      ring)
    (fun n s => by rw [norm_mul, norm_exp_mul_I, mul_one])
    (hasSum_realization (summable_norm_of_summable_norm_derivCoeff h) 0).summable t

/-- Termwise differentiation of the real realization. -/
theorem hasDerivAt_realRealization {c : ℤ → ℂ} (h : Summable fun n => ‖derivCoeff c n‖)
    (t : ℝ) : HasDerivAt (realRealization c) (realRealization (derivCoeff c) t) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_realization h t)

end Derivative

/-! ### E. Holomorphy on the strip and real analyticity -/

section Strip

variable {ν : PosReal}

/-- **Strip holomorphy** (full width): for `a ∈ Y ℂ ν`, the complex-time realization is
holomorphic on the open strip `|Im z| < log ν`. -/
theorem analyticOnNhd_complexRealization (a : Y ℂ ν) :
    AnalyticOnNhd ℂ (complexRealization (coeff a)) {z : ℂ | |z.im| < Real.log ν} := by
  intro z hz
  obtain ⟨s, hzs, hsν⟩ := exists_between (show |z.im| < Real.log ν from hz)
  have hU : IsOpen {w : ℂ | |w.im| < s} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine DifferentiableOn.analyticAt ?_ (hU.mem_nhds hzs)
  refine Complex.differentiableOn_tsum_of_summable_norm
    (F := fun n w => coeff a n * Complex.exp (n * w * I))
    (u := fun n => ‖coeff a n‖ * Real.exp s ^ n.natAbs) ?_
    (fun n => ((((differentiable_id.const_mul (n : ℂ)).mul_const I).cexp).const_mul
      (coeff a n)).differentiableOn) hU fun n w hw => ?_
  · simpa only [pow_zero, one_mul] using
      summable_moment_Y a (Real.exp_pos s).le ((Real.lt_log_iff_exp_lt ν.coe_pos).1 hsν) 0
  · rw [norm_mul, Complex.norm_exp, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have hre : ((n : ℂ) * w * I).re = -((n : ℝ) * w.im) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hre, Nat.cast_natAbs, Int.cast_abs]
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt hw) (abs_nonneg _)

/-- **Real analyticity** (`ν > 1`): the real realization of `a ∈ Y ℂ ν` is real-analytic on `ℝ`. -/
theorem analyticOnNhd_realRealization (a : Y ℂ ν) (hν : 1 < (ν : ℝ)) :
    AnalyticOnNhd ℝ (realRealization (coeff a)) Set.univ := fun t _ => by
  have hz : |(t : ℂ).im| < Real.log ν := by
    rw [Complex.ofReal_im, abs_zero]
    exact Real.log_pos hν
  exact (Complex.reCLM.analyticAt _).comp
    (((analyticOnNhd_complexRealization a (t : ℂ) hz).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt t))

end Strip

/-! ### F. The quadratic family `c₂ u'' + c₁ u' + c₀ u − u² = u_b` and the Duffing family
`u'' + c₁ u' + c₂ u − u² = c₃ cos t` -/

section Duffing

/-- The cosine coefficients `bₙ = 1/2` at `n = ±1`, `0` elsewhere. -/
def cosCoeff (n : ℤ) : ℂ := if n = 1 ∨ n = -1 then 1 / 2 else 0

theorem summable_norm_cosCoeff : Summable fun n => ‖cosCoeff n‖ :=
  summable_of_ne_finset_zero (s := {1, -1}) fun n hn => by
    rw [cosCoeff, ite_eq_right (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hn),
      norm_zero]

/-- The realization of the cosine coefficients is `cos t`. -/
theorem realization_cosCoeff (t : ℝ) : realization cosCoeff t = Real.cos t := by
  rw [realization, tsum_eq_sum (s := {1, -1}) fun n hn => by
    rw [cosCoeff, ite_eq_right (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hn),
      zero_mul], Finset.sum_pair (by decide), Complex.ofReal_cos, Complex.cos,
    cosCoeff, ite_eq_left (Or.inl rfl), cosCoeff, ite_eq_left (Or.inr rfl)]
  push_cast
  ring_nf

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
  have hq : Summable fun n => ‖convCoeff a a n‖ := hLL ▸ summable_norm_toRealSeq ν' _
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

/-- **Equation transfer for the quadratic family** (`ν > 1`): a coefficient zero `a ∈ X₂ ℂ ν` of
`(c₀ + i c₁ n − c₂ n²) aₙ − (a ⋆ a)ₙ − bₙ` realizes a solution of
`c₂ u'' + c₁ u' + c₀ u − u² = u_b` on `ℝ`, `u_b = realization b`. -/
theorem realization_secondOrder (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) {c₀ c₁ c₂ : ℝ} {b : ℤ → ℂ}
    (h : ∀ n : ℤ, (c₀ + I * c₁ * n - c₂ * (n : ℂ) ^ 2) * coeff a n - convCoeff a a n - b n = 0)
    (t : ℝ) :
    c₂ * deriv (deriv (realization (coeff a))) t + c₁ * deriv (realization (coeff a)) t +
      c₀ * realization (coeff a) t - realization (coeff a) t ^ 2 = realization b t := by
  obtain ⟨-, h1, h2⟩ := summable_norm_derivCoeff_X₂ hν a
  rw [funext fun s => (hasDerivAt_realization h1 s).deriv, (hasDerivAt_realization h2 t).deriv]
  exact realization_secondOrder_coeff hν a h t

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

/-- **Equation transfer for the first-order quadratic family** (`ν > 1`): a coefficient zero
`a ∈ X₂ ℂ ν` of `(c₀ + i c₁ n) aₙ − (a ⋆ a)ₙ − bₙ` realizes a solution of
`c₁ u' + c₀ u − u² = u_b` on `ℝ` (`realization_secondOrder` at `c₂ = 0`). -/
theorem realization_firstOrder (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) {c₀ c₁ : ℝ} {b : ℤ → ℂ}
    (h : ∀ n : ℤ, (c₀ + I * c₁ * n) * coeff a n - convCoeff a a n - b n = 0) (t : ℝ) :
    c₁ * deriv (realization (coeff a)) t + c₀ * realization (coeff a) t -
      realization (coeff a) t ^ 2 = realization b t := by
  have key := realization_secondOrder hν a (c₀ := c₀) (c₁ := c₁) (c₂ := 0) (b := b)
    (fun n => by rw [Complex.ofReal_zero, zero_mul, sub_zero]; exact h n) t
  rwa [Complex.ofReal_zero, zero_mul, zero_add] at key

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

/-- **Equation transfer for the Duffing family** (`ν > 1`): a coefficient zero `a ∈ X₂ ℂ ν` of
`(−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ` realizes a solution of
`u'' + c₁ u' + c₂ u − u² = c₃ cos t` on `ℝ`. -/
theorem realization_duffing (hν : 1 < (ν : ℝ)) (a : X₂ ℂ ν) {c₁ c₂ c₃ : ℝ}
    (h : ∀ n : ℤ, (-(n : ℂ) ^ 2 + I * c₁ * n + c₂) * coeff a n - convCoeff a a n -
      c₃ * cosCoeff n = 0) (t : ℝ) :
    deriv (deriv (realization (coeff a))) t + c₁ * deriv (realization (coeff a)) t +
      c₂ * realization (coeff a) t - realization (coeff a) t ^ 2 = c₃ * Real.cos t := by
  obtain ⟨-, h1, h2⟩ := summable_norm_derivCoeff_X₂ hν a
  rw [funext fun s => (hasDerivAt_realization h1 s).deriv, (hasDerivAt_realization h2 t).deriv]
  exact realization_duffing_coeff hν a h t

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

section Summability

open WeightedLp

/-- If `∑ (weight n)⁻¹ ^ 2 < ∞`, then every `x : WeightedLp M E 2` has
`Summable fun n => ‖WeightedLp.coeff x n‖`. -/
theorem summable_norm_coeff_of_summable_inv_sq {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
    {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E]
    (hw : Summable fun n => (FiberTrivialization.weight (E := E) n)⁻¹ ^ 2)
    (x : WeightedLp M E 2) : Summable fun n => ‖WeightedLp.coeff x n‖ := by
  have hx : Summable fun n => ‖x n‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((hx.add hw).div_const 2)
  rw [WeightedLp.norm_coeff, div_eq_mul_inv]
  nlinarith [two_mul_le_add_sq ‖x n‖ (FiberTrivialization.weight (E := E) n)⁻¹]

/-- If `∑ (w n)⁻¹ ^ 2 < ∞`, then every `x : WeightedLp M (WeightedScalar 𝕜 w) 2` has
`Summable fun n => ‖WeightedLp.coeff x n‖`. -/
theorem summable_norm_coeff_weightedScalar {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
    {w : M → ℝ} [PosWeight w] (hw : Summable fun n => (w n)⁻¹ ^ 2)
    (x : WeightedLp M (WeightedScalar 𝕜 w) 2) : Summable fun n => ‖WeightedLp.coeff x n‖ :=
  summable_norm_coeff_of_summable_inv_sq
    (by simpa only [WeightedScalar.fiberTrivialization_weight] using hw) x

/-- For `1 ≤ j`, `Summable fun n : ℤ => ((1 + |n|) ^ j)⁻¹ ^ 2`. -/
theorem summable_inv_one_add_abs_pow_sq {j : ℕ} (hj : 1 ≤ j) :
    Summable fun n : ℤ => ((1 + |(n : ℝ)|) ^ j)⁻¹ ^ 2 := by
  have h2 := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  have hN : Summable fun n : ℕ => ((1 + (n : ℝ)) ^ j)⁻¹ ^ 2 :=
    h2.of_nonneg_of_le (fun _ => by positivity) fun n => by
      rw [inv_pow, ← pow_mul, Nat.cast_add_one, add_comm (n : ℝ) 1]
      exact inv_anti₀ (by positivity)
        (pow_le_pow_right₀ (le_add_of_nonneg_right n.cast_nonneg) (by omega))
  refine Summable.of_nat_of_neg (hN.congr fun n => ?_) (hN.congr fun n => ?_)
  · rw [Int.cast_natCast, abs_of_nonneg n.cast_nonneg]
  · rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg n.cast_nonneg]

end Summability

section RealizationEnd

open WeightedLp WeightedLp.Bilateral
open Complex (I)
open scoped _root_.DiscreteConvolution ComplexConjugate

/-! ### Product realization -/

/-- For `c : ℤ → ℂ` with `n ↦ ‖c n‖` summable, `MemL1v` holds for `c` at the weight
`k ↦ ((1 : PosReal) : ℝ) ^ k.natAbs`. -/
private theorem memL1v_one {c : ℤ → ℂ} (hc : Summable fun n => ‖c n‖) :
    MemL1v (fun k : ℤ => ((1 : PosReal) : ℝ) ^ k.natAbs) c :=
  hc.congr fun n => by
    show ‖c n‖ = ‖c n‖ * ((1 : PosReal) : ℝ) ^ n.natAbs
    rw [show ((1 : PosReal) : ℝ) = 1 from rfl, one_pow, mul_one]

/-- For `p v : ℤ → ℂ` with `n ↦ ‖p n‖` and `n ↦ ‖v n‖` summable, `n ↦ ‖(p ⋆ᵣ₊ v) n‖` is
summable. -/
theorem summable_norm_addRingConvolution {p v : ℤ → ℂ} (hp : Summable fun n => ‖p n‖)
    (hv : Summable fun n => ‖v n‖) : Summable fun n => ‖(p ⋆ᵣ₊ v) n‖ := by
  have : Fact (1 ≤ ((1 : PosReal) : ℝ)) := ⟨le_rfl⟩
  let P : lpOneAlg ℤ (geomFiberZ ℂ 1) := ofRaw p (memL1v_one hp)
  let V : lpOneAlg ℤ (geomFiberZ ℂ 1) := ofRaw v (memL1v_one hv)
  have hc : (P * V).toRealSeq = p ⋆ᵣ₊ v := lpOneAlg.toRealSeq_mul_fun P V
  exact hc ▸ summable_norm_toRealSeq 1 (P * V)

/-- For `p v : ℤ → ℂ` with `n ↦ ‖p n‖` and `n ↦ ‖v n‖` summable and every `t : ℝ`,
`realization (p ⋆ᵣ₊ v) t = realization p t * realization v t`. -/
theorem realization_addRingConvolution {p v : ℤ → ℂ} (hp : Summable fun n => ‖p n‖)
    (hv : Summable fun n => ‖v n‖) (t : ℝ) :
    realization (p ⋆ᵣ₊ v) t = realization p t * realization v t := by
  have : Fact (1 ≤ ((1 : PosReal) : ℝ)) := ⟨le_rfl⟩
  let P : lpOneAlg ℤ (geomFiberZ ℂ 1) := ofRaw p (memL1v_one hp)
  let V : lpOneAlg ℤ (geomFiberZ ℂ 1) := ofRaw v (memL1v_one hv)
  have hc : (P * V).toRealSeq = p ⋆ᵣ₊ v := lpOneAlg.toRealSeq_mul_fun P V
  exact hc ▸ realization_mul 1 P V t

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
      ((summable_norm_addRingConvolution hp hv).mul_left ‖(κ : ℂ)‖)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
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
    ((hasSum_realization (summable_norm_addRingConvolution hp hv) t).mul_left (κ : ℂ))
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

/-! ### Fourier-coefficient recovery and injectivity -/

/-- For `ν : PosReal` with `1 ≤ ν`, `a : lpOneAlg ℤ (geomFiberZ ℂ ν)` and `n : ℤ`,
`fourierCoeff (circleLift ν a) n = a.toRealSeq n`. -/
theorem fourierCoeff_circleLift (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) (n : ℤ) :
    fourierCoeff (circleLift ν a) n = a.toRealSeq n := by
  have h := ((hasSum_circleLift ν a).mapL (ContinuousMap.toLp (E := ℂ) 2
    (AddCircle.haarAddCircle (T := 2 * Real.pi)) ℂ)).mapL
      (innerSL ℂ (fourierBasis (T := 2 * Real.pi) n))
  rw [← fourierCoeff_toLp, ← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  refine h.unique ?_
  have hb : ∀ m, innerSL ℂ (fourierBasis (T := 2 * Real.pi) n)
      (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (a.toRealSeq m • fourier m)) =
        if m = n then a.toRealSeq n else 0 := fun m => by
    rw [innerSL_apply_apply, ← HilbertBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_toLp,
      ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply]
    split_ifs with h1 h2 h2
    · subst h1; rw [smul_eq_mul, mul_one]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact smul_zero _
  simp only [hb]
  exact hasSum_ite_eq n _

/-- For `ν : PosReal` with `1 ≤ ν`, `circleLift ν` is injective. -/
theorem circleLift_injective (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    Function.Injective (circleLift ν) := fun a b hab =>
  lpOneAlg.ext_toRealSeq <| funext fun m => by
    rw [← fourierCoeff_circleLift, ← fourierCoeff_circleLift, hab]

/-! ### Nonvanishing -/

/-- If `n ↦ ‖v n‖` is summable (`v : ℤ → ℂ`) and `realization v = 0`, then `v = 0`. -/
theorem eq_zero_of_realization_eq_zero {v : ℤ → ℂ} (hv : Summable fun n => ‖v n‖)
    (hV : realization v = 0) : v = 0 := by
  have : Fact (1 ≤ ((1 : PosReal) : ℝ)) := ⟨le_rfl⟩
  let a : lpOneAlg ℤ (geomFiberZ ℂ 1) := ofRaw v (memL1v_one hv)
  have h0 : circleLift 1 a = 0 := ContinuousMap.ext fun x => by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact (circleLift_apply_coe 1 a t).trans (congrFun hV t)
  have := congrArg lpOneAlg.toRealSeq (circleLift_injective 1 (h0.trans (map_zero _).symm))
  exact this.trans lpOneAlg.toRealSeq_zero

/-- If `n ↦ ‖v n‖` is summable (`v : ℤ → ℂ`), `v (-n) = conj (v n)` for every `n : ℤ`, and
`realRealization v = 0`, then `v = 0`. -/
theorem eq_zero_of_realRealization_eq_zero {v : ℤ → ℂ} (hv : Summable fun n => ‖v n‖)
    (hsym : ∀ n, v (-n) = conj (v n)) (hV : realRealization v = 0) : v = 0 :=
  eq_zero_of_realization_eq_zero hv <| funext fun t => by
    rw [← ofReal_realRealization hsym t, congrFun hV t, Pi.zero_apply, Pi.zero_apply,
      Complex.ofReal_zero]

end RealizationEnd

end RadiiPolynomial.Fourier

end
