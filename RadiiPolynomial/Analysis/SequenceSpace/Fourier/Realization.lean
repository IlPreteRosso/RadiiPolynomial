import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Carrier
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
in complex time and as `realRealization c t = Re (realization c t)`. No equation is read here; the
equation transfers are in `Applications/Fourier/Transfer.lean`.

## The faces

* **The algebra lift.** For `ν ≥ 1` the family `n ↦ fourier n` of Mathlib's exponential monomials
  on `AddCircle (2π)` is unital, multiplicative and dominated by the weight `ν^|n|` at `C = 1`, so
  `liftAlgHom` gives `circleLift ν : ℓ¹_ν →A[ℂ] C(AddCircle (2π), ℂ)`. Its series converges in
  the sup norm (`hasSum_circleLift`: uniform convergence), its coefficients are absolutely
  summable (`WeightedLp.Bilateral.summable_norm_toRealSeq`), `‖circleLift ν a‖ ≤ ‖a‖`, and at
  `t : ℝ` it is `realization (toRealSeq a) t` (`circleLift_apply_coe`). Multiplicativity
  `realization_mul` is `map_mul` of the lift; no rearrangement of double series is proved here.
  The exponential: `realization_exp` (`u_(e^a)(t) = exp (u_a(t))` at every `t`, no evenness or
  reality hypothesis), since the lift and the evaluation at `t` are continuous ring homomorphisms
  (`NormHelpers.map_exp_of_continuous`).
* **Exponential decay.** For the bounded-coefficient carrier `Y ℂ ν = ℓ^∞_{ν^|n|}`, the moment
  estimate `WeightedLp.Bilateral.summable_moment_Y` and the
  coefficient-preserving map `WeightedLp.Bilateral.toL1 : Y 𝕜 ν →L[𝕜] ℓ¹_{ν'}` (`0 < ν' < ν`) are
  owned by `WeightedLp/Bilateral/Carrier.lean`.
* **Derivatives in moment form.** `derivCoeff c n = i n cₙ`. If `∑ |n| ‖cₙ‖ < ∞`, then
  `realization c` has derivative `realization (derivCoeff c)` at every `t`
  (`hasDerivAt_realization`); the summability of `‖cₙ‖` is derived, the zero mode handled
  explicitly.
* **Strip holomorphy.** For `a ∈ Y ℂ ν`, `complexRealization (coeff a)` is holomorphic on the full
  open strip `|Im z| < log ν` (`analyticOnNhd_complexRealization`) and restricts to
  `realization (coeff a)` on `ℝ` (`complexRealization_ofReal`); for `ν > 1` the real realization
  is real-analytic on `ℝ` (`analyticOnNhd_realRealization`).
* **Reality and parity.** Conjugate symmetry `c₋ₙ = conj cₙ` makes `realization c` real-valued
  (`ofReal_realRealization`); an even family `c₋ₙ = cₙ` has an even realization
  (`realization_neg_of_even`).
* **The cosine.** `cosCoeff` (`b_{±1} = 1/2`) realizes `cos t` (`realization_cosCoeff`).
* **Products, recovery and nonvanishing.** Absolutely summable families multiply under the
  realization (`realization_addRingConvolution`); the lift recovers its coefficients
  (`fourierCoeff_circleLift`), so it is injective (`circleLift_injective`). An absolutely summable family with zero
  complex realization is zero (`eq_zero_of_realization_eq_zero`). For conjugate-symmetric
  coefficients, zero real realization suffices (`eq_zero_of_realRealization_eq_zero`).
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

/-! ### C. Derivatives in moment form -/

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

/-! ### D. Holomorphy on the strip and real analyticity -/

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

/-! ### E. The cosine -/

section Cosine

/-- The cosine coefficients `bₙ = 1/2` at `n = ±1`, `0` elsewhere. -/
def cosCoeff (n : ℤ) : ℂ := if n = 1 ∨ n = -1 then 1 / 2 else 0

/-- The realization of the cosine coefficients is `cos t`. -/
theorem realization_cosCoeff (t : ℝ) : realization cosCoeff t = Real.cos t := by
  rw [realization, tsum_eq_sum (s := {1, -1}) fun n hn => by
    rw [cosCoeff, ite_eq_right (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hn),
      zero_mul], Finset.sum_pair (by decide), Complex.ofReal_cos, Complex.cos,
    cosCoeff, ite_eq_left (Or.inl rfl), cosCoeff, ite_eq_left (Or.inr rfl)]
  push_cast
  ring_nf

end Cosine

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
