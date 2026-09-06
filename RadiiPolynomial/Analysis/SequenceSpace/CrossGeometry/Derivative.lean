import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega

/-!
# Differentiation across the Chebyshev--Taylor realization

The Taylor realization of `Tₖ` differentiates to `k Uₖ₋₁`, coefficient for
coefficient.  The zero mode is included by retaining Mathlib's integer-indexed
`U₋₁ = 0`.  The intrinsic Chebyshev derivative lands in omega-weighted
`U`-coefficients; a separate synthesis map realizes those polynomials on a
Taylor disc.  Their composite is Taylor differentiation after restriction,
giving the four-corner derivative naturality square.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace CrossGeometry

open lpOneAlg Polynomial

/-! ### Polynomial coefficient realizations -/

private lemma polynomialOmega_mem (σ : PosReal) (p : ℝ[X]) :
    l1Omega.Mem σ p.coeff := by
  rw [l1Omega.mem_iff]
  refine summable_of_ne_finset_zero (s := p.support) fun n hn => ?_
  have hcoeff : p.coeff n = 0 := by
    exact Classical.not_not.mp (fun hne => hn (Polynomial.mem_support_iff.mpr hne))
  rw [hcoeff, abs_zero, zero_mul]

/-- The coefficient realization of the integer-indexed Chebyshev polynomial
`Uₙ` in the omega-weighted Taylor range.  In particular, `U₋₁` is represented
by the zero vector. -/
def uPolyOmega (σ : PosReal) (n : ℤ) : l1Omega σ :=
  l1Omega.mk (Chebyshev.U ℝ n).coeff (polynomialOmega_mem σ _)

@[simp] theorem uPolyOmega_toSeq (σ : PosReal) (n : ℤ) (m : ℕ) :
    l1Omega.toSeq (uPolyOmega σ n) m = (Chebyshev.U ℝ n).coeff m :=
  rfl

private lemma coeff_derivative_T (k m : ℕ) :
    (Polynomial.derivative (Chebyshev.T ℝ (k : ℤ))).coeff m =
      (k : ℝ) * (Chebyshev.U ℝ ((k : ℤ) - 1)).coeff m := by
  rw [Chebyshev.T_derivative_eq_U, ← Polynomial.C_eq_intCast,
    Polynomial.coeff_C_mul]
  norm_num

/-- **Columnwise derivative naturality.** For every natural mode, including
`k = 0`, differentiating the Taylor realization of `Tₖ` is exactly the
omega-weighted coefficient realization of `k Uₖ₋₁`. -/
theorem derivShift_chebPolyTaylor (σ : PosReal) (k : ℕ) :
    derivShift (chebPolyTaylor σ k) =
      (k : ℝ) • uPolyOmega σ ((k : ℤ) - 1) := by
  apply l1Omega.ext
  intro m
  rw [derivShift_apply, chebPolyTaylor_toSeq, l1Omega.smul_toSeq,
    uPolyOmega_toSeq, ← coeff_derivative_T, Polynomial.coeff_derivative]
  ring

/-! ### The intrinsic Chebyshev derivative -/

private abbrev l1OmegaWrapped (ν : PosReal) :=
  lpOneAlg ℕ (OmegaScaledReal ν)

private def omegaSingle (ν : PosReal) (n : ℕ) (x : ℝ) : l1Omega ν :=
  (lpOneAlg.single n x : l1OmegaWrapped ν).toLp

@[simp] private theorem omegaSingle_toSeq (ν : PosReal) (n : ℕ) (x : ℝ)
    (m : ℕ) :
    l1Omega.toSeq (omegaSingle ν n x) m = if m = n then x else 0 := by
  change lpOneAlg.toRealSeq (lpOneAlg.single n x : l1OmegaWrapped ν) m = _
  rw [lpOneAlg.toRealSeq_single]

private theorem norm_omegaSingle (ν : PosReal) (n : ℕ) (x : ℝ) :
    ‖omegaSingle ν n x‖ = |x| * OmegaScaledReal.omegaWeight ν n := by
  change ‖(lpOneAlg.single n x : l1OmegaWrapped ν)‖ = _
  rw [lpOneAlg.norm_single, Real.norm_eq_abs]
  change |x| * (|1| * OmegaScaledReal.omegaWeight ν n) = _
  rw [abs_one, one_mul]

private def omegaWrapCLM (ν : PosReal) :
    l1Omega ν →L[ℝ] l1OmegaWrapped ν :=
  LinearMap.mkContinuous
    { toFun := lpOneAlg.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun a => by
      change ‖a‖ ≤ 1 * ‖a‖
      rw [one_mul]

@[simp] private theorem omegaWrapCLM_omegaSingle (ν : PosReal)
    (n : ℕ) (x : ℝ) :
    omegaWrapCLM ν (omegaSingle ν n x) = lpOneAlg.single n x :=
  rfl

private def omegaToSeqCLM (ν : PosReal) (m : ℕ) :
    l1Omega ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => l1Omega.toSeq a m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (OmegaScaledReal.omegaWeight ν m)⁻¹ fun a => by
      have h := lp.norm_apply_le_norm one_ne_zero a m
      change |l1Omega.toSeq a m| * OmegaScaledReal.omegaWeight ν m ≤ ‖a‖ at h
      change |l1Omega.toSeq a m| ≤
        (OmegaScaledReal.omegaWeight ν m)⁻¹ * ‖a‖
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ OmegaScaledReal.omegaWeight_pos).2 h

@[simp] private theorem omegaToSeqCLM_apply (ν : PosReal) (m : ℕ)
    (a : l1Omega ν) :
    omegaToSeqCLM ν m a = l1Omega.toSeq a m :=
  rfl

private def chebyshevDerivativeToUColumn (ν : PosReal) (k : ℕ) : l1Omega ν :=
  chebyshevStorageFactor k •
    ((k : ℝ) • omegaSingle ν (k - 1) 1)

private lemma chebyshevDerivativeToUColumn_le (ν : PosReal) (k : ℕ) :
    ‖chebyshevDerivativeToUColumn ν k‖ ≤
      ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) k (1 : ℝ)‖ := by
  cases k with
  | zero =>
      simp [chebyshevDerivativeToUColumn]
  | succ k =>
      rw [BorderedScaledReal.norm_lpAlgRingData_ofReal, abs_one, one_mul,
        borderedWeight_succ, chebyshevDerivativeToUColumn]
      simp only [Nat.succ_ne_zero, chebyshevStorageFactor, if_false,
        norm_smul, Real.norm_eq_abs]
      rw [norm_omegaSingle, abs_one, one_mul]
      simp only [Nat.add_sub_cancel]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (Nat.cast_nonneg (k + 1)),
        omegaWeight_mul_index]

private def chebyshevDerivativeToUBorderedCLM (ν : PosReal) :
    l1Bordered ν →L[ℝ] l1Omega ν :=
  lpOneAlg.liftCLM (chebyshevDerivativeToUColumn ν) 1 fun k => by
    rw [one_mul]
    exact chebyshevDerivativeToUColumn_le ν k

private theorem chebyshevDerivativeToUBorderedCLM_toSeq (ν : PosReal)
    (b : l1Bordered ν) (m : ℕ) :
    l1Omega.toSeq (chebyshevDerivativeToUBorderedCLM ν b) m =
      2 * ((m : ℝ) + 1) * lpOneAlg.toRealSeq b (m + 1) := by
  have hs := lpOneAlg.liftCLM_summable
    (chebyshevDerivativeToUColumn ν)
    (fun k => by rw [one_mul]; exact chebyshevDerivativeToUColumn_le ν k) b
  have hmapped := hs.hasSum.mapL (omegaToSeqCLM ν m)
  have hsum : (∑' k,
      omegaToSeqCLM ν m
        (lpOneAlg.toRealSeq b k • chebyshevDerivativeToUColumn ν k)) =
      omegaToSeqCLM ν m (chebyshevDerivativeToUBorderedCLM ν b) := by
    rw [chebyshevDerivativeToUBorderedCLM, lpOneAlg.liftCLM_apply]
    exact hmapped.tsum_eq
  rw [← omegaToSeqCLM_apply ν m, ← hsum]
  have hterm : ∀ k : ℕ,
      omegaToSeqCLM ν m
          (lpOneAlg.toRealSeq b k • chebyshevDerivativeToUColumn ν k) =
        if k = m + 1 then
          2 * ((m : ℝ) + 1) * lpOneAlg.toRealSeq b (m + 1)
        else 0 := by
    intro k
    cases k with
    | zero =>
        simp [chebyshevDerivativeToUColumn]
    | succ k =>
        simp only [map_smul, omegaToSeqCLM_apply,
          chebyshevDerivativeToUColumn, Nat.succ_ne_zero,
          chebyshevStorageFactor, if_false,
          omegaSingle_toSeq, Nat.add_sub_cancel]
        by_cases hkm : k = m
        · subst k
          simp
          ring
        · have hsucc : k + 1 ≠ m + 1 := by omega
          rw [if_neg (Ne.symm hkm), if_neg hsucc]
          ring
  rw [tsum_congr hterm, tsum_ite_eq]

/-- The intrinsic derivative of a physical Chebyshev series, expressed in
`U`-coefficients with the omega weight at the same ellipse parameter. -/
def chebyshevDerivativeToUCLM (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev.symmetricSubalgebra ν →L[ℝ] l1Omega ν :=
  (chebyshevDerivativeToUBorderedCLM ν).comp
    ((l1Chebyshev.nonnegRestrictCLM ν).comp
      (l1Chebyshev.symmetricSubalgebra ν).toSubmodule.subtypeL)

/-- Coefficient formula for the intrinsic derivative: the `Uₘ` coefficient is
`2(m+1)` times the physical `Tₘ₊₁` coefficient. -/
theorem chebyshevDerivativeToUCLM_toSeq (ν : PosReal)
    [Fact (1 ≤ (ν : ℝ))] (a : l1Chebyshev.symmetricSubalgebra ν) (m : ℕ) :
    l1Omega.toSeq (chebyshevDerivativeToUCLM ν a) m =
      2 * ((m : ℝ) + 1) *
        l1Chebyshev.toSeq (a : l1Chebyshev ν) ((m + 1 : ℕ) : ℤ) := by
  change l1Omega.toSeq
      (chebyshevDerivativeToUBorderedCLM ν
        (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))) m = _
  rw [chebyshevDerivativeToUBorderedCLM_toSeq,
    l1Chebyshev.nonnegRestrictCLM_apply, nonnegRestrict_toSeq]
  rfl

theorem norm_chebyshevDerivativeToUCLM_apply_le (ν : PosReal)
    [Fact (1 ≤ (ν : ℝ))] (a : l1Chebyshev.symmetricSubalgebra ν) :
    ‖chebyshevDerivativeToUCLM ν a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_liftCLM_apply_le
    (chebyshevDerivativeToUColumn ν) 1
    (fun k => by rw [one_mul]; exact chebyshevDerivativeToUColumn_le ν k)
    (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))
  rw [one_mul] at h
  exact h.trans_eq (l1Chebyshev.nonnegRestrictCLM_norm_of_isSymmetric _ a.2)

theorem norm_chebyshevDerivativeToUCLM_le (ν : PosReal)
    [Fact (1 ≤ (ν : ℝ))] :
    ‖chebyshevDerivativeToUCLM ν‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul] using norm_chebyshevDerivativeToUCLM_apply_le ν a

/-! ### Synthesis of `U`-polynomials on a smaller Taylor radius -/

private lemma norm_uPolyOmega_natCast_le {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) (n : ℕ) :
    ‖uPolyOmega σ (n : ℤ)‖ ≤ OmegaScaledReal.omegaWeight ν n := by
  have hindex : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
  have hderiv := congrArg norm (derivShift_chebPolyTaylor σ (n + 1))
  rw [hindex, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (n + 1))] at hderiv
  have hρ0 : 0 ≤ bernsteinParameter (σ : ℝ) := by
    unfold bernsteinParameter
    exact add_nonneg σ.coe_nonneg (Real.sqrt_nonneg _)
  have hupper : ‖derivShift (chebPolyTaylor σ (n + 1))‖ ≤
      (ν : ℝ) ^ (n + 1) :=
    (derivShift_norm_le _).trans <|
      (chebPolyTaylor_norm_le σ (n + 1)).trans
        (pow_le_pow_left₀ hρ0 hgate (n + 1))
  have hscaled : ((n + 1 : ℕ) : ℝ) * ‖uPolyOmega σ (n : ℤ)‖ ≤
      (ν : ℝ) ^ (n + 1) := by
    rw [← hderiv]
    exact hupper
  rw [OmegaScaledReal.omegaWeight]
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))).2
  simpa only [mul_comm] using hscaled

private lemma uPolyOmegaSynthesisColumn_le {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) (n : ℕ) :
    ‖uPolyOmega σ (n : ℤ)‖ ≤
      ‖lpAlgRingData.ofReal (E := OmegaScaledReal ν) n (1 : ℝ)‖ := by
  have h := norm_uPolyOmega_natCast_le hgate n
  change ‖uPolyOmega σ (n : ℤ)‖ ≤
    |(1 : ℝ)| * OmegaScaledReal.omegaWeight ν n
  simpa using h

private def uPolyOmegaSynthesisWrappedCLM {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) :
    l1OmegaWrapped ν →L[ℝ] l1Omega σ :=
  lpOneAlg.liftCLM (fun n => uPolyOmega σ (n : ℤ)) 1 fun n => by
    rw [one_mul]
    exact uPolyOmegaSynthesisColumn_le hgate n

/-- Synthesis of `U`-coefficient data as omega-weighted Taylor coefficients.
The raw gate says exactly that the target Taylor disc lies in the source
Bernstein ellipse. -/
def uPolyOmegaSynthesisCLM {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) :
    l1Omega ν →L[ℝ] l1Omega σ :=
  (uPolyOmegaSynthesisWrappedCLM hgate).comp (omegaWrapCLM ν)

/-- The synthesis map is the absolutely convergent sum of the input
`U`-coefficients against their monomial coefficient realizations. -/
theorem uPolyOmegaSynthesisCLM_apply {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) (a : l1Omega ν) :
    uPolyOmegaSynthesisCLM hgate a =
      ∑' n : ℕ, l1Omega.toSeq a n • uPolyOmega σ (n : ℤ) :=
  rfl

private theorem uPolyOmegaSynthesisCLM_omegaSingle {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) (n : ℕ) (x : ℝ) :
    uPolyOmegaSynthesisCLM hgate (omegaSingle ν n x) =
      x • uPolyOmega σ (n : ℤ) := by
  rw [uPolyOmegaSynthesisCLM, ContinuousLinearMap.comp_apply,
    omegaWrapCLM_omegaSingle, uPolyOmegaSynthesisWrappedCLM,
    lpOneAlg.liftCLM_single]

theorem norm_uPolyOmegaSynthesisCLM_apply_le {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) (a : l1Omega ν) :
    ‖uPolyOmegaSynthesisCLM hgate a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_liftCLM_apply_le
    (fun n : ℕ => uPolyOmega σ (n : ℤ)) 1
    (fun n : ℕ => by rw [one_mul]; exact uPolyOmegaSynthesisColumn_le hgate n)
    (omegaWrapCLM ν a)
  rw [one_mul] at h
  exact h

theorem norm_uPolyOmegaSynthesisCLM_le {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) :
    ‖uPolyOmegaSynthesisCLM hgate‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul] using norm_uPolyOmegaSynthesisCLM_apply_le hgate a

/-! ### The physical derivative and its naturality square -/

private def chebyshevDerivativeToTaylorColumn (σ : PosReal) (k : ℕ) : l1Omega σ :=
  chebyshevStorageFactor k • ((k : ℝ) • uPolyOmega σ ((k : ℤ) - 1))

private lemma chebyshevDerivativeToTaylorColumn_le {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν) (k : ℕ) :
    ‖chebyshevDerivativeToTaylorColumn σ k‖ ≤
      ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) k (1 : ℝ)‖ := by
  have hsource := chebyshevToTaylorBorderedCLM_norm_le hgate
    (lpOneAlg.single k 1 : l1Bordered ν)
  rw [chebyshevToTaylorBorderedCLM_single hgate k 1, one_smul,
    lpOneAlg.norm_single, norm_one, one_mul] at hsource
  rw [chebyshevDerivativeToTaylorColumn, ← derivShift_chebPolyTaylor,
    ← derivShift_linear_smul]
  exact (derivShift_norm_le _).trans hsource

private def chebyshevDerivativeToTaylorBorderedCLM {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    l1Bordered ν →L[ℝ] l1Omega σ :=
  lpOneAlg.liftCLM (chebyshevDerivativeToTaylorColumn σ) 1 fun k => by
    rw [one_mul]
    exact chebyshevDerivativeToTaylorColumn_le hgate k

private theorem derivShift_comp_chebyshevToTaylorBorderedCLM
    {σ ν : PosReal} (hgate : (σ : ℝ) ≤ semiMinor ν) :
    derivShift_CLM.comp (chebyshevToTaylorBorderedCLM hgate) =
      chebyshevDerivativeToTaylorBorderedCLM hgate := by
  apply lpOneAlg.continuousLinearMap_ext
  intro k
  rw [ContinuousLinearMap.comp_apply,
    chebyshevToTaylorBorderedCLM_single hgate k 1, one_smul, derivShift_CLM_apply,
    chebyshevDerivativeToTaylorBorderedCLM, lpOneAlg.liftCLM_single, one_smul,
    chebyshevDerivativeToTaylorColumn, derivShift_linear_smul,
    derivShift_chebPolyTaylor]

/-- The physical Chebyshev derivative realized in the omega-weighted Taylor
range.  Its columns carry the physical storage factors `1, 2, 2, ...` and the
polynomial identity `Tₖ' = k Uₖ₋₁`. -/
def chebyshevDerivativeToTaylorCLM {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    l1Chebyshev.symmetricSubalgebra ν →L[ℝ] l1Omega σ :=
  (chebyshevDerivativeToTaylorBorderedCLM hgate).comp
    ((l1Chebyshev.nonnegRestrictCLM ν).comp
      (l1Chebyshev.symmetricSubalgebra ν).toSubmodule.subtypeL)

theorem norm_chebyshevDerivativeToTaylorCLM_apply_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν)
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    ‖chebyshevDerivativeToTaylorCLM hgate a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_liftCLM_apply_le
    (chebyshevDerivativeToTaylorColumn σ) 1
    (fun k => by rw [one_mul]; exact chebyshevDerivativeToTaylorColumn_le hgate k)
    (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))
  rw [one_mul] at h
  exact h.trans_eq (l1Chebyshev.nonnegRestrictCLM_norm_of_isSymmetric _ a.2)

theorem norm_chebyshevDerivativeToTaylorCLM_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    ‖chebyshevDerivativeToTaylorCLM hgate‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul] using norm_chebyshevDerivativeToTaylorCLM_apply_le hgate a

/-- Differentiation commutes with restriction from the physical Chebyshev
algebra to its Taylor realization. -/
theorem derivShift_CLM_comp_chebyshevToTaylorCLM {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    derivShift_CLM.comp (chebyshevToTaylorCLM hgate) =
      chebyshevDerivativeToTaylorCLM hgate := by
  change derivShift_CLM.comp
      ((chebyshevToTaylorBorderedCLM hgate).comp
        ((l1Chebyshev.nonnegRestrictCLM ν).comp
          (l1Chebyshev.symmetricSubalgebra ν).toSubmodule.subtypeL)) = _
  rw [← ContinuousLinearMap.comp_assoc,
    derivShift_comp_chebyshevToTaylorBorderedCLM]
  rfl

private theorem uPolyOmegaSynthesis_comp_chebyshevDerivativeToUBorderedCLM
    {σ ν : PosReal}
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ))
    (hreverse : (σ : ℝ) ≤ semiMinor ν) :
    (uPolyOmegaSynthesisCLM hgate).comp
        (chebyshevDerivativeToUBorderedCLM ν) =
      chebyshevDerivativeToTaylorBorderedCLM hreverse := by
  apply lpOneAlg.continuousLinearMap_ext
  intro k
  rw [ContinuousLinearMap.comp_apply, chebyshevDerivativeToUBorderedCLM,
    lpOneAlg.liftCLM_single, one_smul, chebyshevDerivativeToUColumn,
    map_smul, map_smul, chebyshevDerivativeToTaylorBorderedCLM,
    lpOneAlg.liftCLM_single, one_smul, chebyshevDerivativeToTaylorColumn]
  cases k with
  | zero => simp
  | succ k =>
      rw [uPolyOmegaSynthesisCLM_omegaSingle]
      simp

/-- **The genuine derivative naturality square.** Intrinsic Chebyshev
differentiation followed by `U`-polynomial synthesis agrees with first
restricting the physical series to Taylor coefficients and then applying the
Taylor derivative shift. -/
theorem uPolyOmegaSynthesisCLM_comp_chebyshevDerivativeToUCLM
    {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ)) :
    (uPolyOmegaSynthesisCLM hgate).comp (chebyshevDerivativeToUCLM ν) =
      derivShift_CLM.comp
        (chebyshevToTaylorCLM
          (bernsteinParameter_le_iff_le_semiMinor.mp hgate)) := by
  let hreverse : (σ : ℝ) ≤ semiMinor ν :=
    bernsteinParameter_le_iff_le_semiMinor.mp hgate
  calc
    (uPolyOmegaSynthesisCLM hgate).comp (chebyshevDerivativeToUCLM ν) =
        chebyshevDerivativeToTaylorCLM hreverse := by
      change (uPolyOmegaSynthesisCLM hgate).comp
          ((chebyshevDerivativeToUBorderedCLM ν).comp
            ((l1Chebyshev.nonnegRestrictCLM ν).comp
              (l1Chebyshev.symmetricSubalgebra ν).toSubmodule.subtypeL)) = _
      rw [← ContinuousLinearMap.comp_assoc,
        uPolyOmegaSynthesis_comp_chebyshevDerivativeToUBorderedCLM hgate hreverse]
      rfl
    _ = derivShift_CLM.comp (chebyshevToTaylorCLM hreverse) :=
      (derivShift_CLM_comp_chebyshevToTaylorCLM hreverse).symm

end CrossGeometry

end RadiiPolynomial

end
