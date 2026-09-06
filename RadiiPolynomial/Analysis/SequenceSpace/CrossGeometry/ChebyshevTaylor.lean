import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.RadiusRestriction
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.AnalyticExt
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Restricting physical Chebyshev series to a Taylor disc

When the Taylor disc of radius `σ` lies in the Bernstein ellipse of parameter
`ν`, the Taylor coefficients of the Chebyshev polynomials define a contraction
from the physical, flip-fixed Chebyshev algebra into `l1Weighted σ`.  Real
evaluation commutes with this map near the expansion centre.  Taylor analytic
extensionality then supplies its unital and multiplicative laws, so the
contraction upgrades to a continuous algebra homomorphism.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace RadiiPolynomial

namespace CrossGeometry

open lpOneAlg Polynomial

/-! ### Chebyshev polynomial columns -/

private lemma T_cast_add_two (k : ℕ) :
    Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)
      = Polynomial.X * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ) +
          Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)) - Chebyshev.T ℝ (k : ℤ) := by
  push_cast
  rw [Chebyshev.T_add_two]
  ring

/-- The Taylor realization of `Tₖ`, defined intrinsically by polynomial
evaluation at the Taylor generator. -/
def chebPolyTaylor (σ : PosReal) (k : ℕ) : l1Weighted σ :=
  Polynomial.aeval (l1Weighted.single 1 1) (Chebyshev.T ℝ (k : ℤ))

private theorem toSeq_aeval_generator (σ : PosReal) (p : ℝ[X]) (n : ℕ) :
    l1Weighted.toSeq
      (Polynomial.aeval (l1Weighted.single (ν := σ) 1 1) p) n = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, l1Weighted.add_toSeq, hp, hq, Polynomial.coeff_add]
  | monomial m a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, l1Weighted.single_eq_lpOneAlg_single,
        lpOneAlg.single_pow]
      simp only [one_mul, nsmul_eq_mul, mul_one, l1Weighted.smul_toSeq,
        Polynomial.coeff_monomial]
      change a * lpOneAlg.toRealSeq
        (lpOneAlg.single (E := ScaledReal σ) m 1) n =
          if m = n then a else 0
      rw [lpOneAlg.toRealSeq_single]
      split_ifs <;> simp_all

/-- Coefficients of the Taylor realization of `Tₖ` are the ordinary
polynomial coefficients of `Tₖ`. -/
theorem chebPolyTaylor_toSeq (σ : PosReal) (k m : ℕ) :
    l1Weighted.toSeq (chebPolyTaylor σ k) m =
      (Chebyshev.T ℝ (k : ℤ)).coeff m :=
  toSeq_aeval_generator σ _ m

theorem chebPolyTaylor_norm_le (σ : PosReal) (k : ℕ) :
    ‖chebPolyTaylor σ k‖ ≤ bernsteinParameter (σ : ℝ) ^ k := by
  set ρ := bernsteinParameter (σ : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef, bernsteinParameter]
    exact add_nonneg σ.coe_nonneg (Real.sqrt_nonneg _)
  have hρsq : ρ ^ 2 = 2 * (σ : ℝ) * ρ + 1 := by
    rw [hρdef, bernsteinParameter]
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1 + (σ : ℝ) ^ 2 by positivity)
    nlinarith
  have hx : ‖(l1Weighted.single 1 1 : l1Weighted σ)‖ = (σ : ℝ) := by
    rw [l1Weighted.norm_single]
    norm_num
  induction k using Nat.twoStepInduction with
  | zero => simp [chebPolyTaylor, hρdef]
  | one =>
    rw [chebPolyTaylor, Nat.cast_one, Chebyshev.T_one, Polynomial.aeval_X, hx, pow_one]
    rw [hρdef, bernsteinParameter]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  | more k ih ih1 =>
    rw [chebPolyTaylor, T_cast_add_two, map_sub, map_mul, map_add, Polynomial.aeval_X]
    change ‖(l1Weighted.single 1 1 : l1Weighted σ) *
        (chebPolyTaylor σ (k + 1) + chebPolyTaylor σ (k + 1)) -
          chebPolyTaylor σ k‖ ≤ ρ ^ (k + 2)
    have hadd :
        ‖chebPolyTaylor σ (k + 1) + chebPolyTaylor σ (k + 1)‖ ≤ 2 * ρ ^ (k + 1) := by
      calc
        _ ≤ ‖chebPolyTaylor σ (k + 1)‖ + ‖chebPolyTaylor σ (k + 1)‖ := norm_add_le _ _
        _ ≤ 2 * ρ ^ (k + 1) := by linarith
    have hmul : ‖(l1Weighted.single 1 1 : l1Weighted σ) *
        (chebPolyTaylor σ (k + 1) + chebPolyTaylor σ (k + 1))‖
        ≤ (σ : ℝ) * (2 * ρ ^ (k + 1)) := by
      refine (norm_mul_le _ _).trans ?_
      rw [hx]
      exact mul_le_mul_of_nonneg_left hadd σ.coe_nonneg
    have hpow : ρ ^ (k + 2) = 2 * (σ : ℝ) * ρ ^ (k + 1) + ρ ^ k := by
      rw [pow_add, hρsq, pow_succ]
      ring
    exact (norm_sub_le _ _).trans <| by nlinarith [hmul, ih]

private lemma chebPolyTaylor_zero (σ : PosReal) :
    chebPolyTaylor σ 0 = l1Weighted.single 0 1 := by
  rw [chebPolyTaylor, Nat.cast_zero, Chebyshev.T_zero, map_one,
    l1Weighted.single_eq_lpOneAlg_single, ← lpOneAlg.one_eq_single_zero]

/-- The `T₁ = X` column is the Taylor generator. -/
@[simp] theorem chebPolyTaylor_one (σ : PosReal) :
    chebPolyTaylor σ 1 = l1Weighted.single 1 1 := by
  rw [chebPolyTaylor, Nat.cast_one, Chebyshev.T_one, Polynomial.aeval_X]

private lemma eval_chebPolyTaylor (σ : PosReal) (k : ℕ) (t : ℝ)
    (ht : |t| ≤ (σ : ℝ)) :
    l1Weighted.evalContinuousAlgHom t ht (chebPolyTaylor σ k) =
      (Chebyshev.T ℝ (k : ℤ)).eval t := by
  rw [chebPolyTaylor]
  calc
    l1Weighted.evalContinuousAlgHom t ht
        (Polynomial.aeval (l1Weighted.single 1 1) (Chebyshev.T ℝ (k : ℤ))) =
        Polynomial.aeval
          (l1Weighted.evalContinuousAlgHom t ht (l1Weighted.single 1 1))
          ((Chebyshev.T ℝ (k : ℤ)).map (RingHom.id ℝ)) := by
      exact Polynomial.map_aeval_eq_aeval_map
        (by ext x; simp) (Chebyshev.T ℝ (k : ℤ)) (l1Weighted.single 1 1)
    _ = (Chebyshev.T ℝ (k : ℤ)).eval t := by
      simp [l1Weighted.evalContinuousAlgHom_apply, l1Weighted.eval_single,
        Chebyshev.aeval_T]

/-! ### The contraction -/

/-- Storage multiplicity of the physical Chebyshev mode: one at mode zero
and two at every positive mode. -/
def chebyshevStorageFactor (k : ℕ) : ℝ := if k = 0 then 1 else 2

/-- Physical Chebyshev storage multiplicities are nonnegative. -/
theorem chebyshevStorageFactor_nonneg (k : ℕ) : 0 ≤ chebyshevStorageFactor k := by
  unfold chebyshevStorageFactor
  split_ifs <;> norm_num

private lemma chebColumn_le_borderedWeight {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν) (k : ℕ) :
    ‖chebyshevStorageFactor k • chebPolyTaylor σ k‖
      ≤ ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) k (1 : ℝ)‖ := by
  have hparam : bernsteinParameter (σ : ℝ) ≤ (ν : ℝ) :=
    bernsteinParameter_le_iff_le_semiMinor.mpr hgate
  rw [BorderedScaledReal.norm_lpAlgRingData_ofReal, abs_one, one_mul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (chebyshevStorageFactor_nonneg k)]
  cases k with
  | zero =>
    rw [chebPolyTaylor_zero, l1Weighted.norm_single, borderedWeight_zero]
    norm_num [chebyshevStorageFactor]
  | succ k =>
    rw [borderedWeight_succ]
    have hf : chebyshevStorageFactor (k + 1) = 2 := by norm_num [chebyshevStorageFactor]
    rw [hf]
    have hρ0 : 0 ≤ bernsteinParameter (σ : ℝ) := by
      unfold bernsteinParameter
      exact add_nonneg σ.coe_nonneg (Real.sqrt_nonneg _)
    have hcol := (chebPolyTaylor_norm_le σ (k + 1)).trans
      (pow_le_pow_left₀ hρ0 hparam (k + 1))
    nlinarith

/-- The storage-level Chebyshev-to-Taylor contraction.  Its source carries
only the bordered norm; the physical algebra map is `chebyshevToTaylorAeval`. -/
def chebyshevToTaylorBorderedCLM {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν) : l1Bordered ν →L[ℝ] l1Weighted σ :=
  lpOneAlg.liftCLM (fun k => chebyshevStorageFactor k • chebPolyTaylor σ k) 1 fun k => by
    rw [one_mul]
    exact chebColumn_le_borderedWeight hgate k

/-- The storage-level reverse map is contractive. -/
theorem chebyshevToTaylorBorderedCLM_norm_le {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν) (a : l1Bordered ν) :
    ‖chebyshevToTaylorBorderedCLM hgate a‖ ≤ ‖a‖ := by
  have h := lpOneAlg.norm_liftCLM_apply_le
    (fun k => chebyshevStorageFactor k • chebPolyTaylor σ k) 1
    (fun k => by rw [one_mul]; exact chebColumn_le_borderedWeight hgate k) a
  rwa [one_mul] at h

/-- Computation of the storage-level reverse map on a single mode. -/
@[simp]
theorem chebyshevToTaylorBorderedCLM_single {σ ν : PosReal}
    (hgate : (σ : ℝ) ≤ semiMinor ν)
    (k : ℕ) (x : ℝ) :
    chebyshevToTaylorBorderedCLM hgate (lpOneAlg.single k x) =
      x • (chebyshevStorageFactor k • chebPolyTaylor σ k) := by
  rw [chebyshevToTaylorBorderedCLM, lpOneAlg.liftCLM_single]

/-- Restriction of a physical Chebyshev series to the Taylor disc of radius
`σ`, under the geometric inclusion gate `σ ≤ semiMinor ν`. -/
def chebyshevToTaylorCLM {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    l1Chebyshev.symmetricSubalgebra ν →L[ℝ] l1Weighted σ :=
  (chebyshevToTaylorBorderedCLM hgate).comp
    ((l1Chebyshev.nonnegRestrictCLM ν).comp
      (l1Chebyshev.symmetricSubalgebra ν).toSubmodule.subtypeL)

theorem norm_chebyshevToTaylorCLM_apply_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν)
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    ‖chebyshevToTaylorCLM hgate a‖ ≤ ‖a‖ := by
  calc
    ‖chebyshevToTaylorCLM hgate a‖
        ≤ ‖l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν)‖ :=
      chebyshevToTaylorBorderedCLM_norm_le hgate _
    _ = ‖a‖ := l1Chebyshev.nonnegRestrictCLM_norm_of_isSymmetric _ a.2

theorem norm_chebyshevToTaylorCLM_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    ‖chebyshevToTaylorCLM hgate‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul] using norm_chebyshevToTaylorCLM_apply_le hgate a

/-! ### Evaluation naturality -/

private lemma borderedEvalColumn_le (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (t : ℝ) (ht : |t| ≤ 1) (k : ℕ) :
    ‖chebyshevStorageFactor k * (Chebyshev.T ℝ (k : ℤ)).eval t‖
      ≤ ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) k (1 : ℝ)‖ := by
  rw [BorderedScaledReal.norm_lpAlgRingData_ofReal, abs_one, one_mul,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (chebyshevStorageFactor_nonneg k)]
  cases k with
  | zero => simp [chebyshevStorageFactor]
  | succ k =>
    rw [borderedWeight_succ]
    have hf : chebyshevStorageFactor (k + 1) = 2 := by norm_num [chebyshevStorageFactor]
    rw [hf]
    have hT := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) ht
    have hpow : (1 : ℝ) ≤ (ν : ℝ) ^ (k + 1) := one_le_pow₀ Fact.out
    nlinarith

private def borderedEvalCLM (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (t : ℝ) (ht : |t| ≤ 1) : l1Bordered ν →L[ℝ] ℝ :=
  lpOneAlg.liftCLM
    (fun k => chebyshevStorageFactor k * (Chebyshev.T ℝ (k : ℤ)).eval t) 1 fun k => by
      rw [one_mul]
      exact borderedEvalColumn_le ν t ht k

private theorem evalCLM_comp_chebyshevToTaylorBorderedCLM
    {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) (t : ℝ)
    (htσ : |t| ≤ (σ : ℝ)) (ht1 : |t| ≤ 1) :
    (l1Weighted.eval_CLM t htσ).comp (chebyshevToTaylorBorderedCLM hgate) =
      borderedEvalCLM ν t ht1 := by
  apply lpOneAlg.continuousLinearMap_ext
  intro k
  rw [ContinuousLinearMap.comp_apply, chebyshevToTaylorBorderedCLM,
    lpOneAlg.liftCLM_single, one_smul, l1Weighted.eval_CLM_apply,
    borderedEvalCLM, lpOneAlg.liftCLM_single, one_smul, l1Weighted.eval_smul]
  rw [show l1Weighted.eval (chebPolyTaylor σ k) t =
      (Chebyshev.T ℝ (k : ℤ)).eval t by
    exact eval_chebPolyTaylor σ k t htσ]

private theorem borderedEvalCLM_nonnegRestrict
    {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (t : ℝ) (ht : |t| ≤ 1)
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    borderedEvalCLM ν t ht (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν)) =
      l1Chebyshev.symmetricEvalCharacter ν t ht a := by
  rw [borderedEvalCLM, lpOneAlg.liftCLM_apply,
    l1Chebyshev.symmetricEvalCharacter_apply, l1Chebyshev.eval]
  have hs := lpOneAlg.liftCLM_summable
    (fun k => chebyshevStorageFactor k * (Chebyshev.T ℝ (k : ℤ)).eval t)
    (fun k => by rw [one_mul]; exact borderedEvalColumn_le ν t ht k)
    (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))
  rw [hs.tsum_eq_zero_add]
  have hzero : lpOneAlg.toRealSeq
      (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν)) 0 •
        (chebyshevStorageFactor 0 * (Chebyshev.T ℝ (0 : ℤ)).eval t) =
      l1Chebyshev.toSeq (a : l1Chebyshev ν) 0 := by
    rw [l1Chebyshev.nonnegRestrictCLM_apply, nonnegRestrict_toSeq]
    simp [chebyshevStorageFactor]
    rfl
  have hzero' : lpOneAlg.toRealSeq
      (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν)) 0 •
        (chebyshevStorageFactor 0 * (Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval t) =
      l1Chebyshev.toSeq (a : l1Chebyshev ν) 0 := by
    simpa using hzero
  rw [hzero']
  congr 1
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by
    rw [l1Chebyshev.nonnegRestrictCLM_apply, nonnegRestrict_toSeq]
    simp only [Nat.succ_ne_zero, chebyshevStorageFactor, if_false, smul_eq_mul]
    have hseq : lpOneAlg.toRealSeq (a : l1Chebyshev ν) ((k + 1 : ℕ) : ℤ) =
        l1Chebyshev.toSeq (a : l1Chebyshev ν) ((k + 1 : ℕ) : ℤ) := rfl
    rw [hseq]
    ring

/-- Real evaluation commutes with restriction from the physical Chebyshev
algebra to the Taylor disc. -/
theorem eval_chebyshevToTaylorCLM {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) (t : ℝ)
    (ht1 : |t| ≤ 1) (htσ : |t| ≤ (σ : ℝ))
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    l1Weighted.evalContinuousAlgHom t htσ (chebyshevToTaylorCLM hgate a) =
      l1Chebyshev.symmetricEvalCharacter ν t ht1 a := by
  change l1Weighted.eval_CLM t htσ (chebyshevToTaylorCLM hgate a) = _
  change l1Weighted.eval_CLM t htσ
      (chebyshevToTaylorBorderedCLM hgate
        (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))) = _
  have hcomp := DFunLike.congr_fun
    (evalCLM_comp_chebyshevToTaylorBorderedCLM hgate t htσ ht1)
    (l1Chebyshev.nonnegRestrictCLM ν (a : l1Chebyshev ν))
  rw [ContinuousLinearMap.comp_apply] at hcomp
  rw [hcomp]
  exact borderedEvalCLM_nonnegRestrict t ht1 a

/-! ### Multiplicative structure from analytic extensionality -/

private theorem eventually_abs_le_one_and_sigma (σ : PosReal) :
    ∀ᶠ t : ℝ in nhds 0, |t| ≤ 1 ∧ |t| ≤ (σ : ℝ) := by
  have hδ : 0 < min (1 : ℝ) (σ : ℝ) := lt_min one_pos σ.coe_pos
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  have habs : |t| < min (1 : ℝ) (σ : ℝ) := by
    simpa [Real.dist_eq] using Metric.mem_ball.mp ht
  exact ⟨(habs.trans_le (min_le_left _ _)).le,
    (habs.trans_le (min_le_right _ _)).le⟩

private theorem chebyshevToTaylorCLM_map_one {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    chebyshevToTaylorCLM hgate (1 : l1Chebyshev.symmetricSubalgebra ν) = 1 := by
  apply l1Weighted.ext_of_eventuallyEq_eval
  filter_upwards [eventually_abs_le_one_and_sigma σ] with t ht
  have hsquare := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2
    (1 : l1Chebyshev.symmetricSubalgebra ν)
  simpa [l1Weighted.evalContinuousAlgHom_apply, l1Weighted.eval_one,
    l1Chebyshev.eval_one] using hsquare

private theorem chebyshevToTaylorCLM_map_mul {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν)
    (a b : l1Chebyshev.symmetricSubalgebra ν) :
    chebyshevToTaylorCLM hgate (a * b) =
      chebyshevToTaylorCLM hgate a * chebyshevToTaylorCLM hgate b := by
  apply l1Weighted.ext_of_eventuallyEq_eval
  filter_upwards [eventually_abs_le_one_and_sigma σ] with t ht
  have hab := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 (a * b)
  have ha := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 a
  have hb := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 b
  rw [l1Weighted.evalContinuousAlgHom_apply] at hab ha hb
  calc
    l1Weighted.eval (chebyshevToTaylorCLM hgate (a * b)) t =
        l1Chebyshev.symmetricEvalCharacter ν t ht.1 (a * b) := hab
    _ = l1Chebyshev.symmetricEvalCharacter ν t ht.1 a *
          l1Chebyshev.symmetricEvalCharacter ν t ht.1 b :=
      map_mul (l1Chebyshev.symmetricEvalCharacter ν t ht.1) a b
    _ = l1Weighted.eval (chebyshevToTaylorCLM hgate a) t *
          l1Weighted.eval (chebyshevToTaylorCLM hgate b) t := by rw [ha, hb]
    _ = l1Weighted.eval
          (chebyshevToTaylorCLM hgate a * chebyshevToTaylorCLM hgate b) t :=
      l1Weighted.eval_mul _ _ ht.2

private def chebyshevToTaylorAlgHom {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    l1Chebyshev.symmetricSubalgebra ν →ₐ[ℝ] l1Weighted σ where
  toFun := chebyshevToTaylorCLM hgate
  map_one' := chebyshevToTaylorCLM_map_one hgate
  map_mul' := chebyshevToTaylorCLM_map_mul hgate
  map_zero' := (chebyshevToTaylorCLM hgate).map_zero
  map_add' := (chebyshevToTaylorCLM hgate).map_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul,
      chebyshevToTaylorCLM_map_one, Algebra.algebraMap_eq_smul_one]

/-- Restriction from the physical Chebyshev algebra to the Taylor disc as a
continuous algebra homomorphism.  Multiplicativity is recovered from the real
evaluation square by Taylor analytic extensionality. -/
def chebyshevToTaylorAeval {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    l1Chebyshev.symmetricSubalgebra ν →A[ℝ] l1Weighted σ where
  toAlgHom := chebyshevToTaylorAlgHom hgate
  cont := (chebyshevToTaylorCLM hgate).continuous

@[simp] theorem chebyshevToTaylorAeval_apply {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν)
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    chebyshevToTaylorAeval hgate a = chebyshevToTaylorCLM hgate a :=
  rfl

theorem norm_chebyshevToTaylorAeval_apply_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν)
    (a : l1Chebyshev.symmetricSubalgebra ν) :
    ‖chebyshevToTaylorAeval hgate a‖ ≤ ‖a‖ :=
  norm_chebyshevToTaylorCLM_apply_le hgate a

theorem norm_chebyshevToTaylorAeval_le {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    ‖(chebyshevToTaylorAeval hgate).toContinuousLinearMap‖ ≤ 1 := by
  change ‖chebyshevToTaylorCLM hgate‖ ≤ 1
  exact norm_chebyshevToTaylorCLM_le hgate

/-- The reverse homomorphism has norm exactly one: its contraction bound is
attained on the unit. -/
theorem norm_chebyshevToTaylorAeval {σ ν : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : (σ : ℝ) ≤ semiMinor ν) :
    ‖(chebyshevToTaylorAeval hgate).toContinuousLinearMap‖ = 1 := by
  apply le_antisymm (norm_chebyshevToTaylorAeval_le hgate)
  have h := (chebyshevToTaylorAeval hgate).toContinuousLinearMap.le_opNorm
    (1 : l1Chebyshev.symmetricSubalgebra ν)
  have hsource : ‖(1 : l1Chebyshev.symmetricSubalgebra ν)‖ = 1 := by
    change ‖(1 : l1Chebyshev ν)‖ = 1
    exact norm_one
  rw [ContinuousAlgHom.coe_toContinuousLinearMap, map_one, norm_one, hsource,
    mul_one] at h
  exact h

/-- **Character naturality for the reverse map.** Taylor evaluation after
restriction is the physical Chebyshev character at the same real point. -/
theorem evalContinuousAlgHom_comp_chebyshevToTaylorAeval
    {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) (t : ℝ)
    (ht1 : |t| ≤ 1) (htσ : |t| ≤ (σ : ℝ)) :
    (l1Weighted.evalContinuousAlgHom t htσ).comp (chebyshevToTaylorAeval hgate) =
      l1Chebyshev.symmetricEvalCharacter ν t ht1 := by
  ext a
  exact eval_chebyshevToTaylorCLM hgate t ht1 htσ a

/-- Restriction to the Taylor disc is injective.  The reverse gate forces
`ν > 1`; Chebyshev strip analyticity then promotes local equality near the
midpoint to equality of the physical coefficients. -/
theorem chebyshevToTaylorAeval_injective
    {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    Function.Injective (chebyshevToTaylorAeval hgate) := by
  intro a b hab
  apply l1Chebyshev.ext_of_eventuallyEq_eval
    (one_lt_of_pos_le_semiMinor hgate)
  filter_upwards [eventually_abs_le_one_and_sigma σ] with t ht
  have ha := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 a
  have hb := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 b
  simp only [l1Weighted.evalContinuousAlgHom_apply,
    l1Chebyshev.symmetricEvalCharacter_apply] at ha hb
  change chebyshevToTaylorCLM hgate a = chebyshevToTaylorCLM hgate b at hab
  rw [← ha, ← hb, hab]

/-- The reverse map sends the physical coordinate function to the Taylor
generator. -/
@[simp] theorem chebyshevToTaylorAeval_joukowskiGenSymm
    {σ ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : (σ : ℝ) ≤ semiMinor ν) :
    chebyshevToTaylorAeval hgate (joukowskiGenSymm ν) = l1Weighted.single 1 1 := by
  apply l1Weighted.ext_of_eventuallyEq_eval
  filter_upwards [eventually_abs_le_one_and_sigma σ] with t ht
  have hreverse := eval_chebyshevToTaylorCLM hgate t ht.1 ht.2 (joukowskiGenSymm ν)
  let r : PosReal := ⟨semiMajor ν, semiMajor_pos ν⟩
  have hforward := symmetricEvalCharacter_comp_joukowskiAevalSymm
    (ν := ν) (r := r) (show semiMajor ν ≤ (r : ℝ) by rfl) t ht.1
  have hgen := DFunLike.congr_fun hforward (lpOneAlg.single 1 1)
  rw [ContinuousAlgHom.comp_apply, joukowskiAevalSymm_gen,
    l1Weighted.evalContinuousAlgHom_gen] at hgen
  rw [l1Weighted.evalContinuousAlgHom_apply] at hreverse
  rw [chebyshevToTaylorAeval_apply]
  rw [hreverse, hgen, l1Weighted.eval_single]
  ring

/-- A forward Joukowski map followed by reverse restriction is exactly the
coefficient-preserving map to the smaller Taylor radius.  The two geometric
gates force that radius loss (`roundtrip_radius_lt`). -/
theorem chebyshevToTaylorAeval_comp_joukowskiAevalSymm
    {ν r σ : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hforward : semiMajor ν ≤ (r : ℝ))
    (hreverse : (σ : ℝ) ≤ semiMinor ν) :
    (chebyshevToTaylorAeval hreverse).comp (joukowskiAevalSymm hforward) =
      l1Weighted.radiusRestrict (roundtrip_radius_lt hforward hreverse).le := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, joukowskiAevalSymm_gen,
    chebyshevToTaylorAeval_joukowskiGenSymm, l1Weighted.radiusRestrict_gen]
  exact l1Weighted.single_eq_lpOneAlg_single 1 1

end CrossGeometry

end RadiiPolynomial

end
