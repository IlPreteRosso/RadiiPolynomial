import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Analytic extensionality for physical Chebyshev series

At an exponential weight `ν > 1`, a physical Chebyshev series is determined by
its values in any neighbourhood of the midpoint.  The proof passes through the
holomorphic exponential extension of the bilateral series on a horizontal
strip, applies the identity principle, and then recovers the bilateral
coefficients as Fourier coefficients on the real boundary.
-/

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory AddCircle Set

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

open lpOneAlg

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-! ### Fourier recovery on the real boundary -/

private theorem summable_coeff (f : l1Chebyshev ν) :
    Summable fun k : ℤ => ‖((lpOneAlg.toRealSeq f k : ℝ) : ℂ)‖ := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using lpOneAlg.summable_abs_toRealSeq f

/-- The boundary function on `ℝ/ℤ`, in the normalization used by Mathlib's
Fourier basis. -/
private def boundary (f : l1Chebyshev ν) : AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑' k : ℤ, ((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x

private theorem fourierCoeff_boundary (f : l1Chebyshev ν) (n : ℤ) :
    fourierCoeff (boundary f) n = ((lpOneAlg.toRealSeq f n : ℝ) : ℂ) := by
  simp only [fourierCoeff, boundary, smul_eq_mul]
  have hpull : ∀ x : AddCircle (1 : ℝ),
      fourier (-n) x * ∑' k : ℤ, ((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x =
        ∑' k : ℤ, fourier (-n) x *
          (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x) :=
    fun x => (tsum_mul_left).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hpull)]
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable
      (fun x : AddCircle (1 : ℝ) => fourier (-n) x *
        (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)) haarAddCircle :=
    fun k => ((map_continuous (fourier (-n))).mul
      (continuous_const.mul (map_continuous (fourier k)))).aestronglyMeasurable
  have hptnorm : ∀ (k : ℤ) (x : AddCircle (1 : ℝ)),
      ‖fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)‖ =
        ‖((lpOneAlg.toRealSeq f k : ℝ) : ℂ)‖ := by
    intro k x
    rw [norm_mul, norm_mul]
    have hneg : ‖fourier (-n) x‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    have hk : ‖fourier k x‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [hneg, hk, one_mul, mul_one]
  have hlint : ∑' k : ℤ, ∫⁻ x : AddCircle (1 : ℝ),
      ‖fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)‖ₑ
        ∂haarAddCircle ≠ ∞ := by
    have hbound : ∀ k : ℤ, ∫⁻ x : AddCircle (1 : ℝ),
        ‖fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)‖ₑ
          ∂haarAddCircle = ‖((lpOneAlg.toRealSeq f k : ℝ) : ℂ)‖ₑ := by
      intro k
      have hfun : (fun x : AddCircle (1 : ℝ) =>
          ‖fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)‖ₑ) =
          fun _ => ‖((lpOneAlg.toRealSeq f k : ℝ) : ℂ)‖ₑ := by
        funext x
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
        exact congrArg ((↑·) : ℝ≥0 → ℝ≥0∞) (NNReal.coe_injective (by
          rw [coe_nnnorm, coe_nnnorm]
          exact hptnorm k x))
      rw [hfun, lintegral_const, measure_univ, mul_one]
    rw [tsum_congr hbound]
    have hsum : Summable fun k : ℤ => ‖((lpOneAlg.toRealSeq f k : ℝ) : ℂ)‖₊ := by
      rw [← NNReal.summable_coe]
      simpa [coe_nnnorm] using summable_coeff f
    simp only [enorm_eq_nnnorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum
  rw [integral_tsum hmeas hlint]
  have horth : ∀ m : ℤ, ∫ x : AddCircle (1 : ℝ), fourier m x ∂haarAddCircle =
      if (0 : ℤ) = m then 1 else 0 := by
    intro m
    have h0 := congr_fun (fourierCoeff_fourier (T := 1) m) 0
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h0
    rw [h0, Pi.single_apply]
  have hterm : ∀ k : ℤ, ∫ x : AddCircle (1 : ℝ),
      fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x)
        ∂haarAddCircle =
      ((lpOneAlg.toRealSeq f k : ℝ) : ℂ) *
        (if (0 : ℤ) = -n + k then 1 else 0) := by
    intro k
    have hre : ∀ x : AddCircle (1 : ℝ),
        fourier (-n) x * (((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier k x) =
          ((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * fourier (-n + k) x := by
      intro x
      rw [fourier_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hre), integral_const_mul, horth]
  rw [tsum_congr hterm]
  rw [tsum_eq_single n (fun k hk => by rw [if_neg (by omega), mul_zero])]
  rw [if_pos (by omega), mul_one]

private theorem eq_zero_of_boundary_eq_zero (f : l1Chebyshev ν)
    (h : ∀ x, boundary f x = 0) : f = 0 := by
  have hb : boundary f = fun _ => (0 : ℂ) := funext h
  apply lpOneAlg.ext_toRealSeq
  funext n
  have hn := fourierCoeff_boundary f n
  rw [hb] at hn
  simp only [fourierCoeff, smul_zero, integral_zero] at hn
  rw [lpOneAlg.toRealSeq_zero]
  exact Complex.ofReal_injective (by simpa using hn.symm)

/-! ### Holomorphic extension on a horizontal strip -/

private def stripRadius (ν : PosReal) : ℝ := (1 + (ν : ℝ)) / 2

private def strip (ν : PosReal) : Set ℂ :=
  Complex.im ⁻¹' Set.Ioo (-Real.log (stripRadius ν)) (Real.log (stripRadius ν))

private def exponentialTerm (f : l1Chebyshev ν) (k : ℤ) (z : ℂ) : ℂ :=
  ((lpOneAlg.toRealSeq f k : ℝ) : ℂ) * Complex.exp ((k : ℂ) * (Complex.I * z))

private def exponentialExtension (f : l1Chebyshev ν) (z : ℂ) : ℂ :=
  ∑' k : ℤ, exponentialTerm f k z

private theorem stripRadius_pos (ν : PosReal) : 0 < stripRadius ν := by
  unfold stripRadius
  exact div_pos (add_pos one_pos ν.coe_pos) (by norm_num)

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem one_lt_stripRadius (hν : 1 < (ν : ℝ)) : 1 < stripRadius ν := by
  unfold stripRadius
  linarith

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem stripRadius_lt (hν : 1 < (ν : ℝ)) : stripRadius ν < (ν : ℝ) := by
  unfold stripRadius
  linarith

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem summable_strip_majorant (f : l1Chebyshev ν) (hν : 1 < (ν : ℝ)) :
    Summable fun k : ℤ => |lpOneAlg.toRealSeq f k| * stripRadius ν ^ k.natAbs := by
  refine (lpOneAlg.summable_norm f).of_nonneg_of_le
    (fun _ => mul_nonneg (abs_nonneg _) (pow_nonneg (stripRadius_pos ν).le _))
    (fun k => ?_)
  rw [l1Chebyshev.norm_fiber]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (stripRadius_pos ν).le (stripRadius_lt hν).le k.natAbs) (abs_nonneg _)

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem norm_exponentialTerm_le (f : l1Chebyshev ν)
    (k : ℤ) {z : ℂ} (hz : z ∈ strip ν) :
    ‖exponentialTerm f k z‖ ≤
      |lpOneAlg.toRealSeq f k| * stripRadius ν ^ k.natAbs := by
  have hρ : 0 < stripRadius ν := stripRadius_pos ν
  have hexp (n : ℕ) :
      Real.exp ((n : ℝ) * Real.log (stripRadius ν)) = stripRadius ν ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log hρ]
  rcases hz with ⟨hzlow, hzhigh⟩
  rw [exponentialTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  cases k with
  | ofNat n =>
    have hre : (((n : ℤ) : ℂ) * (Complex.I * z)).re = -(n : ℝ) * z.im := by
      simp
    change Real.exp ((((n : ℤ) : ℂ) * (Complex.I * z)).re) ≤ stripRadius ν ^ n
    rw [hre, ← hexp n, Real.exp_le_exp]
    have him : -z.im ≤ Real.log (stripRadius ν) := by linarith
    calc
      -(n : ℝ) * z.im = (n : ℝ) * (-z.im) := by ring
      _ ≤ (n : ℝ) * Real.log (stripRadius ν) :=
        mul_le_mul_of_nonneg_left him (Nat.cast_nonneg n)
  | negSucc n =>
    have hre : (((Int.negSucc n : ℤ) : ℂ) * (Complex.I * z)).re =
        (n + 1 : ℝ) * z.im := by
      rw [Int.negSucc_eq]
      simp
      ring
    change Real.exp ((((Int.negSucc n : ℤ) : ℂ) * (Complex.I * z)).re) ≤
      stripRadius ν ^ (n + 1)
    rw [hre, ← hexp (n + 1), Real.exp_le_exp]
    push_cast
    exact mul_le_mul_of_nonneg_left hzhigh.le (show 0 ≤ (n : ℝ) + 1 by positivity)

private theorem isOpen_strip (ν : PosReal) : IsOpen (strip ν) := by
  exact isOpen_Ioo.preimage Complex.continuous_im

private theorem isPreconnected_strip (ν : PosReal) : IsPreconnected (strip ν) := by
  have hconv : Convex ℝ (strip ν) := by
    simpa [strip, Complex.imLm_coe] using
      (convex_Ioo (-Real.log (stripRadius ν)) (Real.log (stripRadius ν))).linear_preimage
        Complex.imLm
  exact hconv.isPreconnected

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem summableLocallyUniformlyOn_exponentialTerm
    (f : l1Chebyshev ν) (hν : 1 < (ν : ℝ)) :
    SummableLocallyUniformlyOn (exponentialTerm f) (strip ν) := by
  apply SummableLocallyUniformlyOn_of_locally_bounded (isOpen_strip ν)
  intro K hK _
  exact ⟨fun k : ℤ => |lpOneAlg.toRealSeq f k| * stripRadius ν ^ k.natAbs,
    summable_strip_majorant f hν, fun k z hz => norm_exponentialTerm_le f k (hK hz)⟩

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem analyticOnNhd_exponentialExtension
    (f : l1Chebyshev ν) (hν : 1 < (ν : ℝ)) :
    AnalyticOnNhd ℂ (exponentialExtension f) (strip ν) := by
  apply DifferentiableOn.analyticOnNhd
  · exact (summableLocallyUniformlyOn_exponentialTerm f hν).differentiableOn
      (isOpen_strip ν) fun k z _ => by
        unfold exponentialTerm
        fun_prop
  · exact isOpen_strip ν

private theorem exponentialExtension_ofReal (f : l1Chebyshev ν) (θ : ℝ) :
    exponentialExtension f (θ : ℂ) =
      l1Chebyshev.evalLaurentC ν (Complex.exp (θ * Complex.I))
        (l1Chebyshev.evalLaurentC_circle ν θ) f := by
  rw [exponentialExtension, l1Chebyshev.evalLaurentC_apply]
  exact tsum_congr fun k => by
    unfold exponentialTerm
    congr 1
    rw [← Complex.exp_int_mul]
    congr 1
    ring

private theorem exponentialExtension_real_eq_eval (f : l1Chebyshev ν)
    (hf : f.IsSymmetric) (θ : ℝ) :
    exponentialExtension f (θ : ℂ) = ((l1Chebyshev.eval f (Real.cos θ) : ℝ) : ℂ) := by
  rw [exponentialExtension_ofReal]
  exact l1Chebyshev.evalLaurentC_circle_eq_eval ν f hf θ

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem boundary_coe_eq_exponentialExtension (f : l1Chebyshev ν) (x : ℝ) :
    boundary f (x : AddCircle (1 : ℝ)) = exponentialExtension f (2 * Real.pi * x : ℂ) := by
  rw [boundary, exponentialExtension]
  exact tsum_congr fun k => by
    unfold exponentialTerm
    rw [fourier_coe_apply]
    congr 1
    congr 1
    push_cast
    ring

/-- Unit-circle Laurent characters separate the full bilateral Chebyshev
carrier.  This is the operational semisimplicity statement before imposing
the physical symmetry condition. -/
theorem ext_of_evalLaurentC_circle {a b : l1Chebyshev ν}
    (h : ∀ θ : ℝ,
      l1Chebyshev.evalLaurentC ν (Complex.exp (θ * Complex.I))
          (l1Chebyshev.evalLaurentC_circle ν θ) a =
        l1Chebyshev.evalLaurentC ν (Complex.exp (θ * Complex.I))
          (l1Chebyshev.evalLaurentC_circle ν θ) b) :
    a = b := by
  apply sub_eq_zero.mp
  apply eq_zero_of_boundary_eq_zero (a - b)
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rw [boundary_coe_eq_exponentialExtension]
      have harg : 2 * (Real.pi : ℂ) * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [harg, exponentialExtension_ofReal,
        map_sub, h, sub_self]

private theorem eq_zero_of_eventuallyEq_eval (f : l1Chebyshev ν)
    (hf : f.IsSymmetric) (hν : 1 < (ν : ℝ))
    (hzero : l1Chebyshev.eval f =ᶠ[nhds 0] 0) : f = 0 := by
  let θ0 : ℝ := Real.pi / 2
  let θ : ℕ → ℝ := fun n => θ0 + 1 / (n + 1 : ℝ)
  let z0 : ℂ := (θ0 : ℂ)
  let z : ℕ → ℂ := fun n => (θ n : ℂ)
  have hθ : Tendsto θ atTop (nhds θ0) := by
    dsimp only [θ]
    have hc : Tendsto (fun _ : ℕ => θ0) atTop (nhds θ0) := tendsto_const_nhds
    have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using hc.add hi
  have hz : Tendsto z atTop (nhds z0) := by
    exact (Complex.continuous_ofReal.tendsto θ0).comp hθ
  have hzne : ∀ n, z n ≠ z0 := by
    intro n hn
    have hn' := Complex.ofReal_injective hn
    dsimp only [z, z0, θ] at hn'
    have hpos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    linarith
  have hzpunct : Tendsto z atTop (𝓝[≠] z0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z hz
      (Filter.Eventually.of_forall fun n => hzne n)
  have hcos : Tendsto (fun n => Real.cos (θ n)) atTop (nhds 0) := by
    have hc := (Real.continuous_cos.tendsto θ0).comp hθ
    change Tendsto (Real.cos ∘ θ) atTop (nhds 0)
    simpa only [θ0, Real.cos_pi_div_two] using hc
  have heval : ∀ᶠ n in atTop, l1Chebyshev.eval f (Real.cos (θ n)) = 0 :=
    hcos.eventually hzero
  have hext : ∀ᶠ n in atTop, exponentialExtension f (z n) = 0 := by
    filter_upwards [heval] with n hn
    rw [show z n = ((θ n : ℝ) : ℂ) from rfl,
      exponentialExtension_real_eq_eval f hf, hn, Complex.ofReal_zero]
  have hfreq : ∃ᶠ w in 𝓝[≠] z0, exponentialExtension f w = 0 :=
    hzpunct.frequently hext.frequently
  have hheight : 0 < Real.log (stripRadius ν) :=
    Real.log_pos (one_lt_stripRadius hν)
  have hz0 : z0 ∈ strip ν := by
    change -Real.log (stripRadius ν) < (z0 : ℂ).im ∧
      (z0 : ℂ).im < Real.log (stripRadius ν)
    change -Real.log (stripRadius ν) < 0 ∧ 0 < Real.log (stripRadius ν)
    exact ⟨neg_lt_zero.mpr hheight, hheight⟩
  have hstrip : Set.EqOn (exponentialExtension f) 0 (strip ν) :=
    (analyticOnNhd_exponentialExtension f hν).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_strip ν) hz0 hfreq
  apply eq_zero_of_boundary_eq_zero f
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rw [boundary_coe_eq_exponentialExtension]
      apply hstrip
      change -Real.log (stripRadius ν) < (2 * (Real.pi : ℂ) * (x : ℂ)).im ∧
        (2 * (Real.pi : ℂ) * (x : ℂ)).im < Real.log (stripRadius ν)
      have him : (2 * (Real.pi : ℂ) * (x : ℂ)).im = 0 := by simp
      rw [him]
      exact ⟨neg_lt_zero.mpr hheight, hheight⟩

/-- At an exponential weight `ν > 1`, physical Chebyshev elements are
determined by their real evaluations in any neighbourhood of the midpoint. -/
theorem ext_of_eventuallyEq_eval (hν : 1 < (ν : ℝ))
    {a b : l1Chebyshev.symmetricSubalgebra ν}
    (h : (fun t => l1Chebyshev.eval (a : l1Chebyshev ν) t) =ᶠ[nhds 0]
      fun t => l1Chebyshev.eval (b : l1Chebyshev ν) t) : a = b := by
  apply Subtype.ext
  let f : l1Chebyshev ν := (a : l1Chebyshev ν) - (b : l1Chebyshev ν)
  have hf : f.IsSymmetric := a.2.sub b.2
  have hzero : l1Chebyshev.eval f =ᶠ[nhds 0] 0 := by
    filter_upwards [h, Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht htball
    have ht1 : |t| ≤ 1 := by
      exact (by simpa [Real.dist_eq] using (Metric.mem_ball.mp htball).le)
    rw [show l1Chebyshev.eval f t =
        l1Chebyshev.eval (a : l1Chebyshev ν) t -
          l1Chebyshev.eval (b : l1Chebyshev ν) t by
      exact l1Chebyshev.eval_sub _ _ ht1,
      ht, sub_self]
    rfl
  exact sub_eq_zero.mp (eq_zero_of_eventuallyEq_eval f hf hν hzero)

end l1Chebyshev

end RadiiPolynomial

end
