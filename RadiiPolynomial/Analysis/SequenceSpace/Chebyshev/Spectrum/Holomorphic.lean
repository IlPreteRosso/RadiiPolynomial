import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Series
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy on the open Bernstein ellipse, and analyticity at the endpoints

Analytic layer, and the consumer-visible end of the spectrum branch. `complexEval`
is the complex Chebyshev realization in the production normalization
`a₀ + 2 Σ aₙ Tₙ`; it agrees with production `l1Chebyshev.eval` on all of `ℝ`
(`complexEval_ofReal`, no interior truncation), it is the classified character on the
physical carrier, and Weierstrass on the uniformly convergent series makes it
holomorphic on the whole open ellipse (`analyticOnNhd_complexEval`) with no loss of
coefficient radius. Scalar restriction then gives real analyticity of the *production*
evaluator on a neighbourhood of the closed interval, endpoints included, whenever
`1 < ν` (`analyticOnNhd_eval_Icc`, `analyticAt_eval_endpoints`).

Closes the Chebyshev analyticity gap: the production predicate asserted continuity and
a one-sided derivative only.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry Polynomial

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- The complex Chebyshev realization in the production normalization.
Like production real evaluation, it reads the nonnegative modes only. -/
def complexEval (a : l1Chebyshev ν) (w : ℂ) : ℂ :=
  (l1Chebyshev.toSeq a 0 : ℂ) + 2 * ∑' n : ℕ,
    (l1Chebyshev.toSeq a ((n + 1 : ℕ) : ℤ) : ℂ) * (Chebyshev.T ℂ (n + 1)).eval w

/-- The open filled Bernstein ellipse, empty at the degenerate weight one. -/
def openEllipse : Set ℂ :=
  {w | ‖w - 1‖ + ‖w + 1‖ < (ν : ℝ) + (ν : ℝ)⁻¹}

omit [Fact (1 ≤ (ν : ℝ))] in
theorem isOpen_openEllipse : IsOpen (openEllipse ν) :=
  isOpen_lt ((continuous_id.sub continuous_const).norm.add
    (continuous_id.add continuous_const).norm) continuous_const

private theorem chebyshev_eval_ofReal (n : ℤ) (t : ℝ) :
    (Chebyshev.T ℂ n).eval (t : ℂ) = (((Chebyshev.T ℝ n).eval t : ℝ) : ℂ) := by
  simpa only [Chebyshev.map_T, Complex.ofRealHom_eq_coe] using
    (Polynomial.eval_map_apply (p := Chebyshev.T ℝ n) (f := Complex.ofRealHom) t)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- Agreement with the existing real evaluator is global; consequently it
also holds in full real neighborhoods of the endpoints `±1`. -/
theorem complexEval_ofReal (a : l1Chebyshev ν) (t : ℝ) :
    complexEval ν a (t : ℂ) = (l1Chebyshev.eval a t : ℂ) := by
  simp only [complexEval, l1Chebyshev.eval, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_tsum, chebyshev_eval_ofReal, Nat.cast_add, Nat.cast_one]

/-- On the physical carrier the holomorphic realization is exactly the
previously classified character; the bilateral series pairs into production's
`a₀ + 2 Σ aₙ Tₙ` normalization. -/
theorem complexEval_eq_ellipseCharacter (a : Physical ν) (w : Ellipse ν) :
    complexEval ν a.val w.val = ellipseCharacter ν w a := by
  let f : ℤ → ℂ := fun k => (toRealSeq a.val k : ℂ) *
    (Chebyshev.T ℂ k.natAbs).eval w.val
  have hs : Summable f := (summable_character_series ν w a).of_norm
  have hp : Summable (fun n : ℕ => f (n : ℤ)) :=
    hs.comp_injective (fun n m h => by omega)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hs.comp_injective (fun n m h => by omega)
  have hpair : ∀ n : ℕ, f (-((n : ℤ) + 1)) = f ((n + 1 : ℕ) : ℤ) := by
    intro n
    dsimp only [f]
    rw [a.property, Int.natAbs_neg]
    congr 2
  have hzero : f ((0 : ℕ) : ℤ) = (l1Chebyshev.toSeq a.val 0 : ℂ) := by
    simp [f, Chebyshev.T_zero, l1Chebyshev.toSeq]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      (l1Chebyshev.toSeq a.val ((n + 1 : ℕ) : ℤ) : ℂ) *
        (Chebyshev.T ℂ (n + 1)).eval w.val := by
    intro n
    dsimp only [f]
    rw [Int.natAbs_natCast]
    simp only [l1Chebyshev.toSeq, Nat.cast_add, Nat.cast_one]
  symm
  rw [character_apply_eq_tsum]
  change (∑' k : ℤ, f k) = complexEval ν a.val w.val
  rw [tsum_of_nat_of_neg_add_one hp hn, hp.tsum_eq_zero_add,
    hzero, tsum_congr hpair, tsum_congr hpos]
  unfold complexEval
  ring

/-- The weighted coefficient norm uniformly dominates every polynomial
term throughout the closed ellipse. -/
theorem complexEval_term_bound (a : l1Chebyshev ν) (n : ℕ) (w : Ellipse ν) :
    ‖(l1Chebyshev.toSeq a ((n + 1 : ℕ) : ℤ) : ℂ) *
      (Chebyshev.T ℂ (n + 1)).eval w.val‖ ≤ ‖a ((n + 1 : ℕ) : ℤ)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, l1Chebyshev.norm_fiber,
    Int.natAbs_natCast]
  exact mul_le_mul_of_nonneg_left (norm_chebyshev_le ν w (n + 1)) (abs_nonneg _)

/-- Complex analyticity on the whole open ellipse. Uniform convergence on
the closed ellipse already supplies the locally uniform limit required by
Weierstrass; no strict loss of the coefficient radius is necessary. -/
theorem analyticOnNhd_complexEval (a : l1Chebyshev ν) :
    AnalyticOnNhd ℂ (complexEval ν a) (openEllipse ν) := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_openEllipse ν)).mpr
  unfold complexEval
  apply (differentiableOn_const _).add
  apply DifferentiableOn.const_mul
  have hs : Summable (fun n : ℕ => ‖a ((n + 1 : ℕ) : ℤ)‖) :=
    (lpOneAlg.summable_norm a).comp_injective (fun n m h => by omega)
  apply Complex.differentiableOn_tsum_of_summable_norm hs
  · intro n
    exact ((Chebyshev.T ℂ (n + 1)).differentiable.const_mul _).differentiableOn
  · exact isOpen_openEllipse ν
  · intro n w hw
    exact complexEval_term_bound ν a n ⟨w, hw.le⟩

/-- The power-series theorem is for the production real function itself,
through scalar restriction of the complex analytic extension. -/
theorem analyticAt_eval_of_mem_openEllipse (a : l1Chebyshev ν) (t : ℝ)
    (ht : (t : ℂ) ∈ openEllipse ν) : AnalyticAt ℝ (l1Chebyshev.eval a) t := by
  have hcomplex := analyticOnNhd_complexEval ν a (t : ℂ) ht
  have hreal : AnalyticAt ℝ (complexEval ν a) (t : ℂ) := hcomplex.restrictScalars
  have hcomp := hreal.comp (Complex.ofRealCLM.analyticAt t)
  have hre : AnalyticAt ℝ (fun s : ℝ => (complexEval ν a (s : ℂ)).re) t :=
    (Complex.reCLM.analyticAt _).comp hcomp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    complexEval_ofReal, Complex.ofReal_re] using hre

omit [Fact (1 ≤ (ν : ℝ))] in
/-- A weight strictly above one places the full reference interval,
including both endpoints, strictly inside the complex ellipse. -/
theorem real_mem_openEllipse (hν : 1 < (ν : ℝ)) (t : ℝ) (ht : |t| ≤ 1) :
    (t : ℂ) ∈ openEllipse ν := by
  have hνi := mul_inv_cancel₀ ν.coe_ne_zero
  have hsq : 0 < ((ν : ℝ) - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hν)
  have hsum : 2 < (ν : ℝ) + (ν : ℝ)⁻¹ := by
    nlinarith [ν.coe_pos]
  obtain ⟨htlo, hthi⟩ := abs_le.mp ht
  change ‖(t : ℂ) - 1‖ + ‖(t : ℂ) + 1‖ < _
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : t - 1 ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ t + 1)]
  linarith

/-- Actual production Chebyshev evaluation is real analytic on a neighborhood
of every point of `[-1,1]`, not merely on its relative interior. -/
theorem analyticOnNhd_eval_Icc (hν : 1 < (ν : ℝ)) (a : l1Chebyshev ν) :
    AnalyticOnNhd ℝ (l1Chebyshev.eval a) (Set.Icc (-1) 1) := by
  intro t ht
  exact analyticAt_eval_of_mem_openEllipse ν a t
    (real_mem_openEllipse ν hν t (abs_le.mpr ht))

/-- The two endpoint analyticity statements are included explicitly. -/
theorem analyticAt_eval_endpoints (hν : 1 < (ν : ℝ)) (a : l1Chebyshev ν) :
    AnalyticAt ℝ (l1Chebyshev.eval a) (-1) ∧ AnalyticAt ℝ (l1Chebyshev.eval a) 1 := by
  constructor <;> apply analyticOnNhd_eval_Icc ν hν a <;> constructor <;> norm_num

end RadiiPolynomial.PhysicalSpectrum
