import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Ellipse
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The character as a uniformly convergent Chebyshev series

Synthesis layer. The symmetric-mode recurrence is literally the Chebyshev recurrence
(`character_mode_eq_chebyshev`), from which contractivity of characters yields
Bernstein's bound `‖Tₙ(w)‖ ≤ νⁿ` on the *closed* ellipse (`norm_chebyshev_le`),
boundary and `ν = 1` included. The production weighted-ℓ¹ universal lift
`lpOneAlg.liftCLM` then builds all ellipse evaluations at once as
`synthesis : l1Chebyshev ν →L[ℝ] (Ellipse ν →ᵇ ℂ)`, identified with the classified
character (`synthesis_eq_character`) and giving continuity in the ellipse parameter
plus the exact bilateral series formula `character_apply_eq_tsum`.

Closes the "series description of the spectrum" part of the spectrum gap.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry Polynomial
open scoped BoundedContinuousFunction

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- The normalized mode convention on the actual physical algebra. -/
theorem character_mode_eq_chebyshev (χ : Character ν) (n : ℕ) :
    χ (mode ν n) = 2 * (Chebyshev.T ℂ n).eval (χ (joukowskiGenSymm ν)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [mode_zero, map_add, map_one]
    norm_num [Chebyshev.T_zero]
  | one => simp [mode_one, Chebyshev.T_one, Complex.real_smul]
  | more n h0 h1 =>
    have hm := congrArg χ (mode_recurrence ν n)
    simp only [map_mul, map_add] at hm
    rw [h0, h1, mode_one, map_smul, Complex.real_smul] at hm
    norm_num at hm
    have hT := congrArg (Polynomial.eval (χ (joukowskiGenSymm ν)))
      (Chebyshev.T_add_two ℂ (n : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hT
    have hn2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [hn2]
    linear_combination -hm - 2 * hT

/-- Bernstein's weight bound, including the boundary and `ν = 1`. -/
theorem norm_chebyshev_le (w : Ellipse ν) (n : ℕ) :
    ‖(Chebyshev.T ℂ n).eval w.val‖ ≤ (ν : ℝ) ^ n := by
  have hc := norm_character_apply_le ν (ellipseCharacter ν w) (mode ν n)
  rw [character_mode_eq_chebyshev, ellipseCharacter_gen, norm_mul] at hc
  norm_num at hc
  linarith [norm_mode_le ν n]

/-- Each polynomial column is a bounded continuous function on the ellipse. -/
def chebyshevColumn (n : ℕ) : Ellipse ν →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => (Chebyshev.T ℂ n).eval w.val)
    ((Chebyshev.T ℂ n).continuous.comp continuous_subtype_val)
    ((ν : ℝ) ^ n) (fun w => norm_chebyshev_le ν w n)

@[simp] theorem chebyshevColumn_apply (n : ℕ) (w : Ellipse ν) :
    chebyshevColumn ν n w = (Chebyshev.T ℂ n).eval w.val := rfl

theorem norm_chebyshevColumn_le (n : ℕ) :
    ‖chebyshevColumn ν n‖ ≤ (ν : ℝ) ^ n :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (pow_nonneg ν.coe_nonneg n) _

/-- A single weighted lift constructs all the ellipse evaluations together,
with uniform control on the entire closed ellipse. -/
def synthesis : l1Chebyshev ν →L[ℝ] (Ellipse ν →ᵇ ℂ) :=
  liftCLM (fun k : ℤ => chebyshevColumn ν k.natAbs) 1 (fun k => by
    rw [ScaledRealZ.norm_lpAlgRingData_ofReal]
    simpa using norm_chebyshevColumn_le ν k.natAbs)

@[simp] theorem synthesis_single (k : ℤ) (r : ℝ) (w : Ellipse ν) :
    synthesis ν (single k r) w = (r : ℂ) * (Chebyshev.T ℂ k.natAbs).eval w.val := by
  simp only [synthesis, liftCLM_single, BoundedContinuousFunction.smul_apply,
    chebyshevColumn_apply, Complex.real_smul]

@[simp] theorem synthesis_one (w : Ellipse ν) : synthesis ν 1 w = 1 := by
  rw [one_eq_single_zero, synthesis_single]
  simp [Chebyshev.T_zero]

@[simp] theorem synthesis_mode (n : ℕ) (w : Ellipse ν) :
    synthesis ν (mode ν n).val w = 2 * (Chebyshev.T ℂ n).eval w.val := by
  change synthesis ν (single (n : ℤ) 1 + single (-(n : ℤ)) 1) w = _
  rw [map_add, BoundedContinuousFunction.add_apply, synthesis_single, synthesis_single]
  simp only [Complex.ofReal_one, one_mul, Int.natAbs_natCast, Int.natAbs_neg]
  ring

/-- Evaluation of the uniformly convergent synthesis is the unique character
at the prescribed physical coordinate. -/
theorem synthesis_eq_character (w : Ellipse ν) (a : Physical ν) :
    synthesis ν a.val w = ellipseCharacter ν w a := by
  let S : Physical ν →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ w).comp
    ((synthesis ν).comp (l1Chebyshev.symmetricSubalgebra ν).valA.toContinuousLinearMap)
  have hS : S = (ellipseCharacter ν w).toContinuousLinearMap := by
    apply linear_ext ν
    · change synthesis ν 1 w = ellipseCharacter ν w 1
      rw [synthesis_one, map_one]
    · intro n
      change synthesis ν (mode ν (n + 1)).val w = ellipseCharacter ν w (mode ν (n + 1))
      rw [synthesis_mode, character_mode_eq_chebyshev, ellipseCharacter_gen]
  exact DFunLike.congr_fun hS a

/-- The parameter-to-character evaluation is continuous for every fixed
physical coefficient vector, also on the boundary of the ellipse. -/
theorem continuous_ellipseCharacter_apply (a : Physical ν) :
    Continuous (fun w : Ellipse ν => ellipseCharacter ν w a) := by
  have h : (fun w : Ellipse ν => ellipseCharacter ν w a) = synthesis ν a.val := by
    funext w
    exact (synthesis_eq_character ν w a).symm
  rw [h]
  exact (synthesis ν a.val).continuous

/-- The bilateral Chebyshev series is absolutely convergent. For symmetric
coefficients, pairing its ±k modes is the usual `a₀ + 2 Σ aₖ Tₖ(w)`. -/
theorem summable_character_series (w : Ellipse ν) (a : Physical ν) :
    Summable (fun k : ℤ => ‖(toRealSeq a.val k : ℂ) *
      (Chebyshev.T ℂ k.natAbs).eval w.val‖) := by
  refine (lpOneAlg.summable_norm a.val).of_nonneg_of_le (fun k => norm_nonneg _) ?_
  intro k
  rw [l1Chebyshev.norm_fiber, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_chebyshev_le ν w k.natAbs) (abs_nonneg _)

/-- Exact complex character formula on the production physical carrier. -/
theorem character_apply_eq_tsum (w : Ellipse ν) (a : Physical ν) :
    ellipseCharacter ν w a = ∑' k : ℤ, (toRealSeq a.val k : ℂ) *
      (Chebyshev.T ℂ k.natAbs).eval w.val := by
  rw [← synthesis_eq_character]
  change (BoundedContinuousFunction.evalCLM ℝ w) (synthesis ν a.val) = _
  rw [synthesis, liftCLM_apply, (BoundedContinuousFunction.evalCLM ℝ w).map_tsum]
  · rfl
  · exact liftCLM_summable _ (C := 1) (fun k => by
      rw [ScaledRealZ.norm_lpAlgRingData_ofReal]
      simpa using norm_chebyshevColumn_le ν k.natAbs) a.val

end RadiiPolynomial.PhysicalSpectrum
