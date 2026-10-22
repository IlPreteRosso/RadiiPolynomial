import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Ellipse
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Character values on the Chebyshev modes, and Bernstein's bound

The symmetric-mode recurrence is literally the Chebyshev recurrence
(`character_mode_eq_chebyshev`: `χ (mode n) = 2 Tₙ(χ g)` for the Joukowski generator `g`),
from which contractivity of characters yields Bernstein's bound `‖Tₙ(w)‖ ≤ νⁿ` on the
*closed* ellipse (`norm_chebyshev_le`), boundary and `ν = 1` included.
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












end RadiiPolynomial.PhysicalSpectrum
