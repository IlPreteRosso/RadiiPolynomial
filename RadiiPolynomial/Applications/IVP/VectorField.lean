import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative

/-!
# The real vector field of a polynomial system

`IVP.vectorField` reads the geometry-free ODE right-hand side from a `CompPoly` system.
The Taylor and Chebyshev trajectory/solution modules use this same real field. Their
coefficient-space `banachField` maps are defined in their respective geometry modules.

The file proves `vectorField_lipschitzOnWith`,
`lipschitzOnWith_vectorField_closedBall` and `exists_lipschitz_vectorField_closedBall`:
the Lipschitz constants are read from `CompPoly.lipschitzBound`. The explicit closed-ball
face accepts a constant dominating those component bounds. Polynomial derivative witnesses
are in `CompPoly/Derivative.lean`.
-/

open RadiiPolynomial MvPolyBridge

namespace IVP

variable {L : ℕ}

/-- The polynomial vector field `f : ℝ^L → ℝ^L` derived from a CompPoly representation.
This is the original ODE right-hand side recovered from its symbolic encoding. -/
noncomputable def vectorField (φ_cpoly : Fin L → CompPoly L) (x : Fin L → ℝ) (l : Fin L) :
    ℝ :=
  (φ_cpoly l).evalBanach x

/-- The vector field is Lipschitz on the closed ball of radius `R ≥ 0` with the syntactic
constant `∑ l, lipschitzBound (φ_cpoly l) R`, which dominates every component's own
constant. Internal to the solution faces: the constant never reaches a statement. -/
theorem vectorField_lipschitzOnWith (φ_cpoly : Fin L → CompPoly L) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (∑ l, (φ_cpoly l).lipschitzBound fun _ => R))
      (vectorField φ_cpoly) (Metric.closedBall 0 R) :=
  CompPoly.lipschitzOnWith_evalBanach_pi φ_cpoly R fun l => by
    rw [Real.coe_toNNReal']
    exact le_max_of_le_left (Finset.single_le_sum
      (fun i _ => CompPoly.lipschitzBound_nonneg (φ_cpoly i) _ fun _ => hR)
      (Finset.mem_univ l))

/-! ## Calculus of the vector field -/





/-- Explicit form: on `closedBall 0 R` the vector field is Lipschitz with any constant `K`
dominating every component's syntactic constant `CompPoly.lipschitzBound`, so a certificate can
state `K` as a number. -/
theorem lipschitzOnWith_vectorField_closedBall (φ_cpoly : Fin L → CompPoly L) (R : ℝ)
    {K : NNReal} (hK : ∀ l, (φ_cpoly l).lipschitzBound (fun _ => R) ≤ (K : ℝ)) :
    LipschitzOnWith K (fun x : Fin L → ℝ => vectorField φ_cpoly x)
      (Metric.closedBall (0 : Fin L → ℝ) R) :=
  CompPoly.lipschitzOnWith_evalBanach_pi φ_cpoly R hK

/-- Existence form, for every radius `R` (no sign condition): the constant
`(∑ l, |lipschitzBound (φ_cpoly l) R|)⁺` is read off the syntax; no compactness argument. -/
theorem exists_lipschitz_vectorField_closedBall
    (φ_cpoly : Fin L → CompPoly L) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun x : Fin L → ℝ => vectorField φ_cpoly x)
                  (Metric.closedBall (0 : Fin L → ℝ) R) :=
  ⟨Real.toNNReal (∑ l, |(φ_cpoly l).lipschitzBound (fun _ => R)|),
    lipschitzOnWith_vectorField_closedBall φ_cpoly R fun l => by
      rw [Real.coe_toNNReal']
      exact le_max_of_le_left ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |(φ_cpoly j).lipschitzBound (fun _ => R)|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ l)))⟩

end IVP
