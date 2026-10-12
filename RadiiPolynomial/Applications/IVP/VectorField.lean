import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative

/-!
# The real vector field of a polynomial system

Geometry-free application layer: the right-hand side of the ODE `ẋ = f(x)` read off a
`CompPoly` system, with no reference to any coefficient space. Both discretizations need
it — the Taylor bridge in `Applications/IVP/Taylor/Trajectory.lean` states its
function-space conclusions in terms of it, and so do the Chebyshev solution faces in
`Applications/IVP/Chebyshev/AnalyticPolynomial.lean` — so it lives above neither of them.

The coefficient-space companions are the two `banachField` maps, one per geometry
(`IVP.banachField` on `l1Weighted`, `ChebyshevIVP.banachField` on `l1Chebyshev`); they
stay in their own modules because each mentions its own carrier.

`vectorField_lipschitzOnWith` packages the syntactic Lipschitz constant of the system on a
ball as the `NNReal` the solution faces consume, so no certificate states one by hand.

## Calculus of the vector field

- `contDiff_vectorField`, `contDiff_vectorField_pi`: the field is `C^ω` on `ℝ^L`
  (from `MvPolyBridge.contDiff_evalBanach`, `CompPoly/Derivative`);
- `differentiable_vectorField`, `differentiable_vectorField_pi`: hence differentiable;
- `lipschitzOnWith_vectorField_closedBall`: Lipschitz on `closedBall 0 R` with any constant
  dominating the components' syntactic `CompPoly.lipschitzBound`;
- `exists_lipschitz_vectorField_closedBall`: the existence form, with the constant read off the
  syntax for every radius.
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

/-- Each component `x ↦ vectorField φ_cpoly x l` is `ContDiff ℝ ⊤` on `ℝ^L`, i.e. of class
`C^ω` (analytic), in particular `C^∞`. Smoothness is what the analytic-solution side needs; the
Lipschitz constant for uniqueness is read off the syntax
(`lipschitzOnWith_vectorField_closedBall`). -/
theorem contDiff_vectorField (φ_cpoly : Fin L → CompPoly L) (l : Fin L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => vectorField φ_cpoly x l) :=
  MvPolyBridge.contDiff_evalBanach (φ_cpoly l)

/-- The full vector field `vectorField φ_cpoly : ℝ^L → (Fin L → ℝ)` is `ContDiff ℝ ⊤`
(class `C^ω`). -/
theorem contDiff_vectorField_pi (φ_cpoly : Fin L → CompPoly L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => vectorField φ_cpoly x) :=
  contDiff_pi.mpr (contDiff_vectorField φ_cpoly)

/-- Each component of the vector field is differentiable on `ℝ^L`
(`MvPolyBridge.differentiable_evalBanach`). -/
theorem differentiable_vectorField (φ_cpoly : Fin L → CompPoly L) (l : Fin L) :
    Differentiable ℝ (fun x : Fin L → ℝ => vectorField φ_cpoly x l) :=
  MvPolyBridge.differentiable_evalBanach (φ_cpoly l)

/-- The full vector field is differentiable on `ℝ^L`. -/
theorem differentiable_vectorField_pi (φ_cpoly : Fin L → CompPoly L) :
    Differentiable ℝ (fun x : Fin L → ℝ => vectorField φ_cpoly x) :=
  differentiable_pi.mpr (differentiable_vectorField φ_cpoly)

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
