import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds

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

end IVP
