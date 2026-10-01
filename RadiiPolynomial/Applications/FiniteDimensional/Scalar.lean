import RadiiPolynomial.Applications.FiniteDimensional.Polynomial
import RadiiPolynomial.Core.Transport

/-!
# The scalar instance `n = 1`

`R^1 = Fin 1 → R` is isometric to `R` (`IsometryEquiv.funUnique`), so a unique zero of the field
of a `StdFinDimData 1` in a closed ball of `R^1` is a unique zero of the scalar map
`g x = (P 0).evalBanach (fun _ => x)` in the corresponding closed ball of `R`
(`StdFinDimData.existsUnique_scalar_of`, through `existsUnique_zero_transport`).
-/

open Metric
open MvPolyBridge MvPolyBridge.CompPoly

namespace RadiiPolynomial

/-- The scalar instance `R^1 ≃ R`, for any coordinate ring `R`: a unique zero of the field in a
closed ball of `R^1` gives a unique zero of `g` in the corresponding closed ball of `R`. -/
theorem StdFinDimData.existsUnique_scalar_of (R : Type*) [NormedCommRing R] [NormedAlgebra ℝ R]
    (d : StdFinDimData 1)
    (h : ∃! x ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), d.field R x = 0) {g : R → R}
    (hg : ∀ x, g x = (d.P 0).evalBanach (fun _ => x)) {xBar : R} {r : ℝ}
    (hx : ratMap R (d.xBar 0) = xBar) (hr : ((d.r₀ : ℚ) : ℝ) = r) :
    ∃! x ∈ closedBall xBar r, g x = 0 := by
  subst hx hr
  have key := existsUnique_zero_transport (IsometryEquiv.funUnique (Fin 1) R)
    (g := g) (F := d.field R) (fun x => ?_) h
  · simpa [StdFinDimData.xBarR, Fin.default_eq_zero] using key
  · have hx : (fun _ : Fin 1 => x default) = x :=
      funext fun i => by rw [Subsingleton.elim i default]
    rw [IsometryEquiv.funUnique_apply, hg, hx]
    refine ⟨fun h0 => funext fun i => ?_, fun h0 => congrFun h0 0⟩
    rw [Subsingleton.elim i 0]
    exact h0

end RadiiPolynomial
