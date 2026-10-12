import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Univariate `CompPoly` maps on a normed commutative real algebra

For a univariate polynomial `P : CompPoly 1` of any degree and any normed commutative real
algebra `𝔸`, `polyMap P b x = P(x) - b`. Its Fréchet derivative at `x` is left multiplication
by the evaluated formal derivative `P′(x)`, `P′ = pderiv 0 P`: the gradient row
`hasFDerivAt_evalBanach` (`CompPoly/Derivative`) composed with the diagonal `y ↦ fun _ => y`.

## Main results

- `polyMap`: the map `x ↦ P(x) - b`
- `hasFDerivAt_evalBanach_one`: `D(P(·))(x) = mul (P′(x))`
- `hasFDerivAt_polyMap`, `fderiv_polyMap`, `differentiable_polyMap`
-/

namespace MvPolyBridge.CompPoly

section Univariate

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The polynomial map `x ↦ P(x) - b` of a univariate `CompPoly` on a normed commutative real
algebra. General in `P` (any degree), `b`, `𝔸`. -/
noncomputable def polyMap (P : CompPoly 1) (b x : 𝔸) : 𝔸 :=
  P.evalBanach (fun _ => x) - b

/-- The derivative of a univariate `CompPoly` evaluation is left multiplication by the
evaluated formal derivative `P′ = pderiv 0 P`: the gradient row `hasFDerivAt_evalBanach`
composed with the diagonal `y ↦ fun _ => y` (`gradCLM_eq_mul_comp_proj`).
General in `P`, `𝔸`, `x`. -/
theorem hasFDerivAt_evalBanach_one (P : CompPoly 1) (x : 𝔸) :
    HasFDerivAt (fun y : 𝔸 => P.evalBanach (fun _ => y))
      (ContinuousLinearMap.mul ℝ 𝔸 ((P.pderiv 0).evalBanach (fun _ => x))) x := by
  have hdiag : HasFDerivAt (fun y : 𝔸 => fun _ : Fin 1 => y)
      (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ 𝔸) x :=
    hasFDerivAt_pi.2 fun _ => hasFDerivAt_id x
  refine ((CompPoly.hasFDerivAt_evalBanach P fun _ => x).comp x hdiag).congr_fderiv ?_
  rw [CompPoly.gradCLM_eq_mul_comp_proj]
  rfl

/-- General in `P`, `b`, `𝔸`, `x`. -/
theorem hasFDerivAt_polyMap (P : CompPoly 1) (b x : 𝔸) :
    HasFDerivAt (polyMap P b)
      (ContinuousLinearMap.mul ℝ 𝔸 ((P.pderiv 0).evalBanach (fun _ => x))) x :=
  (hasFDerivAt_evalBanach_one P x).sub_const b

/-- General in `P`, `b`, `𝔸`, `x`. -/
theorem fderiv_polyMap (P : CompPoly 1) (b x : 𝔸) :
    fderiv ℝ (polyMap P b) x =
      ContinuousLinearMap.mul ℝ 𝔸 ((P.pderiv 0).evalBanach (fun _ => x)) :=
  (hasFDerivAt_polyMap P b x).fderiv

/-- General in `P`, `b`, `𝔸`. -/
theorem differentiable_polyMap (P : CompPoly 1) (b : 𝔸) :
    Differentiable ℝ (polyMap P b) :=
  fun x => (hasFDerivAt_polyMap P b x).differentiableAt

end Univariate

end MvPolyBridge.CompPoly
