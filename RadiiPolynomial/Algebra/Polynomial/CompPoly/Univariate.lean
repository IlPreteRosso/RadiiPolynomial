import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Univariate `CompPoly` maps on a normed commutative real algebra

For a univariate polynomial `P : CompPoly 1` of any degree and any normed commutative real
algebra `𝔸`, `polyMap P b x = P(x) - b`. Its Fréchet derivative at `x` is left multiplication
by the evaluated formal derivative `P′(x)`, `P′ = pderiv 0 P`, proved by structural induction
on the syntax tree (no `MvPolynomial` detour).

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
evaluated formal derivative `P′ = pderiv 0 P`. Structural induction; no `MvPolynomial`.
General in `P`, `𝔸`, `x`. -/
theorem hasFDerivAt_evalBanach_one (P : CompPoly 1) (x : 𝔸) :
    HasFDerivAt (fun y : 𝔸 => P.evalBanach (fun _ => y))
      (ContinuousLinearMap.mul ℝ 𝔸 ((P.pderiv 0).evalBanach (fun _ => x))) x := by
  induction P with
  | C r =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv, Rat.cast_zero, map_zero]
      exact hasFDerivAt_const _ x
  | X i =>
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [CompPoly.evalBanach, CompPoly.pderiv, if_true, Rat.cast_one, map_one]
      have h1 : ContinuousLinearMap.mul ℝ 𝔸 1 = ContinuousLinearMap.id ℝ 𝔸 := by
        ext h; simp
      rw [h1]
      exact hasFDerivAt_id x
  | add p q hp hq =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv, map_add]
      exact hp.add hq
  | sub p q hp hq =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv, map_sub]
      exact hp.sub hq
  | mul p q hp hq =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv]
      refine (hp.mul hq).congr_fderiv ?_
      ext h
      simp only [ContinuousLinearMap.mul_apply', add_apply,
        smul_apply, smul_eq_mul, map_add]
      ring
  | neg p hp =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv, map_neg]
      exact hp.neg
  | smul r p hp =>
      simp only [CompPoly.evalBanach, CompPoly.pderiv, map_smul]
      exact hp.const_smul ((r : ℚ) : ℝ)

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
