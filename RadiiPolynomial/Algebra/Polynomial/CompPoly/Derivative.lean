import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Calculus
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Derivatives of `CompPoly` evaluations on `R^L`

For a normed commutative real algebra `R`, the Fréchet derivative of `u ↦ p.evalBanach u` on
`R^L = Fin L → R` is the syntactic gradient row `gradCLM p x : h ↦ Σₖ (∂ₖp)(x) · hₖ`, and the
derivative of a polynomial system `u ↦ (Pᵢ.evalBanach u)ᵢ` on `R^n` is the syntactic Jacobian
`jacCLM P x`, the continuous linear map with rows `gradCLM (P i) x`. The proof goes through
the library's `MvPolynomial` calculus (`MvPolynomial.hasFDerivAt_aeval`, `MvPolynomial/Calculus`) along
`evalBanach_eq_aeval_map`, with the canonical `Algebra ℝ R` only.

`gradCLM`, `jacobian` and `jacCLM` are transparent definitions: componentwise identities such as
`(jacCLM P a - jacCLM P b) h i = (gradCLM (P i) a - gradCLM (P i) b) h` hold by `rfl`.

## Main results

- `gradCLM`, `gradCLM_apply`, `gradCLM_eq_polynomialDerivative`
- `hasFDerivAt_evalBanach`: `D(p(·))(x) = gradCLM p x`
- `jacobian`, `jacCLM`, `jacCLM_apply`
- `hasFDerivAt_system`: `D(P(·))(x) = jacCLM P x`
- `gradCLM_eq_mul_comp_proj`: at `L = 1`, the gradient row is multiplication by `p′(x)` after
  the coordinate projection
- `MvPolyBridge.contDiff_evalBanach`, `MvPolyBridge.differentiable_evalBanach`: on `ℝ^L` itself
  the evaluation `x ↦ p.evalBanach x` is `C^ω` (through `MvPolynomial.contDiff_aeval`), hence
  differentiable; the real vector field `IVP.vectorField` inherits both
-/

open scoped BigOperators

namespace MvPolyBridge.CompPoly

section PolyDeriv

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {L : ℕ}

/-- Gradient row of a scalar polynomial on `R^L`: `h ↦ Σₖ (∂ₖp)(x) · hₖ`. -/
noncomputable def gradCLM (p : CompPoly L) (x : Fin L → R) : (Fin L → R) →L[ℝ] R :=
  ∑ k : Fin L, (p.pderiv k).evalBanach x •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => R) k)

@[simp] theorem gradCLM_apply (p : CompPoly L) (x h : Fin L → R) :
    gradCLM p x h = ∑ k : Fin L, (p.pderiv k).evalBanach x * h k := by
  simp [gradCLM]

/-- The gradient row is the library's `polynomialDerivative` of the `ℝ`-mapped polynomial (stated
through the canonical `Algebra ℝ R`; no `Algebra ℚ R` is needed). -/
theorem gradCLM_eq_polynomialDerivative (p : CompPoly L) (x : Fin L → R) :
    gradCLM p x = MvPolynomial.polynomialDerivative (𝕜 := ℝ)
      (MvPolynomial.map (algebraMap ℚ ℝ) p.toMvPoly) x := by
  refine ContinuousLinearMap.ext fun h => ?_
  rw [gradCLM_apply, MvPolynomial.polynomialDerivative_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.pderiv_map, ← CompPoly.pderiv_toMvPoly, evalBanach_eq_aeval_map]

/-- The derivative of `u ↦ p.evalBanach u` on `R^L` is the syntactic gradient. -/
theorem hasFDerivAt_evalBanach (p : CompPoly L) (x : Fin L → R) :
    HasFDerivAt (fun u : Fin L → R => p.evalBanach u) (gradCLM p x) x := by
  have he : (fun u : Fin L → R => p.evalBanach u) =
      fun u => MvPolynomial.aeval u (MvPolynomial.map (algebraMap ℚ ℝ) p.toMvPoly) :=
    funext fun u => evalBanach_eq_aeval_map p u
  rw [he, gradCLM_eq_polynomialDerivative]
  exact MvPolynomial.hasFDerivAt_aeval _ x

/-- The syntactic Jacobian matrix of a polynomial system at `x : R^n`. -/
noncomputable def jacobian {n : ℕ} (P : Fin n → CompPoly n) (x : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j k => ((P j).pderiv k).evalBanach x

/-- Jacobian of a polynomial system on `R^n`, as an `ℝ`-linear map. -/
noncomputable def jacCLM {n : ℕ} (P : Fin n → CompPoly n) (x : Fin n → R) :
    (Fin n → R) →L[ℝ] (Fin n → R) :=
  ContinuousLinearMap.pi fun i => gradCLM (P i) x

theorem jacCLM_apply {n : ℕ} (P : Fin n → CompPoly n) (x h : Fin n → R) (i : Fin n) :
    jacCLM P x h i = ∑ k, jacobian P x i k * h k := by
  simp [jacCLM, jacobian]

/-- The derivative of a polynomial system `u ↦ (Pᵢ.evalBanach u)ᵢ` on `R^n` is its syntactic
Jacobian. -/
theorem hasFDerivAt_system {n : ℕ} (P : Fin n → CompPoly n) (x : Fin n → R) :
    HasFDerivAt (fun u i => (P i).evalBanach u) (jacCLM P x) x :=
  hasFDerivAt_pi.2 fun i => hasFDerivAt_evalBanach (P i) x

/-- At `L = 1` the gradient row is left multiplication by the evaluated formal derivative
`p′(x) = (pderiv 0 p)(x)` after the coordinate projection. Composing with `y ↦ fun _ => y` gives
the derivative of `y ↦ p.evalBanach (fun _ => y)` on `R` itself as `ContinuousLinearMap.mul`
(`CompPoly.hasFDerivAt_evalBanach_one`, `CompPoly/Univariate`). -/
theorem gradCLM_eq_mul_comp_proj (p : CompPoly 1) (x : Fin 1 → R) :
    gradCLM p x = (ContinuousLinearMap.mul ℝ R ((p.pderiv 0).evalBanach x)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => R) 0) := by
  refine ContinuousLinearMap.ext fun h => ?_
  rw [gradCLM_apply, Fin.sum_univ_one]
  rfl

end PolyDeriv

end MvPolyBridge.CompPoly

/-! ## Smoothness of the real evaluation -/

namespace MvPolyBridge

/-- The pointwise interpretation of a `CompPoly` on `Fin L → ℝ` is `ContDiff ℝ ⊤`, i.e. of
class `C^ω` (analytic), which in particular makes it smooth. -/
theorem contDiff_evalBanach {L : ℕ} (p : CompPoly L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => p.evalBanach x) := by
  have h : (fun x : Fin L → ℝ => p.evalBanach x) =
           (fun x => MvPolynomial.aeval x p.toMvPoly) :=
    funext fun x => (p.evalBanach_eq_evalAlg x).trans (p.evalAlg_eq_aeval x)
  rw [h]
  exact MvPolynomial.contDiff_aeval p.toMvPoly ⊤

/-- The pointwise interpretation of a `CompPoly` on `Fin L → ℝ` is differentiable (from
`contDiff_evalBanach`). -/
theorem differentiable_evalBanach {L : ℕ} (p : CompPoly L) :
    Differentiable ℝ (fun x : Fin L → ℝ => p.evalBanach x) :=
  (contDiff_evalBanach p).differentiable (by decide)

end MvPolyBridge
