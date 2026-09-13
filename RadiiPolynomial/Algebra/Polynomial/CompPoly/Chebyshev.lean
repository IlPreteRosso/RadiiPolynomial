import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev.Coefficients
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Calculus
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra

/-!
# Polynomial semantics for stored Chebyshev coefficients

The stored nonnegative modes determine a symmetric Laurent sequence. `eval`
interprets a `CompPoly` after this symmetrization, so its output belongs to the
physical Chebyshev algebra. `eval_eval` commutes this interpretation with evaluation
on the real interval through algebra-hom naturality.

`derivative` composes the generic polynomial derivative with the linear
symmetrization of directions. Its single-mode formulas expose both Laurent shifts
for a positive stored mode, and zero for a negative stored mode.
-/

noncomputable section

open scoped BigOperators
open RadiiPolynomial
open MvPolynomial (aeval polynomialDerivative polynomialDerivative_apply hasFDerivAt_aeval)

namespace MvPolyBridge.CompPoly.Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {L : ℕ}

local instance : Algebra ℚ (l1Chebyshev ν) :=
  ((algebraMap ℝ (l1Chebyshev ν)).comp (algebraMap ℚ ℝ)).toAlgebra

local instance : IsScalarTower ℚ ℝ (l1Chebyshev ν) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Interpret a polynomial on stored coefficients through the physical algebra. -/
def eval (p : CompPoly L) (a : Fin L → l1Chebyshev ν) : l1Chebyshev ν :=
  p.evalBanach (fun i => l1Chebyshev.symmetrize (a i))

private def physicalInput (a : l1Chebyshev ν) : l1Chebyshev.symmetricSubalgebra ν :=
  ⟨l1Chebyshev.symmetrize a, l1Chebyshev.symmetrize_isSymmetric a⟩

private theorem coe_physical_eval (p : CompPoly L) (a : Fin L → l1Chebyshev ν) :
    (↑(p.evalBanach (fun i => physicalInput (a i)) :
      l1Chebyshev.symmetricSubalgebra ν) : l1Chebyshev ν) = eval p a :=
  map_evalBanach (l1Chebyshev.symmetricSubalgebra ν).val p (fun i => physicalInput (a i))

/-- Polynomial outputs lie in the physical, flip-fixed algebra. -/
theorem eval_isSymmetric (p : CompPoly L) (a : Fin L → l1Chebyshev ν) :
    (eval p a).IsSymmetric := by
  rw [← coe_physical_eval]
  exact (p.evalBanach (fun i => physicalInput (a i))).property

/-- Pointwise evaluation commutes with the stored-coefficient nonlinearity. -/
theorem eval_eval (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    {t : ℝ} (ht : |t| ≤ 1) :
    l1Chebyshev.eval (eval p a) t =
      p.evalBanach (fun i => l1Chebyshev.eval (a i) t) := by
  rw [← coe_physical_eval]
  change (l1Chebyshev.symmetricEvalCharacter ν t ht).toAlgHom
    (p.evalBanach (fun i => physicalInput (a i))) = _
  rw [map_evalBanach]
  congr 1

/-- Differential of a stored-coefficient polynomial nonlinearity. -/
def derivative (p : CompPoly L) (a : Fin L → l1Chebyshev ν) :
    (Fin L → l1Chebyshev ν) →L[ℝ] l1Chebyshev ν :=
  (polynomialDerivative p.toMvPoly (fun i => l1Chebyshev.symmetrize (a i))).comp
    (ContinuousLinearMap.pi fun i =>
      l1Chebyshev.symmetrize_CLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem derivative_apply (p : CompPoly L) (a h : Fin L → l1Chebyshev ν) :
    derivative p a h = ∑ i : Fin L, eval (p.pderiv i) a *
      l1Chebyshev.symmetrize (h i) := by
  simp only [derivative, ContinuousLinearMap.comp_apply, polynomialDerivative_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    l1Chebyshev.symmetrize_CLM_apply]
  congr 1
  funext i
  rw [eval, (p.pderiv i).evalBanach_eq_evalAlg,
    (p.pderiv i).evalAlg_eq_aeval, CompPoly.pderiv_toMvPoly]

/-- The stored-coefficient derivative acts on symmetrized directions. -/
theorem hasFDerivAt_eval (p : CompPoly L) (a : Fin L → l1Chebyshev ν) :
    HasFDerivAt (eval p) (derivative p a) a := by
  let S : (Fin L → l1Chebyshev ν) →L[ℝ] (Fin L → l1Chebyshev ν) :=
    ContinuousLinearMap.pi fun i =>
      l1Chebyshev.symmetrize_CLM.comp (ContinuousLinearMap.proj i)
  have h := (hasFDerivAt_aeval (𝕜 := ℝ) p.toMvPoly
    (S a)).comp a S.hasFDerivAt
  have he : eval (ν := ν) p = fun a =>
      aeval (fun i => l1Chebyshev.symmetrize (a i)) p.toMvPoly :=
    funext fun _ => (p.evalBanach_eq_evalAlg _).trans (p.evalAlg_eq_aeval _)
  rw [he]
  exact h

/-- Every polynomial nonlinearity is differentiable on bilateral storage. -/
theorem differentiable_eval (p : CompPoly L) : Differentiable ℝ (eval (ν := ν) p) :=
  fun a => (hasFDerivAt_eval p a).differentiableAt

/-- The Fréchet derivative agrees with the polynomial derivative after symmetrization. -/
theorem fderiv_eval (p : CompPoly L) (a : Fin L → l1Chebyshev ν) :
    fderiv ℝ (eval p) a = derivative p a :=
  (hasFDerivAt_eval p a).fderiv

/-- Apply the Fréchet derivative through the formal partial derivatives. -/
theorem fderiv_eval_apply (p : CompPoly L) (a h : Fin L → l1Chebyshev ν) :
    fderiv ℝ (eval p) a h =
      ∑ i : Fin L, eval (p.pderiv i) a * l1Chebyshev.symmetrize (h i) := by
  rw [(hasFDerivAt_eval p a).fderiv, derivative_apply]

/-- A single component direction extracts the corresponding formal partial derivative. -/
theorem derivative_single (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    (m : Fin L) (h : l1Chebyshev ν) :
    derivative p a (Pi.single m h) = eval (p.pderiv m) a * l1Chebyshev.symmetrize h := by
  rw [derivative_apply]
  simp only [Pi.single_apply]
  simp_rw [apply_ite l1Chebyshev.symmetrize, ← l1Chebyshev.symmetrize_CLM_apply,
    map_zero, mul_ite, mul_zero]
  simp

/-- The finite Jacobian column formula for a stored nonnegative mode. -/
theorem derivative_single_toSeq (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    (m : Fin L) (k : ℕ) (n : ℤ) :
    l1Chebyshev.toSeq (derivative p a
      (Pi.single m (l1Chebyshev.single (k : ℤ) 1))) n =
      if k = 0 then l1Chebyshev.toSeq (eval (p.pderiv m) a) n
      else l1Chebyshev.toSeq (eval (p.pderiv m) a) (n - k) +
        l1Chebyshev.toSeq (eval (p.pderiv m) a) (n + k) := by
  rw [derivative_single, l1Chebyshev.mul_symmetrize_single_toSeq]

/-- Stored negative columns do not enter the physical nonlinearity. -/
theorem derivative_single_negSucc (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    (m : Fin L) (k : ℕ) (x : ℝ) :
    derivative p a (Pi.single m (l1Chebyshev.single (Int.negSucc k) x)) = 0 := by
  rw [derivative_single, l1Chebyshev.symmetrize_single_negSucc, mul_zero]

end MvPolyBridge.CompPoly.Chebyshev
