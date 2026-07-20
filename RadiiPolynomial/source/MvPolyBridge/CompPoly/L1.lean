import RadiiPolynomial.source.MvPolyBridge.CompPoly.Core
import RadiiPolynomial.source.MvPolyBridge.L1Weighted
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Weighted l1 Semantics for CompPoly

Specializes the generic computable polynomial AST to `l1Weighted`, connecting semantic
evaluation, computable coefficients, smoothness, and pointwise power-series evaluation.
-/

open scoped BigOperators
open RadiiPolynomial

namespace MvPolyBridge

open CompPoly in
theorem compPoly_evalAlg_eq_evalInBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) :
    p.evalAlg a = evalInBanach p.toMvPoly a :=
  p.evalAlg_eq_aeval a

open CompPoly in
theorem compPoly_evalBanach_eq_evalInBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) :
    p.evalBanach a = evalInBanach p.toMvPoly a :=
  (p.evalBanach_eq_evalAlg a).trans (p.evalAlg_eq_aeval a)

namespace CompPoly

/-- Sequence-level coefficient extraction commutes with `CompPoly.evalBanach`. -/
theorem toSeq_evalBanach_of_coeffs {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (a : Fin L → l1Weighted ν) (coeffs : Fin L → ℕ → ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = (coeffs i n : ℝ)) (n : ℕ) :
    l1Weighted.toSeq (p.evalBanach a) n = (p.evalCoeffSeq coeffs n : ℝ) := by
  rw [compPoly_evalBanach_eq_evalInBanach,
    toSeq_evalInBanach_of_coeffs _ a coeffs ha n]
  exact_mod_cast (p.evalCoeffSeq_eq_mvPolyCoeff coeffs n).symm

/-- Array-valued coefficient extraction commutes with `CompPoly.evalBanach`. -/
theorem toSeq_evalBanach {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (a : Fin L → l1Weighted ν) (arrs : Fin L → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ)) (n : ℕ) :
    l1Weighted.toSeq (p.evalBanach a) n = (p.evalCoeff arrs n : ℝ) := by
  simpa only [evalCoeff] using
    p.toSeq_evalBanach_of_coeffs a (fun i k => (arrs i).getD k 0) ha n

end CompPoly

/-- The pointwise interpretation of a `CompPoly` is smooth. -/
theorem contDiff_evalBanach {L : ℕ} (p : CompPoly L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => p.evalBanach x) := by
  have h : (fun x : Fin L → ℝ => p.evalBanach x) =
           (fun x => MvPolynomial.aeval x p.toMvPoly) :=
    funext fun x => (p.evalBanach_eq_evalAlg x).trans (p.evalAlg_eq_aeval x)
  rw [h]
  exact MvPolynomial.contDiff_aeval p.toMvPoly ⊤

/-- Differentiability follows from smoothness. -/
theorem differentiable_evalBanach {L : ℕ} (p : CompPoly L) :
    Differentiable ℝ (fun x : Fin L → ℝ => p.evalBanach x) :=
  (contDiff_evalBanach p).differentiable (by decide)

/-- Banach-algebra interpretation of a computable polynomial is differentiable on
`l1Weighted`. -/
theorem differentiable_evalBanach_l1Weighted {ν : PosReal} {L : ℕ} (p : CompPoly L) :
    Differentiable ℝ (fun x : Fin L → l1Weighted ν => p.evalBanach x) := by
  have h :
      (fun x : Fin L → l1Weighted ν => p.evalBanach x) =
        fun x => evalInBanach p.toMvPoly x :=
    funext fun x => compPoly_evalBanach_eq_evalInBanach p x
  rw [h]
  exact differentiable_evalInBanach p.toMvPoly

/-- Pointwise evaluation commutes with polynomial substitution in `l1Weighted`. -/
theorem eval_evalBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) {t : ℝ} (ht : |t| ≤ ν) :
    l1Weighted.eval (p.evalBanach a) t =
      p.evalBanach (fun i => l1Weighted.eval (a i) t) := by
  rw [p.evalBanach_eq_evalAlg, p.evalAlg_eq_aeval]
  rw [show l1Weighted.eval (MvPolynomial.aeval a p.toMvPoly) t =
        l1Weighted.evalAlgHomQ t ht (MvPolynomial.aeval a p.toMvPoly) from rfl]
  rw [MvPolynomial.comp_aeval_apply]
  rw [← p.evalAlg_eq_aeval, ← p.evalBanach_eq_evalAlg]
  rfl

/-- Partial derivatives of a `CompPoly` system agree with the rational coefficient
evaluator used by finite Jacobian certificates. -/
theorem compPoly_Dφ_bridge {ν : PosReal} {L : ℕ}
    (φ_comp : Fin L → CompPoly L)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (hφ : ∀ j, (φ_comp j).toMvPoly = φ_spec j)
    (arrs : Fin L → Array ℚ)
    (ā : Fin L → l1Weighted ν)
    (ha : ∀ i n, l1Weighted.toSeq (ā i) n = ((arrs i).getD n 0 : ℝ))
    (j m : Fin L) (k : ℕ) :
    l1Weighted.toSeq (evalInBanach
      (MvPolynomial.pderiv m (φ_spec j)) ā) k =
      (((φ_comp j).pderiv m).evalCoeff arrs k : ℝ) := by
  rw [← hφ, ← CompPoly.pderiv_toMvPoly,
    ← compPoly_evalBanach_eq_evalInBanach]
  exact ((φ_comp j).pderiv m).toSeq_evalBanach ā arrs ha k

end MvPolyBridge
