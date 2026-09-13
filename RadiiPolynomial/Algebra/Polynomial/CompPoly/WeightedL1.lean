import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.WeightedL1
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation

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


/-! ## Certificate constants from syntax (Taylor face)

On `l1Weighted ν` the inputs enter unsymmetrized, so the operator norm of the derivative
is bounded by the geometry-free `CompPoly.derivativeBound` with no extra factor. -/

theorem sum_norm_evalInBanach_pderiv_le {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (a : Fin L → l1Weighted ν) (R : Fin L → ℝ) (ha : ∀ i, ‖a i‖ ≤ R i) :
    ∑ m, ‖evalInBanach (MvPolynomial.pderiv m p.toMvPoly) a‖ ≤ p.derivativeBound R := by
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← pderiv_toMvPoly, ← compPoly_evalBanach_eq_evalInBanach]
  exact norm_evalBanach_le _ a R ha

/-- The derivative of a Taylor polynomial nonlinearity applied to a direction, bounded by
the syntactic constant. -/
theorem norm_fderiv_evalBanach_apply_le {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (a : Fin L → l1Weighted ν) (R : Fin L → ℝ) (ha : ∀ i, ‖a i‖ ≤ R i)
    (h : Fin L → l1Weighted ν) :
    ‖fderiv ℝ (fun x => p.evalBanach x) a h‖ ≤ p.derivativeBound R * ‖h‖ := by
  rw [show (fun x : Fin L → l1Weighted ν => p.evalBanach x) =
      fun x => evalInBanach p.toMvPoly x from funext (compPoly_evalBanach_eq_evalInBanach p)]
  exact (ContinuousLinearMap.le_opNorm _ h).trans (mul_le_mul_of_nonneg_right
    ((norm_fderiv_evalInBanach_le p.toMvPoly a).trans
      (sum_norm_evalInBanach_pderiv_le p a R ha)) (norm_nonneg _))

/-- Operator norm of the derivative of a Taylor polynomial nonlinearity. -/
theorem norm_fderiv_evalBanach_le {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (a : Fin L → l1Weighted ν) (R : Fin L → ℝ) (ha : ∀ i, ‖a i‖ ≤ R i) :
    ‖fderiv ℝ (fun x => p.evalBanach x) a‖ ≤ p.derivativeBound R :=
  ContinuousLinearMap.opNorm_le_bound _
    (derivativeBound_nonneg p R fun i => (norm_nonneg _).trans (ha i))
    (norm_fderiv_evalBanach_apply_le p a R ha)

/-- Lipschitz bound on the derivative of a Taylor polynomial nonlinearity in the raw
displacement `‖c - a‖`, from the syntactic constant `derivativeLipschitzBound` at radii
dominating both points. Taylor face of
`CompPoly.Chebyshev.norm_derivative_sub_le_of_norm_sub`: no symmetrization, no factor `2`. -/
theorem norm_fderiv_evalBanach_sub_le {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (c a : Fin L → l1Weighted ν) (R : Fin L → ℝ)
    (hc : ∀ i, ‖c i‖ ≤ R i) (ha : ∀ i, ‖a i‖ ≤ R i) (h : Fin L → l1Weighted ν) :
    ‖(fderiv ℝ (fun x => p.evalBanach x) c - fderiv ℝ (fun x => p.evalBanach x) a) h‖ ≤
      p.derivativeLipschitzBound R * ‖c - a‖ * ‖h‖ := by
  rw [show (fun x : Fin L → l1Weighted ν => p.evalBanach x) =
      fun x => evalInBanach p.toMvPoly x from funext (compPoly_evalBanach_eq_evalInBanach p),
    fderiv_diff_evalInBanach]
  refine (norm_sum_mul_pi_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [derivativeLipschitzBound, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← pderiv_toMvPoly, ← compPoly_evalBanach_eq_evalInBanach,
    ← compPoly_evalBanach_eq_evalInBanach]
  exact norm_evalBanach_sub_le _ c a R hc ha

/-- Ball-free face of `norm_fderiv_evalBanach_sub_le`: the radii are the two points' own
norms. For a syntactically quadratic presentation the constant is independent of these
radii. Semantic degree `≤ 2` alone does not suffice: the bound reads the unreduced AST
and does not cancel higher-degree terms. -/
theorem norm_fderiv_evalBanach_sub_le_max {ν : PosReal} {L : ℕ} (p : CompPoly L)
    (c a h : Fin L → l1Weighted ν) :
    ‖(fderiv ℝ (fun x => p.evalBanach x) c - fderiv ℝ (fun x => p.evalBanach x) a) h‖ ≤
      p.derivativeLipschitzBound (fun i => max ‖c i‖ ‖a i‖) * ‖c - a‖ * ‖h‖ :=
  norm_fderiv_evalBanach_sub_le p c a _ (fun _ => le_max_left _ _)
    (fun _ => le_max_right _ _) h

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
      p.evalBanach (fun i => l1Weighted.eval (a i) t) :=
  p.map_evalBanach (l1Weighted.evalAlgHom t ht) a

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
