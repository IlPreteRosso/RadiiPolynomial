import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev

/-!
# Certificate constants for stored Chebyshev nonlinearities, from syntax

The two norm constants a Chebyshev certificate needs from its nonlinearity — the operator
norm of `derivative p a` (the Z₁ constant `K`) and the Lipschitz constant of
`a ↦ derivative p a` (the Z₂ constant) — are read off the syntax tree; the size bound
`norm_eval_le` is the building block for both. The input radii are stated on the
symmetrized inputs `‖symmetrize (a i)‖ ≤ R i`, which is the quantity a certificate bounds
in exact arithmetic (bilateral finite support), so no factor is lost on the way in; the
only geometric constants are `‖symmetrize‖ ≤ 2` on the direction `h` (absorbed into
`derivativeBound` and `derivativeLipschitzBound`) and, in the raw-displacement faces, on
the displacement `a - b` (the explicit factor `2`).

`derivativeBound p R = 2 · Σᵢ normBound (∂ᵢ p) R` and
`derivativeLipschitzBound p R = 2 · Σᵢ lipschitzBound (∂ᵢ p) R` are exact rationals when
`R` is; the `_ratCast` lemmas connect them to the real statements.
-/

noncomputable section

open scoped BigOperators
open RadiiPolynomial

namespace MvPolyBridge.CompPoly.Chebyshev

variable {L : ℕ}

section Constants

variable {K : Type*} [DivisionRing K]

/-- Operator-norm constant of `derivative p a` when `‖symmetrize (a i)‖ ≤ R i`. -/
def derivativeBound (p : CompPoly L) (R : Fin L → K) : K :=
  2 * ∑ i, (p.pderiv i).normBound R

/-- Lipschitz constant of `a ↦ derivative p a` with respect to the sup norm of the
symmetrized displacement, on the ball `‖symmetrize (a i)‖ ≤ R i`; the raw-displacement
faces carry one more factor `2`. -/
def derivativeLipschitzBound (p : CompPoly L) (R : Fin L → K) : K :=
  2 * ∑ i, (p.pderiv i).lipschitzBound R

/-- The Chebyshev constant is the geometry-free one times `‖symmetrize‖ ≤ 2`. -/
theorem derivativeBound_eq_two_mul (p : CompPoly L) (R : Fin L → K) :
    derivativeBound p R = 2 * CompPoly.derivativeBound p R := rfl

theorem derivativeLipschitzBound_eq_two_mul (p : CompPoly L) (R : Fin L → K) :
    derivativeLipschitzBound p R = 2 * CompPoly.derivativeLipschitzBound p R := rfl

end Constants

section Cast

variable {K : Type*} [DivisionRing K] [CharZero K]

@[norm_cast] theorem derivativeBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((derivativeBound p R : ℚ) : K) = derivativeBound p (fun i => (R i : K)) := by
  simp [derivativeBound, normBound_ratCast]

@[norm_cast] theorem derivativeLipschitzBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((derivativeLipschitzBound p R : ℚ) : K) =
      derivativeLipschitzBound p (fun i => (R i : K)) := by
  simp [derivativeLipschitzBound, lipschitzBound_ratCast]

end Cast

section Order

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem derivativeBound_nonneg (p : CompPoly L) (R : Fin L → K) (hR : ∀ i, 0 ≤ R i) :
    0 ≤ derivativeBound p R :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => normBound_nonneg _ R hR)

theorem derivativeLipschitzBound_nonneg (p : CompPoly L) (R : Fin L → K)
    (hR : ∀ i, 0 ≤ R i) : 0 ≤ derivativeLipschitzBound p R :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => lipschitzBound_nonneg _ R hR)

end Order

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

private theorem norm_symmetrize_pi_le (h : Fin L → l1Chebyshev ν) :
    ‖fun i => l1Chebyshev.symmetrize (h i)‖ ≤ 2 * ‖h‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (l1Chebyshev.symmetrize_norm_le _).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (by norm_num))

private theorem symmetrize_pi_sub (a b : Fin L → l1Chebyshev ν) :
    ((fun i => l1Chebyshev.symmetrize (a i)) - fun i => l1Chebyshev.symmetrize (b i)) =
      fun i => l1Chebyshev.symmetrize ((a - b) i) := by
  funext i
  simp only [Pi.sub_apply, ← l1Chebyshev.symmetrize_CLM_apply, map_sub]

/-- Size of the stored nonlinearity from the syntactic bound. -/
theorem norm_eval_le (p : CompPoly L) (a : Fin L → l1Chebyshev ν) (R : Fin L → ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i) :
    ‖eval p a‖ ≤ p.normBound R :=
  norm_evalBanach_le p _ R ha

/-- Lipschitz control of the stored nonlinearity, symmetrized-displacement face. -/
theorem norm_eval_sub_le (p : CompPoly L) (a b : Fin L → l1Chebyshev ν) (R : Fin L → ℝ)
    (d : ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i)
    (hd : ∀ i, ‖l1Chebyshev.symmetrize (a i) - l1Chebyshev.symmetrize (b i)‖ ≤ d)
    (hd0 : 0 ≤ d) :
    ‖eval p a - eval p b‖ ≤ p.lipschitzBound R * d :=
  norm_evalBanach_sub_le_of_forall_le p _ _ R d ha hb hd hd0

/-- Lipschitz control of the stored nonlinearity, raw-displacement face. -/
theorem norm_eval_sub_le_of_norm_sub (p : CompPoly L) (a b : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i) :
    ‖eval p a - eval p b‖ ≤ p.lipschitzBound R * (2 * ‖a - b‖) := by
  refine (norm_evalBanach_sub_le p _ _ R ha hb).trans (mul_le_mul_of_nonneg_left ?_
    (lipschitzBound_nonneg p R fun i => (norm_nonneg _).trans (ha i)))
  rw [symmetrize_pi_sub]
  exact norm_symmetrize_pi_le (a - b)

/-- The derivative applied to a direction, bounded by the syntactic constant. -/
theorem norm_derivative_apply_le (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ) (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (h : Fin L → l1Chebyshev ν) :
    ‖derivative p a h‖ ≤ derivativeBound p R * ‖h‖ := by
  rw [derivative_apply]
  refine (norm_sum_mul_pi_le _ fun i => l1Chebyshev.symmetrize (h i)).trans ?_
  have h1 : ∑ i, ‖eval (p.pderiv i) a‖ ≤ ∑ i, (p.pderiv i).normBound R :=
    Finset.sum_le_sum fun i _ => norm_eval_le _ a R ha
  refine (mul_le_mul h1 (norm_symmetrize_pi_le h) (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => (norm_nonneg _).trans (norm_eval_le _ a R ha))).trans
    (le_of_eq ?_)
  rw [derivativeBound]
  ring

/-- Operator norm of the derivative from the syntactic constant. -/
theorem norm_derivative_le (p : CompPoly L) (a : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ) (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i) :
    ‖derivative p a‖ ≤ derivativeBound p R :=
  ContinuousLinearMap.opNorm_le_bound _
    (derivativeBound_nonneg p R fun i => (norm_nonneg _).trans (ha i))
    (norm_derivative_apply_le p a R ha)

/-- The difference of two derivatives applied to a direction, symmetrized-displacement face. -/
theorem norm_derivative_sub_apply_le (p : CompPoly L) (a b : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ) (d : ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i)
    (hd : ∀ i, ‖l1Chebyshev.symmetrize (a i) - l1Chebyshev.symmetrize (b i)‖ ≤ d)
    (hd0 : 0 ≤ d) (h : Fin L → l1Chebyshev ν) :
    ‖derivative p a h - derivative p b h‖ ≤ derivativeLipschitzBound p R * d * ‖h‖ := by
  rw [derivative_apply, derivative_apply, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  refine (norm_sum_mul_pi_le _ fun i => l1Chebyshev.symmetrize (h i)).trans ?_
  have h1 : ∑ i, ‖eval (p.pderiv i) a - eval (p.pderiv i) b‖ ≤
      ∑ i, (p.pderiv i).lipschitzBound R * d :=
    Finset.sum_le_sum fun i _ => norm_eval_sub_le _ a b R d ha hb hd hd0
  refine (mul_le_mul h1 (norm_symmetrize_pi_le h) (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => mul_nonneg
      (lipschitzBound_nonneg _ R fun j => (norm_nonneg _).trans (ha j)) hd0)).trans
    (le_of_eq ?_)
  rw [← Finset.sum_mul, derivativeLipschitzBound]
  ring

/-- Operator-norm Lipschitz bound on the derivative, symmetrized-displacement face. -/
theorem norm_derivative_sub_le (p : CompPoly L) (a b : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ) (d : ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i)
    (hd : ∀ i, ‖l1Chebyshev.symmetrize (a i) - l1Chebyshev.symmetrize (b i)‖ ≤ d)
    (hd0 : 0 ≤ d) :
    ‖derivative p a - derivative p b‖ ≤ derivativeLipschitzBound p R * d := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (derivativeLipschitzBound_nonneg p R fun i => (norm_nonneg _).trans (ha i))
      hd0) fun h => ?_
  exact norm_derivative_sub_apply_le p a b R d ha hb hd hd0 h

/-- Operator-norm Lipschitz bound on the derivative, raw-displacement face: the
symmetrization of the displacement costs the explicit factor `2`. -/
theorem norm_derivative_sub_le_of_norm_sub (p : CompPoly L) (a b : Fin L → l1Chebyshev ν)
    (R : Fin L → ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i) :
    ‖derivative p a - derivative p b‖ ≤ (2 * derivativeLipschitzBound p R) * ‖a - b‖ := by
  refine (norm_derivative_sub_le p a b R (2 * ‖a - b‖) ha hb (fun i => ?_) (by positivity)).trans
    (le_of_eq (by ring))
  rw [← l1Chebyshev.symmetrize_CLM_apply, ← l1Chebyshev.symmetrize_CLM_apply, ← map_sub,
    l1Chebyshev.symmetrize_CLM_apply]
  exact (l1Chebyshev.symmetrize_norm_le _).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm (a - b) i) (by norm_num))

/-- Ball-free raw-displacement face: the radii are the symmetrized inputs' own norms. -/
theorem norm_derivative_sub_le_max (p : CompPoly L) (a b : Fin L → l1Chebyshev ν) :
    ‖derivative p a - derivative p b‖ ≤
      (2 * derivativeLipschitzBound p
        (fun i => max ‖l1Chebyshev.symmetrize (a i)‖ ‖l1Chebyshev.symmetrize (b i)‖)) *
        ‖a - b‖ :=
  norm_derivative_sub_le_of_norm_sub p a b _ (fun _ => le_max_left _ _)
    (fun _ => le_max_right _ _)

end MvPolyBridge.CompPoly.Chebyshev
