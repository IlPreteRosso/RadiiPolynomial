import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core

/-!
# Norm and Lipschitz bounds computed from polynomial syntax

`normBound p R` bounds `‖p.evalBanach a‖` when `‖a i‖ ≤ R i`, and `lipschitzBound p R`
is a Lipschitz constant of `a ↦ p.evalBanach a` on that ball with respect to the sup norm
`‖a - b‖` of `Fin L → A`. Both are structural recursions over the syntax tree, valued in
any division ring (`ℚ` for exact certificates, `ℝ` for analytic statements;
`normBound_ratCast` connects the two), and hold in any normed commutative real algebra
whose unit has norm one. No calculus is used; the multiplication case is
`x y - x' y' = (x - x') y' + x (y - y')`.

The bounds are triangle-inequality bounds: they cannot see cancellation inside the
evaluated polynomial, so a certificate that bounds the evaluated element itself in exact
arithmetic (`finsum_bound` on its coefficient array) can be sharper. They are exact for
the constants a radii-polynomial certificate usually states (Example 14.2.1's `K`, `Z₂`
factor and vector-field Lipschitz constant are all equal to the syntactic values).

The vector-field consequence `lipschitzOnWith_evalBanach_pi` gives an explicit Lipschitz
constant on a closed ball of `Fin L → ℝ`, replacing compactness arguments that only produce
an existential constant.

`anchoredBound c ρ p` bounds the difference anchored at a rational centre `c`,
`‖p(c + u) - p(c)‖ ≤ anchoredBound c ρ p · ‖u‖` for `‖u‖ ≤ ρ` (`norm_evalBanach_add_sub_le`,
`norm_evalBanach_sub_center_le`), with the centre values computed exactly by `evalQ`.
-/

namespace MvPolyBridge.CompPoly

variable {L : ℕ}

section Defs

variable {K : Type*} [DivisionRing K]

/-- A bound on `‖p.evalBanach a‖` from bounds `R i ≥ ‖a i‖` on the inputs. -/
@[simp] def normBound : CompPoly L → (Fin L → K) → K
  | .C r, _ => ((|r| : ℚ) : K)
  | .X i, R => R i
  | .add p q, R => p.normBound R + q.normBound R
  | .sub p q, R => p.normBound R + q.normBound R
  | .mul p q, R => p.normBound R * q.normBound R
  | .neg p, R => p.normBound R
  | .smul r p, R => ((|r| : ℚ) : K) * p.normBound R

/-- A Lipschitz constant of `a ↦ p.evalBanach a` on the ball `‖a i‖ ≤ R i`, with respect to
the sup norm `‖a - b‖`. -/
@[simp] def lipschitzBound : CompPoly L → (Fin L → K) → K
  | .C _, _ => 0
  | .X _, _ => 1
  | .add p q, R => p.lipschitzBound R + q.lipschitzBound R
  | .sub p q, R => p.lipschitzBound R + q.lipschitzBound R
  | .mul p q, R => p.lipschitzBound R * q.normBound R + p.normBound R * q.lipschitzBound R
  | .neg p, R => p.lipschitzBound R
  | .smul r p, R => ((|r| : ℚ) : K) * p.lipschitzBound R

/-- Operator-norm constant of the derivative of `a ↦ p.evalBanach a` on the ball
`‖a i‖ ≤ R i`, for a geometry whose inputs enter unsymmetrized (Taylor): the sum of the
syntactic bounds of the formal partials. The Chebyshev constant is twice this
(`CompPoly.Chebyshev.derivativeBound_eq_two_mul`). -/
def derivativeBound (p : CompPoly L) (R : Fin L → K) : K :=
  ∑ i, (p.pderiv i).normBound R

/-- Lipschitz constant of `a ↦ fderiv (evalBanach p) a` on the same ball, same geometry:
the sum of the syntactic Lipschitz constants of the formal partials. -/
def derivativeLipschitzBound (p : CompPoly L) (R : Fin L → K) : K :=
  ∑ i, (p.pderiv i).lipschitzBound R

@[simp] theorem normBound_add_op (p q : CompPoly L) (R : Fin L → K) :
    (p + q).normBound R = p.normBound R + q.normBound R := rfl

@[simp] theorem normBound_sub_op (p q : CompPoly L) (R : Fin L → K) :
    (p - q).normBound R = p.normBound R + q.normBound R := rfl

@[simp] theorem normBound_mul_op (p q : CompPoly L) (R : Fin L → K) :
    (p * q).normBound R = p.normBound R * q.normBound R := rfl

@[simp] theorem normBound_neg_op (p : CompPoly L) (R : Fin L → K) :
    (-p).normBound R = p.normBound R := rfl

@[simp] theorem lipschitzBound_add_op (p q : CompPoly L) (R : Fin L → K) :
    (p + q).lipschitzBound R = p.lipschitzBound R + q.lipschitzBound R := rfl

@[simp] theorem lipschitzBound_sub_op (p q : CompPoly L) (R : Fin L → K) :
    (p - q).lipschitzBound R = p.lipschitzBound R + q.lipschitzBound R := rfl

@[simp] theorem lipschitzBound_mul_op (p q : CompPoly L) (R : Fin L → K) :
    (p * q).lipschitzBound R =
      p.lipschitzBound R * q.normBound R + p.normBound R * q.lipschitzBound R := rfl

@[simp] theorem lipschitzBound_neg_op (p : CompPoly L) (R : Fin L → K) :
    (-p).lipschitzBound R = p.lipschitzBound R := rfl

end Defs

section Cast

variable {K : Type*} [DivisionRing K] [CharZero K]

/-- The exact rational bound casts to the bound computed over `K`. -/
@[norm_cast] theorem normBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((p.normBound R : ℚ) : K) = p.normBound (fun i => (R i : K)) := by
  induction p with
  | C r => simp
  | X i => simp
  | add p q ihp ihq => simp [ihp, ihq]
  | sub p q ihp ihq => simp [ihp, ihq]
  | mul p q ihp ihq => simp [ihp, ihq]
  | neg p ih => simp [ih]
  | smul r p ih => simp [ih]

/-- The exact rational Lipschitz constant casts to the constant computed over `K`. -/
@[norm_cast] theorem lipschitzBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((p.lipschitzBound R : ℚ) : K) = p.lipschitzBound (fun i => (R i : K)) := by
  induction p with
  | C r => simp
  | X i => simp
  | add p q ihp ihq => simp [ihp, ihq]
  | sub p q ihp ihq => simp [ihp, ihq]
  | mul p q ihp ihq => simp [normBound_ratCast, ihp, ihq]
  | neg p ih => simp [ih]
  | smul r p ih => simp [ih]

@[norm_cast] theorem derivativeBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((derivativeBound p R : ℚ) : K) = derivativeBound p (fun i => (R i : K)) := by
  simp [derivativeBound, normBound_ratCast]

@[norm_cast] theorem derivativeLipschitzBound_ratCast (p : CompPoly L) (R : Fin L → ℚ) :
    ((derivativeLipschitzBound p R : ℚ) : K) =
      derivativeLipschitzBound p (fun i => (R i : K)) := by
  simp [derivativeLipschitzBound, lipschitzBound_ratCast]

end Cast

/-- The derivative Lipschitz constant of a univariate polynomial is the Lipschitz constant of
its formal derivative. General in `P`, `K`. -/
theorem derivativeLipschitzBound_one {K : Type*} [DivisionRing K] (P : CompPoly 1)
    (R : Fin 1 → K) : P.derivativeLipschitzBound R = (P.pderiv 0).lipschitzBound R := by
  simp [CompPoly.derivativeLipschitzBound]

section Order

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem normBound_nonneg (p : CompPoly L) (R : Fin L → K) (hR : ∀ i, 0 ≤ R i) :
    0 ≤ p.normBound R := by
  induction p with
  | C r => exact Rat.cast_nonneg.mpr (abs_nonneg r)
  | X i => exact hR i
  | add p q ihp ihq => exact add_nonneg ihp ihq
  | sub p q ihp ihq => exact add_nonneg ihp ihq
  | mul p q ihp ihq => exact mul_nonneg ihp ihq
  | neg p ih => exact ih
  | smul r p ih => exact mul_nonneg (Rat.cast_nonneg.mpr (abs_nonneg r)) ih

theorem lipschitzBound_nonneg (p : CompPoly L) (R : Fin L → K) (hR : ∀ i, 0 ≤ R i) :
    0 ≤ p.lipschitzBound R := by
  induction p with
  | C r => exact le_rfl
  | X i => exact zero_le_one
  | add p q ihp ihq => exact add_nonneg ihp ihq
  | sub p q ihp ihq => exact add_nonneg ihp ihq
  | mul p q ihp ihq =>
      exact add_nonneg (mul_nonneg ihp (normBound_nonneg q R hR))
        (mul_nonneg (normBound_nonneg p R hR) ihq)
  | neg p ih => exact ih
  | smul r p ih => exact mul_nonneg (Rat.cast_nonneg.mpr (abs_nonneg r)) ih

theorem derivativeBound_nonneg (p : CompPoly L) (R : Fin L → K) (hR : ∀ i, 0 ≤ R i) :
    0 ≤ derivativeBound p R :=
  Finset.sum_nonneg fun _ _ => normBound_nonneg _ R hR

theorem derivativeLipschitzBound_nonneg (p : CompPoly L) (R : Fin L → K)
    (hR : ∀ i, 0 ≤ R i) : 0 ≤ derivativeLipschitzBound p R :=
  Finset.sum_nonneg fun _ _ => lipschitzBound_nonneg _ R hR

end Order

/-- The syntactic norm bound is monotone in nonnegative radii. -/
theorem normBound_mono (p : CompPoly L) {R S : Fin L → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hRS : ∀ i, R i ≤ S i) : p.normBound R ≤ p.normBound S := by
  have hS : ∀ i, 0 ≤ S i := fun i => (hR i).trans (hRS i)
  induction p with
  | C r => exact le_rfl
  | X i => exact hRS i
  | add p q ihp ihq => exact add_le_add ihp ihq
  | sub p q ihp ihq => exact add_le_add ihp ihq
  | mul p q ihp ihq =>
      exact mul_le_mul ihp ihq (CompPoly.normBound_nonneg q R hR)
        (CompPoly.normBound_nonneg p S hS)
  | neg p ih => exact ih
  | smul r p ih => exact mul_le_mul_of_nonneg_left ih (Rat.cast_nonneg.mpr (abs_nonneg r))

/-- The syntactic Lipschitz constant is monotone in nonnegative radii. -/
theorem lipschitzBound_mono (p : CompPoly L) {R S : Fin L → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hRS : ∀ i, R i ≤ S i) : p.lipschitzBound R ≤ p.lipschitzBound S := by
  have hS : ∀ i, 0 ≤ S i := fun i => (hR i).trans (hRS i)
  induction p with
  | C r => exact le_rfl
  | X _ => exact le_rfl
  | add p q ihp ihq => exact add_le_add ihp ihq
  | sub p q ihp ihq => exact add_le_add ihp ihq
  | mul p q ihp ihq =>
      exact add_le_add
        (mul_le_mul ihp (normBound_mono q hR hRS) (CompPoly.normBound_nonneg q R hR)
          (CompPoly.lipschitzBound_nonneg p S hS))
        (mul_le_mul (normBound_mono p hR hRS) ihq (CompPoly.lipschitzBound_nonneg q R hR)
          (CompPoly.normBound_nonneg p S hS))
  | neg p ih => exact ih
  | smul r p ih => exact mul_le_mul_of_nonneg_left ih (Rat.cast_nonneg.mpr (abs_nonneg r))

/-- The derivative Lipschitz constant is monotone in nonnegative radii. -/
theorem derivativeLipschitzBound_mono (p : CompPoly L) {R S : Fin L → ℝ}
    (hR : ∀ i, 0 ≤ R i) (hRS : ∀ i, R i ≤ S i) :
    p.derivativeLipschitzBound R ≤ p.derivativeLipschitzBound S :=
  Finset.sum_le_sum fun _ _ => lipschitzBound_mono _ hR hRS

section SumMul

variable {A ι : Type*} [NonUnitalSeminormedRing A] [Fintype ι]

/-- `‖∑ᵢ fᵢ * hᵢ‖ ≤ (∑ᵢ ‖fᵢ‖) * ‖h‖` for a sup-normed direction `h : ι → A`: triangle
inequality, submultiplicativity, and `‖hᵢ‖ ≤ ‖h‖`. -/
theorem norm_sum_mul_pi_le (f h : ι → A) :
    ‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖ := by
  refine ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => norm_mul_le _ _)).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _)

end SumMul

section Normed

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A]

/-- The syntactic norm bound is a bound on the completed evaluation. -/
theorem norm_evalBanach_le (p : CompPoly L) (a : Fin L → A) (R : Fin L → ℝ)
    (ha : ∀ i, ‖a i‖ ≤ R i) :
    ‖p.evalBanach a‖ ≤ p.normBound R := by
  induction p with
  | C r =>
      simp only [evalBanach, normBound, Rat.cast_abs]
      rw [norm_algebraMap', Real.norm_eq_abs]
  | X i => simpa [evalBanach] using ha i
  | add p q ihp ihq =>
      simp only [evalBanach, normBound]
      exact (norm_add_le _ _).trans (add_le_add ihp ihq)
  | sub p q ihp ihq =>
      simp only [evalBanach, normBound]
      exact (norm_sub_le _ _).trans (add_le_add ihp ihq)
  | mul p q ihp ihq =>
      simp only [evalBanach, normBound]
      exact (norm_mul_le _ _).trans
        (mul_le_mul ihp ihq (norm_nonneg _) ((norm_nonneg _).trans ihp))
  | neg p ih => simpa [evalBanach] using ih
  | smul r p ih =>
      simp only [evalBanach, normBound, Rat.cast_abs]
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg _)

/-- The syntactic Lipschitz constant controls the difference of two completed evaluations
whose inputs stay in the ball `‖·‖ ≤ R i`, with respect to the sup norm of the inputs. -/
theorem norm_evalBanach_sub_le (p : CompPoly L) (a b : Fin L → A) (R : Fin L → ℝ)
    (ha : ∀ i, ‖a i‖ ≤ R i) (hb : ∀ i, ‖b i‖ ≤ R i) :
    ‖p.evalBanach a - p.evalBanach b‖ ≤ p.lipschitzBound R * ‖a - b‖ := by
  have hR : ∀ i, 0 ≤ R i := fun i => (norm_nonneg _).trans (ha i)
  induction p with
  | C r => simp [evalBanach]
  | X i => simpa [evalBanach] using norm_le_pi_norm (a - b) i
  | add p q ihp ihq =>
      simp only [evalBanach, lipschitzBound]
      rw [add_sub_add_comm, add_mul]
      exact (norm_add_le _ _).trans (add_le_add ihp ihq)
  | sub p q ihp ihq =>
      simp only [evalBanach, lipschitzBound]
      rw [sub_sub_sub_comm, add_mul]
      exact (norm_sub_le _ _).trans (add_le_add ihp ihq)
  | mul p q ihp ihq =>
      simp only [evalBanach, lipschitzBound]
      have hsplit : p.evalBanach a * q.evalBanach a - p.evalBanach b * q.evalBanach b
          = (p.evalBanach a - p.evalBanach b) * q.evalBanach b
            + p.evalBanach a * (q.evalBanach a - q.evalBanach b) := by ring
      rw [hsplit, add_mul]
      have hl : (0 : ℝ) ≤ p.lipschitzBound R := lipschitzBound_nonneg p R hR
      have hn : (0 : ℝ) ≤ p.normBound R := normBound_nonneg p R hR
      have h1 := mul_le_mul ihp (norm_evalBanach_le q b R hb) (norm_nonneg _)
        (mul_nonneg hl (norm_nonneg _))
      have h2 := mul_le_mul (norm_evalBanach_le p a R ha) ihq (norm_nonneg _) hn
      rw [mul_right_comm] at h1
      rw [← mul_assoc] at h2
      exact (norm_add_le _ _).trans
        ((add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans (add_le_add h1 h2))
  | neg p ih =>
      simp only [evalBanach, lipschitzBound]
      rw [neg_sub_neg, norm_sub_rev]
      exact ih
  | smul r p ih =>
      simp only [evalBanach, lipschitzBound, Rat.cast_abs]
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg _)

/-- Coordinatewise face: inputs differing by at most `d` in every coordinate. -/
theorem norm_evalBanach_sub_le_of_forall_le (p : CompPoly L) (a b : Fin L → A)
    (R : Fin L → ℝ) (d : ℝ) (ha : ∀ i, ‖a i‖ ≤ R i) (hb : ∀ i, ‖b i‖ ≤ R i)
    (hd : ∀ i, ‖a i - b i‖ ≤ d) (hd0 : 0 ≤ d) :
    ‖p.evalBanach a - p.evalBanach b‖ ≤ p.lipschitzBound R * d :=
  (norm_evalBanach_sub_le p a b R ha hb).trans (mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg hd0).mpr fun i => hd i)
    (lipschitzBound_nonneg p R fun i => (norm_nonneg _).trans (ha i)))

/-- Ball-free face: the radii are the inputs' own norms. -/
theorem norm_evalBanach_sub_le_max (p : CompPoly L) (a b : Fin L → A) :
    ‖p.evalBanach a - p.evalBanach b‖ ≤
      p.lipschitzBound (fun i => max ‖a i‖ ‖b i‖) * ‖a - b‖ :=
  norm_evalBanach_sub_le p a b _ (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

end Normed

section Anchored

/-! Centre-anchored difference bound. For `‖u‖ ≤ ρ`, `anchoredBound c ρ p` bounds the difference
quotient anchored at the rational centre `c` (embedded by `ratMap`):
`‖p(c + u) - p(c)‖ ≤ anchoredBound c ρ p · ‖u‖`. It is not a Lipschitz constant on the ball (for
`p = X·X`, `c = 0` it is `ρ`, while `x ↦ x²` has Lipschitz constant `2ρ` on the ball). The centre
values enter through `evalQ`, so the bound is computed in exact rational arithmetic. Holds in any
normed commutative real algebra whose unit has norm one. -/

/-- Centre-anchored difference bound of `p` at the rational centre `c`, for displacements of norm at
most `ρ`. -/
def anchoredBound (c : Fin L → ℚ) (ρ : ℚ) : CompPoly L → ℚ
  | .C _ => 0
  | .X _ => 1
  | .add p q => anchoredBound c ρ p + anchoredBound c ρ q
  | .sub p q => anchoredBound c ρ p + anchoredBound c ρ q
  | .mul p q => anchoredBound c ρ p * |evalQ q c| + |evalQ p c| * anchoredBound c ρ q +
      anchoredBound c ρ p * anchoredBound c ρ q * ρ
  | .neg p => anchoredBound c ρ p
  | .smul r p => |r| * anchoredBound c ρ p

theorem anchoredBound_nonneg (c : Fin L → ℚ) {ρ : ℚ} (hρ : 0 ≤ ρ) (p : CompPoly L) :
    0 ≤ anchoredBound c ρ p := by
  induction p with
  | C _ => exact le_rfl
  | X _ => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    exact add_nonneg (add_nonneg (mul_nonneg hp (abs_nonneg _)) (mul_nonneg (abs_nonneg _) hq))
      (mul_nonneg (mul_nonneg hp hq) hρ)
  | neg p hp => exact hp
  | smul r p hp => exact mul_nonneg (abs_nonneg r) hp

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A]

theorem norm_evalBanach_center (p : CompPoly L) (c : Fin L → ℚ) :
    ‖p.evalBanach (fun i => ratMap A (c i))‖ = |((evalQ p c : ℚ) : ℝ)| := by
  rw [evalBanach_ratMap, norm_ratMap]

theorem norm_evalBanach_add_sub_le (p : CompPoly L) (c : Fin L → ℚ) (ρ : ℚ)
    (u : Fin L → A) (hu : ‖u‖ ≤ ρ) :
    ‖p.evalBanach (fun i => ratMap A (c i) + u i) -
        p.evalBanach (fun i => ratMap A (c i))‖ ≤
      (anchoredBound c ρ p : ℝ) * ‖u‖ := by
  have hρ : (0 : ℚ) ≤ ρ := by exact_mod_cast (norm_nonneg u).trans hu
  induction p with
  | C r => simp [CompPoly.evalBanach, anchoredBound]
  | X i => simpa [CompPoly.evalBanach, anchoredBound] using norm_le_pi_norm u i
  | add p q ihp ihq =>
    simp only [CompPoly.evalBanach, anchoredBound, Rat.cast_add]
    rw [add_sub_add_comm, add_mul]
    exact (norm_add_le _ _).trans (add_le_add ihp ihq)
  | sub p q ihp ihq =>
    simp only [CompPoly.evalBanach, anchoredBound, Rat.cast_add]
    rw [sub_sub_sub_comm, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add ihp ihq)
  | mul p q ihp ihq =>
    simp only [CompPoly.evalBanach, anchoredBound]
    set P := p.evalBanach (fun i => ratMap A (c i) + u i)
    set P₀ := p.evalBanach (fun i => ratMap A (c i))
    set Q := q.evalBanach (fun i => ratMap A (c i) + u i)
    set Q₀ := q.evalBanach (fun i => ratMap A (c i))
    have hP₀ : ‖P₀‖ = |((evalQ p c : ℚ) : ℝ)| := norm_evalBanach_center p c
    have hQ₀ : ‖Q₀‖ = |((evalQ q c : ℚ) : ℝ)| := norm_evalBanach_center q c
    have hAp : (0 : ℝ) ≤ anchoredBound c ρ p := by exact_mod_cast anchoredBound_nonneg c hρ p
    have hAq : (0 : ℝ) ≤ anchoredBound c ρ q := by exact_mod_cast anchoredBound_nonneg c hρ q
    have hu' : ‖u‖ ≤ (ρ : ℝ) := hu
    have hsplit : P * Q - P₀ * Q₀ = (P - P₀) * (Q - Q₀) + (P - P₀) * Q₀ + P₀ * (Q - Q₀) := by
      ring
    rw [hsplit]
    have h1 : ‖(P - P₀) * (Q - Q₀)‖ ≤
        (anchoredBound c ρ p : ℝ) * ‖u‖ * ((anchoredBound c ρ q : ℝ) * ‖u‖) :=
      (norm_mul_le _ _).trans (mul_le_mul ihp ihq (norm_nonneg _)
        (mul_nonneg hAp (norm_nonneg _)))
    have h2 : ‖(P - P₀) * Q₀‖ ≤ (anchoredBound c ρ p : ℝ) * ‖u‖ * ‖Q₀‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ihp (norm_nonneg _))
    have h3 : ‖P₀ * (Q - Q₀)‖ ≤ ‖P₀‖ * ((anchoredBound c ρ q : ℝ) * ‖u‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ihq (norm_nonneg _))
    have h4 : (anchoredBound c ρ p : ℝ) * ‖u‖ * ((anchoredBound c ρ q : ℝ) * ‖u‖) ≤
        (anchoredBound c ρ p : ℝ) * (anchoredBound c ρ q : ℝ) * ρ * ‖u‖ := by
      have := mul_le_mul_of_nonneg_left hu'
        (mul_nonneg (mul_nonneg hAp hAq) (norm_nonneg u))
      nlinarith [this]
    rw [hP₀] at h3
    rw [hQ₀] at h2
    push_cast
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    nlinarith [h1, h2, h3, h4]
  | neg p ih =>
    simp only [CompPoly.evalBanach, anchoredBound]
    rw [neg_sub_neg, norm_sub_rev]
    exact ih
  | smul r p ih =>
    simp only [CompPoly.evalBanach, anchoredBound, Rat.cast_mul, Rat.cast_abs]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (abs_nonneg _)

/-- Anchored difference bound at a point `x` of the ball around the rational centre `c`. -/
theorem norm_evalBanach_sub_center_le (p : CompPoly L) (c : Fin L → ℚ) (ρ : ℚ)
    (x : Fin L → A) (hx : ‖x - fun i => ratMap A (c i)‖ ≤ ρ) :
    ‖p.evalBanach x - p.evalBanach (fun i => ratMap A (c i))‖ ≤
      (anchoredBound c ρ p : ℝ) * ‖x - fun i => ratMap A (c i)‖ := by
  have h := norm_evalBanach_add_sub_le p c ρ _ hx
  have hx' : (fun i => ratMap A (c i) + (x - fun i => ratMap A (c i)) i) = x :=
    funext fun i => by simp
  rwa [hx'] at h

end Anchored

section Univariate

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- Ball Lipschitz bound of a univariate evaluation from the syntactic constant.
General in `P`, `𝔸`, `R`. -/
theorem norm_evalBanach_one_sub_le [NormOneClass 𝔸] (P : CompPoly 1) (x y : 𝔸) (R : ℝ)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖P.evalBanach (fun _ => x) - P.evalBanach (fun _ => y)‖ ≤
      P.lipschitzBound (fun _ => R) * ‖x - y‖ := by
  have h := CompPoly.norm_evalBanach_sub_le P (fun _ : Fin 1 => x) (fun _ => y) (fun _ => R)
    (fun _ => hx) (fun _ => hy)
  have hn : ‖(fun _ : Fin 1 => x) - (fun _ => y)‖ = ‖x - y‖ :=
    pi_norm_const (ι := Fin 1) (x - y)
  rwa [hn] at h

end Univariate

section VectorField

open Metric

/-- A scalar polynomial vector field on `Fin L → ℝ` is Lipschitz on the closed ball of radius
`R` with the syntactic constant `lipschitzBound p (fun _ => R)`. -/
theorem lipschitzOnWith_evalBanach (p : CompPoly L) (R : ℝ) {K : NNReal}
    (hK : p.lipschitzBound (fun _ => R) ≤ (K : ℝ)) :
    LipschitzOnWith K (fun u : Fin L → ℝ => p.evalBanach u) (closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  have hbound : ∀ w ∈ closedBall (0 : Fin L → ℝ) R, ∀ l : Fin L, ‖w l‖ ≤ R := by
    intro w hw l
    have h := mem_closedBall.mp hw
    rw [dist_zero_right] at h
    exact (norm_le_pi_norm w l).trans h
  rw [dist_eq_norm, dist_eq_norm]
  exact (norm_evalBanach_sub_le p u v (fun _ => R) (hbound u hu) (hbound v hv)).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

/-- A polynomial system on `Fin L → ℝ` is Lipschitz on the closed ball of radius `R` with
any constant dominating every component's syntactic constant. -/
theorem lipschitzOnWith_evalBanach_pi {L' : ℕ} (f : Fin L' → CompPoly L) (R : ℝ)
    {K : NNReal} (hK : ∀ l, (f l).lipschitzBound (fun _ => R) ≤ (K : ℝ)) :
    LipschitzOnWith K (fun u : Fin L → ℝ => fun l => (f l).evalBanach u) (closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro l
  exact (lipschitzOnWith_evalBanach (f l) R (hK l)).dist_le_mul u hu v hv

end VectorField

end MvPolyBridge.CompPoly
