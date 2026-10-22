import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Interval.Set.OrdConnectedComponent


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap


/-!
# General Radii Polynomial Theorem

This file generalizes the radii polynomial approach to maps `f : E → F` between possibly
different spaces: a real Banach space `E` and a real normed space `F`. This corresponds to
Theorem 7.6.2 in the informal proof.

## Spaces

The domain `E` is a real Banach space (`NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace`);
completeness is used only by the fixed-point argument (Neumann series, contraction mapping) and
is declared section-locally where it is used. The codomain `F` is a real normed space
(`NormedAddCommGroup`, `NormedSpace ℝ`); no statement of this file assumes completeness of `F`.

## Local layers and faces

Beside the global theorem, the file carries the local forms, with derivative data on the
closed ball of the certified radius only (section `LocalTheorems`); the global theorem is
proved as one application of its local form. It also carries the finite-dimensional
Neumann rungs (section `NeumannSeries`), the radii polynomials and the implication
`p(r₀) < 0 ⟹ Z(r₀) < 1` (sections `RadiiPolynomialDefinitions` and
`RadiiPolynomialImplications`), and the finite-dimensional face with its output record
`Enclosure` (section `FiniteDimensionalFace`).
-/

namespace RadiiPolynomial

-- Domain E (complete where a section needs the fixed-point argument) and codomain F (normed only)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Identity operators on each space
abbrev I_E := ContinuousLinearMap.id ℝ E


section NeumannSeries
/-!
## Neumann Series and Operator Invertibility

The Neumann series results establish when operators close to the identity are invertible.
These results apply to operators on a single space (E →L[ℝ] E or F →L[ℝ] F).

In the general E to F setting, we use these results for the composition AA† : E →L[ℝ] E,
which must be close to the identity I_E for the method to work.

Key insight: If ‖I - B‖ < 1 for an operator B : E →L[ℝ] E, then B is invertible.
This is the Neumann series theorem, already available in Mathlib.
-/

variable [CompleteSpace E]

/-- If an operator is close to identity, it is a unit (invertible in the multiplicative sense).
    This is a direct application of Mathlib's `isUnit_one_sub_of_norm_lt_one`. -/
theorem isUnit_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  IsUnit B := by
  have : B = I_E - (I_E - B) := by
    simp only [sub_sub_cancel]
  rw [this]
  exact isUnit_one_sub_of_norm_lt_one h

/-- Alternative formulation: explicit existence of a two-sided inverse -/
theorem invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E), B * B_inv = 1 ∧ B_inv * B = 1 := by
  have hu := isUnit_of_norm_sub_id_lt_one h
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- Composition form: useful for working with .comp notation -/
lemma invertible_comp_form {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E), B.comp B_inv = I_E ∧ B_inv.comp B = I_E :=
  invertible_of_norm_sub_id_lt_one h

/-- In finite dimension, `E →L[ℝ] E` is Dedekind-finite (`A B = 1 → B A = 1`): transported from
`Module.End ℝ E` along the algebra equivalence `Module.End.toContinuousLinearMap E`. -/
private theorem isDedekindFiniteMonoid_clm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : IsDedekindFiniteMonoid (E →L[ℝ] E) :=
  (MulEquivClass.isDedekindFiniteMonoid_iff (Module.End.toContinuousLinearMap E)).mp inferInstance

/-- Finite-dimensional Neumann rung: `‖I - A B‖ < 1` makes `A` injective (`A B` is a unit, so
`A` is a unit by Dedekind-finiteness). -/
theorem injective_left_of_norm_id_sub_comp_lt_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A B : E →L[ℝ] E}
    (h : ‖I_E - A.comp B‖ < 1) : Function.Injective A := by
  have := isDedekindFiniteMonoid_clm (E := E)
  obtain ⟨u, rfl⟩ := isUnit_of_mul_isUnit_left (isUnit_of_norm_sub_id_lt_one h)
  exact (ContinuousLinearEquiv.unitsEquiv ℝ E u).injective

/-- Finite-dimensional Neumann rung: `‖I - A B‖ < 1` makes `B` a unit (`A B` is a unit and
`E →L[ℝ] E` is Dedekind-finite). -/
theorem isUnit_right_of_norm_id_sub_comp_lt_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A B : E →L[ℝ] E}
    (h : ‖I_E - A.comp B‖ < 1) : IsUnit B := by
  have := isDedekindFiniteMonoid_clm (E := E)
  exact isUnit_of_mul_isUnit_right (isUnit_of_norm_sub_id_lt_one h)

/-- Finite-dimensional Neumann rung: `‖I - A B‖ < 1` makes `A` a unit (the left twin of
`isUnit_right_of_norm_id_sub_comp_lt_one`). -/
theorem isUnit_left_of_norm_id_sub_comp_lt_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A B : E →L[ℝ] E}
    (h : ‖I_E - A.comp B‖ < 1) : IsUnit A := by
  have := isDedekindFiniteMonoid_clm (E := E)
  exact isUnit_of_mul_isUnit_left (isUnit_of_norm_sub_id_lt_one h)

end NeumannSeries



section NewtonLikeOperator
/-!
## Newton-Like Operator for E to F Maps

For a function f : E → F and an approximate inverse A : F →L[ℝ] E, we define:
  T(x) = x - A(f(x))

This operator T : E → E transforms the zero-finding problem f(x) = 0 into a
fixed point problem T(x) = x.

Key differences from E to E case:
- f : E → F (not E → E)
- A : F →L[ℝ] E (approximate inverse, goes "backwards")
- T : E → E (the Newton operator still maps E to itself)
-/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Newton-like operator T(x) = x - Af(x) for maps from E to F -/
def NewtonLikeMap (A : F →L[ℝ] E) (f : E → F) (x : E) : E := x - A (f x)


end NewtonLikeOperator



section Proposition_2_3_1
/-!
## Fixed Points ⟺ Zeros (Proposition 2.3.1)

This fundamental equivalence holds in the general E to F setting:
  T(x) = x  ⟺  f(x) = 0

when A : F →L[ℝ] E is injective.

The proof is **identical** to the E to E case - injectivity of A is the key requirement,
not invertibility.
-/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Proposition 2.3.1**: Fixed points of Newton operator ⟺ Zeros of f

    Let T(x) = x - Af(x) be the Newton-like operator where:
    - f : E → F
    - A : F →L[ℝ] E is an injective linear map

    Then: T(x) = x  ⟺  f(x) = 0

    This fundamental equivalence allows us to:
    - Convert zero-finding problems (f(x) = 0) to fixed point problems (T(x) = x)
    - Apply fixed point theorems (like Banach's) to find zeros of f -/
lemma fixedPoint_injective_iff_zero
  {f : E → F} {A : F →L[ℝ] E}
  (hA : Function.Injective A)
  (x : E) :
  NewtonLikeMap A f x = x ↔ f x = 0 := by
  unfold NewtonLikeMap
  simp only [sub_eq_self, map_eq_zero_iff A hA]

end Proposition_2_3_1



section RadiiPolynomialDefinitions
/-!
## Radii Polynomial Definitions

The radii polynomial approach uses polynomial inequalities to verify contraction conditions.

For the general E to F case (Theorem 7.6.2), we have an additional parameter Z₁:
  p(r) = Z₂(r)r² - (1 - Z₀ - Z₁)r + Y₀

Where:
- Y₀: bound on ‖A(f(x̄))‖ (initial defect)
- Z₀: bound on ‖I_E - AA†‖ (how close AA† is to identity)
- Z₁: bound on ‖A[A† - Df(x̄)]‖ (how well A† approximates Df(x̄))
- Z₂(r): Z₂(r)·r bounds ‖A[Df(c) - Df(x̄)]‖ for c ∈ B̄ᵣ(x̄) (Lipschitz-type bound)

The simpler case (when E = F and A† = Df(x̄)) has Z₁ = 0.
-/

/-- The general radii polynomial with Z₁ parameter (Theorem 7.6.2, equation 7.34)

    p(r) = Z₂(r)r² - (1 - Z₀ - Z₁)r + Y₀

    This is used when we have:
    - f : E → F with E and F potentially different
    - A : F →L[ℝ] E (approximate inverse)
    - A† : E →L[ℝ] F (approximate derivative) -/
def generalRadiiPolynomial (Y₀ Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₂ r * r^2 - (1 - Z₀ - Z₁) * r + Y₀

/-- Combined bound Z(r) = Z₀ + Z₁ + Z₂(r)·r

    This represents the total bound on ‖DT(c)‖ for c ∈ B̄ᵣ(x̄).
    See equation (7.35) in the proof of Theorem 7.6.2. -/
def Z_bound_general (Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₀ + Z₁ + Z₂ r * r

/-- Alternative formulation: p(r) = (Z(r) - 1)r + Y₀

    This connects the polynomial form to the contraction constant bound.
    When p(r₀) < 0 with Y₀ ≥ 0 and r₀ > 0, we get Z(r₀) < 1
    (`general_radii_poly_neg_implies_Z_lt_one`), which means T is a contraction. -/
lemma generalRadiiPolynomial_alt_form (Y₀ Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r = (Z_bound_general Z₀ Z₁ Z₂ r - 1) * r + Y₀ := by
  unfold generalRadiiPolynomial Z_bound_general
  ring

/-- Simple radii polynomial (when Z₁ = 0, corresponds to Theorem 2.4.1/2.4.2)

    This is the special case Z₁ = 0 (`radiiPolynomial_is_special_case`), e.g. when
    A† = Df(x̄) exactly.

    p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀ -/
def radiiPolynomial (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₂ r * r^2 - (1 - Z₀) * r + Y₀


/-- Simple radii polynomial as special case of general one -/
lemma radiiPolynomial_is_special_case (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  radiiPolynomial Y₀ Z₀ Z₂ r = generalRadiiPolynomial Y₀ Z₀ 0 Z₂ r := by
  unfold radiiPolynomial generalRadiiPolynomial
  ring


/-- Simple polynomial for fixed point theorem (used in Theorem 2.4.1) -/
def simpleRadiiPolynomial (Y₀ : ℝ) (Z : ℝ → ℝ) (r : ℝ) : ℝ :=
  (Z r - 1) * r + Y₀




end RadiiPolynomialDefinitions



section RadiiPolynomialImplications
/-!
## Key Implications of Radii Polynomial Negativity

If p(r₀) < 0, this implies the contraction constant Z(r₀) < 1,
which is the key requirement for the Banach fixed point theorem.
-/

/-- If the general radii polynomial is negative, then Z(r₀) < 1 -/
lemma general_radii_poly_neg_implies_Z_lt_one
  {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_poly : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
  Z_bound_general Z₀ Z₁ Z₂ r₀ < 1 := by
  rw [generalRadiiPolynomial_alt_form] at h_poly; nlinarith


/-- Simple polynomial version -/
lemma simple_radii_poly_neg_implies_Z_lt_one
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_poly : simpleRadiiPolynomial Y₀ Z r₀ < 0) :
  Z r₀ < 1 := by
  unfold simpleRadiiPolynomial at h_poly; nlinarith





end RadiiPolynomialImplications



section OperatorBounds
/-!
## Operator Bounds for Newton-Like Map

In the general E to F setting, the derivative of the Newton-like map is DT(x) = I_E - A ∘ Df(x).
The derivative-free three-term split `norm_id_sub_comp_le_Z_bound` bounds `‖I - A Q‖` by
`Z₀ + Z₁ + W` from `‖I - A A†‖ ≤ Z₀`, `‖A (A† - P)‖ ≤ Z₁` and `‖A (Q - P)‖ ≤ W`.
-/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative-free three-term split:
`I - A Q = (I - A A†) + A (A† - P) - A (Q - P)`, whence `‖I - A Q‖ ≤ Z₀ + Z₁ + W`. -/
theorem norm_id_sub_comp_le_Z_bound
    {A : F →L[ℝ] E} {A_dagger P Q : E →L[ℝ] F} {Z₀ Z₁ W : ℝ}
    (h_Z₀ : ‖ContinuousLinearMap.id ℝ E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - P)‖ ≤ Z₁) (h_W : ‖A.comp (Q - P)‖ ≤ W) :
    ‖ContinuousLinearMap.id ℝ E - A.comp Q‖ ≤ Z₀ + Z₁ + W := by
  have hsplit : ContinuousLinearMap.id ℝ E - A.comp Q =
      (ContinuousLinearMap.id ℝ E - A.comp A_dagger) + A.comp (A_dagger - P) - A.comp (Q - P) := by
    simp only [ContinuousLinearMap.comp_sub]; abel
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h_Z₀ h_Z₁)) h_W)





end OperatorBounds

section LocalTheorems
/-!
## Local layers: derivative data on the closed ball only

The global theorem `general_radii_polynomial_theorem` of a later section assumes
`Differentiable ℝ f` on the whole space. The local forms below need derivative data
`HasFDerivWithinAt f (Df x) (closedBall x̄ r₀) x` on the closed ball of the certified radius only,
and the global theorem is one application of `general_radii_polynomial_theorem_local`.
The local forms
`radii_polynomial_theorem_of_norm_id_sub_le_local` and
`general_radii_polynomial_theorem_nondegenerate_local` also locate the zero in the open ball and
return the invertibility of `Df x̃`.
-/

variable [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Invertibility of `D : E →L[ℝ] F` from an injective `A : F →L[ℝ] E` with `‖I - A D‖ < 1`:
`A D` is invertible (Neumann series), so `(A D)⁻¹ A` is a two-sided inverse of `D`. -/
theorem isInvertible_of_injective_of_norm_id_sub_comp_lt_one
    {A : F →L[ℝ] E} {D : E →L[ℝ] F} (hA : Function.Injective A)
    (h : ‖I_E - A.comp D‖ < 1) : D.IsInvertible := by
  obtain ⟨U, hU₁, hU₂⟩ := invertible_comp_form h
  have hL : Function.LeftInverse (U.comp A) D := fun x => by
    simpa using congrArg (fun L : E →L[ℝ] E => L x) hU₂
  have hR : Function.RightInverse (U.comp A) D := fun y => hA <| by
    simpa using congrArg (fun L : E →L[ℝ] E => L (A y)) hU₁
  exact ⟨ContinuousLinearEquiv.equivOfInverse D (U.comp A) hL hR, rfl⟩

/-- **Local fixed-point theorem** (local form of Theorem 7.6.1). Let `T : E → E` have derivative
`DT x` within the closed ball `B̄_{r₀}(x̄)` at every point of it, with `‖T x̄ - x̄‖ ≤ Y₀`,
`‖DT c‖ ≤ Z(r₀)` on the ball and `(Z(r₀) - 1) r₀ + Y₀ < 0`. Then `T` has a fixed point `x̃` in
the open ball, and it is the only fixed point in the closed ball. -/
theorem general_fixed_point_theorem_local
    {T : E → E} {DT : E → E →L[ℝ] E} {xBar : E} {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hT : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt T (DT x) (closedBall xBar r₀) x)
    (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)
    (h_bound_Z : ∀ c ∈ closedBall xBar r₀, ‖DT c‖ ≤ Z r₀)
    (h_radii : simpleRadiiPolynomial Y₀ Z r₀ < 0) :
    ∃ xTilde ∈ ball xBar r₀, T xTilde = xTilde ∧
      ∀ z ∈ closedBall xBar r₀, T z = z → z = xTilde := by
  have hY₀ : 0 ≤ Y₀ := (norm_nonneg _).trans h_bound_Y
  have hZ1 : Z r₀ < 1 := simple_radii_poly_neg_implies_Z_lt_one hY₀ hr₀ h_radii
  have hxBar : xBar ∈ closedBall xBar r₀ := mem_closedBall_self hr₀.le
  have hZ0 : 0 ≤ Z r₀ := (norm_nonneg _).trans (h_bound_Z xBar hxBar)
  have hlt : Z r₀ * r₀ + Y₀ < r₀ := by unfold simpleRadiiPolynomial at h_radii; linarith
  -- contraction on the closed ball (mean-value step with within-derivatives)
  have hlip : ∀ x ∈ closedBall xBar r₀, ∀ y ∈ closedBall xBar r₀,
      dist (T x) (T y) ≤ Z r₀ * dist x y := fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hT h_bound_Z
      (convex_closedBall xBar r₀) hy hx
  -- T maps the closed ball into the open ball
  have hball : ∀ x ∈ closedBall xBar r₀, T x ∈ ball xBar r₀ := fun x hx => by
    rw [mem_ball, dist_eq_norm]
    have h1 := hlip x hx xBar hxBar
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖x - xBar‖ ≤ r₀ := by rw [← dist_eq_norm]; exact hx
    exact ((norm_sub_le_norm_sub_add_norm_sub _ (T xBar) _).trans
      (add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 hZ0)) h_bound_Y)).trans_lt hlt
  have h_maps : Set.MapsTo T (closedBall xBar r₀) (closedBall xBar r₀) := fun x hx =>
    ball_subset_closedBall (hball x hx)
  have h_contr : ContractingWith (Real.toNNReal (Z r₀)) (h_maps.restrict T _ _) :=
    ⟨Real.toNNReal_lt_one.mpr hZ1, LipschitzWith.of_dist_le' fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      hlip x hx y hy⟩
  obtain ⟨x, hx, hfix, -⟩ :=
    h_contr.exists_fixedPoint' isClosed_closedBall.isComplete h_maps hxBar (edist_ne_top _ _)
  refine ⟨x, hfix.eq ▸ hball x hx, hfix.eq, fun z hz hzf => ?_⟩
  have hz' : Function.IsFixedPt (h_maps.restrict T _ _) ⟨z, hz⟩ := Subtype.ext hzf
  have hx' : Function.IsFixedPt (h_maps.restrict T _ _) ⟨x, hx⟩ := Subtype.ext hfix.eq
  exact congrArg Subtype.val (h_contr.fixedPoint_unique' hz' hx')

/-- **Local radii polynomial theorem, single-`Z` form.** With derivative data `Df` of
`f : E → F` within the closed ball `B̄_{r₀}(x̄)`, an injective `A : F →L[ℝ] E`,
`‖A f(x̄)‖ ≤ Y₀`, `‖I - A Df(c)‖ ≤ Z(r₀)` on the ball and `(Z(r₀) - 1) r₀ + Y₀ < 0`, the map `f`
has a zero `x̃` in the open ball, `Df x̃` is invertible, and `x̃` is the only zero in the closed
ball. -/
theorem radii_polynomial_theorem_of_norm_id_sub_le_local
    {f : E → F} {Df : E → E →L[ℝ] F} {xBar : E} {A : F →L[ℝ] E} {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z : ∀ c ∈ closedBall xBar r₀, ‖I_E - A.comp (Df c)‖ ≤ Z r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : simpleRadiiPolynomial Y₀ Z r₀ < 0) (hA_inj : Function.Injective A) :
    ∃ xTilde ∈ ball xBar r₀, f xTilde = 0 ∧ (Df xTilde).IsInvertible ∧
      ∀ z ∈ closedBall xBar r₀, f z = 0 → z = xTilde := by
  have hT : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt (NewtonLikeMap A f)
      (I_E - A.comp (Df x)) (closedBall xBar r₀) x := fun x hx =>
    (hasFDerivWithinAt_id x _).sub (A.hasFDerivAt.comp_hasFDerivWithinAt x (hf x hx))
  have hY : ‖NewtonLikeMap A f xBar - xBar‖ ≤ Y₀ := by
    simpa [NewtonLikeMap] using h_Y₀
  obtain ⟨x, hx, hfix, hu⟩ := general_fixed_point_theorem_local hr₀ hT hY h_Z h_radii
  have hY0 : 0 ≤ Y₀ := (norm_nonneg _).trans h_Y₀
  have hZ1 : Z r₀ < 1 := simple_radii_poly_neg_implies_Z_lt_one hY0 hr₀ h_radii
  refine ⟨x, hx, (fixedPoint_injective_iff_zero hA_inj x).mp hfix,
    isInvertible_of_injective_of_norm_id_sub_comp_lt_one hA_inj
      ((h_Z x (ball_subset_closedBall hx)).trans_lt hZ1), ?_⟩
  intro z hz hz0
  exact hu z hz ((fixedPoint_injective_iff_zero hA_inj z).mpr hz0)

/-- **Local general radii polynomial theorem with nondegeneracy** (local form of Theorem 7.6.2):
the bounds `Y₀, Z₀, Z₁, Z₂` of `general_radii_polynomial_theorem` with derivative data `Df` on the
closed ball only. The zero `x̃` lies in the open ball and `Df x̃` is invertible. -/
theorem general_radii_polynomial_theorem_nondegenerate_local
    {f : E → F} {Df : E → E →L[ℝ] F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - Df xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀, ‖A.comp (Df c - Df xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (hA_inj : Function.Injective A) :
    ∃ xTilde ∈ ball xBar r₀, f xTilde = 0 ∧ (Df xTilde).IsInvertible ∧
      ∀ z ∈ closedBall xBar r₀, f z = 0 → z = xTilde :=
  radii_polynomial_theorem_of_norm_id_sub_le_local (Z := Z_bound_general Z₀ Z₁ Z₂) hr₀ h_Y₀
    (fun c hc => norm_id_sub_comp_le_Z_bound h_Z₀ h_Z₁ (h_Z₂ c hc)) hf
    ((generalRadiiPolynomial_alt_form ..).symm.trans_lt h_radii)
    hA_inj

/-- **Local general radii polynomial theorem** (local form of Theorem 7.6.2): the conclusion of
`general_radii_polynomial_theorem` from derivative data `Df` on the closed ball only. -/
theorem general_radii_polynomial_theorem_local
    {f : E → F} {Df : E → E →L[ℝ] F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - Df xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀, ‖A.comp (Df c - Df xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (hA_inj : Function.Injective A) :
    ∃! xTilde ∈ closedBall xBar r₀, f xTilde = 0 := by
  obtain ⟨x, hx, hfx, -, hu⟩ :=
    general_radii_polynomial_theorem_nondegenerate_local hr₀ h_Y₀ h_Z₀ h_Z₁ h_Z₂ hf h_radii hA_inj
  exact ⟨x, ⟨ball_subset_closedBall hx, hfx⟩, fun z ⟨hz, hz0⟩ => hu z hz hz0⟩


end LocalTheorems

section GeneralRadiiPolynomialTheorem
/-!
## General Radii Polynomial Theorem (Theorem 7.6.2)

This is the main theorem for the E to F case, corresponding to Theorem 7.6.2
in the informal proof.

Given:
- f : E → F (potentially different spaces)
- A : F →L[ℝ] E (approximate inverse, must be injective)
- A† : E →L[ℝ] F (approximation to Df(x̄))
- Bounds Y₀, Z₀, Z₁, Z₂ satisfying the radii polynomial condition

If p(r₀) < 0, then there exists a unique zero x̃ ∈ B̄ᵣ₀(x̄).

The proof strategy: Apply Theorem 7.6.1 to the Newton-like operator T(x) = x - A(f(x)),
then use Proposition 2.3.1 to convert the fixed point to a zero.

Note: The global statement does not record invertibility of Df(x̃). Under the same
hypotheses it holds: the local form
`RadiiPolynomial.general_radii_polynomial_theorem_nondegenerate_local` proves that
Df(x̃) : E →L[ℝ] F is invertible (a continuous linear equivalence E ≃ F).
-/

variable [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 7.6.2**: General Radii Polynomial Theorem for E to F maps

    Given a differentiable f : E → F with E a Banach space and F a real normed space
    (no completeness of F is assumed), approximate inverse A : F →L[ℝ] E,
    and approximate derivative A† : E →L[ℝ] F satisfying:

    - ‖A(f(x̄))‖ ≤ Y₀                               (eq. 7.30: initial defect)
    - ‖I_E - A∘A†‖ ≤ Z₀                            (eq. 7.31: AA† close to identity)
    - ‖A∘[A† - Df(x̄)]‖ ≤ Z₁                        (eq. 7.32: A† approximates Df(x̄))
    - ‖A∘[Df(c) - Df(x̄)]‖ ≤ Z₂(r₀)·r₀ for c ∈ B̄ᵣ₀(x̄) (eq. 7.33: Lipschitz bound, at r₀)

    If p(r₀) < 0 where p(r) = Z₂(r)r² - (1-Z₀-Z₁)r + Y₀ (eq. 7.34),
    then there exists a unique x̃ ∈ B̄ᵣ₀(x̄) with f(x̃) = 0.

    Only one radius r₀ > 0 with p(r₀) < 0 is required, not p(r) < 0 for all r ∈ (0, r₀];
    this is slightly more general than the book's statement.

    Proof: one application of the local form
    `RadiiPolynomial.general_radii_polynomial_theorem_local` (derivative data `fderiv ℝ f`
    within the closed ball), which runs the local fixed-point theorem on the Newton-like
    operator T(x) = x - A(f(x)) and converts the fixed point by Proposition 2.3.1.

    The key requirement is that A is injective. -/
theorem general_radii_polynomial_theorem
  {f : E → F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
  {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hr₀ : 0 < r₀)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                      -- eq. 7.30
  (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)                           -- eq. 7.31
  (h_Z₁ : ‖A.comp (A_dagger - fderiv ℝ f xBar)‖ ≤ Z₁)             -- eq. 7.32
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                        -- eq. 7.33
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hf_diff : Differentiable ℝ f)
  (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)           -- eq. 7.34
  (hA_inj : Function.Injective A) :
  ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 :=
  RadiiPolynomial.general_radii_polynomial_theorem_local hr₀ h_Y₀ h_Z₀ h_Z₁ h_Z₂
    (fun x _ => (hf_diff x).hasFDerivAt.hasFDerivWithinAt) h_radii hA_inj

end GeneralRadiiPolynomialTheorem

section FiniteDimensionalFace
/-!
## Finite-dimensional face

Faces of the local theorems for `f : E → E` on a finite-dimensional real normed space `E`
(completeness is inferred from finite dimension):
* the output record `Enclosure` (invertible `A`, invertible `Df` on the closed ball, a unique zero
  in the closed ball lying in the open ball) and its projection `Enclosure.existsUnique`;
* the single-`Z` face `enclosure_of_Z` (no hypothesis on `A`: finite dimension turns
  `‖I - A Df(x̄)‖ < 1` into invertibility of `A`) and the derived faces `enclosure_of_general`
  (`Y₀, Z₀, Z₁, Z₂` with `A†`) and `enclosure_of_radii` (`A† = Df x̄`);
* `general_rp_findim_local`, the local general theorem without an injectivity hypothesis on `A`.
-/

/-- The output of the finite-dimensional face: `A` is invertible, `Df` is invertible on the whole
closed ball, and `f` has exactly one zero in `B̄_{r₀}(x̄)`, which lies in the open ball. -/
structure Enclosure (f : E → E) (Df : E → E →L[ℝ] E) (A : E →L[ℝ] E) (xBar : E) (r₀ : ℝ) :
    Prop where
  isUnit_A : IsUnit A
  isUnit_Df : ∀ c ∈ closedBall xBar r₀, IsUnit (Df c)
  exists_zero : ∃ xTilde ∈ ball xBar r₀, f xTilde = 0 ∧
    ∀ z ∈ closedBall xBar r₀, f z = 0 → z = xTilde

/-- Existence and uniqueness of the zero in the closed ball, from an `Enclosure`. -/
theorem Enclosure.existsUnique {f : E → E} {Df : E → E →L[ℝ] E} {A : E →L[ℝ] E} {xBar : E}
    {r₀ : ℝ} (h : Enclosure f Df A xBar r₀) : ∃! xTilde ∈ closedBall xBar r₀, f xTilde = 0 := by
  obtain ⟨x, hx, hfx, hu⟩ := h.exists_zero
  exact ⟨x, ⟨ball_subset_closedBall hx, hfx⟩, fun z ⟨hz, hz0⟩ => hu z hz hz0⟩

-- `CompleteSpace E` is inferred from `FiniteDimensional ℝ E` (no completeness binder on the faces).
variable [FiniteDimensional ℝ E]

/-- **Single-`Z` face** (local; derivative data on the closed ball only).
`p(r₀) = (Z - 1) r₀ + Y₀ < 0` with `‖I - A Df(c)‖ ≤ Z` on `B̄_{r₀}(x̄)`. No hypothesis on `A`. -/
theorem enclosure_of_Z {f : E → E} {Df : E → E →L[ℝ] E} {xBar : E} {A : E →L[ℝ] E}
    {Y₀ Z r₀ : ℝ} (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z : ∀ c ∈ closedBall xBar r₀, ‖ContinuousLinearMap.id ℝ E - A.comp (Df c)‖ ≤ Z)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (hp : (Z - 1) * r₀ + Y₀ < 0) : Enclosure f Df A xBar r₀ := by
  have hZ1 : Z < 1 := by nlinarith [(norm_nonneg _).trans h_Y₀]
  have hres : ∀ c ∈ closedBall xBar r₀, ‖I_E - A.comp (Df c)‖ < 1 :=
    fun c hc => (h_Z c hc).trans_lt hZ1
  have hc : xBar ∈ closedBall xBar r₀ := mem_closedBall_self hr₀.le
  obtain ⟨x, hx, hfx, -, hu⟩ := radii_polynomial_theorem_of_norm_id_sub_le_local
    (Z := fun _ => Z) hr₀ h_Y₀ h_Z hf hp (injective_left_of_norm_id_sub_comp_lt_one (hres xBar hc))
  exact ⟨isUnit_left_of_norm_id_sub_comp_lt_one (hres xBar hc),
    fun c hc => isUnit_right_of_norm_id_sub_comp_lt_one (hres c hc), x, hx, hfx, hu⟩

/-- Derived face: four bounds `Y₀, Z₀, Z₁, Z₂` with an approximate derivative `A†`
(`generalRadiiPolynomial`). -/
theorem enclosure_of_general {f : E → E} {Df : E → E →L[ℝ] E} {xBar : E} {A A_dagger : E →L[ℝ] E}
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖ContinuousLinearMap.id ℝ E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - Df xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀, ‖A.comp (Df c - Df xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) : Enclosure f Df A xBar r₀ :=
  enclosure_of_Z (Z := Z_bound_general Z₀ Z₁ Z₂ r₀) hr₀ h_Y₀
    (fun c hc => norm_id_sub_comp_le_Z_bound h_Z₀ h_Z₁ (h_Z₂ c hc)) hf
    (by rw [← generalRadiiPolynomial_alt_form]; exact h_radii)

/-- Derived face: the three bounds `Y₀, Z₀, Z₂` (`A† = Df x̄`, `Z₁ = 0`). -/
theorem enclosure_of_radii {f : E → E} {Df : E → E →L[ℝ] E} {xBar : E} {A : E →L[ℝ] E}
    {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖ContinuousLinearMap.id ℝ E - A.comp (Df xBar)‖ ≤ Z₀)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀, ‖A.comp (Df c - Df xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0) : Enclosure f Df A xBar r₀ :=
  enclosure_of_general (A_dagger := Df xBar) (Z₁ := 0) hr₀ h_Y₀ h_Z₀ (by simp) h_Z₂ hf
    (by rw [← radiiPolynomial_is_special_case]; exact h_radii)








/-- **Finite-dimensional local radii polynomial theorem, general form**: general `A†` (`Z₁`
slot), `Z₂ : ℝ → ℝ`, derivative data on the closed ball only. Injectivity of `A` is not a
hypothesis: `p(r₀) < 0` forces `‖I − A Df(x̄)‖ < 1`, so `A` is onto, hence injective in finite
dimension. -/
theorem general_rp_findim_local {f : E → E} {Df : E → E →L[ℝ] E} {xBar : E}
    {A A_dagger : E →L[ℝ] E} {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖ContinuousLinearMap.id ℝ E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - Df xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ closedBall xBar r₀, ‖A.comp (Df c - Df xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf : ∀ x ∈ closedBall xBar r₀, HasFDerivWithinAt f (Df x) (closedBall xBar r₀) x)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃ xTilde ∈ ball xBar r₀, f xTilde = 0 ∧ (Df xTilde).IsInvertible ∧
      ∀ z ∈ closedBall xBar r₀, f z = 0 → z = xTilde := by
  have hZ : ∀ c ∈ closedBall xBar r₀,
      ‖ContinuousLinearMap.id ℝ E - A.comp (Df c)‖ ≤ Z_bound_general Z₀ Z₁ Z₂ r₀ :=
    fun c hc => norm_id_sub_comp_le_Z_bound h_Z₀ h_Z₁ (h_Z₂ c hc)
  have hp := (generalRadiiPolynomial_alt_form ..).symm.trans_lt h_radii
  have hZ1 := simple_radii_poly_neg_implies_Z_lt_one ((norm_nonneg _).trans h_Y₀) hr₀ hp
  exact radii_polynomial_theorem_of_norm_id_sub_le_local (Z := Z_bound_general Z₀ Z₁ Z₂) hr₀
    h_Y₀ hZ hf hp
    (injective_left_of_norm_id_sub_comp_lt_one
      ((hZ xBar (mem_closedBall_self hr₀.le)).trans_lt hZ1))

end FiniteDimensionalFace

end RadiiPolynomial
