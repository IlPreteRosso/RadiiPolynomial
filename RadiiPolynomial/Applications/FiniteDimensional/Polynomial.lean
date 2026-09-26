import RadiiPolynomial.Applications.FiniteDimensional.Face
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds

/-!
# Polynomial systems on `R^n` with rational certificate data

A `StdFinDimData n` records a polynomial system `P : Fin n → CompPoly n`, a rational centre `x̄`,
a rational matrix `A` (the approximate inverse), a radius `r₀` and the three bounds `Y₀`, `Z₀`,
`Z₂`, all in `ℚ`. The certificate `ChecksC` is a decidable rational proposition (the `Z₂` row
sums are centre-anchored, `anchoredBound`), independent of the coordinate ring; `tightC` fills
in the tightest bounds for given `P`, `x̄`, `A`, `r₀`.

The semantic side takes the coordinate ring `R` explicitly: any normed commutative real algebra
(finite-dimensional, with `‖1‖ = 1`, for the faces), e.g. `R = ℝ` or `R = ℂ`. The field is
`u ↦ (Pᵢ.evalBanach u)ᵢ` on `R^n`, its derivative is the syntactic Jacobian `jacCLM P`, and the
data embed along `ratMap R`.

## Main results

- `enclosureC`, `existsUniqueC`, `isUnit_fderivC`: `ChecksC` gives an `Enclosure` of the field
  around `x̄` of radius `r₀`, hence a unique zero and an invertible derivative on the ball
- `enclosure_of_bounds`, `existsUnique_of_bounds`: the same from user-supplied rational
  `Y₀`, `Z₀`, `Z₂` with proofs (override slot)
-/

open scoped BigOperators
open Metric
open MvPolyBridge MvPolyBridge.CompPoly

namespace RadiiPolynomial

/-- Rational certificate data for a polynomial system on `R^n`. -/
structure StdFinDimData (n : ℕ) where
  P : Fin n → CompPoly n
  xBar : Fin n → ℚ
  A : Matrix (Fin n) (Fin n) ℚ
  r₀ : ℚ
  Y₀ : ℚ
  Z₀ : ℚ
  Z₂ : ℚ

namespace StdFinDimData

section Rational

variable {n : ℕ} (d : StdFinDimData n)

/-- Rational Jacobian at `x̄`. -/
def jacQ : Matrix (Fin n) (Fin n) ℚ := fun j k => evalQ ((d.P j).pderiv k) d.xBar

/-- Centred `Z₂` row sum: `∑ₖ ∑ⱼ |Aᵢⱼ| · anchoredBound x̄ r₀ (∂ₖPⱼ)`. -/
def z2RowC (i : Fin n) : ℚ :=
  ∑ k, ∑ j, |d.A i j| * anchoredBound d.xBar d.r₀ ((d.P j).pderiv k)

/-- The ℚ-decidable certificate (centred `Z₂`). Independent of the coordinate ring. -/
def ChecksC : Prop :=
  0 < d.r₀ ∧
  (∀ i, |∑ j, d.A i j * evalQ (d.P j) d.xBar| ≤ d.Y₀) ∧
  (∀ i, ∑ k, |(1 - d.A * d.jacQ) i k| ≤ d.Z₀) ∧
  (∀ i, d.z2RowC i ≤ d.Z₂) ∧
  d.Z₂ * d.r₀ ^ 2 - (1 - d.Z₀) * d.r₀ + d.Y₀ < 0

instance : Decidable d.ChecksC := by unfold ChecksC z2RowC; infer_instance

/-- Max of a finite family of rationals (0 for `n = 0`); computable. -/
def maxRow {n : ℕ} (g : Fin n → ℚ) : ℚ := (List.finRange n).foldl (fun m i => max m (g i)) 0

/-- Tight centred data: `Y₀`, `Z₀` exact; `Z₂` = max of the centred row sums. -/
def tightC {n : ℕ} (P : Fin n → CompPoly n) (xBar : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (r₀ : ℚ) : StdFinDimData n :=
  let d₀ : StdFinDimData n := ⟨P, xBar, A, r₀, 0, 0, 0⟩
  { d₀ with
    Y₀ := maxRow fun i => |∑ j, A i j * evalQ (P j) xBar|
    Z₀ := maxRow fun i => ∑ k, |(1 - A * d₀.jacQ) i k|
    Z₂ := maxRow d₀.z2RowC }

end Rational

section Semantic

variable (R : Type*) [NormedCommRing R] [NormedAlgebra ℝ R] {n : ℕ} (d : StdFinDimData n)

/-- The field `f(u)ᵢ = Pᵢ(u)` on `R^n`. -/
noncomputable def field (u : Fin n → R) : Fin n → R := fun i => (d.P i).evalBanach u

/-- `x̄` embedded in `R^n`. -/
noncomputable def xBarR : Fin n → R := fun i => ratMap R (d.xBar i)

/-- `A` embedded in `R`. -/
noncomputable def AR : Matrix (Fin n) (Fin n) R := d.A.map (ratMap R)

/-- The syntactic Jacobian at `x : R^n`. -/
noncomputable def JR (x : Fin n → R) : Matrix (Fin n) (Fin n) R := jacobian d.P x

theorem hasFDerivAt_field (x : Fin n → R) : HasFDerivAt (d.field R) (jacCLM d.P x) x :=
  hasFDerivAt_system d.P x

theorem jacCLM_apply' (x h : Fin n → R) (i : Fin n) :
    jacCLM d.P x h i = ∑ k, d.JR R x i k * h k :=
  jacCLM_apply d.P x h i

theorem evalBanach_xBarR (p : CompPoly n) :
    p.evalBanach (d.xBarR R) = ratMap R (evalQ p d.xBar) :=
  evalBanach_ratMap p d.xBar

theorem AR_mul_field_xBarR (i : Fin n) :
    ∑ j, d.AR R i j * d.field R (d.xBarR R) j =
      ratMap R (∑ j, d.A i j * evalQ (d.P j) d.xBar) := by
  simp only [AR, field, Matrix.map_apply, evalBanach_xBarR, map_sum, map_mul]

theorem JR_xBarR : d.JR R (d.xBarR R) = d.jacQ.map (ratMap R) := by
  ext j k
  simp only [JR, jacobian, jacQ, Matrix.of_apply, Matrix.map_apply, evalBanach_xBarR]

theorem one_sub_AR_mul_JR :
    1 - d.AR R * d.JR R (d.xBarR R) = (1 - d.A * d.jacQ).map (ratMap R) := by
  rw [JR_xBarR, AR, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, map_sub, map_one, map_mul]

variable [NormOneClass R]

/-- `Y₀` row-sum clause over `R` from its exact rational form. -/
theorem rowSumY_of_le {Y₀ : ℚ} (hY : ∀ i, |∑ j, d.A i j * evalQ (d.P j) d.xBar| ≤ Y₀) :
    ∀ i, ‖∑ j, d.AR R i j * d.field R (d.xBarR R) j‖ ≤ (Y₀ : ℝ) := fun i => by
  rw [AR_mul_field_xBarR, norm_ratMap]
  exact_mod_cast hY i

/-- `Z₀` row-sum clause over `R` from its exact rational form. -/
theorem rowSumZ₀_of_le {Z₀ : ℚ} (hZ₀ : ∀ i, ∑ k, |(1 - d.A * d.jacQ) i k| ≤ Z₀) :
    ∀ i, ∑ k, ‖(1 - d.AR R * d.JR R (d.xBarR R)) i k‖ ≤ (Z₀ : ℝ) := fun i => by
  rw [one_sub_AR_mul_JR]
  simp only [Matrix.map_apply, norm_ratMap]
  exact_mod_cast hZ₀ i

/-- `Z₂` row-sum clause on the ball from the centred (anchored) row sums. -/
theorem rowSumZ₂_of_anchored {Z₂ : ℚ} (hr : 0 < d.r₀) (hZ₂ : ∀ i, d.z2RowC i ≤ Z₂) :
    ∀ c ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), ∀ i,
      ∑ k, ‖(d.AR R * (d.JR R c - d.JR R (d.xBarR R))) i k‖ ≤ (Z₂ : ℝ) * d.r₀ := by
  intro c hc i
  have hr0 : (0 : ℝ) ≤ d.r₀ := by exact_mod_cast hr.le
  have hcx : ‖c - d.xBarR R‖ ≤ d.r₀ := by rwa [mem_closedBall, dist_eq_norm] at hc
  have hLip : ∀ j k, ‖((d.P j).pderiv k).evalBanach c -
      ((d.P j).pderiv k).evalBanach (d.xBarR R)‖ ≤
        (anchoredBound d.xBar d.r₀ ((d.P j).pderiv k) : ℝ) * d.r₀ := fun j k =>
    (norm_evalBanach_sub_center_le _ d.xBar d.r₀ c hcx).trans
      (mul_le_mul_of_nonneg_left hcx (by exact_mod_cast anchoredBound_nonneg _ hr.le _))
  have hsum : ∀ k, ‖(d.AR R * (d.JR R c - d.JR R (d.xBarR R))) i k‖ ≤
      (∑ j, |(d.A i j : ℝ)| * (anchoredBound d.xBar d.r₀ ((d.P j).pderiv k) : ℝ)) * d.r₀ := by
    intro k
    simp only [AR, JR, jacobian, Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply,
      Matrix.of_apply]
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [mul_assoc]
    refine (norm_mul_le _ _).trans ?_
    rw [norm_ratMap]
    exact mul_le_mul_of_nonneg_left (hLip j k) (abs_nonneg _)
  refine (Finset.sum_le_sum fun k _ => hsum k).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hr0
  have := hZ₂ i
  simp only [z2RowC] at this
  exact_mod_cast this

variable [FiniteDimensional ℝ R]

/-- **Override slot**, enclosure form: user-supplied `Y₀ Z₀ Z₂ : ℚ` with proofs. -/
theorem enclosure_of_bounds [NeZero n] (Y₀ Z₀ Z₂ : ℚ) (hr : 0 < d.r₀)
    (hY : ∀ i, |∑ j, d.A i j * evalQ (d.P j) d.xBar| ≤ Y₀)
    (hZ₀ : ∀ i, ∑ k, |(1 - d.A * d.jacQ) i k| ≤ Z₀)
    (hZ₂ : ∀ c ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), ∀ i,
      ∑ k, ‖(d.AR R * (d.JR R c - d.JR R (d.xBarR R))) i k‖ ≤ (Z₂ : ℝ) * d.r₀)
    (hp : Z₂ * d.r₀ ^ 2 - (1 - Z₀) * d.r₀ + Y₀ < 0) :
    Enclosure (d.field R) (jacCLM d.P) (matCLM (d.AR R)) (d.xBarR R) d.r₀ :=
  enclosure_of_rowSum (fun x _ => (d.hasFDerivAt_field R x).hasFDerivWithinAt)
    (fun x _ => d.jacCLM_apply' R x) (by exact_mod_cast hr) (d.rowSumY_of_le R hY)
    (d.rowSumZ₀_of_le R hZ₀) hZ₂ (by simp only [radiiPolynomial]; exact_mod_cast hp)

/-- **Override face**: the unique zero from user-supplied rational `Y₀ Z₀ Z₂` with proofs. -/
theorem existsUnique_of_bounds [NeZero n] (Y₀ Z₀ Z₂ : ℚ) (hr : 0 < d.r₀)
    (hY : ∀ i, |∑ j, d.A i j * evalQ (d.P j) d.xBar| ≤ Y₀)
    (hZ₀ : ∀ i, ∑ k, |(1 - d.A * d.jacQ) i k| ≤ Z₀)
    (hZ₂ : ∀ c ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), ∀ i,
      ∑ k, ‖(d.AR R * (d.JR R c - d.JR R (d.xBarR R))) i k‖ ≤ (Z₂ : ℝ) * d.r₀)
    (hp : Z₂ * d.r₀ ^ 2 - (1 - Z₀) * d.r₀ + Y₀ < 0) :
    ∃! x ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), d.field R x = 0 :=
  (d.enclosure_of_bounds R Y₀ Z₀ Z₂ hr hY hZ₀ hZ₂ hp).existsUnique

/-- **Centred polynomial face**, enclosure form. -/
theorem enclosureC [NeZero n] (h : d.ChecksC) :
    Enclosure (d.field R) (jacCLM d.P) (matCLM (d.AR R)) (d.xBarR R) d.r₀ := by
  obtain ⟨hr, hY, hZ₀, hZ₂, hp⟩ := h
  exact d.enclosure_of_bounds R d.Y₀ d.Z₀ d.Z₂ hr hY hZ₀ (d.rowSumZ₂_of_anchored R hr hZ₂) hp

/-- **Centred polynomial face**. -/
theorem existsUniqueC [NeZero n] (h : d.ChecksC) :
    ∃! x ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), d.field R x = 0 :=
  (d.enclosureC R h).existsUnique

/-- **Centred face, nondegeneracy output**. -/
theorem isUnit_fderivC [NeZero n] (h : d.ChecksC) :
    ∀ c ∈ closedBall (d.xBarR R) (d.r₀ : ℝ), IsUnit (fderiv ℝ (d.field R) c) := fun c hc =>
  (d.hasFDerivAt_field R c).fderiv ▸ (d.enclosureC R h).isUnit_Df c hc

end Semantic

end StdFinDimData

end RadiiPolynomial
