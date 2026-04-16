import RadiiPolynomial.source.lpSpace.LpOneAlg
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Generic Weighted Scalar Fiber

`WeightedScalar 𝕜 w m` is `𝕜` equipped with norm `‖x‖ * w(m)` where `w : M → ℝ` is a
positive weight function. This provides a single parameterized fiber type that unifies
`ScaledReal`, `ScaledRealZ`, and `OmegaScaledReal`.

## Main definitions

- `WeightedScalar 𝕜 w m`: 𝕜 with weighted norm
- `PosWeight w`: weight with positive values (→ NormedAddCommGroup)
- `SuperUnitWeight w`: weight ≥ 1 (→ ℓ¹_w ↪ ℓ¹, uniform convergence)
- `SubMulWeight w`: submultiplicative weight (→ Banach algebra on lpOneAlg)
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### Weight Typeclasses -/

/-- A weight function with positive values. Provides `NormedAddCommGroup` on
`WeightedScalar 𝕜 w m` via norm `‖x‖ * w(m)`. -/
class PosWeight {M : Type*} (w : M → ℝ) where
  weight_pos : ∀ m, 0 < w m

namespace PosWeight

variable {M : Type*} {w : M → ℝ} [PosWeight w]

lemma weight_nonneg (m : M) : 0 ≤ w m := le_of_lt (weight_pos m)
lemma weight_ne_zero (m : M) : w m ≠ 0 := ne_of_gt (weight_pos m)

end PosWeight

/-- Weight ≥ 1: ensures `‖x‖_𝕜 ≤ ‖x‖` and hence ℓ¹_w ↪ ℓ¹.
This gives uniform convergence of function series (Thm 14.1.3).
Ref: for ν ≥ 1, the weight `ν^n ≥ 1`, so `‖a_n‖ ≤ ‖a_n‖·ν^n = ‖a_n‖_w`. -/
class SuperUnitWeight {M : Type*} (w : M → ℝ) extends PosWeight w where
  one_le : ∀ m, 1 ≤ w m

/-- Submultiplicative weight with identity (extends PosWeight).
Sufficient for Ring on `lpOneAlg` when fibers are finite (HasAntidiagonal). -/
class SubMulWeightBase {M : Type*} [AddCommMonoid M] (w : M → ℝ) extends PosWeight w where
  submul : ∀ m n, w (m + n) ≤ w m * w n
  weight_zero : w 0 = 1

/-- Submultiplicative weight with weight ≥ 1 (extends SubMulWeightBase + SuperUnitWeight).
Needed for tsum-based Ring on general M (infinite fibers). -/
class SubMulWeight {M : Type*} [AddCommMonoid M] (w : M → ℝ)
    extends SubMulWeightBase w, SuperUnitWeight w

/-! ### WeightedScalar Type -/

/-- Generic weighted scalar fiber: `𝕜` with norm `‖x‖_𝕜 * w(m)`.
`def` (not `abbrev`) prevents typeclass diamond with the standard `𝕜` norm. -/
def WeightedScalar (𝕜 : Type*) {M : Type*} (_w : M → ℝ) (_m : M) := 𝕜

namespace WeightedScalar

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} {m : M}

/-! ### Instances inherited from 𝕜 -/

instance : AddCommGroup (WeightedScalar 𝕜 w m) := inferInstanceAs (AddCommGroup 𝕜)
instance : Module 𝕜 (WeightedScalar 𝕜 w m) := inferInstanceAs (Module 𝕜 𝕜)
instance : Ring (WeightedScalar 𝕜 w m) := inferInstanceAs (Ring 𝕜)

/-! ### Coercion to 𝕜 -/

/-- Identity map to `𝕜`. -/
@[coe] def toReal (x : WeightedScalar 𝕜 w m) : 𝕜 := x

instance : CoeOut (WeightedScalar 𝕜 w m) 𝕜 := ⟨toReal⟩

/-- Additive equivalence from `𝕜`. -/
def ofReal : 𝕜 ≃+ WeightedScalar 𝕜 w m := AddEquiv.refl 𝕜

omit [NormedField 𝕜] in
@[simp] lemma toReal_apply (x : WeightedScalar 𝕜 w m) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : 𝕜) : (ofReal x : WeightedScalar 𝕜 w m) = x := rfl

@[simp] lemma coe_zero : ((0 : WeightedScalar 𝕜 w m) : 𝕜) = 0 := rfl
@[simp] lemma coe_one : ((1 : WeightedScalar 𝕜 w m) : 𝕜) = 1 := rfl
@[simp] lemma coe_add (x y : WeightedScalar 𝕜 w m) :
    ((x + y : WeightedScalar 𝕜 w m) : 𝕜) = x + y := rfl
@[simp] lemma coe_sub (x y : WeightedScalar 𝕜 w m) :
    ((x - y : WeightedScalar 𝕜 w m) : 𝕜) = x - y := rfl
@[simp] lemma coe_neg (x : WeightedScalar 𝕜 w m) :
    ((-x : WeightedScalar 𝕜 w m) : 𝕜) = -x := rfl
@[simp] lemma coe_mul (x y : WeightedScalar 𝕜 w m) :
    ((x * y : WeightedScalar 𝕜 w m) : 𝕜) = x * y := rfl
@[simp] lemma coe_smul (r : 𝕜) (x : WeightedScalar 𝕜 w m) :
    ((r • x : WeightedScalar 𝕜 w m) : 𝕜) = r • ↑x := rfl
@[simp] lemma coe_pow (x : WeightedScalar 𝕜 w m) (k : ℕ) :
    ((x ^ k : WeightedScalar 𝕜 w m) : 𝕜) = (↑x) ^ k := rfl
@[simp] lemma coe_natCast (k : ℕ) : ((k : WeightedScalar 𝕜 w m) : 𝕜) = k := rfl
@[simp] lemma coe_intCast (k : ℤ) : ((k : WeightedScalar 𝕜 w m) : 𝕜) = k := rfl

/-! ### Weighted Norm -/

instance instNorm : Norm (WeightedScalar 𝕜 w m) where
  norm x := ‖toReal x‖ * w m

lemma norm_def (x : WeightedScalar 𝕜 w m) : ‖x‖ = ‖toReal x‖ * w m := rfl

@[simp] lemma norm_ofReal (r : 𝕜) : ‖(ofReal r : WeightedScalar 𝕜 w m)‖ = ‖r‖ * w m := rfl

/-- `‖1‖ = w m` for WeightedScalar. Bridge for lpAlgRingData.norm_ofReal_eq. -/
@[simp] lemma norm_one_eq_weight : ‖(1 : WeightedScalar 𝕜 w m)‖ = w m := by
  show ‖(1 : 𝕜)‖ * w m = w m; rw [norm_one, one_mul]

/-- `norm_ofReal_eq` for lpAlgRingData: `‖ofReal r‖ = ‖r‖ * ‖ofReal 1‖`. -/
lemma norm_ofReal_eq_mul_norm_one (r : 𝕜) :
    ‖(ofReal r : WeightedScalar 𝕜 w m)‖ = ‖r‖ * ‖(ofReal 1 : WeightedScalar 𝕜 w m)‖ := by
  show ‖r‖ * w m = ‖r‖ * (‖(1 : 𝕜)‖ * w m); rw [norm_one, one_mul]

/-- Submultiplicativity of the weighted norm: `‖a*b‖ * w(j+l) ≤ (‖a‖*w j) * (‖b‖*w l)`.
Bridge for lpOneAlgWeightMul.norm_ofReal_mul_le. -/
lemma norm_ofReal_mul_le [AddCommMonoid M] [SubMulWeightBase w] (j l : M) (a b : 𝕜) :
    ‖(ofReal (a * b) : WeightedScalar 𝕜 w (j + l))‖ ≤
    ‖(ofReal a : WeightedScalar 𝕜 w j)‖ * ‖(ofReal b : WeightedScalar 𝕜 w l)‖ := by
  simp only [norm_ofReal, norm_mul]
  exact (mul_le_mul_of_nonneg_left (SubMulWeightBase.submul j l)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

/-- Weight ≥ 1 via norm: `1 ≤ ‖ofReal 1‖`.
Bridge for lpOneAlgWeightSubMul.norm_ofReal_one_ge. -/
lemma norm_ofReal_one_ge [AddCommMonoid M] [SubMulWeight w] (m : M) :
    1 ≤ ‖(ofReal 1 : WeightedScalar 𝕜 w m)‖ := by
  simp only [norm_ofReal, norm_one, one_mul]; exact SuperUnitWeight.one_le m

@[simp] lemma norm_zero' : ‖(0 : WeightedScalar 𝕜 w m)‖ = 0 := by
  show ‖(0 : 𝕜)‖ * w m = 0; rw [norm_zero, zero_mul]

@[simp] lemma norm_neg' (x : WeightedScalar 𝕜 w m) : ‖-x‖ = ‖x‖ := by
  show ‖(-toReal x : 𝕜)‖ * w m = ‖toReal x‖ * w m; rw [norm_neg]

lemma norm_smul' (c : 𝕜) (x : WeightedScalar 𝕜 w m) : ‖c • x‖ = ‖c‖ * ‖x‖ := by
  simp only [norm_def, show toReal (c • x) = c * toReal x from rfl, norm_mul, mul_assoc]

/-! ### NormedAddCommGroup (requires PosWeight) -/

variable [PosWeight w]

lemma norm_nonneg' (x : WeightedScalar 𝕜 w m) : 0 ≤ ‖x‖ :=
  mul_nonneg (norm_nonneg _) (PosWeight.weight_nonneg m)

lemma norm_add_le' (x y : WeightedScalar 𝕜 w m) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  simp only [norm_def, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (PosWeight.weight_nonneg m)

lemma norm_eq_zero' (x : WeightedScalar 𝕜 w m) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero]
  constructor
  · intro h
    cases h with
    | inl h => exact norm_eq_zero.mp h
    | inr h => exact absurd h (PosWeight.weight_ne_zero m)
  · intro h; left; rw [h]; exact norm_zero

instance instNormedAddCommGroup : NormedAddCommGroup (WeightedScalar 𝕜 w m) where
  dist x y := ‖-x + y‖
  dist_self x := by
    show ‖toReal (-x + x)‖ * w m = 0
    rw [show toReal (-x + x) = (0 : 𝕜) from neg_add_cancel x, norm_zero, zero_mul]
  dist_comm x y := by
    simp only [norm_def]; congr 1
    show ‖(-toReal x + toReal y : 𝕜)‖ = ‖(-toReal y + toReal x : 𝕜)‖
    rw [show -toReal x + toReal y = toReal y - toReal x from by ring,
        show -toReal y + toReal x = toReal x - toReal y from by ring, norm_sub_rev]
  dist_triangle x y z := by
    rw [show -x + z = (-x + y) + (-y + z) from by abel_nf]
    show ‖toReal ((-x + y) + (-y + z))‖ * w m ≤
      ‖toReal (-x + y)‖ * w m + ‖toReal (-y + z)‖ * w m
    rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (le_of_lt (PosWeight.weight_pos m))
  edist_dist x y := rfl
  eq_of_dist_eq_zero {a b} h := by
    have : ‖toReal (-a + b)‖ * w m = 0 := h
    have h1 : ‖toReal (-a + b)‖ = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt (PosWeight.weight_pos m))
    have h2 : -a + b = (0 : WeightedScalar 𝕜 w m) := norm_eq_zero.mp h1
    have h3 : a + (-a + b) = a + 0 := congr_arg (a + ·) h2
    rwa [add_neg_cancel_left, add_zero, eq_comm] at h3
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace 𝕜 (WeightedScalar 𝕜 w m) where
  toModule := inferInstance
  norm_smul_le c x := by
    show ‖c * toReal x‖ * w m ≤ ‖c‖ * (‖toReal x‖ * w m)
    rw [norm_mul, mul_assoc]

instance instFiniteDimensional : FiniteDimensional 𝕜 (WeightedScalar 𝕜 w m) :=
  inferInstanceAs (FiniteDimensional 𝕜 𝕜)

end WeightedScalar

/-- `CompleteSpace` for `WeightedScalar 𝕜 w m`.
Requires `NontriviallyNormedField 𝕜` (for `FiniteDimensional.complete`). -/
instance WeightedScalar.instCompleteSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w] {m : M} :
    CompleteSpace (WeightedScalar 𝕜 w m) :=
  FiniteDimensional.complete (𝕜 := 𝕜) (E := WeightedScalar 𝕜 w m)

/-! ### Generic lpOneAlg instances for WeightedScalar -/

/-- Generic `lpAlgRingData` for any `WeightedScalar 𝕜 w` with `PosWeight`.
All fields are trivial since `WeightedScalar 𝕜 w m = 𝕜` with identity coercions. -/
instance WeightedScalar.instLpAlgRingData {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {w : M → ℝ} [PosWeight w] :
    lpAlgRingData 𝕜 M (WeightedScalar 𝕜 w) where
  toReal _m x := WeightedScalar.toReal x
  ofReal _m r := WeightedScalar.ofReal r
  toReal_ofReal _ _ := rfl
  ofReal_toReal _ _ := rfl
  ofReal_add _ _ _ := rfl
  ofReal_zero _ := rfl
  toReal_add _ _ _ := rfl
  toReal_zero _ := rfl
  toReal_neg _ _ := rfl
  norm_ofReal_eq _ := WeightedScalar.norm_ofReal_eq_mul_norm_one

/-- Generic `lpAlgSmulCompat` — scalar multiplication is just 𝕜 multiplication. -/
instance WeightedScalar.instLpAlgSmulCompat {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {w : M → ℝ} [PosWeight w] :
    lpAlgSmulCompat 𝕜 M (WeightedScalar 𝕜 w) where
  toReal_smul _ _ _ := rfl

/-- Generic `lpOneAlgWeightMul` from `SubMulWeightBase` (submultiplicativity only).
Available for ALL ν > 0 — no weight ≥ 1 requirement. -/
instance WeightedScalar.instLpOneAlgWeightMul {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeightBase w] : lpOneAlgWeightMul 𝕜 M (WeightedScalar 𝕜 w) where
  norm_ofReal_mul_le := WeightedScalar.norm_ofReal_mul_le
  norm_ofReal_one_zero := by
    show ‖(1 : 𝕜)‖ * w 0 = 1; simp [norm_one, SubMulWeightBase.weight_zero (w := w)]

/-- Generic `lpOneAlgWeightSubMul` from `SubMulWeight`.
Adds weight ≥ 1 on top of `lpOneAlgWeightMul`. Needs `[Fact (1 ≤ ν)]`. -/
instance WeightedScalar.instLpOneAlgWeightSubMul {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeight w] : lpOneAlgWeightSubMul 𝕜 M (WeightedScalar 𝕜 w) where
  norm_ofReal_one_ge := WeightedScalar.norm_ofReal_one_ge

end RadiiPolynomial

end
