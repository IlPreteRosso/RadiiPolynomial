import RadiiPolynomial.source.lpSpace.LpOneAlg
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Generic Weighted Scalar Fiber

`WeightedScalar w m` is `ℝ` equipped with norm `|x| * w(m)` where `w : M → ℝ` is a
positive weight function. This provides a single parameterized fiber type that unifies
`ScaledReal`, `ScaledRealZ`, and `OmegaScaledReal`.

## Main definitions

- `WeightedScalar w m`: ℝ with weighted norm
- `PosWeight w`: weight with positive values (→ NormedAddCommGroup)
- `SuperUnitWeight w`: weight ≥ 1 (→ ℓ¹_w ↪ ℓ¹, uniform convergence)
- `SubMulWeight w`: submultiplicative weight (→ Banach algebra on lpOneAlg)
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### Weight Typeclasses -/

/-- A weight function with positive values. Provides `NormedAddCommGroup` on
`WeightedScalar w m` via norm `|x| * w(m)`. -/
class PosWeight {M : Type*} (w : M → ℝ) where
  weight_pos : ∀ m, 0 < w m

namespace PosWeight

variable {M : Type*} {w : M → ℝ} [PosWeight w]

lemma weight_nonneg (m : M) : 0 ≤ w m := le_of_lt (weight_pos m)
lemma weight_ne_zero (m : M) : w m ≠ 0 := ne_of_gt (weight_pos m)

end PosWeight

/-- Weight ≥ 1: ensures `|x| ≤ ‖x‖` and hence ℓ¹_w ↪ ℓ¹.
This gives uniform convergence of function series (Thm 14.1.3).
Ref: for ν ≥ 1, the weight `ν^n ≥ 1`, so `|a_n| ≤ |a_n|·ν^n = ‖a_n‖`. -/
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

/-- Generic weighted scalar fiber: `ℝ` with norm `|x| * w(m)`.
`def` (not `abbrev`) prevents typeclass diamond with the standard `ℝ` norm. -/
def WeightedScalar {M : Type*} (_w : M → ℝ) (_m : M) := ℝ

namespace WeightedScalar

variable {M : Type*} {w : M → ℝ} {m : M}

/-! ### Instances inherited from ℝ -/

instance : AddCommGroup (WeightedScalar w m) := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ (WeightedScalar w m) := inferInstanceAs (Module ℝ ℝ)
instance : Ring (WeightedScalar w m) := inferInstanceAs (Ring ℝ)
instance : Lattice (WeightedScalar w m) := inferInstanceAs (Lattice ℝ)
instance : LinearOrder (WeightedScalar w m) := inferInstanceAs (LinearOrder ℝ)
instance : AddLeftMono (WeightedScalar w m) := inferInstanceAs (AddLeftMono ℝ)

/-! ### Coercion to ℝ -/

/-- Identity map to `ℝ`. -/
@[coe] def toReal (x : WeightedScalar w m) : ℝ := x

instance : CoeOut (WeightedScalar w m) ℝ := ⟨toReal⟩

/-- Additive equivalence from `ℝ`. -/
def ofReal : ℝ ≃+ WeightedScalar w m := AddEquiv.refl ℝ

@[simp] lemma toReal_apply (x : WeightedScalar w m) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : WeightedScalar w m) = x := rfl

@[simp] lemma coe_zero : ((0 : WeightedScalar w m) : ℝ) = 0 := rfl
@[simp] lemma coe_one : ((1 : WeightedScalar w m) : ℝ) = 1 := rfl
@[simp] lemma coe_add (x y : WeightedScalar w m) :
    ((x + y : WeightedScalar w m) : ℝ) = x + y := rfl
@[simp] lemma coe_sub (x y : WeightedScalar w m) :
    ((x - y : WeightedScalar w m) : ℝ) = x - y := rfl
@[simp] lemma coe_neg (x : WeightedScalar w m) :
    ((-x : WeightedScalar w m) : ℝ) = -x := rfl
@[simp] lemma coe_mul (x y : WeightedScalar w m) :
    ((x * y : WeightedScalar w m) : ℝ) = x * y := rfl
@[simp] lemma coe_abs (x : WeightedScalar w m) :
    ((|x| : WeightedScalar w m) : ℝ) = |↑x| := rfl
@[simp] lemma coe_smul (r : ℝ) (x : WeightedScalar w m) :
    ((r • x : WeightedScalar w m) : ℝ) = r • ↑x := rfl
@[simp] lemma coe_pow (x : WeightedScalar w m) (k : ℕ) :
    ((x ^ k : WeightedScalar w m) : ℝ) = (↑x) ^ k := rfl
@[simp] lemma coe_natCast (k : ℕ) : ((k : WeightedScalar w m) : ℝ) = k := rfl
@[simp] lemma coe_intCast (k : ℤ) : ((k : WeightedScalar w m) : ℝ) = k := rfl

/-! ### Weighted Norm -/

instance instNorm : Norm (WeightedScalar w m) where
  norm x := |toReal x| * w m

lemma norm_def (x : WeightedScalar w m) : ‖x‖ = |toReal x| * w m := rfl

@[simp] lemma norm_ofReal (r : ℝ) : ‖(ofReal r : WeightedScalar w m)‖ = |r| * w m := rfl

/-- `‖1‖ = w m` for WeightedScalar. Bridge for lpOneAlgRingData.norm_ofReal_eq. -/
@[simp] lemma norm_one_eq_weight : ‖(1 : WeightedScalar w m)‖ = w m := by
  show |(1 : ℝ)| * w m = w m; rw [abs_one, one_mul]

/-- `norm_ofReal_eq` for lpOneAlgRingData: `‖ofReal r‖ = |r| * ‖ofReal 1‖`. -/
lemma norm_ofReal_eq_mul_norm_one (r : ℝ) :
    ‖(ofReal r : WeightedScalar w m)‖ = |r| * ‖(ofReal 1 : WeightedScalar w m)‖ := by
  show |(r : ℝ)| * w m = |(r : ℝ)| * (|(1 : ℝ)| * w m); rw [abs_one, one_mul]

/-- Submultiplicativity of the weighted norm: `|a*b| * w(j+l) ≤ (|a|*w j) * (|b|*w l)`.
Bridge for lpOneAlgWeightSubMul.norm_ofReal_mul_le. -/
lemma norm_ofReal_mul_le [AddCommMonoid M] [SubMulWeightBase w] (j l : M) (a b : ℝ) :
    ‖(ofReal (a * b) : WeightedScalar w (j + l))‖ ≤
    ‖(ofReal a : WeightedScalar w j)‖ * ‖(ofReal b : WeightedScalar w l)‖ := by
  simp only [norm_ofReal, abs_mul]
  exact (mul_le_mul_of_nonneg_left (SubMulWeightBase.submul j l)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)

/-- Weight ≥ 1 via norm: `1 ≤ ‖ofReal 1‖`.
Bridge for lpOneAlgWeightSubMul.norm_ofReal_one_ge. -/
lemma norm_ofReal_one_ge [AddCommMonoid M] [SubMulWeight w] (m : M) :
    1 ≤ ‖(ofReal 1 : WeightedScalar w m)‖ := by
  simp only [norm_ofReal, abs_one, one_mul]; exact SuperUnitWeight.one_le m

@[simp] lemma norm_zero' : ‖(0 : WeightedScalar w m)‖ = 0 := by
  show |(0 : ℝ)| * w m = 0; rw [abs_zero, zero_mul]

@[simp] lemma norm_neg' (x : WeightedScalar w m) : ‖-x‖ = ‖x‖ := by
  show |(-toReal x : ℝ)| * w m = |toReal x| * w m; rw [abs_neg]

lemma norm_smul' (c : ℝ) (x : WeightedScalar w m) : ‖c • x‖ = |c| * ‖x‖ := by
  simp only [norm_def, show toReal (c • x) = c * toReal x from rfl, abs_mul, mul_assoc]

/-! ### NormedAddCommGroup (requires PosWeight) -/

variable [PosWeight w]

lemma norm_nonneg' (x : WeightedScalar w m) : 0 ≤ ‖x‖ :=
  mul_nonneg (abs_nonneg _) (PosWeight.weight_nonneg m)

lemma norm_add_le' (x y : WeightedScalar w m) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  simp only [norm_def, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (PosWeight.weight_nonneg m)

lemma norm_eq_zero' (x : WeightedScalar w m) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero]
  constructor
  · intro h
    cases h with
    | inl h => exact abs_eq_zero.mp h
    | inr h => exact absurd h (PosWeight.weight_ne_zero m)
  · intro h; left; rw [h]; exact abs_zero

instance instNormedAddCommGroup : NormedAddCommGroup (WeightedScalar w m) where
  dist x y := ‖-x + y‖
  dist_self x := by
    show |toReal (-x + x)| * w m = 0
    rw [show toReal (-x + x) = 0 from neg_add_cancel x, abs_zero, zero_mul]
  dist_comm x y := by
    simp only [norm_def]
    congr 1
    show |(-toReal x + toReal y)| = |(-toReal y + toReal x)|
    rw [show -toReal x + toReal y = toReal y - toReal x from by ring,
        show -toReal y + toReal x = toReal x - toReal y from by ring, abs_sub_comm]
  dist_triangle x y z := by
    rw [show -x + z = (-x + y) + (-y + z) from by abel_nf]
    exact norm_add_le' _ _
  edist_dist x y := by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg' _)]
  eq_of_dist_eq_zero {a b} h := by
    have h1 := (norm_eq_zero' (-a + b)).mp h
    have h2 : a + (-a + b) = a + 0 := congr_arg (a + ·) h1
    rwa [add_neg_cancel_left, add_zero, eq_comm] at h2
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace ℝ (WeightedScalar w m) where
  toModule := inferInstance
  norm_smul_le c x := by
    show |c * toReal x| * w m ≤ |c| * (|toReal x| * w m)
    rw [abs_mul, mul_assoc]

instance instFiniteDimensional : FiniteDimensional ℝ (WeightedScalar w m) :=
  inferInstanceAs (FiniteDimensional ℝ ℝ)

instance instCompleteSpace : CompleteSpace (WeightedScalar w m) := by
  simpa using (FiniteDimensional.complete (𝕜 := ℝ) (E := WeightedScalar w m))

end WeightedScalar

/-! ### Generic lpOneAlg instances for WeightedScalar -/

/-- Generic `lpOneAlgRingData` for any `WeightedScalar w` with `PosWeight`.
All fields are trivial since `WeightedScalar w m = ℝ` with identity coercions. -/
instance WeightedScalar.instLpOneAlgRingData {M : Type*} [AddMonoid M]
    {w : M → ℝ} [PosWeight w] : lpOneAlgRingData M (WeightedScalar w) where
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

/-- Generic `lpOneAlgSmulCompat` — scalar multiplication is just ℝ multiplication. -/
instance WeightedScalar.instLpOneAlgSmulCompat {M : Type*} [AddMonoid M]
    {w : M → ℝ} [PosWeight w] : lpOneAlgSmulCompat M (WeightedScalar w) where
  toReal_smul _ _ _ := rfl

/-- Generic `lpOneAlgWeightMul` from `SubMulWeightBase` (submultiplicativity only).
Available for ALL ν > 0 — no weight ≥ 1 requirement. -/
instance WeightedScalar.instLpOneAlgWeightMul {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeightBase w] : lpOneAlgWeightMul M (WeightedScalar w) where
  norm_ofReal_mul_le := WeightedScalar.norm_ofReal_mul_le
  norm_ofReal_one_zero := by
    show |(1 : ℝ)| * w 0 = 1; simp [abs_one, SubMulWeightBase.weight_zero (w := w)]

/-- Generic `lpOneAlgWeightSubMul` from `SubMulWeight`.
Adds weight ≥ 1 on top of `lpOneAlgWeightMul`. Needs `[Fact (1 ≤ ν)]`. -/
instance WeightedScalar.instLpOneAlgWeightSubMul {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeight w] : lpOneAlgWeightSubMul M (WeightedScalar w) where
  norm_ofReal_one_ge := WeightedScalar.norm_ofReal_one_ge

end RadiiPolynomial

end
