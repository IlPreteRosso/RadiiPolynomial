import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Generic Weighted Scalar Fiber

`WeightedScalar 𝕜 w m` is `𝕜` equipped with norm `‖x‖ * w(m)` where `w : M → ℝ` is a
positive weight function. This provides a single parameterized fiber type that unifies
`ScaledReal`, `ScaledRealZ`, and `OmegaScaledReal`.

## Main definitions

- `WeightedScalar 𝕜 w m`: 𝕜 with weighted norm
- `WeightedScalar.equiv`: the standard frame `θ_m : 𝕜 ≃ₗ[𝕜] WeightedScalar 𝕜 w m` (the identity
  of `𝕜`), with its additive view `WeightedScalar.ofReal` and the inverse map
  `WeightedScalar.toReal`
- `PosWeight w`: weight with positive values (→ NormedAddCommGroup)
- `SubMulWeightBase w`: positive submultiplicative weight (→ ring and normed-ring
  structure on lpOneAlg, through `WeightedScalar.instLpOneAlgWeightMul`)
- `NormalizedWeight w`: independent normalization `w 0 = 1` (adds a norm-one unit)

The lower bound `∀ m, 1 ≤ w m` is independent of positivity and submultiplicativity.
Pointwise coefficient estimates can use it with the weighted norm identity
`lpOneAlg.norm_eq_abs_toReal_mul_weight`.
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

/-- Positive submultiplicative weight (extends PosWeight).
Sufficient for Ring on `lpOneAlg` (through `WeightedScalar.instLpOneAlgWeightMul`) when the
addition fibers are finite (HasAntidiagonal) or the scalar field is complete. -/
class SubMulWeightBase {M : Type*} [AddCommMonoid M] (w : M → ℝ) extends PosWeight w where
  submul : ∀ m n, w (m + n) ≤ w m * w n

/-- Unit normalization of a weight. Neither positivity nor submultiplicativity is assumed. -/
class NormalizedWeight {M : Type*} [Zero M] (w : M → ℝ) : Prop where
  weight_zero : w 0 = 1

/-! ### WeightedScalar Type -/

/-- Generic weighted scalar fiber: `𝕜` with norm `‖x‖_𝕜 * w(m)`.
`def` (not `abbrev`) prevents typeclass diamond with the standard `𝕜` norm.
`@[implicit_reducible]` lets `isDefEq` see through the synonym when checking implicit and
instance-implicit arguments — enough for `simp`/`rfl` to close goals that differ only by it —
while keeping it opaque to typeclass *search*, so the custom norm instance is still found. -/
@[implicit_reducible]
def WeightedScalar (𝕜 : Type*) {M : Type*} (_w : M → ℝ) (_m : M) := 𝕜

namespace WeightedScalar

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} {m : M}

/-! ### Instances inherited from 𝕜 -/

instance : AddCommGroup (WeightedScalar 𝕜 w m) := inferInstanceAs (AddCommGroup 𝕜)
instance : Module 𝕜 (WeightedScalar 𝕜 w m) := inferInstanceAs (Module 𝕜 𝕜)

/-! No `Ring` instance: no construction multiplies inside a fiber. The product of the
weighted ℓ¹ algebra is the cross-fiber convolution, and the atom of a fiber is
`equiv 1` with `1 : 𝕜`, not a fiber-internal unit. -/

/-- The standard frame `θ_m : 𝕜 ≃ₗ[𝕜] WeightedScalar 𝕜 w m` (the identity of `𝕜`). It is the
`FiberTrivialization` of the standard model (instance in `ScalarInstances.lean`). -/
def equiv : 𝕜 ≃ₗ[𝕜] WeightedScalar 𝕜 w m := LinearEquiv.refl 𝕜 𝕜

/-! ### Coercion to 𝕜 -/

/-- Identity map to `𝕜`. -/
@[coe] def toReal (x : WeightedScalar 𝕜 w m) : 𝕜 := x

/-- Additive equivalence from `𝕜` (the additive view of `equiv`). The body is kept as
`AddEquiv.refl 𝕜` rather than `equiv.toAddEquiv`, so its unfolding behaviour is unchanged;
the two are definitionally equal. -/
def ofReal : 𝕜 ≃+ WeightedScalar 𝕜 w m := AddEquiv.refl 𝕜


/-- The frame applied is the additive view `ofReal` (the simp normal form). -/
@[simp] lemma equiv_apply (r : 𝕜) : (equiv r : WeightedScalar 𝕜 w m) = ofReal r := rfl

@[simp] lemma equiv_symm_apply (x : WeightedScalar 𝕜 w m) :
    (equiv : 𝕜 ≃ₗ[𝕜] WeightedScalar 𝕜 w m).symm x = toReal x := rfl


-- No coe_*/toReal_apply simp lemmas; use equiv_apply, equiv_symm_apply and norm_def.

/-! ### Weighted Norm -/

instance instNorm : Norm (WeightedScalar 𝕜 w m) where
  norm x := ‖toReal x‖ * w m

lemma norm_def (x : WeightedScalar 𝕜 w m) : ‖x‖ = ‖toReal x‖ * w m := rfl

@[simp] lemma norm_ofReal (r : 𝕜) : ‖(ofReal r : WeightedScalar 𝕜 w m)‖ = ‖r‖ * w m := rfl


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

/-- The weighted-norm laws `norm_nonneg'`, `norm_smul'`, `norm_add_le'`, `norm_eq_zero'` as a
`NormedSpace.Core`: the source of the normed-group and normed-space instances below. -/
theorem normedSpaceCore : NormedSpace.Core 𝕜 (WeightedScalar 𝕜 w m) :=
  ⟨⟨norm_nonneg', norm_smul', norm_add_le'⟩, norm_eq_zero'⟩

/-- The normed group of the weighted norm, built from `normedSpaceCore`. The explicit `edist`
field is the default `ENNReal.ofReal ∘ dist`; `NormedAddCommGroup.ofCore` alone constructs the
extended distance through a different term. -/
instance instNormedAddCommGroup : NormedAddCommGroup (WeightedScalar 𝕜 w m) :=
  { NormedAddCommGroup.ofCore normedSpaceCore with
    edist := fun x y => ENNReal.ofReal ‖-x + y‖
    edist_dist := fun _ _ => rfl }

instance instNormedSpace : NormedSpace 𝕜 (WeightedScalar 𝕜 w m) :=
  NormedSpace.ofCore normedSpaceCore

instance instFiniteDimensional : FiniteDimensional 𝕜 (WeightedScalar 𝕜 w m) :=
  inferInstanceAs (FiniteDimensional 𝕜 𝕜)

end WeightedScalar

/-- `CompleteSpace` for `WeightedScalar 𝕜 w m`, transferred from the complete scalar field
through the identity frame and its positive norm-scaling factor. -/
instance WeightedScalar.instCompleteSpace {𝕜 : Type*} [NormedField 𝕜]
    [CompleteSpace 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w] {m : M} :
    CompleteSpace (WeightedScalar 𝕜 w m) := by
  let e : 𝕜 ≃L[𝕜] WeightedScalar 𝕜 w m :=
    (WeightedScalar.equiv : 𝕜 ≃ₗ[𝕜] WeightedScalar 𝕜 w m).toContinuousLinearEquivOfBounds
      (w m) (w m)⁻¹
      (fun r => by rw [WeightedScalar.equiv_apply, WeightedScalar.norm_ofReal, mul_comm])
      (fun x => by
        rw [WeightedScalar.equiv_symm_apply, WeightedScalar.norm_def, mul_left_comm,
          inv_mul_cancel₀ (PosWeight.weight_ne_zero m), mul_one])
  exact (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp
    inferInstance

end RadiiPolynomial

end
