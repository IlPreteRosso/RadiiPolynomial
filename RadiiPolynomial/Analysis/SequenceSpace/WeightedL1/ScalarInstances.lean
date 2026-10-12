import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier

/-!
# Glue: WeightedScalar as a lpOneAlg Fiber

Registers the standard frame of `WeightedScalar 𝕜 w` as a `FiberTrivialization` (from which the
legacy `lpAlgRingData` / `lpAlgSmulCompat` instances are derived) and the Beurling-weight classes
`lpOneAlgWeightMul`, `lpOneAlgWeightSubMul`.

Separating these instances from `WeightedL1/Scalar.lean` keeps `WeightedScalar` as a
self-contained weighted-scalar module, independent of `lpOneAlg`. Files that build
`lpOneAlg M (WeightedScalar 𝕜 w)` should import this file.
-/

noncomputable section

namespace RadiiPolynomial

/-- The standard frame of `WeightedScalar 𝕜 w`: `θ_m = WeightedScalar.equiv` (the identity of
`𝕜`). The legacy `lpAlgRingData` / `lpAlgSmulCompat` instances on `WeightedScalar 𝕜 w` are the
ones derived from this instance (`FiberTrivialization.toLpAlgRingData`,
`FiberTrivialization.toLpAlgSmulCompat`); there is no second instance path. -/
instance WeightedScalar.instFiberTrivialization {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {w : M → ℝ} [PosWeight w] :
    FiberTrivialization 𝕜 M (WeightedScalar 𝕜 w) where
  equiv _ := WeightedScalar.equiv

namespace WeightedScalar

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]

@[simp] lemma fiberTrivialization_equiv (m : M) :
    FiberTrivialization.equiv (E := WeightedScalar 𝕜 w) m = WeightedScalar.equiv := rfl

/-- Lemma of record: the derived weight of the standard model is the weight function. -/
@[simp] lemma fiberTrivialization_weight (m : M) :
    FiberTrivialization.weight (E := WeightedScalar 𝕜 w) m = w m := by
  show ‖(1 : 𝕜)‖ * w m = w m
  rw [norm_one, one_mul]

lemma lpAlgRingData_weight (m : M) :
    lpAlgRingData.weight (E := WeightedScalar 𝕜 w) m = w m :=
  fiberTrivialization_weight m

end WeightedScalar

/-- Generic `lpOneAlgWeightMul` from `SubMulWeightBase` (submultiplicativity only).
No weight ≥ 1 requirement: in the geometric specialization `w n = νⁿ` it is available for
all ν > 0. -/
instance WeightedScalar.instLpOneAlgWeightMul {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeightBase w] : lpOneAlgWeightMul 𝕜 M (WeightedScalar 𝕜 w) where
  weight_add_le j l := by
    simp only [WeightedScalar.lpAlgRingData_weight]
    exact SubMulWeightBase.submul j l
  weight_zero := by
    rw [WeightedScalar.lpAlgRingData_weight]
    exact SubMulWeightBase.weight_zero

/-- Generic `lpOneAlgWeightSubMul` from `SubMulWeight`.
Adds weight ≥ 1 on top of `lpOneAlgWeightMul`. In the geometric specialization `w n = νⁿ`
the `SubMulWeight` instance needs `[Fact (1 ≤ ν)]`. -/
instance WeightedScalar.instLpOneAlgWeightSubMul {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} [AddCommMonoid M]
    {w : M → ℝ} [SubMulWeight w] : lpOneAlgWeightSubMul 𝕜 M (WeightedScalar 𝕜 w) where
  one_le_weight m := by
    rw [WeightedScalar.lpAlgRingData_weight]
    exact SuperUnitWeight.one_le m

end RadiiPolynomial

end
