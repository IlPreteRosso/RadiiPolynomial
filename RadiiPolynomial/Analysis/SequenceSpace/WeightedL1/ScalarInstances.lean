import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Algebra

/-!
# Glue: WeightedScalar as a lpOneAlg Fiber

Registers `WeightedScalar 𝕜 w` as satisfying the `lpOneAlg` fiber-data typeclasses
(`lpAlgRingData`, `lpAlgSmulCompat`, `lpOneAlgWeightMul`, `lpOneAlgWeightSubMul`).

Separating these instances from `WeightedScalar.lean` keeps `WeightedScalar` as a
self-contained weighted-scalar module, independent of `lpOneAlg`. Files that build
`lpOneAlg M (WeightedScalar 𝕜 w)` should import this file.
-/

noncomputable section

namespace RadiiPolynomial

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
