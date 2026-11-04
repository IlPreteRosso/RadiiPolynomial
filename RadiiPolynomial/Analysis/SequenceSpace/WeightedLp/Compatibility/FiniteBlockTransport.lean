import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.WeightedL1Iso
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock

/-!
# Finite matrices on the library ℓ¹ carrier

The finite matrix `WeightedLp.finMatrixCLM F A` of `Operators/FiniteBlock` (a finite sum of
rank-one operators, no column bound) transported to `lpOneAlg M E` through the wrapper
`lpOneAlg.toLpₗᵢ : lpOneAlg M E ≃ₗᵢ[𝕜] WeightedLp M E 1` (`Compatibility/WeightedL1Iso`; no new
carrier equivalence): `lpOneAlg.finMatrixCLM F A = toLpₗᵢ⁻¹ ∘ finMatrixCLM F A ∘ toLpₗᵢ`, with the
coefficient face `toRealSeq_finMatrixCLM` (`(A x)_i = 1_(i ∈ F) ∑_(j ∈ F) A i j x_j`; the
coefficients of the two carriers agree by `rfl`).
-/

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
variable (F : Finset M) (A : M → M → 𝕜)

/-- **A finite matrix on the library ℓ¹ carrier**: `x ↦ ∑_(j ∈ F) x_j ∑_(i ∈ F) A i j e_i`, the
transport of `WeightedLp.finMatrixCLM` at `p = 1` along `toLpₗᵢ`. -/
def finMatrixCLM : lpOneAlg M E →L[𝕜] lpOneAlg M E :=
  (toLpₗᵢ 𝕜 (M := M) (E := E)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((WeightedLp.finMatrixCLM (p := 1) F A).comp
      (toLpₗᵢ 𝕜 (M := M) (E := E)).toLinearIsometry.toContinuousLinearMap)

/-- The finite matrix in coordinates: `(A x)_i = 1_(i ∈ F) ∑_(j ∈ F) A i j x_j`. -/
theorem toRealSeq_finMatrixCLM (x : lpOneAlg M E) (i : M) :
    toRealSeq (finMatrixCLM F A x) i = if i ∈ F then ∑ j ∈ F, A i j * toRealSeq x j else 0 :=
  WeightedLp.coeff_finMatrixCLM F A (toLpₗᵢ 𝕜 x) i

end lpOneAlg

end RadiiPolynomial

end
