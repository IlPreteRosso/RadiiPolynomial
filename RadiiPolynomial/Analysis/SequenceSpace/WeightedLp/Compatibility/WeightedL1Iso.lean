import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.LiftBound

/-!
# The wrapper `lpOneAlg M E ≃ₗᵢ WeightedLp M E 1`

`lpOneAlg.toLpₗᵢ` bundles the carrier wrapper as a linear isometry equivalence.
`WeightedLp.conjL1` conjugates an existing operator between library ℓ¹ carriers to the
framed `p = 1` carriers. Its atom coordinates are `coeff_conjL1_single`; the retained
norm transfers are `norm_apply_le_conjL1` and `opNorm_le_conjL1`.

`opNorm_le_of_kernelLiftBound_one` bounds an already supplied library operator using the
finite synthesis test on its atom images. This bound does not require scalar completeness.
The former wrapper/atom aliases, alternate column-sum wrapper and identification with a
constructed kernel extension are retired. No instance identifying the carriers is added.
-/

open scoped ENNReal

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

section Iso

variable (𝕜 : Type*) [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]

/-- **The wrapper as a linear isometric equivalence** `lpOneAlg M E ≃ₗᵢ[𝕜] WeightedLp M E 1`:
both carriers are `lp E 1`, so every field is `rfl`. -/
def toLpₗᵢ : lpOneAlg M E ≃ₗᵢ[𝕜] WeightedLp M E 1 where
  toFun f := f.toLp
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl


variable {𝕜} [FiberTrivialization 𝕜 M E] [DecidableEq M]



end Iso

end lpOneAlg

namespace WeightedLp

section Conj

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- An operator between two library ℓ¹ carriers, conjugated by the wrappers into an operator
between the `p = 1` carriers: `conjL1 T = toLpₗᵢ ∘ T ∘ toLpₗᵢ⁻¹`. -/
def conjL1 (T : lpOneAlg J E →L[𝕜] lpOneAlg I F) : WeightedLp J E 1 →L[𝕜] WeightedLp I F 1 :=
  (lpOneAlg.toLpₗᵢ 𝕜 (M := I) (E := F)).toLinearIsometry.toContinuousLinearMap.comp
    (T.comp (lpOneAlg.toLpₗᵢ 𝕜 (M := J) (E := E)).symm.toLinearIsometry.toContinuousLinearMap)


variable [FiberTrivialization 𝕜 J E] [FiberTrivialization 𝕜 I F] [DecidableEq J]

/-- The atom coordinates of the conjugate are the coefficients of `T` on the library atoms. -/
theorem coeff_conjL1_single (T : lpOneAlg J E →L[𝕜] lpOneAlg I F) (j : J) (r : 𝕜) (i : I) :
    coeff (conjL1 T (single j r)) i = lpOneAlg.toRealSeq (T (lpOneAlg.single j r)) i :=
  rfl

end Conj

section ConjOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- The norm transfer: `‖T f‖ ≤ ‖conjL1 T‖ ‖f‖` (both wrappers are isometric). -/
theorem norm_apply_le_conjL1 (T : lpOneAlg J E →L[𝕜] lpOneAlg I F) (f : lpOneAlg J E) :
    ‖T f‖ ≤ ‖conjL1 T‖ * ‖f‖ :=
  (conjL1 T).le_opNorm f.toLp

theorem opNorm_le_conjL1 (T : lpOneAlg J E →L[𝕜] lpOneAlg I F) : ‖T‖ ≤ ‖conjL1 T‖ :=
  T.opNorm_le_bound (norm_nonneg _) (norm_apply_le_conjL1 T)

end ConjOpNorm

section Kernel

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {I J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜} {C : ℝ}


end Kernel

section KernelOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜} {C : ℝ}

/-- **The `p = 1` kernel test bounds an existing operator between library ℓ¹ carriers.**
No completeness is needed: the finite test controls the norm of the conjugated operator. -/
theorem opNorm_le_of_kernelLiftBound_one (T : lpOneAlg J E →L[𝕜] lpOneAlg I F)
    (h : KernelLiftBound E F 1 K C)
    (hT : ∀ j i, lpOneAlg.toRealSeq (T (lpOneAlg.single j 1)) i = K i j) : ‖T‖ ≤ C := by
  apply (opNorm_le_conjL1 T).trans
  apply (opNorm_le_iff_liftBound ENNReal.one_ne_top (conjL1 T) h.toLiftBound.nonneg).2
  have hcol : (fun j => conjL1 T (single j 1)) = kcol K h.memℓp_col :=
    funext fun j => ext_coeff <| funext fun i => by
      rw [coeff_conjL1_single, coeff_kcol, hT]
  rw [hcol]
  exact h.toLiftBound


end KernelOpNorm

end WeightedLp

end RadiiPolynomial

end
