import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module

/-!
# Coefficient-preserving reweighting between weighted ℓᵖ carriers

Two frames `[FiberTrivialization 𝕜 I E]` and `[FiberTrivialization 𝕜 I F]` on the same index
type, with derived weights `ω^E` and `ω^F`, and a comparison `ω^F_i ≤ C ω^E_i` (`0 ≤ C`) give the
bounded linear map `reweightCLM hC hw : WeightedLp I E p →L[𝕜] WeightedLp I F p` that keeps the
scalar coordinates (`coeff_reweightCLM`), with `‖reweightCLM hC hw‖ ≤ C` (an upper bound, not the
operator norm). It is injective by coordinate extensionality (`ext_coeff`).

The service is the same exponent `1 ≤ p ≤ ∞` on both sides, an arbitrary index type (no
operation, order or decidable equality) and no completeness. The construction uses a normed
field; the operator-norm face uses a nontrivially normed field. This constructor asserts a
coefficient-preserving bounded linear map; it does not assert an algebra-homomorphism structure.
In its geometric-ℓ²-to-polynomial application, the source has no bounded convolution self-product.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Reweight

variable {𝕜 : Type*} [NormedField 𝕜] {I : Type*} {E F : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I E] [FiberTrivialization 𝕜 I F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ}

/-- The reweighted family `i ↦ θ^F_i (coeff x i)` lies in the target carrier, with norm at most
`C ‖x‖`. -/
private theorem reweight_memℓp (hC : 0 ≤ C)
    (hw : ∀ i, FiberTrivialization.weight (E := F) i ≤ C * FiberTrivialization.weight (E := E) i)
    (x : WeightedLp I E p) :
    ∃ h : Memℓp (fun i => FiberTrivialization.equiv (E := F) i (coeff x i)) p,
      ‖(⟨_, h⟩ : WeightedLp I F p)‖ ≤ C * ‖x‖ :=
  memℓp_norm_le_of_le_comp Function.injective_id x _ hC fun i => by
    rw [FiberTrivialization.norm_equiv_apply, id, norm_apply_eq, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hw i) (norm_nonneg _)

/-- **The coefficient-preserving reweighting** `WeightedLp I E p →L[𝕜] WeightedLp I F p` under
`ω^F ≤ C ω^E`, `0 ≤ C`. -/
def reweightCLM (hC : 0 ≤ C)
    (hw : ∀ i, FiberTrivialization.weight (E := F) i ≤ C * FiberTrivialization.weight (E := E) i) :
    WeightedLp I E p →L[𝕜] WeightedLp I F p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨_, (reweight_memℓp hC hw x).fst⟩
      map_add' := fun x y => ext_coeff <| funext fun i => (coeff_mk_equiv _ _ i).trans <| by
        simp only [coeff_add, Pi.add_apply, coeff_mk_equiv]
      map_smul' := fun c x => ext_coeff <| funext fun i => (coeff_mk_equiv _ _ i).trans <| by
        simp only [coeff_smul, Pi.smul_apply, coeff_mk_equiv, RingHom.id_apply] }
    C fun x => (reweight_memℓp hC hw x).snd

variable (hC : 0 ≤ C)
  (hw : ∀ i, FiberTrivialization.weight (E := F) i ≤ C * FiberTrivialization.weight (E := E) i)

/-- The reweighting keeps the scalar coordinates. -/
@[simp] theorem coeff_reweightCLM (x : WeightedLp I E p) (i : I) :
    coeff (reweightCLM hC hw x) i = coeff x i :=
  coeff_mk_equiv _ _ i

end Reweight

section OpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*} {E F : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I E] [FiberTrivialization 𝕜 I F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ}

/-- `‖reweightCLM hC hw‖ ≤ C`. -/
theorem norm_reweightCLM_le (hC : 0 ≤ C)
    (hw : ∀ i, FiberTrivialization.weight (E := F) i ≤ C * FiberTrivialization.weight (E := E) i) :
    ‖reweightCLM (p := p) hC hw‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end OpNorm

end RadiiPolynomial.WeightedLp

end
