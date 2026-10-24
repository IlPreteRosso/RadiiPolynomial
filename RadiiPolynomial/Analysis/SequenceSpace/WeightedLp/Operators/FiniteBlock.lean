import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDefect

/-! Physical finite matrices and composed head leakage. Matrix multiplication and boundary summation occur before entry modulus; block Schur faces give upper bounds. The finite-head solver service (§FiniteHead) proves head injectivity on the finite-dimensional head range from a defect bound `‖P − M K‖ < 1` and turns it into the raw-zero equivalence of a finite-head / diagonal-tail coefficient solver; it is head injectivity, not full-space injectivity from finite range. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Expansion

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Physical matrix coefficients of an operator, obtained by applying it to the scalar atoms. -/
def matrixOf (T : WeightedLp M E p →L[𝕜] WeightedLp M E p) (n k : M) : 𝕜 :=
  coeff (T (single k 1)) n


omit [Fact (1 ≤ p)] in
/-- **The finite expansion**: a vector whose coordinates vanish off `G` is the finite sum of its
atoms, `x = ∑ j ∈ G, single j (coeff x j)`. -/
theorem eq_sum_single_of_coeff_eq_zero {G : Finset M} {x : WeightedLp M E p}
    (hx : ∀ k ∉ G, coeff x k = 0) : x = ∑ j ∈ G, single j (coeff x j) :=
  ext_coeff <| funext fun i => by
    rw [coeff_sum_single]
    split_ifs with hi
    · rfl
    · exact hx i hi

/-- **The finite input expansion**: for a vector `x` whose coordinates vanish off `G` and every
bounded `T`, `coeff (T x) i = ∑ j ∈ G, matrixOf T i j * coeff x j` (linearity on a finite sum;
no density, every `1 ≤ p ≤ ∞`). -/
theorem coeff_apply_of_coeff_eq_zero (T : WeightedLp M E p →L[𝕜] WeightedLp M E p) {G : Finset M}
    {x : WeightedLp M E p} (hx : ∀ k ∉ G, coeff x k = 0) (i : M) :
    coeff (T x) i = ∑ j ∈ G, matrixOf T i j * coeff x j := by
  have h := map_sum ((coeffCLM (E := E) (p := p) i).comp T)
    (fun j => single (E := E) (p := p) j (coeff x j)) G
  rw [← eq_sum_single_of_coeff_eq_zero hx] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [ContinuousLinearMap.comp_apply, coeffCLM_apply, single_eq_smul, map_smul, coeff_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm, matrixOf]

/-- The kernel of a difference is the difference of the kernels. -/
theorem matrixOf_sub (T₁ T₂ : WeightedLp M E p →L[𝕜] WeightedLp M E p) (i k : M) :
    matrixOf (T₁ - T₂) i k = matrixOf T₁ i k - matrixOf T₂ i k := by
  rw [matrixOf, sub_apply, coeff_sub, Pi.sub_apply]
  rfl

/-- A diagonal operator has the diagonal matrix. -/
theorem matrixOf_diagCLM (d : M → 𝕜) (hd : BddAbove (Set.range fun n => ‖d n‖)) (i k : M) :
    matrixOf (diagCLM (E := E) (p := p) d hd) i k = if i = k then d i else 0 := by
  rw [matrixOf, coeff_diagCLM, coeff_single]
  by_cases h : i = k
  · subst h
    rw [Pi.single_eq_same, mul_one, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne h, mul_zero, ite_eq_right h]

/-- The head projection has the `0/1` identity on `F`. -/
theorem matrixOf_headProj (F : Finset M) (i k : M) :
    matrixOf (headProj (𝕜 := 𝕜) (E := E) (p := p) F) i k = if i = k ∧ i ∈ F then 1 else 0 := by
  rw [matrixOf, coeff_headProj, coeff_single]
  by_cases h : i = k
  · subst h
    simp only [Pi.single_eq_same, true_and]
  · simp [h]

/-- **The composition law through a finite middle**: if the outputs of `T₂` vanish off `F`, then
`matrixOf (T₁ ∘ T₂) i k = ∑ n ∈ F, matrixOf T₁ i n * matrixOf T₂ n k` (the finite input
expansion at `x = T₂ (single k 1)`). -/
theorem matrixOf_comp_of_support (T₁ T₂ : WeightedLp M E p →L[𝕜] WeightedLp M E p)
    {F : Finset M} (h₂ : ∀ x, ∀ n ∉ F, coeff (T₂ x) n = 0) (i k : M) :
    matrixOf (T₁ ∘L T₂) i k = ∑ n ∈ F, matrixOf T₁ i n * matrixOf T₂ n k :=
  coeff_apply_of_coeff_eq_zero T₁ (h₂ _) i

end Expansion

section SymbolLaws

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M)

/-- The symbol action has the Laurent matrix `matrixOf L_β n k = β_{n - k}`. -/
theorem matrixOf_symbolAction₀ (n k : M) :
    matrixOf (symbolAction₀ (p := p) hC β) n k = rawSymbol β (n - k) := by
  rw [matrixOf, symbolAction₀_apply,
    ← kernelCLM_laurent_eq_symbolSeries (memL1v_rawSymbol β) hC, kernelCLM_apply_coeff,
    coeff_single, tsum_eq_single k fun j hj => by rw [Pi.single_eq_of_ne hj, mul_zero],
    Pi.single_eq_same, mul_one, laurentKernel]

/-- The head leakage `P_S L_β Q_S` has the leakage kernel `1_{n ∈ S} 1_{k ∉ S} β_{n - k}`. -/
theorem matrixOf_headLeakage (n k : M) :
    matrixOf (headProj (𝕜 := 𝕜) S ∘L symbolAction₀ (p := p) hC β ∘L tailProj (𝕜 := 𝕜) S) n k =
      leakKernel β S n k := by
  rw [matrixOf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    coeff_headProj_symbolAction_tailProj, coeff_single,
    tsum_eq_single k fun j hj => by rw [Pi.single_eq_of_ne hj, mul_zero], Pi.single_eq_same,
    mul_one]

/-- **The head block of the symbol action** `P_S L_β P_S` has the masked Laurent matrix
`1_{n ∈ S} 1_{k ∈ S} β_{n - k}`. -/
theorem matrixOf_headProj_symbolAction_headProj (n k : M) :
    matrixOf (headProj (𝕜 := 𝕜) S ∘L symbolAction₀ (p := p) hC β ∘L headProj (𝕜 := 𝕜) S) n k =
      if n ∈ S ∧ k ∈ S then rawSymbol β (n - k) else 0 := by
  rw [matrixOf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coeff_headProj]
  by_cases hk : k ∈ S
  · have hPk : headProj (𝕜 := 𝕜) (E := E) (p := p) S (single k 1) = single k 1 :=
      ext_coeff <| funext fun j => by
        rw [coeff_headProj, coeff_single]
        by_cases hj : j ∈ S
        · rw [ite_eq_left hj]
        · rw [ite_eq_right hj, Pi.single_eq_of_ne (fun h : j = k => hj (h ▸ hk))]
    rw [hPk, show coeff (symbolAction₀ (p := p) hC β (single k 1)) n = rawSymbol β (n - k) from
      matrixOf_symbolAction₀ hC β n k]
    simp only [hk, and_true]
  · have hPk : headProj (𝕜 := 𝕜) (E := E) (p := p) S (single k 1) = 0 :=
      ext_coeff <| funext fun j => by
        rw [coeff_headProj, coeff_single, coeff_zero, Pi.zero_apply]
        by_cases hj : j ∈ S
        · rw [ite_eq_left hj, Pi.single_eq_of_ne (fun h : j = k => hk (h ▸ hj))]
        · rw [ite_eq_right hj]
    rw [hPk, map_zero, coeff_zero, Pi.zero_apply]
    simp [hk]

end SymbolLaws

section FinMatrix

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (F : Finset M) (A : M → M → 𝕜)

/-- **A finite matrix as a bounded operator**: `x ↦ ∑ j ∈ F, x_j ∑ i ∈ F, A i j e_i`, a finite
sum of rank-one operators (no Schur hypothesis). -/
def finMatrixCLM : WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  ∑ j ∈ F, (coeffCLM j).smulRight (∑ i ∈ F, single i (A i j))

/-- The finite matrix in coordinates: `coeff (A x) i = 1_{i ∈ F} ∑ j ∈ F, A i j x_j`. -/
@[simp] theorem coeff_finMatrixCLM (x : WeightedLp M E p) (i : M) :
    coeff (finMatrixCLM F A x) i = if i ∈ F then ∑ j ∈ F, A i j * coeff x j else 0 := by
  have h := map_sum (coeffCLM (E := E) (p := p) i)
    (fun j => coeff x j • ∑ i' ∈ F, single (E := E) (p := p) i' (A i' j)) F
  simp only [coeffCLM_apply, coeff_smul, Pi.smul_apply, smul_eq_mul, coeff_sum_single]
    at h
  rw [finMatrixCLM, sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, coeffCLM_apply]
  rw [h]
  split_ifs with hi
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact Finset.sum_eq_zero fun j _ => mul_zero _

/-- The matrix of a finite matrix is its restriction `1_{F × F} A`. -/
theorem matrixOf_finMatrixCLM (i k : M) :
    matrixOf (finMatrixCLM (E := E) (p := p) F A) i k = if i ∈ F ∧ k ∈ F then A i k else 0 := by
  rw [matrixOf, coeff_finMatrixCLM, coeff_single]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_and]

/-- `P_F ∘ A = A` for a finite matrix on `F`. -/
theorem headProj_comp_finMatrixCLM :
    headProj (𝕜 := 𝕜) F ∘L finMatrixCLM F A = finMatrixCLM (E := E) (p := p) F A :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun i => by
    rw [ContinuousLinearMap.comp_apply, coeff_headProj, coeff_finMatrixCLM]
    split_ifs <;> rfl


end FinMatrix

section BlockGeometry

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The block kernel `1_{i ∈ F} 1_{j ∈ G} matrixOf T i j` of an operator on the block `F × G`. -/
def blockKernel (T : WeightedLp M E p →L[𝕜] WeightedLp M E p) (F G : Finset M) : M → M → 𝕜 :=
  fun i j => if i ∈ F ∧ j ∈ G then matrixOf T i j else 0

/-- **The Schur hypotheses of a block kernel are finite sums** (`SchurBound.ofFinsets`): row sums
over `G` at most `R` on `F`, column sums over `F` at most `C` on `G`. -/
theorem schurBound_blockKernel (T : WeightedLp M E p →L[𝕜] WeightedLp M E p) {F G : Finset M}
    {R C : ℝ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hR : ∀ i ∈ F, ∑ j ∈ G, schurEntry (FiberTrivialization.weight (E := E))
      (FiberTrivialization.weight (E := E)) (matrixOf T) i j ≤ R)
    (hC : ∀ j ∈ G, ∑ i ∈ F, schurEntry (FiberTrivialization.weight (E := E))
      (FiberTrivialization.weight (E := E)) (matrixOf T) i j ≤ C) :
    SchurBound (FiberTrivialization.weight (E := E)) (FiberTrivialization.weight (E := E))
      (blockKernel T F G) R C :=
  SchurBound.ofFinsets (fun _ => G) (fun _ => F)
    (fun i j hK => not_not.1 fun hj => hK (by rw [blockKernel, ite_eq_right fun h => hj h.2]))
    (fun i j hK => not_not.1 fun hi => hK (by rw [blockKernel, ite_eq_right fun h => hi h.1]))
    hR0 hC0
    (fun i => if hi : i ∈ F then
        (Finset.sum_congr rfl fun j hj => by
          rw [schurEntry, schurEntry, blockKernel, ite_eq_left ⟨hi, hj⟩]).trans_le (hR i hi)
      else (Finset.sum_eq_zero fun j _ => schurEntry_of_eq_zero (by
          rw [blockKernel, ite_eq_right fun h => hi h.1])).trans_le hR0)
    (fun j => if hj : j ∈ G then
        (Finset.sum_congr rfl fun i hi => by
          rw [schurEntry, schurEntry, blockKernel, ite_eq_left ⟨hi, hj⟩]).trans_le (hC j hj)
      else (Finset.sum_eq_zero fun i _ => schurEntry_of_eq_zero (by
          rw [blockKernel, ite_eq_right fun h => hj h.2])).trans_le hC0)

end BlockGeometry

section BlockNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]

/-- **The block Schur producer** (UPPER) at `p = 2`: an operator with `P_F ∘ T ∘ P_G = T` has
`‖T‖ ≤ √(R C)` for any `R ≥` the normalized row sums of `matrixOf T` over `G` on `F` and any
`C ≥` its normalized column sums over `F` on `G`. -/
theorem norm_le_sqrt_of_block (T : WeightedLp M E 2 →L[𝕜] WeightedLp M E 2) {F G : Finset M}
    (hT : headProj (𝕜 := 𝕜) F ∘L T ∘L headProj (𝕜 := 𝕜) G = T) {R C : ℝ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hR : ∀ i ∈ F, ∑ j ∈ G, schurEntry (FiberTrivialization.weight (E := E))
      (FiberTrivialization.weight (E := E)) (matrixOf T) i j ≤ R)
    (hC : ∀ j ∈ G, ∑ i ∈ F, schurEntry (FiberTrivialization.weight (E := E))
      (FiberTrivialization.weight (E := E)) (matrixOf T) i j ≤ C) :
    ‖T‖ ≤ √(R * C) := by
  classical
  have h := schurBound_blockKernel T hR0 hC0 hR hC
  refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) fun x => ?_
  -- Each row is a finite sum, so its actual scalar convergence needs no completeness.
  have hfinite (i : M) : HasSum (fun j => blockKernel T F G i j * coeff x j)
      (∑ j ∈ G, blockKernel T F G i j * coeff x j) :=
    hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [blockKernel, ite_eq_right fun h' => hj h'.2, zero_mul]
  obtain ⟨_, hm, hle⟩ :=
    schur_bound_of (E := E) (F := E) (p := 2) (K := blockKernel T F G) 2
      (fun _ => h.toRowSum) (fun _ => h.toColSum) x
  have hcoeff (i : M) : coeff (T x) i = ∑' j, blockKernel T F G i j * coeff x j := by
    have hG : ∀ k ∉ G, coeff (headProj (𝕜 := 𝕜) (E := E) (p := 2) G x) k = 0 := fun k hk => by
      rw [coeff_headProj, ite_eq_right hk]
    rw [(hfinite i).tsum_eq, ← DFunLike.congr_fun hT x,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      coeff_headProj, coeff_apply_of_coeff_eq_zero T hG]
    split_ifs with hi
    · exact Finset.sum_congr rfl fun j hj => by
        rw [coeff_headProj, ite_eq_left hj, blockKernel, ite_eq_left ⟨hi, hj⟩]
    · exact (Finset.sum_eq_zero fun j _ => by
        rw [blockKernel, ite_eq_right fun h' => hi h'.1, zero_mul]).symm
  have heq : (⟨_, hm⟩ : WeightedLp M E 2) = T x := by
    apply ext_coeff
    funext i
    change (FiberTrivialization.equiv (E := E) i).symm
      (FiberTrivialization.equiv (E := E) i (∑' j, blockKernel T F G i j * coeff x j)) =
        coeff (T x) i
    rw [LinearEquiv.symm_apply_apply]
    exact (hcoeff i).symm
  rw [heq] at hle
  have hRC : R ^ (1 / (2 : ℝ≥0∞).toReal) * C ^ (1 / (2 : ℝ≥0∞).toReal) = √(R * C) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hR0 hC0]
    norm_num
  simpa only [hRC] using hle

end BlockNorm

section ComposedKernel

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : M → ℝ} [PosWeight v] {C : ℝ}

/-- **The composed leakage kernel**
`K_M(i,k) = ∑ n ∈ leakRows S B, matrixOf headOp i n · β_{n - k}`.
Under a band `B` of `β` the sum over the boundary rows equals the sum over the whole head `S`:
if `n ∈ S`, `k ∉ S` and `β_{n - k} ≠ 0`, then `b := n - k ∈ B` and `n - b = k ∉ S`, so
`n ∈ leakRows S B`. This is an unmasked finite sum; the composite's kernel is its restriction to
`S × leakCols S B`, extended by zero. -/
def composedLeakKernel (headOp : WeightedLp M E p →L[𝕜] WeightedLp M E p)
    (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S B : Finset M) : M → M → 𝕜 :=
  fun i k => ∑ n ∈ leakRows S B, matrixOf headOp i n * rawSymbol β (n - k)

end ComposedKernel

section ComposedIdentities

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S B : Finset M)
  (headOp : WeightedLp M E p →L[𝕜] WeightedLp M E p)

/-- **The composed head leakage lives on the block `S × leakCols S B`** (band `B`,
`P_S ∘ headOp = headOp`): `P_S ∘ (headOp P_S L_β Q_S) ∘ P_{leakCols} = headOp P_S L_β Q_S`. -/
theorem headLeakage_comp_block (hB : ∀ l ∉ B, rawSymbol β l = 0)
    (hPM : headProj (𝕜 := 𝕜) S ∘L headOp = headOp) :
    headProj (𝕜 := 𝕜) S ∘L (headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S) ∘L
        headProj (𝕜 := 𝕜) (leakCols S B) =
      headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S :=
  ContinuousLinearMap.ext fun x => by
    have h1 : (headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S) (headProj (𝕜 := 𝕜) (leakCols S B) x) =
        (headProj (𝕜 := 𝕜) (E := E) (p := p) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S) x := by
      rw [headLeakage_eq_boundary hC β S hB]
      simp only [ContinuousLinearMap.comp_apply]
      rw [show headProj (𝕜 := 𝕜) (E := E) (p := p) (leakCols S B) (headProj (𝕜 := 𝕜) (leakCols S B) x) =
        headProj (𝕜 := 𝕜) (leakCols S B) x from DFunLike.congr_fun (headProj_comp_headProj _) x]
    simp only [ContinuousLinearMap.comp_apply] at h1 ⊢
    rw [h1]
    exact DFunLike.congr_fun hPM _

/-- **The kernel of the composed head leakage on the band columns**: for `k ∈ leakCols S B`,
`matrixOf (headOp P_S L_β Q_S) i k = K_M(i,k)` (the composition law at the finite middle
`leakRows S B`, from the boundary face `headLeakage_eq_boundary`). -/
theorem matrixOf_headOp_headLeakage (hB : ∀ l ∉ B, rawSymbol β l = 0) (i : M) {k : M}
    (hk : k ∈ leakCols S B) :
    matrixOf (headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S) i k =
      composedLeakKernel headOp β S B i k := by
  have h₂ : ∀ x, ∀ n ∉ leakRows S B,
      coeff ((headProj (𝕜 := 𝕜) (E := E) (p := p) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S) x) n = 0 :=
    fun x n hn => by
      rw [headLeakage_eq_boundary hC β S hB, ContinuousLinearMap.comp_apply, coeff_headProj,
        ite_eq_right hn]
  rw [matrixOf_comp_of_support headOp _ h₂]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [matrixOf_headLeakage, leakKernel,
    ite_eq_left ⟨(Finset.mem_filter.1 hn).1, (mem_leakCols.1 hk).1⟩]

end ComposedIdentities

section ComposedNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S B : Finset M)
  (headOp : WeightedLp M E 2 →L[𝕜] WeightedLp M E 2)

/-- **The composed head term** (UPPER): under the band and
`P_S ∘ headOp = headOp`, `‖headOp P_S L_β Q_S‖ ≤ √(R_M C_M)` for any bounds `R_M`, `C_M` of the
normalized row sums (over `leakCols S B`, on `S`) and column sums (over `S`, on `leakCols S B`)
of `‖K_M‖`, the absolute values taken after the finite sum. -/
theorem norm_head_term_le_composed (hB : ∀ l ∉ B, rawSymbol β l = 0)
    (hPM : headProj (𝕜 := 𝕜) S ∘L headOp = headOp) {Rm Cm : ℝ} (hR0 : 0 ≤ Rm) (hC0 : 0 ≤ Cm)
    (hR : ∀ i ∈ S, ∑ k ∈ leakCols S B, ‖composedLeakKernel headOp β S B i k‖ *
      FiberTrivialization.weight (E := E) i / FiberTrivialization.weight (E := E) k ≤ Rm)
    (hCm : ∀ k ∈ leakCols S B, ∑ i ∈ S, ‖composedLeakKernel headOp β S B i k‖ *
      FiberTrivialization.weight (E := E) i / FiberTrivialization.weight (E := E) k ≤ Cm) :
    ‖headOp ∘L headProj (𝕜 := 𝕜) (E := E) (p := 2) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S‖ ≤
      √(Rm * Cm) :=
  norm_le_sqrt_of_block _ (headLeakage_comp_block hC β S B headOp hB hPM) hR0 hC0
    (fun i hi => (Finset.sum_congr rfl fun k hk => by
      rw [schurEntry, matrixOf_headOp_headLeakage hC β S B headOp hB i hk]).trans_le (hR i hi))
    (fun k hk => (Finset.sum_congr rfl fun i _ => by
      rw [schurEntry, matrixOf_headOp_headLeakage hC β S B headOp hB i hk]).trans_le (hCm k hk))

end ComposedNorm

section FiniteHead

/-! ### The finite-head solver service

A coefficient solver `x ↦ M x + d x` with a finite head `F`, a head operator `M` and a diagonal
tail `d` is inverted in three steps. `eq_zero_of_mem_of_norm_sub_comp_lt_one` is the
carrier-neutral head injectivity: on a finite-dimensional subspace `V` with `P|_V = id`,
`K(V) ⊆ V` and `‖P − M K‖ < 1`, `M` is injective on `V`. `eq_zero_of_headProj_eq_of_norm_lt_one`
is its instance at `V = range P_F` on any framed carrier and any `1 ≤ p ≤ ∞`.
`eq_zero_iff_of_coeff_eq_headSolve` turns head injectivity into the raw-zero equivalence
`G u = 0 ↔ R u = 0` for a coefficient solver identity
`coeff (G u) k = coeff (M (J (R u))) k + d k * R u k`. -/

section HeadInjectivity

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Finite-dimensional head injectivity**: on a finite-dimensional subspace `V` with `P v = v`
and `K v ∈ V` for `v ∈ V`, the defect bound `‖P − M ∘ K‖ < 1` makes `M` injective on `V`. The
bound gives `‖v‖ = ‖(P − M K) v‖ ≤ ‖P − M K‖ ‖v‖` when `M K v = 0`, so `M K` is injective on `V`;
then `K|_V` is an injective endomorphism of the finite-dimensional `V`, hence surjective
(`LinearMap.injective_iff_surjective`), and `x = K y`, `M K y = 0` give `y = 0`, `x = 0`. No
completeness, Neumann series or `M(V) ⊆ V` is used. -/
theorem eq_zero_of_mem_of_norm_sub_comp_lt_one (V : Submodule 𝕜 X) [FiniteDimensional 𝕜 V]
    {P M K : X →L[𝕜] X} (hP : ∀ v ∈ V, P v = v) (hK : ∀ v ∈ V, K v ∈ V)
    (h : ‖P - M ∘L K‖ < 1) {x : X} (hx : x ∈ V) (hMx : M x = 0) : x = 0 := by
  have hMK : ∀ v ∈ V, M (K v) = 0 → v = 0 := fun v hv hv0 => by
    have h1 := (P - M ∘L K).le_opNorm v
    rw [sub_apply, ContinuousLinearMap.comp_apply, hv0, sub_zero, hP v hv] at h1
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v))
  have hinj : Function.Injective ((K : X →ₗ[𝕜] X).restrict hK) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext (hMK v v.2 ?_)
    have e := congrArg Subtype.val hv
    rw [LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe] at e
    rw [e, Submodule.coe_zero, map_zero]
  obtain ⟨⟨y, hy⟩, hyx⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨x, hx⟩
  have hKy : K y = x := congrArg Subtype.val hyx
  rw [← hKy, hMK y hy (by rw [hKy, hMx]), map_zero]

end HeadInjectivity

section HeadRange

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The range of `P_F` lies in the span of the atoms `e_j`, `j ∈ F` (the finite expansion). -/
theorem range_headProj_le_span (F : Finset M) :
    LinearMap.range (headProj (𝕜 := 𝕜) (E := E) (p := p) F).toLinearMap ≤
      Submodule.span 𝕜 ((fun j => single (E := E) (p := p) j (1 : 𝕜)) '' (F : Set M)) := by
  rintro _ ⟨x, rfl⟩
  have hx : ∀ k ∉ F, coeff (headProj (𝕜 := 𝕜) (E := E) (p := p) F x) k = 0 := fun k hk => by
    rw [coeff_headProj, ite_eq_right hk]
  rw [ContinuousLinearMap.coe_coe, eq_sum_single_of_coeff_eq_zero hx]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [single_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_coe.2 hj, rfl⟩)

/-- **The head range is finite-dimensional**: `range P_F ⊆ span {e_j : j ∈ F}`. -/
theorem finiteDimensional_range_headProj (F : Finset M) :
    FiniteDimensional 𝕜 (LinearMap.range (headProj (𝕜 := 𝕜) (E := E) (p := p) F).toLinearMap) :=
  haveI := FiniteDimensional.span_of_finite 𝕜
    (F.finite_toSet.image fun j => single (E := E) (p := p) j (1 : 𝕜))
  Submodule.finiteDimensional_of_le (range_headProj_le_span F)

end HeadRange

section HeadSolver

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 ι E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Head injectivity on a framed carrier**: if `K` preserves the head range
(`P_F K P_F = K P_F`) and `‖P_F − M ∘ K‖ < 1`, then `M` is injective on the head range, for every
framed carrier and every `1 ≤ p ≤ ∞` (`eq_zero_of_mem_of_norm_sub_comp_lt_one` at
`V = range P_F`, finite-dimensional by `finiteDimensional_range_headProj`). -/
theorem eq_zero_of_headProj_eq_of_norm_lt_one (F : Finset ι)
    {M K : WeightedLp ι E p →L[𝕜] WeightedLp ι E p}
    (hK : headProj (𝕜 := 𝕜) F ∘L K ∘L headProj (𝕜 := 𝕜) F = K ∘L headProj (𝕜 := 𝕜) F)
    (h : ‖headProj (𝕜 := 𝕜) F - M ∘L K‖ < 1) :
    ∀ x, headProj (𝕜 := 𝕜) F x = x → M x = 0 → x = 0 := by
  have := finiteDimensional_range_headProj (𝕜 := 𝕜) (E := E) (p := p) F
  intro x hx hMx
  refine eq_zero_of_mem_of_norm_sub_comp_lt_one _ ?_ ?_ h (LinearMap.mem_range.2 ⟨x, hx⟩) hMx
  · rintro _ ⟨w, rfl⟩
    exact DFunLike.congr_fun (headProj_comp_headProj (𝕜 := 𝕜) (E := E) (p := p) F) w
  · rintro _ ⟨w, rfl⟩
    exact LinearMap.mem_range.2 ⟨K (headProj (𝕜 := 𝕜) F w), DFunLike.congr_fun hK w⟩

end HeadSolver

section RawZero

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 ι E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Raw zeros through the finite-head / diagonal-tail solver**: let `G u` and the raw family
`R u` be related by the coefficient solver identity
`coeff (G u) k = coeff (M (J (R u))) k + d k * R u k`, where `J` realizes the head of a raw
family (`coeff (J f) k = 1_{k ∈ F} f k`), `M` preserves the head range (`P_F M P_F = M P_F`)
and is injective on it (`hinj`, supplied by `eq_zero_of_headProj_eq_of_norm_lt_one`), and
`d = 0` on `F`, `d ≠ 0` off `F`. Then `G u = 0 ↔ R u = 0`. Off `F` the identity reads
`d k * R u k = 0`; on `F` it reads `coeff (M (J (R u))) k = 0`, so `M (J (R u)) = 0` and head
injectivity gives `J (R u) = 0`. No norm, linearity of `J` or product structure is used. -/
theorem eq_zero_iff_of_coeff_eq_headSolve (F : Finset ι)
    (M : WeightedLp ι E p →L[𝕜] WeightedLp ι E p) (d : ι → 𝕜)
    {J : (ι → 𝕜) → WeightedLp ι E p} (hJ : ∀ f k, coeff (J f) k = if k ∈ F then f k else 0)
    (hM : headProj (𝕜 := 𝕜) F ∘L M ∘L headProj (𝕜 := 𝕜) F = M ∘L headProj (𝕜 := 𝕜) F)
    (hinj : ∀ x, headProj (𝕜 := 𝕜) F x = x → M x = 0 → x = 0)
    (hd₀ : ∀ k ∈ F, d k = 0) (hd : ∀ k ∉ F, d k ≠ 0)
    {U : Type*} {G : U → WeightedLp ι E p} {R : U → ι → 𝕜}
    (hG : ∀ u k, coeff (G u) k = coeff (M (J (R u))) k + d k * R u k) (u : U) :
    G u = 0 ↔ R u = 0 := by
  constructor
  · intro hu
    have hA : ∀ k, coeff (M (J (R u))) k + d k * R u k = 0 := fun k => by
      rw [← hG, hu, coeff_zero, Pi.zero_apply]
    have hP : headProj (𝕜 := 𝕜) F (J (R u)) = J (R u) := ext_coeff <| funext fun k => by
      rw [coeff_headProj, hJ]
      split_ifs <;> rfl
    have hoff : ∀ k ∉ F, coeff (M (J (R u))) k = 0 := fun k hk => by
      have e := congrArg (fun z => coeff z k) (DFunLike.congr_fun hM (J (R u)))
      simp only [ContinuousLinearMap.comp_apply, hP, coeff_headProj, ite_eq_right hk] at e
      exact e.symm
    have hMJ : M (J (R u)) = 0 := ext_coeff <| funext fun k => by
      rw [coeff_zero, Pi.zero_apply]
      by_cases hk : k ∈ F
      · have e := hA k
        rwa [hd₀ k hk, zero_mul, add_zero] at e
      · exact hoff k hk
    have hJ0 := hinj _ hP hMJ
    funext k
    by_cases hk : k ∈ F
    · have e := congrArg (fun z => coeff z k) hJ0
      simp only [hJ, ite_eq_left hk, coeff_zero, Pi.zero_apply] at e
      exact e
    · have e := hA k
      rw [hoff k hk, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_left (hd k hk)
  · intro hu
    have hJ0 : J 0 = 0 := ext_coeff <| funext fun k => by
      rw [hJ, coeff_zero]
      split_ifs <;> rfl
    refine ext_coeff <| funext fun k => ?_
    rw [hG, hu, hJ0, map_zero, coeff_zero, Pi.zero_apply, mul_zero, add_zero]

end RawZero

end FiniteHead

end RadiiPolynomial.WeightedLp

end
