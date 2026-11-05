import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Schur
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.HeadProj

/-! The full shared-input tail defect, finite leakage geometry and disjoint-output p2 upper norm bound. Both summands retain their common input. No exact operator-norm aggregation is claimed. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M)
  (headOp : WeightedLp M E p →L[𝕜] WeightedLp M E p) (r : M → 𝕜)
  (hr : BddAbove (Set.range fun k => ‖r k‖))

/-- **The tail defect** `𝒟 = headOp P_S L_β Q_S + diag(r) L_β` of a finite head `S`, a bounded
operator `headOp`, a symbol `β ∈ ℓ¹_v` and a bounded diagonal `r`. -/
def tailDefect : WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S + diagCLM r hr ∘L symbolAction₀ hC β

/-- The two summands of the tail defect applied to `x`. -/
theorem tailDefect_apply (x : WeightedLp M E p) :
    tailDefect hC β S headOp r hr x =
      headOp (headProj (𝕜 := 𝕜) S (symbolAction₀ hC β (tailProj (𝕜 := 𝕜) S x))) +
        diagCLM r hr (symbolAction₀ hC β x) := rfl

/-- **The tail term, sup-free**: `‖r k‖ ≤ R` for every `k` and `0 ≤ R` give
`‖diag(r) L_β‖ ≤ R C ‖β‖`. -/
theorem norm_tail_term_le_of_bound {R : ℝ} (hR : ∀ k, ‖r k‖ ≤ R) (hR0 : 0 ≤ R) :
    ‖diagCLM (E := E) (p := p) r hr ∘L symbolAction₀ hC β‖ ≤ R * C * ‖β‖ :=
  ((diagCLM (E := E) (p := p) r hr).opNorm_comp_le _).trans <|
    (mul_le_mul (norm_diagCLM_le (E := E) (p := p) r hr hR hR0)
      ((symbolAction₀ (𝕜 := 𝕜) (p := p) hC).le_of_opNorm_le (norm_symbolAction₀_le hC) β)
      (norm_nonneg _) hR0).trans_eq (mul_assoc _ _ _).symm

end Defect

section LeakGeometry

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {v : M → ℝ} [PosWeight v] {C : ℝ}

/-- **The head-leakage kernel** `K n k = 1_{n ∈ S} 1_{k ∉ S} β_{n - k}` (raw coefficients of the
symbol): the kernel of `P_S L_β Q_S`. -/
def leakKernel (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M) : M → M → 𝕜 :=
  fun n k => if n ∈ S ∧ k ∉ S then rawSymbol β (n - k) else 0

/-- **The band column set** `(S − B) \ S`: the tail modes reached from the head `S` by a shift in
the band `B`. -/
def leakCols (S B : Finset M) : Finset M := (S.image₂ (· - ·) B) \ S

/-- `k ∈ (S − B) \ S` iff `k ∉ S` and `n − k ∈ B` for some `n ∈ S`. -/
theorem mem_leakCols {S B : Finset M} {k : M} :
    k ∈ leakCols S B ↔ k ∉ S ∧ ∃ n ∈ S, n - k ∈ B := by
  rw [leakCols, Finset.mem_sdiff, Finset.mem_image₂]
  exact ⟨fun ⟨⟨n, hn, b, hb, h⟩, hk⟩ => ⟨hk, n, hn, by rwa [← h, sub_sub_cancel]⟩,
    fun ⟨hk, n, hn, hb⟩ => ⟨⟨n, hn, n - k, hb, sub_sub_cancel n k⟩, hk⟩⟩

/-- **The boundary rows** `{n ∈ S | ∃ b ∈ B, n − b ∉ S}`: the head output modes reached from the
tail by a shift in the band `B`. -/
def leakRows (S B : Finset M) : Finset M := S.filter fun n => ∃ b ∈ B, n - b ∉ S

end LeakGeometry

section LeakSupport

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M)

variable {S} in
/-- **Under the band `B`** (`β_l = 0` for `l ∉ B`) the leakage kernel vanishes off the band
column set `(S − B) \ S`. -/
theorem leakKernel_eq_zero_of_not_mem_leakCols {B : Finset M}
    (hB : ∀ l ∉ B, rawSymbol β l = 0) (n : M) {k : M} (hk : k ∉ leakCols S B) :
    leakKernel β S n k = 0 := by
  rw [leakKernel]
  split_ifs with h
  · by_contra hne
    have hb : n - k ∈ B := by
      by_contra hb
      exact hne (hB _ hb)
    exact hk (mem_leakCols.2 ⟨h.2, n, h.1, hb⟩)
  · rfl

end LeakSupport

section Leakage

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M)

/-- **The kernel identity**: `coeff (P_S L_β Q_S x) n = ∑' k, K n k * coeff x k`. -/
theorem coeff_headProj_symbolAction_tailProj (x : WeightedLp M E p) (n : M) :
    coeff (headProj (𝕜 := 𝕜) S (symbolAction₀ hC β (tailProj (𝕜 := 𝕜) S x))) n =
      ∑' k, leakKernel β S n k * coeff x k := by
  rw [coeff_headProj, symbolAction₀_apply,
    ← kernelCLM_laurent_eq_symbolSeries (memL1v_rawSymbol β) hC, kernelCLM_apply_coeff]
  split_ifs with hn
  · refine tsum_congr fun k => ?_
    rw [coeff_tailProj, laurentKernel, leakKernel]
    by_cases hk : k ∈ S
    · rw [ite_eq_left hk, mul_zero, ite_eq_right fun h => h.2 hk, zero_mul]
    · rw [ite_eq_right hk, ite_eq_left ⟨hn, hk⟩]
  · exact ((tsum_congr fun k => by rw [leakKernel, ite_eq_right fun h => hn h.1, zero_mul]).trans
      tsum_zero).symm

/-- **The head leakage lives on the boundary** (band `B`):
`P_S L_β Q_S = P_{leakRows} L_β P_{leakCols}`. -/
theorem headLeakage_eq_boundary {B : Finset M} (hB : ∀ l ∉ B, rawSymbol β l = 0) :
    headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S =
      headProj (𝕜 := 𝕜) (E := E) (p := p) (leakRows S B) ∘L symbolAction₀ hC β ∘L
        headProj (𝕜 := 𝕜) (leakCols S B) :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun n => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      coeff_headProj_symbolAction_tailProj, coeff_headProj, symbolAction₀_apply,
      ← kernelCLM_laurent_eq_symbolSeries (memL1v_rawSymbol β) hC, kernelCLM_apply_coeff]
    split_ifs with hn
    · have hnS : n ∈ S := (Finset.mem_filter.1 hn).1
      refine tsum_congr fun k => ?_
      by_cases hk : k ∈ leakCols S B
      · rw [coeff_headProj, ite_eq_left hk, laurentKernel, leakKernel,
          ite_eq_left ⟨hnS, (mem_leakCols.1 hk).1⟩]
      · rw [coeff_headProj, ite_eq_right hk, mul_zero,
          leakKernel_eq_zero_of_not_mem_leakCols β hB n hk, zero_mul]
    · refine (tsum_congr fun k => ?_).trans tsum_zero
      rw [leakKernel]
      split_ifs with h
      · have hb : rawSymbol β (n - k) = 0 := by
          by_contra hne
          have hnB : n - k ∈ B := by
            by_contra hb
            exact hne (hB _ hb)
          exact hn (Finset.mem_filter.2 ⟨h.1, n - k, hnB, by rw [sub_sub_cancel]; exact h.2⟩)
        rw [hb, zero_mul]
      · exact zero_mul _

end Leakage

section DisjointGeometry

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
variable (S : Finset M) (headOp : WeightedLp M E 2 →L[𝕜] WeightedLp M E 2)
  (r : M → 𝕜) (hr : BddAbove (Set.range fun k => ‖r k‖))

omit [AddCommGroup M] in
/-- **Disjoint outputs**: under `P_S headOp = headOp` and `r = 0` on `S`, at every index one of
`headOp y`, `diag(r) z` has a vanishing coordinate. -/
theorem coeff_disjoint (hPM : headProj (𝕜 := 𝕜) S ∘L headOp = headOp) (hrS : ∀ k ∈ S, r k = 0)
    (y z : WeightedLp M E 2) (k : M) :
    coeff (headOp y) k = 0 ∨ coeff (diagCLM r hr z) k = 0 := by
  by_cases hk : k ∈ S
  · exact Or.inr (by rw [coeff_diagCLM, hrS k hk, zero_mul])
  · exact Or.inl (by
      rw [← DFunLike.congr_fun hPM y, ContinuousLinearMap.comp_apply, coeff_headProj,
        ite_eq_right hk])

end DisjointGeometry

section Aggregation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M] [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {v : M → ℝ} [PosWeight v] {C : ℝ}
variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)
  (β : lpOneAlg M (WeightedScalar 𝕜 v)) (S : Finset M)
  (headOp : WeightedLp M E 2 →L[𝕜] WeightedLp M E 2) (r : M → 𝕜)
  (hr : BddAbove (Set.range fun k => ‖r k‖))

/-- **The pointwise `ℓ²` split** under `P_S headOp = headOp` and `r|_S = 0`:
`‖𝒟 x‖² = ‖headOp P_S L_β Q_S x‖² + ‖diag(r) L_β x‖²` (disjoint coordinate supports; the local
use of `norm_add_sq_of_disjoint`). -/
theorem norm_sq_tailDefect_apply (hPM : headProj (𝕜 := 𝕜) S ∘L headOp = headOp) (hrS : ∀ k ∈ S, r k = 0)
    (x : WeightedLp M E 2) :
    ‖tailDefect hC β S headOp r hr x‖ ^ 2 =
      ‖headOp (headProj (𝕜 := 𝕜) S (symbolAction₀ hC β (tailProj (𝕜 := 𝕜) S x)))‖ ^ 2 +
        ‖diagCLM r hr (symbolAction₀ hC β x)‖ ^ 2 := by
  rw [tailDefect_apply]
  exact norm_add_sq_of_disjoint (coeff_disjoint S headOp r hr hPM hrS _ _)

/-- **The `Z₁` aggregation** (UPPER bound, no exactness claim: the two terms share the input):
for bounds `H ≥ ‖headOp P_S L_β Q_S‖` and `T ≥ ‖diag(r) L_β‖`, `‖𝒟‖ ≤ √(H² + T²)`. -/
theorem norm_tailDefect_le (hPM : headProj (𝕜 := 𝕜) S ∘L headOp = headOp) (hrS : ∀ k ∈ S, r k = 0)
    {H T : ℝ} (hH : ‖headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S‖ ≤ H)
    (hT : ‖diagCLM (E := E) (p := 2) r hr ∘L symbolAction₀ hC β‖ ≤ T) :
    ‖tailDefect hC β S headOp r hr‖ ≤ √(H ^ 2 + T ^ 2) := by
  have hH0 : 0 ≤ H := (norm_nonneg _).trans hH
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have h1 : ‖headOp (headProj (𝕜 := 𝕜) S (symbolAction₀ hC β (tailProj (𝕜 := 𝕜) S x)))‖ ≤ H * ‖x‖ :=
    ((headOp ∘L headProj (𝕜 := 𝕜) S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := 𝕜) S).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg x))
  have h2 : ‖diagCLM r hr (symbolAction₀ hC β x)‖ ≤ T * ‖x‖ :=
    ((diagCLM (E := E) (p := 2) r hr ∘L symbolAction₀ hC β).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg x))
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
    Real.sq_sqrt (by positivity), norm_sq_tailDefect_apply hC β S headOp r hr hPM hrS x, add_mul,
    ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pow_le_pow_left₀ (norm_nonneg _) h2 2)

end Aggregation

section HeadDiagonalSum

/-! ### Disjoint-support aggregation, head operator plus tail diagonal
(`[DecidableEq M]`, generic field and frame) -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]

/-- An operator mapping the head into the head and a diagonal vanishing on the
head have disjoint inputs and outputs, so their sum has norm at most the larger bound:
`‖H P_S + diag(r)‖ ≤ max a t`. -/
theorem norm_comp_headProj_add_diagCLM_le (S : Finset M)
    (H : WeightedLp M E 2 →L[𝕜] WeightedLp M E 2)
    (hPHP : headProj (𝕜 := 𝕜) S ∘L (H ∘L headProj (𝕜 := 𝕜) S) =
      H ∘L headProj (𝕜 := 𝕜) S)
    (r : M → 𝕜) (hr : BddAbove (Set.range fun k => ‖r k‖)) (hrS : ∀ k ∈ S, r k = 0) {a t : ℝ}
    (hH : ‖H‖ ≤ a) (ht : ∀ k, ‖r k‖ ≤ t) :
    ‖H ∘L headProj (𝕜 := 𝕜) S + diagCLM r hr‖ ≤ max a t := by
  have hmax0 : 0 ≤ max a t := ((norm_nonneg _).trans hH).trans (le_max_left _ _)
  have hdiag : ‖diagCLM (E := E) (p := 2) r hr‖ ≤ max a t :=
    norm_diagCLM_le r hr (fun k => (ht k).trans (le_max_right _ _)) hmax0
  refine ContinuousLinearMap.opNorm_le_bound _ hmax0 fun x => ?_
  have hPQ : ∀ k, coeff (headProj (𝕜 := 𝕜) S x) k = 0 ∨ coeff (tailProj (𝕜 := 𝕜) S x) k = 0 :=
    fun k => by
      by_cases hk : k ∈ S
      · exact Or.inr (by rw [coeff_tailProj, ite_eq_left hk])
      · exact Or.inl (by rw [coeff_headProj, ite_eq_right hk])
  have hx : headProj (𝕜 := 𝕜) S x + tailProj (𝕜 := 𝕜) S x = x := by
    rw [tailProj_eq_id_sub_headProj, sub_apply, ContinuousLinearMap.id_apply, add_sub_cancel]
  have hsum : ‖headProj (𝕜 := 𝕜) S x‖ ^ 2 + ‖tailProj (𝕜 := 𝕜) S x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← norm_add_sq_of_disjoint hPQ, hx]
  have hdQ : diagCLM (E := E) (p := 2) r hr x = diagCLM r hr (tailProj (𝕜 := 𝕜) S x) :=
    ext_coeff <| funext fun k => by
      rw [coeff_diagCLM, coeff_diagCLM, coeff_tailProj]
      by_cases hk : k ∈ S
      · rw [ite_eq_left hk, hrS k hk, zero_mul, zero_mul]
      · rw [ite_eq_right hk]
  have h₁ : ‖H (headProj (𝕜 := 𝕜) S x)‖ ≤ max a t * ‖headProj (𝕜 := 𝕜) S x‖ :=
    (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hH.trans (le_max_left _ _)) (norm_nonneg _))
  have h₂ : ‖diagCLM r hr (tailProj (𝕜 := 𝕜) S x)‖ ≤ max a t * ‖tailProj (𝕜 := 𝕜) S x‖ :=
    ((diagCLM (E := E) (p := 2) r hr).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hdiag (norm_nonneg _))
  have hdisj : ∀ k, coeff (H (headProj (𝕜 := 𝕜) S x)) k = 0 ∨
      coeff (diagCLM (E := E) (p := 2) r hr x) k = 0 :=
    coeff_disjoint S (H ∘L headProj (𝕜 := 𝕜) S) r hr hPHP hrS x x
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hmax0 (norm_nonneg x)) two_ne_zero,
    add_apply, ContinuousLinearMap.comp_apply,
    norm_add_sq_of_disjoint hdisj, hdQ, mul_pow, ← hsum, mul_add,
    ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h₁ 2) (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)

end HeadDiagonalSum

end RadiiPolynomial.WeightedLp

end
