import LeanCert
import RadiiPolynomial.source.BlockDiag.Scalar

/-!
# LeanCert Evaluators for Block-Diagonal Witness Verification

Equation-independent evaluators and correctness proofs that bridge structural
norm reductions to `finsum_bound`, `finmatrix_bound`, and `native_decide`.

## Contents

1. `weightedTermEval` — per-term evaluator for weighted ℓ¹ norms
2. `defectMatQ` / `blockDefectMatQ` — exact ℚ I-AB defect computation
3. `finWeightedMatrixNorm_le_of_Q_le` — single `native_decide` matrix norm bridge
4. `finiteBlockMatrixNorm_le_of_Q_le` — system-level block matrix norm bridge
5. `norm_toCLM_le_of_Q` / `norm_toScalarCLM_le_of_Q` — CLM norm bridges
6. `scalarBlockDiagActionEval` — scalar block-diagonal action evaluator (Y₀)
7. `systemBlockDiagActionEval` — system block-diagonal action evaluator (Y₀)
8. `Z₂_blockNormQ` — per-component Z₂ block norm evaluator

## Usage Pattern

```lean
-- Matrix norm via single native_decide:
finmatrix_bound (finWeightedMatrixNorm_le_of_Q_le _ cols ν_q hcols hν)

-- Weighted norm via finsum_bound:
finsum_bound using (weightedTermEval arr ν) (fun k _ _ => weightedTermEval_correct ...)
```
-/

open LeanCert.Core LeanCert.Engine

namespace RadiiPolynomial

/-- Per-term evaluator for weighted l1 norm: computes `|arr[k]| * ν^k`. -/
def weightedTermEval (arr : Array ℚ) (ν : ℚ) (k : Nat)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|arr.getD k 0| * ν ^ k)) cfg.precision

theorem weightedTermEval_correct (arr : Array ℚ) (ν : ℚ) (k : Nat)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    {f : ℕ → ℝ} (hf : f k = ((arr.getD k 0 : ℚ) : ℝ)) {ν_r : ℝ} (hν : ν_r = (ν : ℝ)) :
    (|f k| * ν_r ^ k : ℝ) ∈ weightedTermEval arr ν k cfg := by
  simp only [weightedTermEval, hf, hν]
  exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) cfg.precision hprec

/-! ## I - AB defect column computation -/

/-- Build a ℚ matrix from column arrays. -/
def matOfCols {N : ℕ} (cols : Fin (N + 1) → Array ℚ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun i j => (cols j).getD (i : ℕ) 0

/-- Compute the defect matrix `I - A * B` in ℚ from column arrays of A and B. -/
def defectMatQ {N : ℕ} (A_cols B_cols : Fin (N + 1) → Array ℚ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  1 - matOfCols A_cols * matOfCols B_cols


/-- Bridge: if real matrix entries = ℚ cast of column array entries, then
`(I - A * B)` entries = ℚ cast of `defectMatQ` entries.

This is the **equation-independent `I - AB` lemma**. The certificate provides
`A_cols` and `B_cols`, the API computes defect entries automatically. -/
theorem defectMatQ_correct {N : ℕ}
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (A_cols B_cols : Fin (N + 1) → Array ℚ)
    (hA : ∀ j i : Fin (N + 1), A i j = ((A_cols j).getD (i : ℕ) 0 : ℝ))
    (hB : ∀ j i : Fin (N + 1), B i j = ((B_cols j).getD (i : ℕ) 0 : ℝ))
    (i j : Fin (N + 1)) :
    (1 - A * B) i j = ((defectMatQ A_cols B_cols i j : ℚ) : ℝ) := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    defectMatQ, matOfCols]
  simp_rw [hA, hB]
  push_cast
  simp only [apply_ite (Rat.cast (K := ℝ)), Rat.cast_one, Rat.cast_zero]

/-! ## Block-level defect: δ_{l,j}·I - Σ_m A[l,m]·B[m,j] -/

/-- Block-level defect matrix `δ_{l,j}·I - Σ_m A[l,m]·B[m,j]` from per-block column arrays.
For system-level (L > 1) certificate pipelines. -/
def blockDefectMatQ {L N : ℕ}
    (A_cols B_cols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (l j : Fin L) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  (if l = j then 1 else 0) - ∑ m, matOfCols (A_cols l m) * matOfCols (B_cols m j)

/-- Bridge: block defect entries = ℚ cast of `blockDefectMatQ` entries. -/
theorem blockDefectMatQ_correct {L N : ℕ} [DecidableEq (Fin L)]
    (A B : Fin L → Fin L → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (A_cols B_cols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (hA : ∀ l m j i, A l m i j = ((A_cols l m j).getD (i : ℕ) 0 : ℝ))
    (hB : ∀ m j k i, B m j i k = ((B_cols m j k).getD (i : ℕ) 0 : ℝ))
    (l j : Fin L) (i k : Fin (N + 1)) :
    ((if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) -
      ∑ m : Fin L, A l m * B m j) i k =
    ((blockDefectMatQ A_cols B_cols l j i k : ℚ) : ℝ) := by
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply,
    blockDefectMatQ, matOfCols]
  simp_rw [hA, hB]; push_cast
  by_cases hlj : l = j <;> simp [hlj, Matrix.one_apply, apply_ite (Rat.cast (K := ℝ))]

/-! ## ℚ norm evaluator (single native_decide for full matrix norm)

Instead of 31 `finsum_bound` calls per block, compute the full
`finWeightedMatrixNorm` in exact ℚ arithmetic and verify `≤ C` by one `native_decide`.
-/

/-- Column norm in ℚ: `∑ i, |col(i)| * ν^i / ν^j`. -/
def colNormQ (col : Array ℚ) (ν : ℚ) (N : ℕ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc (0 : ℕ) N, |col.getD i 0| * ν ^ i / ν ^ j

/-- Matrix norm in ℚ: `max_j (colNormQ col_j ν N j)`. -/
def finWeightedMatrixNormQ (cols : Fin (N + 1) → Array ℚ) (ν : ℚ) (N : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => colNormQ (cols j) ν N j

/-- Bridge: if ℚ norm ≤ C (decidable), then ℝ norm ≤ C.
Single `native_decide` replaces N+1 `finsum_bound` calls. -/
lemma FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : finWeightedMatrixNormQ cols ν_q N ≤ C) :
    FiniteWeightedNorm.finWeightedMatrixNorm ν M ≤ (C : ℝ) := by
  -- Step 1: each matrixColNorm = (colNormQ : ℝ) via column bridge + cast
  have hcol : ∀ j : Fin (N + 1), FiniteWeightedNorm.matrixColNorm ν M j =
      ((colNormQ (cols j) ν_q N j : ℚ) : ℝ) := by
    intro j
    rw [FiniteWeightedNorm.matrixColNorm_eq_arrayColNormIccSum ν N M (cols j) j (hcols j)]
    simp only [FiniteWeightedNorm.arrayColNormIccSum, colNormQ, hν]
    push_cast; rfl
  -- Step 2: finWeightedMatrixNorm = sup' of (colNormQ : ℝ) ≤ (sup' of colNormQ : ℝ) ≤ (C : ℝ)
  show Finset.sup' _ _ (fun j => FiniteWeightedNorm.matrixColNorm ν M j) ≤ _
  simp_rw [hcol]
  have : Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => (colNormQ (cols j) ν_q N j : ℝ)) ≤
      ((Finset.sup' Finset.univ Finset.univ_nonempty
        (fun j => colNormQ (cols j) ν_q N j) : ℚ) : ℝ) := by
    apply Finset.sup'_le _ _ (fun j _ => ?_)
    exact_mod_cast Finset.le_sup' (fun j => colNormQ (cols j) ν_q N j) (Finset.mem_univ j)
  exact this.trans (by exact_mod_cast hle)

/-! ## Block matrix norm in ℚ (single native_decide for L×L block operator) -/

/-- Block matrix norm in ℚ: max_l (∑_j finWeightedMatrixNormQ(block_lj)). -/
def finiteBlockMatrixNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ j : Fin L, finWeightedMatrixNormQ (blockCols l j) ν N

/-- Generalized Z₂ block norm evaluator with variable factor `C_q`. -/
def Z₂_blockNormQ_gen (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν tailBound C_q : ℚ)
    (active : Finset (Fin L)) : ℚ :=
  C_q * ν * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
    (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν N) +
    if l ∈ active then tailBound else 0

/-- Generalized Z₂ per-component bridge with variable factor.
If `Z₂_blockNormQ_gen ... C_q ≤ bound`, then `C*ν*(∑ blockNorm + tail_if) ≤ bound` for each `l`. -/
lemma Z₂_blockNorm_component_le_gen {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q C_q : ℚ)
    (active : Finset (Fin L)) {bound : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hC_nn : 0 ≤ C_q)
    (hle : Z₂_blockNormQ_gen L N blockCols ν_q tailBound_q C_q active ≤ bound)
    (l : Fin L) :
    (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤ (bound : ℝ) := by
  have hentry : ∀ j : Fin L,
      blockEntryNorm ν A.finBlock l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
    fun j => FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le
      (A.finBlock l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  suffices h : (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ((Z₂_blockNormQ_gen L N blockCols ν_q tailBound_q C_q active : ℚ) : ℝ) from
    h.trans (by exact_mod_cast hle)
  show (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ↑(C_q * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0)
  have hrow : (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      (if l ∈ active then A.tailBound else (0 : ℝ)) ≤
      ((((∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0 : ℚ) : ℝ)) := by
    push_cast
    exact add_le_add
      (Finset.sum_le_sum fun j _ => hentry j)
      (by split <;> simp [htail])
  have hCν_nn : (0 : ℝ) ≤ (C_q : ℝ) * (ν : ℝ) :=
    mul_nonneg (by exact_mod_cast hC_nn) ν.coe_nonneg
  calc (C_q : ℝ) * (ν : ℝ) * _ ≤ (C_q : ℝ) * (ν : ℝ) * ↑((∑ j ∈ active,
        finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) :=
      mul_le_mul_of_nonneg_left hrow hCν_nn
    _ ≤ (C_q : ℝ) * (ν : ℝ) * ↑(Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      apply mul_le_mul_of_nonneg_left _ hCν_nn
      have := Finset.le_sup' (f := fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) (Finset.mem_univ l)
      exact_mod_cast this
    _ = ↑(C_q * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      rw [hν]; push_cast; ring

/-- Per-block Z₂ evaluator with hardcoded factor `2`.
Special case of `Z₂_blockNormQ_gen`. -/
def Z₂_blockNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν tailBound : ℚ)
    (active : Finset (Fin L)) : ℚ :=
  Z₂_blockNormQ_gen L N blockCols ν tailBound 2 active

/-- Z₂ per-component bridge with factor `2`.
Special case of `Z₂_blockNorm_component_le_gen`. -/
lemma Z₂_blockNorm_component_le {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ)
    (active : Finset (Fin L)) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : Z₂_blockNormQ L N blockCols ν_q tailBound_q active ≤ C) (l : Fin L) :
    2 * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤ (C : ℝ) := by
  exact_mod_cast Z₂_blockNorm_component_le_gen A blockCols ν_q tailBound_q 2
    active hcols hν htail (by norm_num) hle l

/-- Bridge: if ℚ block norm ≤ C, then ℝ block norm ≤ C.
Single `native_decide` replaces L×L `finWeightedMatrixNorm_le_of_Q_le` calls. -/
lemma finiteBlockMatrixNorm_le_of_Q_le {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : FiniteBlockMatrix L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : finiteBlockMatrixNormQ L N blockCols ν_q ≤ C) :
    finiteBlockMatrixNorm ν A ≤ (C : ℝ) := by
  -- Per-block: reuse scalar bridge with C = finWeightedMatrixNormQ
  have hentry : ∀ l j : Fin L,
      blockEntryNorm ν A l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
    fun l j => FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le
      (A l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  -- Aggregate: sup'_l (∑_j blockEntryNorm) ≤ (C : ℝ)
  unfold finiteBlockMatrixNorm blockRowNorm
  apply Finset.sup'_le _ _ (fun l _ => ?_)
  calc ∑ j, blockEntryNorm ν A l j
      ≤ ∑ j, ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hentry l j)
    _ = ((∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((Finset.sup' Finset.univ Finset.univ_nonempty
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N) : ℚ) : ℝ) := by
        exact_mod_cast Finset.le_sup'
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N) (Finset.mem_univ l)
    _ ≤ (C : ℝ) := by exact_mod_cast hle

/-- Combined CLM norm bound from ℚ block columns + ℚ tail bound.
`‖A.toCLM‖ ≤ finiteBlockMatrixNormQ + tailBound_q ≤ C` — no intermediate named constants. -/
lemma norm_toCLM_le_of_Q {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : finiteBlockMatrixNormQ L N blockCols ν_q + tailBound_q ≤ C) :
    ‖A.toCLM (ν := ν)‖ ≤ (C : ℝ) :=
  (A.norm_toCLM_le (ν := ν)).trans <|
    (add_le_add
      (finiteBlockMatrixNorm_le_of_Q_le A.finBlock blockCols ν_q hcols hν (le_refl _))
      (le_of_eq htail)).trans (by exact_mod_cast hle)

/-- Combined scalar CLM norm bound from ℚ columns + ℚ tail bound.
`‖A.toScalarCLM‖ ≤ max(finWeightedMatrixNormQ, tailBound_q) ≤ C` — single `native_decide`.
Scalar analogue of `norm_toCLM_le_of_Q`. Uses the tight `max` bound (Exercise 2.7.2). -/
lemma norm_toScalarCLM_le_of_Q {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N)
    (cols : Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ) {C : ℚ}
    (hcols : ∀ j i : Fin (N + 1), A.finBlock0 i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : max (finWeightedMatrixNormQ cols ν_q N) tailBound_q ≤ C) :
    ‖A.toScalarCLM (ν := ν)‖ ≤ (C : ℝ) :=
  (ScalarBlockDiagData.norm_toScalarCLM_le_max (ν := ν) A).trans <|
    (max_le_max
      (FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le A.finBlock0 cols ν_q hcols hν (le_refl _))
      (le_of_eq htail)).trans (by exact_mod_cast hle)

/-- Convert a pointwise interval bound (`∀ x ∈ Icc 0 0, e ≤ c`) to a scalar inequality.
Lets `fast_bound` close scalar inequalities directly in ℝ. -/
lemma of_point_interval {e c : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 0, e ≤ c) : e ≤ c :=
  h 0 ⟨le_refl _, le_refl _⟩

/-- Strict variant of `of_point_interval` for `fast_bound` on `< 0` goals. -/
lemma of_point_interval_lt {e c : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 0, e < c) : e < c :=
  h 0 ⟨le_refl _, le_refl _⟩

/-! ## Norm-to-witness bridge for block-diagonal action

Bridges `|toSeq(A.toScalarCLM v)[n]| * ν^n` to a witness evaluator.
The ℚ computation is internal to the evaluator; the certificate provides
ℚ-valued data (column arrays, vector, tail coefficient) and ℝ-to-ℚ bridges. -/

/-- Block-diagonal action in ℝ: finite modes use matrix-vector product,
tail modes use diagonal multiplication. Certificate-facing API. -/
noncomputable def scalarBlockDiagAction {N : ℕ} (matCols : Fin (N + 1) → Array ℝ)
    (vec : ℕ → ℝ) (tailCoeff : ℝ) (n : ℕ) : ℝ :=
  if n ≤ N then ∑ j : Fin (N + 1), (matCols j).getD n 0 * vec j
  else tailCoeff * vec n

/-- Bridge: `toSeq(A.toScalarCLM v)[n] = scalarBlockDiagAction ...`.
Pure ℝ signature — no ℚ types in parameters or hypotheses. -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_eq_action {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N) (v : l1Weighted ν)
    (matCols : Fin (N + 1) → Array ℝ) (vec : ℕ → ℝ) (tailCoeff : ℝ)
    (hmat : ∀ j i : Fin (N + 1), A.finBlock0 i j = (matCols j).getD (i : ℕ) 0)
    (hvec : ∀ n, l1Weighted.toSeq v n = vec n)
    (htail : ∀ n, N < n → A.tailDiag0 n = tailCoeff)
    (n : ℕ) :
    l1Weighted.toSeq (A.toScalarCLM (ν := ν) v) n =
      scalarBlockDiagAction matCols vec tailCoeff n := by
  simp only [scalarBlockDiagAction]
  by_cases hn : n ≤ N
  · rw [if_pos hn, A.toScalarCLM_toSeq_fin (ν := ν) v ⟨n, Nat.lt_succ_of_le hn⟩]
    simp_rw [hmat, hvec]
  · push_neg at hn
    rw [if_neg (not_le.mpr hn), A.toScalarCLM_toSeq_tail v n hn, htail n hn, hvec]

/-- Per-term evaluator for `‖A · v‖` norm sums.
ℚ parameters for computable interval arithmetic. -/
def scalarBlockDiagActionEval {N : ℕ} (matCols : Fin (N + 1) → Array ℚ) (vec : ℕ → ℚ)
    (tailCoeff : ℚ) (ν : ℚ) (n : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  let action : ℚ :=
    if n ≤ N then ∑ j : Fin (N + 1), (matCols j).getD n 0 * vec j
    else tailCoeff * vec n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton (|action| * ν ^ n)) cfg.precision

/-- Correctness: the ℝ action-norm term lies in the evaluator's interval.
Certificate-facing: pure ℝ signature. ℚ bridge is internal. -/
theorem scalarBlockDiagActionEval_correct {N : ℕ}
    (matCols : Fin (N + 1) → Array ℝ) (vec : ℕ → ℝ) (tailCoeff : ℝ) (ν : ℝ)
    (matCols_q : Fin (N + 1) → Array ℚ) (vec_q : ℕ → ℚ) (tailCoeff_q : ℚ) (ν_q : ℚ)
    (hmat : ∀ j i : Fin (N + 1), (matCols j).getD (i : ℕ) 0 = ((matCols_q j).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ n, vec n = (vec_q n : ℝ))
    (htail : tailCoeff = (tailCoeff_q : ℝ))
    (hν : ν = (ν_q : ℝ))
    (n : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|scalarBlockDiagAction matCols vec tailCoeff n| * ν ^ n : ℝ) ∈
      scalarBlockDiagActionEval matCols_q vec_q tailCoeff_q ν_q n cfg := by
  simp only [scalarBlockDiagAction, scalarBlockDiagActionEval, hν]
  split
  · next hn =>
    simp_rw [show ∀ j : Fin (N + 1), (matCols j).getD n 0 =
        ((matCols_q j).getD n 0 : ℝ) from
      fun j => hmat j ⟨n, Nat.lt_succ_of_le hn⟩, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · rw [htail, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

/-! ## System-level action evaluator (general L, for Y₀-type bounds)

Generalizes `scalarBlockDiagActionEval` from L=1 to arbitrary L.
Computes `|Σ_j Σ_k A[l,j][n,k] * c[j,k]| * ν^n` for n ≤ N,
and `|tailCoeff * c[l,n]| * ν^n` for n > N. -/

/-- Per-term evaluator for system block-diagonal action norm: `|action_l_n| * ν^n`.
Generalizes `scalarBlockDiagActionEval` to L > 1. -/
def systemBlockDiagActionEval {L N : ℕ}
    (matCols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (vec : Fin L → ℕ → ℚ) (tailCoeff : Fin L → ℕ → ℚ)
    (ν : ℚ) (l : Fin L) (n : ℕ) (cfg : DyadicConfig) : IntervalDyadic :=
  let action : ℚ :=
    if n ≤ N then
      ∑ j : Fin L, ∑ k : Fin (N + 1), (matCols l j k).getD n 0 * vec j k
    else tailCoeff l n * vec l n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton (|action| * ν ^ n)) cfg.precision

/-- Correctness: the ℝ system action term lies in the evaluator's interval. -/
theorem systemBlockDiagActionEval_correct {L N : ℕ}
    (A : SystemBlockDiagData L N)
    (c : SystemCoeff L) (c_q : Fin L → ℕ → ℚ)
    (matCols_q : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (tailCoeff_q : Fin L → ℕ → ℚ) (ν_q : ℚ) {ν : PosReal}
    (hmat : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((matCols_q l j k).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ l n, c l n = (c_q l n : ℝ))
    (htail : ∀ l n, N < n → A.tailDiag l n = (tailCoeff_q l n : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (l : Fin L) (n : ℕ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|A.action c l n| * (ν : ℝ) ^ n : ℝ) ∈
      systemBlockDiagActionEval matCols_q c_q tailCoeff_q ν_q l n cfg := by
  simp only [systemBlockDiagActionEval, hν]
  by_cases hn : n ≤ N
  · -- Finite block
    rw [if_pos hn]
    have : A.action c l n =
        ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * c j k :=
      A.action_finite c l n hn
    rw [this]
    simp_rw [hmat, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · -- Tail
    push_neg at hn
    rw [if_neg (not_le.mpr hn)]
    rw [A.action_tail c l n hn, htail l n hn, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

end RadiiPolynomial
