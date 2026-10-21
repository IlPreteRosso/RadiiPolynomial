import Mathlib.Data.List.GetD
import RadiiPolynomial.Operators.BlockDiagonal.Scalar

/-!
# Exact-rational finite matrices and their real bridges

The exact ℚ layer of block-diagonal certificates: stored ℚ columns of the finite blocks, the
defect `I − A B` and the weighted (block) matrix norms computed in exact arithmetic, each with
the bridge that bounds the corresponding real quantity. Every norm bridge reduces a real norm
bound to one decidable ℚ inequality, and the entry and action bridges identify real values with
casts of exact ℚ values; which checker closes an inequality is the consumer's choice.
The module imports no `LeanCert` module; the dyadic evaluators are in
`Certification/LeanCertAdapter.lean`.

## Contents

1. `Certification.Rational.getD_ofFn_fin` — `getD` of `Array.ofFn` at a `Fin` index.
2. `matOfCols`, `defectMatQ` / `blockDefectMatQ` — exact ℚ `I − A B` defect matrices from
   column arrays (`defectMatQ_correct`, `blockDefectMatQ_correct`); `defectCols` — the columns of
   a defect block, for any block operator pair.
3. `colNormQ`, `finWeightedMatrixNormQ` and the bridge
   `FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le`.
4. `finiteBlockMatrixNormQ` and the bridges `finiteBlockMatrixNorm_le_of_Q_le`,
   `finiteBlockMatrixNorm_defect_le_of_Q`; `norm_toCLM_le_of_Q` / `norm_toScalarCLM_le_of_Q` —
   CLM norm bounds.
5. `activeBlockNormQ` — active-block norm with a caller-computed scale
   (`activeBlockNorm_component_le`).
6. `blockActionQ` — the exact ℚ action of a block-diagonal operator with stored columns and a
   rational tail diagonal; `SystemBlockDiagData.action_eq_blockActionQ` — its cast bridge.
-/

namespace RadiiPolynomial

namespace Certification.Rational

/-- `getD` of `Array.ofFn` at a `Fin` index. General in `α`, `n`, `f`, `d`. -/
theorem getD_ofFn_fin {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

end Certification.Rational

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

section Defect

variable {L N : ℕ}

/-- ℚ columns of the defect block `(l, j)`: column `k` of `δ_{lj} I − Σ_m A_{lm} B_{mj}`,
where `A_col l m k` and `DF_col m j k` store column `k` of the blocks. -/
def defectCols (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L)
    (k : Fin (N + 1)) : Array ℚ :=
  Array.ofFn fun (i : Fin (N + 1)) =>
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ))
      l j i k

end Defect

/-! ## Exact ℚ weighted matrix norms

The full `finWeightedMatrixNorm` of a matrix with stored ℚ columns, computed in exact ℚ
arithmetic; a single decidable inequality `≤ C` bounds the real norm. -/

/-- Column norm in ℚ: `∑ i, |col(i)| * ν^i / ν^j`. -/
def colNormQ (col : Array ℚ) (ν : ℚ) (N : ℕ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc (0 : ℕ) N, |col.getD i 0| * ν ^ i / ν ^ j

/-- Matrix norm in ℚ: `max_j (colNormQ col_j ν N j)`. -/
def finWeightedMatrixNormQ {N : ℕ} (cols : Fin (N + 1) → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => colNormQ (cols j) ν N j

/-- Bridge: if the exact ℚ norm is `≤ C` (a decidable inequality), then the real norm is
`≤ C`. -/
lemma FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : finWeightedMatrixNormQ cols ν_q ≤ C) :
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

/-! ## Block matrix norm in ℚ -/

/-- Block matrix norm in ℚ: max_l (∑_j finWeightedMatrixNormQ(block_lj)). -/
def finiteBlockMatrixNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ j : Fin L, finWeightedMatrixNormQ (blockCols l j) ν

/-- `C_q · max_l (Σ_{j ∈ active} ‖A_{lj}‖ + [l ∈ active] · tail)`: the exact ℚ block norm of a
block-diagonal operator restricted to the active columns, scaled by a caller-computed
`C_q`. -/
def activeBlockNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν tailBound C_q : ℚ)
    (active : Finset (Fin L)) : ℚ :=
  C_q * Finset.univ.sup' Finset.univ_nonempty fun l =>
    (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν) +
    if l ∈ active then tailBound else 0

/-- Per-component bridge of `activeBlockNormQ`. -/
theorem activeBlockNorm_component_le {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q C_q : ℚ)
    (active : Finset (Fin L)) {bound : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hC_nn : 0 ≤ C_q)
    (hle : activeBlockNormQ L N blockCols ν_q tailBound_q C_q active ≤ bound)
    (l : Fin L) :
    (C_q : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤ (bound : ℝ) := by
  have hentry : ∀ j : Fin L,
      blockEntryNorm ν A.finBlock l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q : ℚ) : ℝ) :=
    fun j => FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le
      (A.finBlock l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  have hrow : (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      (if l ∈ active then A.tailBound else (0 : ℝ)) ≤
      ((((∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q) +
        if l ∈ active then tailBound_q else 0 : ℚ) : ℝ)) := by
    push_cast; exact add_le_add (Finset.sum_le_sum fun j _ => hentry j) (by split <;> simp [htail])
  have hC : (0 : ℝ) ≤ (C_q : ℝ) := by exact_mod_cast hC_nn
  have hsup := Finset.le_sup' (f := fun l =>
    (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q) +
    if l ∈ active then tailBound_q else 0) (Finset.mem_univ l)
  have hX : C_q * ((∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q) +
      if l ∈ active then tailBound_q else 0) ≤ bound :=
    (mul_le_mul_of_nonneg_left hsup hC_nn).trans hle
  refine (mul_le_mul_of_nonneg_left hrow hC).trans ?_
  exact_mod_cast hX

/-- Bridge: if the exact ℚ block norm is `≤ C`, then the real block norm is `≤ C` (one
decidable inequality for all `L × L` blocks). -/
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
        ((finWeightedMatrixNormQ (blockCols l j) ν_q : ℚ) : ℝ) :=
    fun l j => FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le
      (A l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  -- Aggregate: sup'_l (∑_j blockEntryNorm) ≤ (C : ℝ)
  unfold finiteBlockMatrixNorm blockRowNorm
  apply Finset.sup'_le _ _ (fun l _ => ?_)
  calc ∑ j, blockEntryNorm ν A l j
      ≤ ∑ j, ((finWeightedMatrixNormQ (blockCols l j) ν_q : ℚ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hentry l j)
    _ = ((∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q : ℚ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((Finset.sup' Finset.univ Finset.univ_nonempty
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q) : ℚ) : ℝ) := by
        exact_mod_cast Finset.le_sup'
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q) (Finset.mem_univ l)
    _ ≤ (C : ℝ) := by exact_mod_cast hle

/-- **Operator bridge, family-neutral**: for any block operator pair `(A, B)` whose finite
blocks are the casts of the stored columns, the exact ℚ block norm of `defectCols` bounds the
finite block norm of `I − A B`. -/
theorem finiteBlockMatrixNorm_defect_le_of_Q {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ)
    (hA : ∀ (l m : Fin L) (i k : Fin (N + 1)),
      A.finBlock l m i k = ((A_col l m (k : ℕ)).getD (i : ℕ) 0 : ℝ))
    (hB : ∀ (m j : Fin L) (i k : Fin (N + 1)),
      B.finBlock m j i k = ((DF_col m j (k : ℕ)).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = ((ν_q : ℚ) : ℝ)) {Z₀ : ℚ}
    (h : finiteBlockMatrixNormQ L N (defectCols A_col DF_col) ν_q ≤ Z₀) :
    finiteBlockMatrixNorm ν (defectOfBlockDiagOp A B).finBlock ≤ (Z₀ : ℝ) :=
  finiteBlockMatrixNorm_le_of_Q_le _ (defectCols A_col DF_col) ν_q
    (fun l j k i => by
      rw [defectCols, Certification.Rational.getD_ofFn_fin]
      have := blockDefectMatQ_correct
        (fun l m => A.finBlock l m) (fun m j => B.finBlock m j)
        (fun l m (k : Fin (N + 1)) => A_col l m (k : ℕ))
        (fun m j (k : Fin (N + 1)) => DF_col m j (k : ℕ))
        (fun l m j i => hA l m i j) (fun m j k i => hB m j i k) l j i k
      show ((if l = j then 1 else 0) - ∑ m, A.finBlock l m * B.finBlock m j) i k = _
      exact this)
    hν h


/-- Combined scalar CLM norm bound from ℚ columns + ℚ tail bound.
`‖A.toScalarCLM‖ ≤ max(finWeightedMatrixNormQ, tailBound_q) ≤ C` — one decidable inequality.
Scalar analogue of `norm_toCLM_le_of_Q`. Uses the tight `max` bound (Exercise 2.7.2). -/
lemma norm_toScalarCLM_le_of_Q {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N)
    (cols : Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ) {C : ℚ}
    (hcols : ∀ j i : Fin (N + 1), A.finBlock0 i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : max (finWeightedMatrixNormQ cols ν_q) tailBound_q ≤ C) :
    ‖A.toScalarCLM (ν := ν)‖ ≤ (C : ℝ) :=
  (ScalarBlockDiagData.norm_toScalarCLM_le_max (ν := ν) A).trans <|
    (max_le_max
      (FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le A.finBlock0 cols ν_q hcols hν
        (le_refl _))
      (le_of_eq htail)).trans (by exact_mod_cast hle)

/-! ## Block-diagonal action on coefficient data

The retained exact rational action is `blockActionQ`, with cast bridge
`SystemBlockDiagData.action_eq_blockActionQ` below. The scalar-specialized action/evaluator
wrappers formerly documented here are retired. -/



/-! ## System block-diagonal action in exact ℚ -/

/-- Exact ℚ action of a block-diagonal operator with stored finite columns `matCols` and a
rational tail diagonal `tailQ` on rational coefficients `c`: the finite block for `n ≤ N`, the
diagonal above. -/
def blockActionQ {L N : ℕ} (matCols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (tailQ : Fin L → ℕ → ℚ) (c : Fin L → ℕ → ℚ) (l : Fin L) (n : ℕ) : ℚ :=
  if n ≤ N then ∑ j : Fin L, ∑ k : Fin (N + 1), (matCols l j k).getD n 0 * c j k
  else tailQ l n * c l n

/-- Bridge: if the finite blocks of `A` are the casts of the stored columns `matCols` and its
tail diagonal is the cast of `tailQ`, then on rational coefficients the action of `A` is the
cast of `blockActionQ`. -/
theorem SystemBlockDiagData.action_eq_blockActionQ {L N : ℕ}
    (A : SystemBlockDiagData L N) (matCols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (tailQ : Fin L → ℕ → ℚ)
    (hmat : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((matCols l j k).getD (i : ℕ) 0 : ℝ))
    (htail : ∀ l n, N < n → A.tailDiag l n = (tailQ l n : ℝ))
    (c : SystemCoeff L) (cq : Fin L → ℕ → ℚ) (hc : ∀ l n, c l n = (cq l n : ℝ))
    (l : Fin L) (n : ℕ) :
    A.action c l n = (blockActionQ matCols tailQ cq l n : ℝ) := by
  unfold blockActionQ
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.action_finite _ _ _ _ hn, ite_eq_left hn]
    push_cast
    simp only [hc, hmat]
  · rw [SystemBlockDiagData.action_tail _ _ _ _ (by omega), ite_eq_right hn, htail l n (by omega),
      hc]
    push_cast; ring

end RadiiPolynomial
