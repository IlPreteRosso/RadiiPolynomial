import LeanCert
import RadiiPolynomial.Certification.Rational.Matrix

/-!
# LeanCert Evaluators for Block-Diagonal Witness Verification

Equation-independent dyadic-interval evaluators and their correctness proofs, bridging the
structural norm reductions to LeanCert's `finsum_bound` and to the dyadic matrix-norm checker.
The exact ℚ matrices, norms and their real bridges are in `Certification/Rational/Matrix.lean`
(imported here).

## Contents

1. `colNormTermEval` / `weightedTermEval` — per-term evaluators for column norms and weighted
   ℓ¹ norms
2. `colNormSumDyadic`, `checkMatrixNormDyadic` and
   `FiniteWeightedNorm.finWeightedMatrixNorm_le_of_dyadic` — the dyadic matrix-norm checker;
   `FiniteWeightedNorm.finWeightedMatrixNorm_le_via_cols` — the per-column decomposition used by
   `finmatrix_dyadic`
3. `scalarBlockDiagActionEval` — scalar block-diagonal action evaluator (Y₀)
4. `systemBlockDiagActionEval` — system block-diagonal action evaluator (Y₀)

## Usage Pattern

```lean
-- Weighted norm via finsum_bound:
finsum_bound using (weightedTermEval arr ν) (fun k _ _ => weightedTermEval_correct ...)
```
-/

open LeanCert.Core LeanCert.Engine

namespace RadiiPolynomial

/-! ## Per-term evaluators -/

/-- Per-term evaluator for column norm sums: computes `|col[k]| * ν^k / ν^j`
as a dyadic interval. Used by the `finmatrix_dyadic` tactic (through LeanCert's `finsum_bound`)
for per-column aggregation. -/
def colNormTermEval (col : Array ℚ) (ν : ℚ) (j : ℕ) (k : ℕ)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|col.getD k 0| * ν ^ k / ν ^ j)) cfg.precision

/-- Correctness: the real column-norm term lies in the dyadic interval. -/
theorem colNormTermEval_correct (col : Array ℚ) (ν : ℚ) (j : ℕ)
    (k : ℕ) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j : ℝ) ∈
      colNormTermEval col ν j k cfg := by
  simp only [colNormTermEval]
  exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) cfg.precision hprec

/-- Per-term evaluator for weighted l1 norm: computes `|arr[k]| * ν^k`. -/
def weightedTermEval (arr : Array ℚ) (ν : ℚ) (k : ℕ)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|arr.getD k 0| * ν ^ k)) cfg.precision

theorem weightedTermEval_correct (arr : Array ℚ) (ν : ℚ) (k : ℕ)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    {f : ℕ → ℝ} (hf : f k = ((arr.getD k 0 : ℚ) : ℝ)) {ν_r : ℝ} (hν : ν_r = (ν : ℝ)) :
    (|f k| * ν_r ^ k : ℝ) ∈ weightedTermEval arr ν k cfg := by
  simp only [weightedTermEval, hf, hν]
  exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) cfg.precision hprec

/-! ## Dyadic matrix norm checker (single native_decide, O(1) proof term)

Computes `max_j (∑_i |col_j[i]| * ν^i / ν^j)` in dyadic interval arithmetic
and checks `≤ target`. Unlike `finWeightedMatrixNormQ` (exact ℚ), this uses bounded-precision
dyadic intervals, avoiding potential rational blowup for large N.

Architecture: computable Bool checker + bridge theorem + `native_decide`. -/

/-- Dyadic zero interval containing 0. -/
private def zeroDyadic : IntervalDyadic :=
  IntervalDyadic.singleton LeanCert.Core.Dyadic.zero

private theorem mem_zeroDyadic : (0 : ℝ) ∈ zeroDyadic := by
  have h : LeanCert.Core.Dyadic.zero = (0 : LeanCert.Core.Dyadic) := rfl
  simp only [zeroDyadic, h, IntervalDyadic.mem_def, IntervalDyadic.singleton,
    LeanCert.Core.Dyadic.toRat_zero, Rat.cast_zero, le_refl, and_self]

/-- Accumulate column norm sum in dyadic arithmetic: `∑_{k=0}^{limit} |col[k]| * ν^k / ν^j`. -/
def colNormSumDyadic (col : Array ℚ) (ν : ℚ) (j : ℕ) (cfg : DyadicConfig)
    (limit : ℕ) : IntervalDyadic :=
  (List.range (limit + 1)).foldl (init := zeroDyadic) fun acc k =>
    (acc.add (colNormTermEval col ν j k cfg)).roundOut cfg.precision

/-- Helper: foldl accumulator contains partial sums. -/
private theorem mem_foldl_colNorm (col : Array ℚ) (ν : ℚ) (j : ℕ)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (acc : IntervalDyadic) (val : ℝ) (hval : val ∈ acc)
    (m : ℕ) :
    (val + ∑ k ∈ Finset.Icc 0 m,
      |(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j) ∈
    (List.range (m + 1)).foldl (init := acc) fun acc k =>
      (acc.add (colNormTermEval col ν j k cfg)).roundOut cfg.precision := by
  induction m generalizing acc val with
  | zero =>
    simp only [show Finset.Icc 0 0 = {0} from by decide, Finset.sum_singleton]
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add hval (colNormTermEval_correct col ν j 0 cfg hprec)) _
  | succ n ih =>
    rw [show List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] from List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hIcc : Finset.Icc 0 (n + 1) = Finset.Icc 0 n ∪ {n + 1} := by
      ext x; simp [Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 0 n) {n + 1} := by
      simp [Finset.disjoint_singleton_right]
    simp only [hIcc, Finset.sum_union hdisj, Finset.sum_singleton]
    rw [← add_assoc]
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add (ih acc val hval)
        (colNormTermEval_correct col ν j (n + 1) cfg hprec)) _

/-- Correctness: the real `arrayColNormIccSum` lies in the dyadic accumulator. -/
theorem mem_colNormSumDyadic (col : Array ℚ) (ν_q : ℚ) (N j : ℕ) {ν : PosReal}
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    FiniteWeightedNorm.arrayColNormIccSum ν N col j ∈
      colNormSumDyadic col ν_q j cfg N := by
  unfold FiniteWeightedNorm.arrayColNormIccSum; rw [hν]
  have h := mem_foldl_colNorm col ν_q j cfg hprec zeroDyadic 0 mem_zeroDyadic N
  simp only [zero_add] at h
  exact h

/-- Check all column norms ≤ target, in dyadic arithmetic. Fully computable. -/
def checkMatrixNormDyadic {N : ℕ} (cols : Fin (N + 1) → Array ℚ) (ν : ℚ)
    (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (List.finRange (N + 1)).all fun j =>
    (colNormSumDyadic (cols j) ν j cfg N).upperBoundedBy target

/-- Bridge: if the dyadic checker says `true`, then the real matrix norm ≤ target.
Single `native_decide` produces an O(1) proof term. -/
theorem FiniteWeightedNorm.finWeightedMatrixNorm_le_of_dyadic {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (ν_q : ℚ) {target : ℚ}
    (cfg : DyadicConfig)
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hcheck : checkMatrixNormDyadic cols ν_q target cfg = true) :
    FiniteWeightedNorm.finWeightedMatrixNorm ν M ≤ (target : ℝ) := by
  apply FiniteWeightedNorm.finWeightedMatrixNorm_le_of_matrixColNorm_le
  intro j
  apply FiniteWeightedNorm.matrixColNorm_le_of_arrayColNormIccSum ν N M (cols j) j _ (hcols j)
  have hmem := mem_colNormSumDyadic (cols j) ν_q N j hν cfg hprec
  have hcol : (colNormSumDyadic (cols j) ν_q j cfg N).upperBoundedBy target = true := by
    simpa using (List.all_eq_true (l := List.finRange (N + 1))).mp hcheck j (List.mem_finRange j)
  exact le_trans hmem.2 (by exact_mod_cast IntervalDyadic.upperBoundedBy_spec hcol)

/-- Bound `finWeightedMatrixNorm` given ℚ column arrays + per-column `arrayColNormIccSum` bounds.
Used by `finmatrix_dyadic` to decompose into per-column `finsum_bound` calls. -/
lemma FiniteWeightedNorm.finWeightedMatrixNorm_le_via_cols {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (C : ℝ)
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hbound : ∀ j : Fin (N + 1),
      FiniteWeightedNorm.arrayColNormIccSum ν N (cols j) j ≤ C) :
    FiniteWeightedNorm.finWeightedMatrixNorm ν M ≤ C :=
  FiniteWeightedNorm.finWeightedMatrixNorm_le_of_matrixColNorm_le (ν := ν) (A := M) (C := C)
    (fun j => FiniteWeightedNorm.matrixColNorm_le_of_arrayColNormIccSum ν N M (cols j) j C
      (hcols j) (hbound j))

/-- Per-term evaluator for `‖A · v‖` norm sums.
ℚ parameters for computable interval arithmetic. -/
def scalarBlockDiagActionEval {N : ℕ} (matCols : Fin (N + 1) → Array ℚ) (vec : ℕ → ℚ)
    (tailCoeff : ℚ) (ν : ℚ) (n : ℕ) (cfg : DyadicConfig) : IntervalDyadic :=
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
    (n : ℕ) (cfg : DyadicConfig)
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
    rw [ite_eq_left hn]
    have : A.action c l n =
        ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * c j k :=
      A.action_finite c l n hn
    rw [this]
    simp_rw [hmat, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · -- Tail
    push Not at hn
    rw [ite_eq_right (not_le.mpr hn)]
    rw [A.action_tail c l n hn, htail l n hn, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

end RadiiPolynomial
