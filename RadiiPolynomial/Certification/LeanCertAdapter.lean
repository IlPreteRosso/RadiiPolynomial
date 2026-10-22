import LeanCert
import RadiiPolynomial.Certification.Rational.Matrix

/-!
# LeanCert Evaluators for Block-Diagonal Witness Verification

Equation-independent evaluators and their correctness proofs for weighted terms and system
block-diagonal actions, bridging structural reductions to LeanCert's `finsum_bound`.
The exact ℚ matrices, norms and their real bridges are in `Certification/Rational/Matrix.lean`
(imported here).

## Contents

1. `weightedTermEval` / `weightedTermEval_correct` — weighted ℓ¹ term evaluation
2. `systemBlockDiagActionEval` / `systemBlockDiagActionEval_correct` — system block-diagonal
   action evaluation (Y₀)

## Usage Pattern

```lean
-- Weighted norm via finsum_bound:
finsum_bound using (weightedTermEval arr ν) (fun k _ _ => weightedTermEval_correct ...)
```
-/

open LeanCert.Core LeanCert.Engine

namespace RadiiPolynomial

/-! ## Per-term evaluators -/

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

/-! ## System-level action evaluator (general L, for Y₀-type bounds)

Computes `|Σ_j Σ_k A[l,j][n,k] * c[j,k]| * ν^n` for n ≤ N,
and `|tailCoeff * c[l,n]| * ν^n` for n > N. -/

/-- Per-term evaluator for system block-diagonal action norm: `|action_l_n| * ν^n`,
for any number `L` of components. -/
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
