import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega

/-!
# ℚ bridge for the exact Z₁ column tail bounds (tightening B)

The Z₁ tail operator `π_{>N} ∘ shiftDivN ∘ leftMul b` on `l1Weighted ν` has
weighted column tail masses

  `tailTsum N M := ∑' n, |toSeq (shiftDivN (b · δ_M)) (n+(N+1))| · ν^(n+(N+1))`,

and by `shiftDivN_leftMul_tail_le_of_cols` a uniform bound
`tailTsum N M ≤ C · ν^M` for every `M` gives the operator-level bound
`C · ‖h‖`. For `b` given by exact ℚ coefficient data of finite support `≤ d`
and `ν` a rational weight, each column tail mass is an **exact finite ℚ sum**
of weighted harmonic terms — reindexed by the support window, it is
`∑_{k = max(0, N−M)}^{d} |b_k| · ν^{k+M+1} / (k+M+1)` (`colTailQ` below keeps
the tail-offset index `n = k + M − N` instead, so the ℚ mirror has the same
index set as the analytic tsum and the cast bridge is termwise).

This file provides:
* `colTailTermQ`, `colTailQ` — the computable ℚ mirrors (native_decide-friendly:
  `Finset.range` folds, no `Finset.Icc` on ℤ);
* `shiftDivN_single_tailTsum_eq_colTailQ` — the exact tsum-to-ℚ-sum bridge;
* `shiftDivN_leftMul_tail_cols_le_of_Q` — the certificate-facing reduction:
  a decidable check over the finite range `M ≤ N` (one `native_decide` in the
  certificate) plus `shiftDivN_leftMul_tail_col_antitone` above `N` discharge
  the `∀ M` column hypothesis.

These are weighted harmonic sums, not matrix entries, so this is new
`finmatrix_bound`-style work; the cast/bridge scaffolding (`hcols`-style ℚ
arrays, `hν` weight cast) mirrors `Certification/LeanCertAdapter.lean`.
-/

open scoped BigOperators

namespace RadiiPolynomial

variable {ν : PosReal}

/-- ℚ mirror of the weighted tail term of the column at `single M 1`, indexed
by the tail offset `n` (mode `m = n + N + 1`): the coefficient reaching mode
`m` is `b_{m-1-M}`, weighted by `ν^m / m`. -/
def colTailTermQ (bQ : Array ℚ) (ν_q : ℚ) (N M n : ℕ) : ℚ :=
  if M ≤ n + N then |bQ.getD (n + N - M) 0| * ν_q ^ (n + N + 1) / (n + N + 1)
  else 0

/-- Exact ℚ column tail mass of the Z₁ tail operator at `single M 1`, for
coefficient data of support `≤ d`. Reindexed by `k = n + N − M` this is the
support-window sum `∑_{k = max(0, N−M)}^{d} |b_k| · ν^{k+M+1} / (k+M+1)`;
`Finset.range (d + M + 2)` is a safe superset of the support of the terms. -/
def colTailQ (bQ : Array ℚ) (ν_q : ℚ) (N M d : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (d + M + 2), colTailTermQ bQ ν_q N M n

/-- **Exact bridge**: for `b` with ℚ coefficient data `bQ` of support `≤ d`
and rational weight, the analytic column tail mass at `single M 1` equals the
ℚ sum `colTailQ`, cast to ℝ. -/
theorem shiftDivN_single_tailTsum_eq_colTailQ (b : l1Weighted ν) (bQ : Array ℚ)
    (ν_q : ℚ) (d : ℕ)
    (hb : ∀ k, l1Weighted.toSeq b k = ((bQ.getD k 0 : ℚ) : ℝ))
    (hd : ∀ k, d < k → bQ.getD k 0 = 0)
    (hν : (ν : ℝ) = ((ν_q : ℚ) : ℝ)) (N M : ℕ) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (b * l1Weighted.single M 1)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) =
      ((colTailQ bQ ν_q N M d : ℚ) : ℝ) := by
  -- Termwise identification with the ℚ mirror (same index set, no reindexing).
  have hterm : ∀ n : ℕ,
      |l1Weighted.toSeq (shiftDivN (b * l1Weighted.single M 1)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) = ((colTailTermQ bQ ν_q N M n : ℚ) : ℝ) := by
    intro n
    have e1 : n + (N + 1) = n + N + 1 := by omega
    rw [e1, shiftDivN_succ_mode, l1Weighted.toSeq_mul_single]
    unfold colTailTermQ
    by_cases hM : M ≤ n + N
    · rw [if_pos hM, if_pos hM, hb, hν, abs_div,
        abs_of_nonneg (show (0 : ℝ) ≤ (↑(n + N + 1) : ℝ) from Nat.cast_nonneg _)]
      push_cast
      ring
    · rw [if_neg hM, if_neg hM]
      simp
  refine (tsum_congr hterm).trans ?_
  rw [tsum_eq_sum (s := Finset.range (d + M + 2)) ?_]
  · unfold colTailQ
    push_cast
    rfl
  · intro n hn
    have hn' : d + M + 2 ≤ n := by
      by_contra hcon
      exact hn (Finset.mem_range.mpr (by omega))
    show ((colTailTermQ bQ ν_q N M n : ℚ) : ℝ) = 0
    unfold colTailTermQ
    rw [if_pos (by omega : M ≤ n + N), hd (n + N - M) (by omega)]
    simp

/-- **Certificate-facing reduction** of the `∀ M` column hypothesis of
`shiftDivN_leftMul_tail_le_of_cols`: the finite range `M ≤ N` is checked by
exact ℚ computation (`hle`, decidable — one `native_decide` in a certificate),
and columns above `N` are covered by `shiftDivN_leftMul_tail_col_antitone`. -/
theorem shiftDivN_leftMul_tail_cols_le_of_Q (b : l1Weighted ν) (bQ : Array ℚ)
    (ν_q : ℚ) (d N : ℕ) {C : ℚ}
    (hb : ∀ k, l1Weighted.toSeq b k = ((bQ.getD k 0 : ℚ) : ℝ))
    (hd : ∀ k, d < k → bQ.getD k 0 = 0)
    (hν : (ν : ℝ) = ((ν_q : ℚ) : ℝ))
    (hle : ∀ M : Fin (N + 1), colTailQ bQ ν_q N (M : ℕ) d ≤ C * ν_q ^ (M : ℕ)) :
    ∀ M : ℕ,
      ∑' n, |l1Weighted.toSeq (shiftDivN (b * l1Weighted.single M 1)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ ((C : ℚ) : ℝ) * (ν : ℝ) ^ M := by
  have hbase : ∀ M : ℕ, M ≤ N →
      ∑' n, |l1Weighted.toSeq (shiftDivN (b * l1Weighted.single M 1)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ ((C : ℚ) : ℝ) * (ν : ℝ) ^ M := by
    intro M hM
    rw [shiftDivN_single_tailTsum_eq_colTailQ b bQ ν_q d hb hd hν N M, hν]
    exact_mod_cast hle ⟨M, by omega⟩
  have hstep : ∀ j : ℕ,
      ∑' n, |l1Weighted.toSeq (shiftDivN (b * l1Weighted.single (N + j) 1)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ ((C : ℚ) : ℝ) * (ν : ℝ) ^ (N + j) := by
    intro j
    induction j with
    | zero => exact hbase N le_rfl
    | succ j ih =>
      rw [show N + (j + 1) = N + j + 1 from rfl]
      refine (shiftDivN_leftMul_tail_col_antitone b (Nat.le_add_right N j)).trans ?_
      rw [pow_succ, ← mul_assoc, mul_comm (((C : ℚ) : ℝ) * (ν : ℝ) ^ (N + j)) ((ν : ℝ))]
      exact mul_le_mul_of_nonneg_left ih ν.coe_nonneg
  intro M
  by_cases hM : M ≤ N
  · exact hbase M hM
  · have e : M = N + (M - N) := by omega
    rw [e]
    exact hstep (M - N)

end RadiiPolynomial
