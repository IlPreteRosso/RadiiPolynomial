import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Schur

/-! Generic causal tail matrix, column masses and column-sum bounds.
The Taylor `Z₁` tail operator is identified with this kernel in
`Compatibility/TaylorTailL1.lean`. -/

open Finset

noncomputable section

namespace RadiiPolynomial.WeightedLp

/-! ### Row and column masses of a mass sequence -/

section Mass

variable {α : Type*} [DivisionSemiring α]


/-- The column mass `∑_{k ≤ d, N < j + k + 1} m_k / (j + k + 1)` of column `j` of the tail kernel
cut at `N`: the gap `k + 1` reaches the output `i = j + k + 1`, which survives the cut iff
`N < i`. -/
def colMass (m : ℕ → α) (N d j : ℕ) : α :=
  ∑ k ∈ range (d + 1), if N < j + k + 1 then m k / ((j + k + 1 : ℕ) : α) else 0

/-- The head column maximum `max_{j ≤ N} colMass m N d j`. -/
def colMax [SemilatticeSup α] (m : ℕ → α) (N d : ℕ) : α :=
  (range (N + 1)).sup' nonempty_range_add_one (colMass m N d)

end Mass

section RealMass

variable {m m' : ℕ → ℝ} {N d : ℕ}


theorem colMass_nonneg (hm : ∀ k, 0 ≤ m k) (j : ℕ) : 0 ≤ colMass m N d j :=
  sum_nonneg fun k _ => by
    split_ifs
    exacts [div_nonneg (hm k) (Nat.cast_nonneg _), le_rfl]


theorem colMass_mono (h : ∀ k ≤ d, m k ≤ m' k) (j : ℕ) : colMass m N d j ≤ colMass m' N d j :=
  sum_le_sum fun k hk => by
    split_ifs
    exacts [div_le_div_of_nonneg_right (h k (Nat.lt_succ_iff.1 (mem_range.1 hk)))
      (Nat.cast_nonneg _), le_rfl]

/-- **The infinite remainder**: past the cutoff (`N ≤ j`) every gap contributes, so the column
mass decreases in `j`. -/
theorem colMass_antitone_of_ge (hm : ∀ k, 0 ≤ m k) {j j' : ℕ} (hj : N ≤ j) (hjj' : j ≤ j') :
    colMass m N d j' ≤ colMass m N d j :=
  sum_le_sum fun k _ => by
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    exact div_le_div_of_nonneg_left (hm k) (by positivity) (by exact_mod_cast (by omega))

/-- Every column past the cutoff is below column `N`. -/
theorem colMass_le_of_ge (hm : ∀ k, 0 ≤ m k) {j : ℕ} (hj : N ≤ j) :
    colMass m N d j ≤ colMass m N d N :=
  colMass_antitone_of_ge hm le_rfl hj

/-- A bound on the finitely many head columns `j ≤ N` bounds every column. -/
theorem colMass_le_of_forall_le (hm : ∀ k, 0 ≤ m k) {C : ℝ}
    (hC : ∀ j ≤ N, colMass m N d j ≤ C) (j : ℕ) : colMass m N d j ≤ C :=
  (le_total j N).elim (hC j) fun h => (colMass_le_of_ge hm h).trans (hC N le_rfl)




/-- The rational column mass computes the real one. -/
theorem cast_colMass (q : ℕ → ℚ) (N d j : ℕ) :
    ((colMass q N d j : ℚ) : ℝ) = colMass (fun k => (q k : ℝ)) N d j := by
  simp only [colMass, Rat.cast_sum, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_div, Rat.cast_natCast,
    Rat.cast_zero]

end RealMass

/-! ### The tail kernel and its Schur sums on the geometric weight -/

section Kernel

/-- The tail kernel of the integrated product with symbol `β`, cut at the output index `N`:
`K i j = β (i - 1 - j) / i` for `N < i` and `j < i`, and `0` otherwise. -/
def tailKernel {𝕜 : Type*} [DivisionRing 𝕜] (N : ℕ) (β : ℕ → 𝕜) (i j : ℕ) : 𝕜 :=
  if N < i ∧ j < i then β (i - 1 - j) / i else 0


section SymbolMass

variable {𝕜 : Type*} [NormedField 𝕜] {ν : ℝ} {β : ℕ → 𝕜}

/-- The normalized mass `‖β k‖ ν^(k+1)` of the symbol at the diagonal gap `i - j = k + 1`. -/
def symbolMass (ν : ℝ) (β : ℕ → 𝕜) (k : ℕ) : ℝ := ‖β k‖ * ν ^ (k + 1)

variable [Fact (0 < ν)]

theorem symbolMass_nonneg (k : ℕ) : 0 ≤ symbolMass ν β k :=
  mul_nonneg (norm_nonneg _) (pow_nonneg (Fact.out : 0 < ν).le _)

omit [Fact (0 < ν)] in
theorem symbolMass_of_eq_zero {k : ℕ} (h : β k = 0) : symbolMass ν β k = 0 := by
  rw [symbolMass, h, norm_zero, zero_mul]

end SymbolMass

variable {𝕜 : Type*} [RCLike 𝕜] {ν : ℝ} [Fact (0 < ν)] {N d : ℕ} {β : ℕ → 𝕜}

/-- The normalized entries of the tail kernel on the geometric weight. -/
theorem schurEntry_tailKernel (i j : ℕ) :
    schurEntry (fun n => ν ^ n) (fun n => ν ^ n) (tailKernel N β) i j =
      if N < i ∧ j < i then symbolMass ν β (i - 1 - j) / i else 0 := by
  simp only [schurEntry, tailKernel]
  split_ifs with h
  · have hpow : ν ^ i = ν ^ (i - 1 - j + 1) * ν ^ j := by rw [← pow_add]; congr 1; omega
    rw [norm_div, RCLike.norm_natCast, hpow, ← mul_assoc,
      mul_div_cancel_right₀ _ (pow_ne_zero j (Fact.out : 0 < ν).ne'), symbolMass,
      div_mul_eq_mul_div]
  · rw [norm_zero, zero_mul, zero_div]





/-- **Columns**: column `j` of the tail kernel has normalized mass exactly
`colMass (symbolMass ν β) N d j`. -/
theorem hasSum_col_tailKernel (hβ : ∀ k, d < k → β k = 0) (j : ℕ) :
    HasSum (fun i => schurEntry (fun n => ν ^ n) (fun n => ν ^ n) (tailKernel N β) i j)
      (colMass (symbolMass ν β) N d j) := by
  have h0 : ∀ i ∉ Ico (j + 1) (j + d + 2),
      schurEntry (fun n => ν ^ n) (fun n => ν ^ n) (tailKernel N β) i j = 0 := fun i hi => by
    rw [schurEntry_tailKernel]
    split_ifs with h
    · rw [symbolMass_of_eq_zero (hβ _ (by rw [mem_Ico] at hi; omega)), zero_div]
    · rfl
  convert (hasSum_sum_of_ne_finset_zero h0 : HasSum _ _) using 1
  rw [sum_Ico_eq_sum_range, show j + d + 2 - (j + 1) = d + 1 by omega, colMass]
  refine sum_congr rfl fun k _ => ?_
  rw [schurEntry_tailKernel, show j + 1 + k - 1 - j = k by omega,
    show j + 1 + k = j + k + 1 by omega]
  simp only [show j < j + k + 1 by omega, and_true]

/-- **Columns** from the finitely many head columns: any `C` above `colMass m N d j` for
`j ≤ N` bounds every column (`colMass_antitone_of_ge` covers `j > N`). -/
theorem colSum_tailKernel_of_le (hβ : ∀ k, d < k → β k = 0) {C : ℝ}
    (hC : ∀ j ≤ N, colMass (symbolMass ν β) N d j ≤ C) :
    ColSum (fun n => ν ^ n) (fun n => ν ^ n) (tailKernel N β) C where
  col_nonneg := (colMass_nonneg symbolMass_nonneg 0).trans (hC 0 N.zero_le)
  col_summable j := (hasSum_col_tailKernel hβ j).summable
  col_le j := (hasSum_col_tailKernel hβ j).tsum_eq.trans_le
    (colMass_le_of_forall_le symbolMass_nonneg hC j)




end Kernel

end RadiiPolynomial.WeightedLp

end
