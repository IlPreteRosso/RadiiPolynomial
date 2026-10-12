import RadiiPolynomial.Tactic.FinMatrixBound

/-!
# Test (family TC): the two matrix-norm tactics resolve their quoted names

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.TC.FinMatrixBound`.

A `2 × 2` matrix with stored rational columns at weight `ν = 2`. `finmatrix_bound` closes the
exact-ℚ bridge `FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le`; `finmatrix_dyadic` runs the
per-column dyadic route (`finWeightedMatrixNorm_le_via_cols`, `arrayColNormIccSum`,
`colNormTermEval`, `colNormTermEval_correct`), which no production certificate invokes. Both
syntaxes now have node kinds `RadiiPolynomial.Tactic.finMatrixBound` / `finMatrixDyadic`. The
numerical checks close by `native_decide` (numerical faces only); their auxiliary axioms stay in
these test theorems and enter no library theorem.
-/

open RadiiPolynomial

namespace Tests.TC

def cols : Fin 2 → Array ℚ := ![#[1, 1/2], #[0, 1]]

noncomputable def M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ((cols j).getD (i : ℕ) 0 : ℝ)

def ν : PosReal := ⟨2, by norm_num⟩

theorem hν : ((ν : ℝ)) = ((2 : ℚ) : ℝ) := by show (2 : ℝ) = ((2 : ℚ) : ℝ); norm_num

theorem hcols : ∀ j i : Fin 2, M i j = ((cols j).getD (i : ℕ) 0 : ℝ) := fun _ _ => rfl

/-- Exact-ℚ path. -/
theorem t_bound : FiniteWeightedNorm.finWeightedMatrixNorm ν M ≤ ((3 : ℚ) : ℝ) := by
  finmatrix_bound (FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le (N := 1) M cols 2 hcols hν)

/-- Per-column dyadic path. -/
theorem t_dyadic : FiniteWeightedNorm.finWeightedMatrixNorm ν M ≤ 3 := by
  finmatrix_dyadic cols, hcols, 2, hν

end Tests.TC

#print axioms Tests.TC.t_bound
#print axioms Tests.TC.t_dyadic
