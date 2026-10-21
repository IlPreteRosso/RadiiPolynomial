import RadiiPolynomial.Tactic.FinMatrixBound

/-!
# Test (family TC): the exact rational matrix-norm tactic

A `2 × 2` matrix with stored rational columns at weight `ν = 2`.
`finmatrix_bound` closes the exact rational bridge
`FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le`. The numerical check uses
`native_decide`; its auxiliary axiom belongs to this test, not to a library theorem.
The separate dyadic route and its test are kept in the staged record.
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


end Tests.TC

#print axioms Tests.TC.t_bound
