import RadiiPolynomial.source.lpSpace.ScaledReal
import RadiiPolynomial.source.lpSpace.NormHelpers

/-!
# Finite Weighted Matrix Norms

Finite weighted `ℓ¹` norm, weighted column norm, and weighted matrix norm
for `(N+1)×(N+1)` real matrices with a positive weight `ν`.
These are the building blocks for the block-diagonal operator norm estimates.
-/

open scoped BigOperators NNReal Matrix
noncomputable section

namespace RadiiPolynomial.FiniteWeightedNorm

variable {ν : PosReal} {N : ℕ}

/-- Finite weighted `ℓ¹` norm on `Fin (N+1)`. -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Weighted matrix column norm: `‖col_j(A)‖_{1,ν} / ν^j`. -/
def matrixColNorm (ν : PosReal)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) : ℝ :=
  finl1WeightedNorm (ν : ℝ≥0) (fun i => A i j) / (ν : ℝ) ^ (j : ℕ)

/-- Finite weighted matrix norm: max of weighted column norms. -/
def finWeightedMatrixNorm (ν : PosReal)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun j => matrixColNorm ν A j)

lemma weighted_term_nonneg (a : ℝ) (n : ℕ) : 0 ≤ |a| * (ν : ℝ) ^ n :=
  mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _)

lemma matrixColNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    0 ≤ matrixColNorm ν A j := by
  unfold matrixColNorm
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => weighted_term_nonneg _ _))
    (pow_nonneg ν.coe_nonneg _)

lemma finWeightedMatrixNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ finWeightedMatrixNorm ν A := by
  apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
  exact matrixColNorm_nonneg (ν := ν) A 0

@[simp]
lemma matrixColNorm_mul_pow (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ) =
      ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ) := by
  simp [matrixColNorm, finl1WeightedNorm, div_mul_cancel₀ _
    (pow_ne_zero _ (PosReal.coe_ne_zero ν))]

/-- Weighted matrix/mulVec submultiplicativity:
`‖Mv‖_{1,ν} ≤ ‖M‖_{1,ν} · ‖v‖_{1,ν}`, stated symbolically via
`finl1WeightedNorm` and `Matrix.mulVec`.

Proof: `show` reduces to expanded sums (definitional), then
`weighted_sum_abs_sum_le` (triangle + sum swap) →
`simp_rw` (factor `|v k|`, recognize `matrixColNorm_mul_pow`) →
`Finset.le_sup'` (column norm ≤ matrix norm). -/
lemma finWeightedMatrixNorm_mulVec_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) :
    finl1WeightedNorm (ν : ℝ≥0) (A *ᵥ v) ≤
      finWeightedMatrixNorm ν A * finl1WeightedNorm (ν : ℝ≥0) v := by
  show ∑ n : Fin (N + 1), |∑ k : Fin (N + 1), A n k * v k| * (ν : ℝ) ^ (n : ℕ) ≤
      finWeightedMatrixNorm ν A * ∑ k : Fin (N + 1), |v k| * (ν : ℝ) ^ (k : ℕ)
  -- Triangle + sum swap
  refine (NormHelpers.weighted_sum_abs_sum_le (fun n => (ν : ℝ) ^ (n : ℕ))
    (fun _ => pow_nonneg ν.coe_nonneg _) (fun k n => A n k * v k)).trans ?_
  -- Factor |v k|, recognize matrixColNorm
  simp_rw [abs_mul, show ∀ (k n : Fin (N + 1)),
    |A n k| * |v k| * (ν : ℝ) ^ (n : ℕ) =
      |v k| * (|A n k| * (ν : ℝ) ^ (n : ℕ)) from fun _ _ => by ring,
    ← Finset.mul_sum, ← matrixColNorm_mul_pow]
  -- Bound matrixColNorm ≤ finWeightedMatrixNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hsup : matrixColNorm ν A k ≤ finWeightedMatrixNorm ν A :=
    Finset.le_sup' _ (Finset.mem_univ k)
  have h1 : matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ) ≤
      finWeightedMatrixNorm ν A * (ν : ℝ) ^ (k : ℕ) :=
    mul_le_mul_of_nonneg_right hsup (pow_nonneg ν.coe_nonneg _)
  have h2 : |v k| * (matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ)) ≤
      |v k| * (finWeightedMatrixNorm ν A * (ν : ℝ) ^ (k : ℕ)) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg (v k))
  exact h2.trans_eq (mul_left_comm _ _ _)

lemma finWeightedMatrixNorm_le_of_matrixColNorm_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (C : ℝ)
    (hcol : ∀ j : Fin (N + 1), matrixColNorm ν A j ≤ C) :
    finWeightedMatrixNorm ν A ≤ C := by
  unfold finWeightedMatrixNorm
  exact Finset.sup'_le Finset.univ_nonempty (fun j => matrixColNorm ν A j) (by
    intro j _
    exact hcol j)

lemma matrixColNorm_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j =
      (∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)) / (ν : ℝ) ^ (j : ℕ) := by
  simp [matrixColNorm, finl1WeightedNorm]

lemma matrixColNorm_eq_sum_div (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j =
      ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ) / (ν : ℝ) ^ (j : ℕ) := by
  rw [matrixColNorm_eq, Finset.sum_div]

/-- Array-backed finite column formula over `Icc 0 N`. -/
noncomputable def arrayColNormIccSum (ν : PosReal) (N : ℕ)
    (col : Array ℚ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (0 : ℕ) N,
    |(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j

lemma matrixColNorm_eq_arrayColNormIccSum
    (ν : PosReal) (N : ℕ)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (col : Array ℚ) (j : Fin (N + 1))
    (hM : ∀ i : Fin (N + 1), M i j = ((col).getD (i : ℕ) 0 : ℝ)) :
    matrixColNorm ν M j = arrayColNormIccSum ν N col j := by
  rw [matrixColNorm_eq_sum_div, arrayColNormIccSum]
  simp_rw [hM]
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k => |(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ (j : ℕ))]
  have hRange : Finset.range (N + 1) = Finset.Icc (0 : ℕ) N := by
    simpa [Nat.add_sub_cancel] using
      (Nat.range_eq_Icc_zero_sub_one (n := N + 1) (Nat.succ_ne_zero N))
  rw [hRange]

lemma matrixColNorm_le_of_arrayColNormIccSum
    (ν : PosReal) (N : ℕ)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (col : Array ℚ) (j : Fin (N + 1)) (C : ℝ)
    (hM : ∀ i : Fin (N + 1), M i j = ((col).getD (i : ℕ) 0 : ℝ))
    (hcol : arrayColNormIccSum ν N col j ≤ C) :
    matrixColNorm ν M j ≤ C := by
  rw [matrixColNorm_eq_arrayColNormIccSum ν N M col j hM]
  exact hcol

end RadiiPolynomial.FiniteWeightedNorm

end
