import RadiiPolynomial.Operators.BlockDiagonal.Scalar

/-!
# Witness reductions — block-diagonal norms on finitely supported vectors

Equation-independent structural lemmas that reduce the norm of a `SystemBlockDiagData` operator
applied to a finitely supported vector to evaluable finite sums. These bridge the gap between
the abstract CLM norms (Y₀, Z₀, ‖A‖) and the `finsum_bound` computational layer.

## Architecture

General-L lemmas first, then L=1 specializations, then the array element `l1OfArrayQ`, and a
closing documentation section (no declarations) on the column norm pipeline.

## What belongs here (equation-independent)

- **Y₀**: `‖A.toCLM(v)‖` for finitely-supported `v` → finite sum per component
- **Z₀**: `finiteBlockMatrixNorm` / `finWeightedMatrixNorm` of defect → column norm sums
- **‖A‖**: `finiteBlockMatrixNorm + tailBound` → column norm sums

(For Z₀ and ‖A‖ this file has no lemmas: §3 documents the column norm reduction, whose lemmas
are in `Operators/Matrix/WeightedNorm.lean`.)

## What stays elsewhere

- Z₁ structure (how A† approximates DF) and Z₂ Lipschitz constant (depends on derivative of
  F): equation-specific, in the application, family certification and example modules
- LeanCert evaluators (`IntervalDyadic` computations): `Certification/LeanCertAdapter.lean`
-/

open scoped BigOperators Topology
open RadiiPolynomial

noncomputable section

namespace RadiiPolynomial

/-! ## 1. Support Bound (General L)

When `v : XL1 ν L` has componentwise support ≤ M with M ≥ N,
`A.toCLM v` also has componentwise support ≤ M.
On tail modes (n > M ≥ N), the action is `A.tailDiag l n * v_l_n = A.tailDiag l n * 0 = 0`. -/

section GeneralL

variable {ν : PosReal} {L N : ℕ}




end GeneralL

/-! ## 2. Support Bound and Norm Reduction (L = 1 Specialization) -/

section ScalarSpecialization

variable {ν : PosReal} {N : ℕ}

/-- Support bound for L=1: if `v` vanishes for `n > M` and `M ≥ N`,
then `A.toScalarCLM v` vanishes for `n > M`. -/
lemma ScalarBlockDiagData.toScalarCLM_support
    (A : ScalarBlockDiagData N) (v : l1Weighted ν) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ n, M < n → l1Weighted.toSeq v n = 0) :
    ∀ n, M < n → l1Weighted.toSeq (A.toScalarCLM (ν := ν) v) n = 0 := by
  intro n hn
  rw [ScalarBlockDiagData.toScalarCLM_toSeq_tail A v n (by omega)]
  rw [hsupp n hn, mul_zero]

/-- Norm of `A.toScalarCLM v` as a finite sum when `v` has support ≤ M with M ≥ N. -/
lemma ScalarBlockDiagData.norm_toScalarCLM_action_eq_Icc_sum
    (A : ScalarBlockDiagData N) (v : l1Weighted ν) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ n, M < n → l1Weighted.toSeq v n = 0) :
    ‖A.toScalarCLM (ν := ν) v‖ =
    ∑ n ∈ Finset.Icc 0 M,
      |l1Weighted.toSeq (A.toScalarCLM (ν := ν) v) n| * (ν : ℝ) ^ n :=
  l1Weighted.norm_eq_Icc_sum_of_support _ M (A.toScalarCLM_support v M hMN hsupp)

end ScalarSpecialization

/-! ## Finitely supported elements from rational arrays -/

section ArrayElements



/-- Bridge: an element of `ℓ¹_ν` whose coefficients are the casts of rationals `q` supported in
`[0, M]`, at a weight `ν` that is the cast of `ν_q`, has norm equal to the cast of the exact
rational sum `Σ_{n ≤ M} |q n| ν_q ^ n`. -/
theorem l1Weighted.norm_eq_ratCast_sum_of_support {ν : PosReal}
    (x : l1Weighted ν) (q : ℕ → ℚ) (ν_q : ℚ) (hx : ∀ n, l1Weighted.toSeq x n = (q n : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ)) (M : ℕ) (hsupp : ∀ n, M < n → q n = 0) :
    ‖x‖ = ((∑ n ∈ Finset.Icc 0 M, |q n| * ν_q ^ n : ℚ) : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ M (fun n hn => by rw [hx, hsupp n hn, Rat.cast_zero])]
  push_cast
  simp_rw [hx, hν]

end ArrayElements

/-! ## 3. Column Norm Pipeline (documentation)

The Z₀ and ‖A‖ bounds reduce to `finWeightedMatrixNorm` (for L=1) or
`finiteBlockMatrixNorm` (for general L), computed via column norms.

The shipped exact-rational bridge is
`FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le` in `Certification/Rational/Matrix.lean`.
The older array-to-column and column-to-matrix helper family is recovered in
`B5RecordDyadicP2`; it is not re-exported by this file.

For general L, `finiteBlockMatrixNorm` = `max_l Σ_j blockEntryNorm l j` where each
`blockEntryNorm ν A.finBlock l j = finWeightedMatrixNorm ν (A.finBlock l j)`
(`Operators/BlockDiagonal/Basic.lean`). The column norm
pipeline applies to each block entry independently. -/

end RadiiPolynomial
