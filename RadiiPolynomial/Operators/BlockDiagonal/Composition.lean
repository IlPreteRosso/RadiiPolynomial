import RadiiPolynomial.Operators.BlockDiagonal.WeightedL1

/-!
# Block-Diagonal Composition with Tail Cancellation

Constructs the bounded composed approximation `A * B` from a bounded
`SystemBlockDiagData` operator `A` and a possibly unbounded `BlockDiagOp` operator `B`.
The only required tail information is that their diagonal factors cancel.

This construction is shared by Taylor and Chebyshev IVP discretizations.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal} {L N : ℕ} [NeZero L]

namespace SystemBlockDiagData

/-- Compose a bounded block-diagonal operator with a possibly unbounded one when their
tail factors cancel. The resulting operator has identity tail. -/
def composedApprox
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (_htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    SystemBlockDiagData L N where
  finBlock l j := ∑ m, A.finBlock l m * B.finBlock m j
  tailDiag _ _ := 1
  tailBound := 1
  tailBound_spec := fun _ _ _ => by simp [abs_of_pos]

/-- The defect of `composedApprox` is `defectOfBlockDiagOp`. -/
lemma composedApprox_defect_eq
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.composedApprox B htailCancel).toCLM (ν := ν) =
    (defectOfBlockDiagOp A B).toCLM (ν := ν) := by
  apply defect_of_composed_toCLM_eq A B
  · intro x l n
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_fin_eq_sum_mulVec]
    simp [composedApprox, Matrix.mulVec, dotProduct]
  · intro x l n hn
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_tail _ _ _ _ hn]
    simp [composedApprox, htailCancel _ _ hn]
  · exact htailCancel

/-- `composedApprox` acts as the identity on tail modes. -/
lemma composedApprox_toCLM_tail
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((A.composedApprox B htailCancel).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) h l n := by
  rw [SystemBlockDiagData.toCoeff_toCLM,
    SystemBlockDiagData.action_tail _ _ _ _ hn]
  simp [composedApprox]

end SystemBlockDiagData

end RadiiPolynomial

/-! Compatibility names for the existing Taylor IVP API. -/

namespace IVP

open RadiiPolynomial

variable {ν : PosReal} {L N : ℕ} [NeZero L]

abbrev ivpComposedApprox
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    SystemBlockDiagData L N :=
  A.composedApprox B htailCancel

lemma ivpComposedApprox_defect_eq
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) -
      (ivpComposedApprox A B htailCancel).toCLM (ν := ν) =
    (defectOfBlockDiagOp A B).toCLM (ν := ν) :=
  A.composedApprox_defect_eq B htailCancel

lemma ivpComposedApprox_toCLM_tail
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((ivpComposedApprox A B htailCancel).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) h l n :=
  A.composedApprox_toCLM_tail B htailCancel h l n hn

end IVP

end
