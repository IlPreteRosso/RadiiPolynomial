import RadiiPolynomial.Operators.BlockDiagonal.WeightedL1

/-!
# Block-Diagonal Composition with Tail Cancellation

Constructs the bounded composed approximation `A * B` from a bounded
`SystemBlockDiagData` operator `A` and a possibly unbounded `BlockDiagOp` operator `B`.
The only required tail information is that their diagonal factors cancel.

This construction is shared by Taylor and Chebyshev IVP discretizations. On `XL1` its CLM is
the carrier-generic `BlockDiagLift.composedApproxCLM` of the defect `defectOfBlockDiagOp A B`
(`composedApprox_toCLM_eq_lift`), so its Z₀ bound is a face of `BlockDiagLift.composedApprox_Z₀`.
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

/-- On `XL1`, the composed approximation is the generic `BlockDiagLift` construction applied
to the defect `defectOfBlockDiagOp A B`. -/
theorem composedApprox_toCLM_eq_lift
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (htailCancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    (A.composedApprox B htailCancel).toCLM (ν := ν) =
      BlockDiagLift.composedApproxCLM (X := XL1 ν L) (ν := ν) (defectOfBlockDiagOp A B) := by
  ext1 x
  have hx := DFunLike.congr_fun (A.composedApprox_defect_eq (ν := ν) B htailCancel) x
  rw [sub_apply, ContinuousLinearMap.id_apply] at hx
  rw [BlockDiagLift.composedApproxCLM_apply]
  refine (sub_sub_cancel x _).symm.trans (congrArg (x - ·) ?_)
  rw [hx]
  apply XL1.ext; intro l n
  rw [SystemBlockDiagData.toCoeff_toCLM]
  show _ = toCoeff (ofCoeff _ _) l n
  rw [toCoeff_ofCoeff, SystemBlockDiagData.action_eq_actionFinite_add_actionTail]
  by_cases hn : n ≤ N
  · simp [SystemBlockDiagData.actionTail_finite _ _ _ _ hn]
  · simp [SystemBlockDiagData.actionTail_tail _ _ _ _ (Nat.lt_of_not_ge hn), defectOfBlockDiagOp]

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

end
