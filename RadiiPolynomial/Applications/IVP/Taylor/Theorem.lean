import RadiiPolynomial.Applications.IVP.Taylor.Operator
import RadiiPolynomial.Core.Theorem
import RadiiPolynomial.Operators.BlockDiagonal.Composition

/-!
# System-Level IVP Radii Polynomial Theorem (Theorem 8.2.2)

Formalizes the system-level IVP theorem from Section 8.2: given a polynomial IVP system
with approximate inverse `A`, approximate derivative `A†`, and approximate solution `ābar`,
provides concrete computable bounds Y₀, Z₀, Z₁, Z₂ satisfying Theorem 7.6.2.

The shared block-diagonal composition and defect identities live in
`Operators.BlockDiagonal.Composition`.

## Main theorem

- `ivp_system_theorem_local` — Theorem 8.2.2, ball-local form: existence and uniqueness of a
  zero of the composed IVP map in a ball around `ābar`, given the radii polynomial is negative,
  with the derivative sparsity and the derivative Lipschitz bound required on the ball only.
- `ivp_system_theorem` — Theorem 8.2.2 with those two hypotheses global; a corollary of the
  ball-local form.
-/

open scoped BigOperators Topology Matrix
open RadiiPolynomial

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-! ## 1. Z₀ Bound -/

/-- Z₀ bound: `‖I - composedApprox.toCLM‖ ≤ Z₀` from the finite block norm of the defect
(the defect's tail bound is `0` by tail cancellation).

Design note. This lemma (`A†` a `BlockDiagOp` with unbounded tail) and
`SystemBlockDiagData.Z₀_le_of_tailCancel` (both factors bounded) are faces of the carrier-generic
`BlockDiagLift.composedApprox_Z₀`; on `XL1`,
`(A.composedApprox B h).toCLM = BlockDiagLift.composedApproxCLM (defectOfBlockDiagOp A B)`
(`SystemBlockDiagData.composedApprox_toCLM_eq_lift`). `A†` stays `BlockDiagOp` data: its tail
`Λ_n = n` is unbounded on `ℓ¹_ν`. Typing `A†` as a bounded map `ℓ¹_ν → ℓ¹_ω` would need block
realizations over a general weight function: `ω_n = ν^(n+1)/(n+1)` is not geometric, and
`l1Omega ν = lp (OmegaScaledReal ν) 1` (`Analysis/SequenceSpace/Geometric/Omega.lean`) is not an
`XL1` at another `PosReal`. -/
lemma ivp_Z₀_le
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    {Z₀ : ℝ} (hZ₀ : finiteBlockMatrixNorm ν (defectOfBlockDiagOp A A_dag).finBlock ≤ Z₀) :
    Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((A.composedApprox A_dag htail_cancel).toCLM (ν := ν)) ≤ Z₀ := by
  show ‖_ - _‖ ≤ _
  rw [SystemBlockDiagData.composedApprox_toCLM_eq_lift]
  exact BlockDiagLift.composedApprox_Z₀ (X := XL1 ν L) _ hZ₀

/-! ## 2. Z₁ Finite-Mode Identity -/

/-- Z₁ finite-mode identity: `composedApprox = fderiv(ivpMap)` on modes ≤ N.
This is the generic version of Example83's `composedApprox_eq_fderiv_G_fin`.

The key hypothesis `hDF_block` connects the fderiv of `ivpCoeffs` (i.e., the Jacobian
of the IVP map) to the `A_dag.finBlock` action. This is equation-specific because
`A_dag` encodes the numerical Jacobian data. -/
lemma composedApprox_eq_fderiv_fin
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    (htail_diag_inv : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā : XL1 ν L)
    -- Equation-specific: fderiv of ivpCoeffs = A_dag.finBlock action
    (hDF_block : ∀ (h : XL1 ν L) (j : Fin L) (k : Fin (N + 1)),
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j ↑k) ā) h =
        ∑ m : Fin L, (A_dag.finBlock j m).mulVec
          (fun p => toCoeff (ν := ν) h m ↑p) k)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((A.composedApprox A_dag htail_cancel).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) ((fderiv ℝ (ivpMap A φ x₀ hmem) ā) h) l n := by
  rw [SystemBlockDiagData.toCoeff_toCLM]
  -- Goal: action(toCoeff h) l n = toCoeff(fderiv G ā h) l n
  -- Chain rule: toCoeff(fderiv G ā h) l n = fderiv(a ↦ A.action(F a) l n)(ā)(h)
  have hG_diff := differentiable_ivpMap A φ x₀ htail_diag_inv hmem hφ
  conv_rhs => rw [show toCoeff ((fderiv ℝ (ivpMap A φ x₀ hmem) ā) h) l n =
    (fderiv ℝ (fun a => A.action (ivpCoeffs φ x₀ a) l n) ā) h from
    fderiv_ivpMap_coeff_at A φ x₀ hmem hG_diff ā h l n]
  rw [A.fderiv_action_fin (ivpCoeffs φ x₀)
    (fun j k => differentiable_ivpCoeffs φ x₀ hφ j ↑k) l n hn ā h]
  set n' : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  -- flattened: the derivative coefficients are `A_dag *ᵥ h`, the composed block is `A * A_dag`
  have hDF : (fun p : Fin L × Fin (N + 1) =>
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a p.1 ↑p.2) ā) h) =
      A_dag.finBlock.toMatrix *ᵥ fun p => toCoeff (ν := ν) h p.1 p.2 :=
    funext fun ⟨j, k⟩ => by
      simp [hDF_block, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [SystemBlockDiagData.action_fin_eq_toMatrix_mulVec _ _ l n',
    SystemBlockDiagData.action_fin_eq_toMatrix_mulVec A _ l n', hDF, Matrix.mulVec_mulVec,
    ← FiniteBlockMatrix.toMatrix_blockMul]
  rfl

/-! ## 3. Main Theorem (Theorem 8.2.2) -/



end IVP
