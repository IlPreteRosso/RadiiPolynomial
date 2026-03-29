import RadiiPolynomial.source.IVP.Setup
import RadiiPolynomial.source.RadiiPolyGeneral

/-!
# System-Level IVP Radii Polynomial Theorem (Theorem 8.2.2)

Formalizes the system-level IVP theorem from Section 8.2: given a polynomial IVP system
with approximate inverse `A`, approximate derivative `A†`, and approximate solution `ābar`,
provides concrete computable bounds Y₀, Z₀, Z₁, Z₂ satisfying Theorem 7.6.2.

## Main definitions

- `ivpComposedApprox` — the block-diagonal product `A · A†` as `SystemBlockDiagData`
- `ivpComposedApprox_defect_eq` — `I - composedApprox.toCLM = defect.toCLM`

## Main theorem

- `ivp_system_theorem` — Theorem 8.2.2: existence and uniqueness of a zero of the
  composed IVP map in a ball around `ābar`, given the radii polynomial is negative.
-/

open scoped BigOperators Topology
open RadiiPolynomial

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-! ## 1. Composed Approximate Derivative -/

/-- The composed approximate derivative `A · A†` as a bounded operator.
When `A.tailDiag * A†.tailDiag = 1` on tail modes, the product has `tailDiag = 1`.
Used as the approximate derivative in `general_radii_polynomial_theorem` with `A_inv = id`. -/
def ivpComposedApprox
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (_htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1) :
    SystemBlockDiagData L N where
  finBlock l j := ∑ m, A.finBlock l m * A_dag.finBlock m j
  tailDiag _ _ := 1
  tailBound := 1
  tailBound_spec := fun _ _ _ => by simp [abs_of_pos]

/-- `I - composedApprox.toCLM = defect.toCLM`: the defect identity. -/
lemma ivpComposedApprox_defect_eq
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) -
      (ivpComposedApprox A A_dag htail_cancel).toCLM (ν := ν) =
    (defectOfBlockDiagOp A A_dag).toCLM (ν := ν) := by
  apply defect_of_composed_toCLM_eq A A_dag
  · intro x l n
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_fin_eq_sum_mulVec]
    simp [ivpComposedApprox, Matrix.mulVec, dotProduct]
  · intro x l n hn
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_tail _ _ _ _ hn]
    simp [ivpComposedApprox, htail_cancel _ _ hn]
  · exact htail_cancel

/-- ComposedApprox tail: `(composedApprox.toCLM h) l n = h l n` for n > N. -/
lemma ivpComposedApprox_toCLM_tail
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((ivpComposedApprox A A_dag htail_cancel).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) h l n := by
  rw [SystemBlockDiagData.toCoeff_toCLM,
    SystemBlockDiagData.action_tail _ _ _ _ hn]
  simp [ivpComposedApprox]

/-! ## 2. Z₀ Bound -/

/-- Z₀ bound: `‖I - composedApprox.toCLM‖ ≤ finBlockMatrixNorm(defect)`.
Since the defect has `tailBound = 0` (from tail cancellation), the bound is purely
from finite block norms. -/
lemma ivp_Z₀_le
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    {Z₀ : ℝ} (hZ₀ : finiteBlockMatrixNorm ν (defectOfBlockDiagOp A A_dag).finBlock ≤ Z₀) :
    Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((ivpComposedApprox A A_dag htail_cancel).toCLM (ν := ν)) ≤ Z₀ := by
  show ‖ContinuousLinearMap.id ℝ _ -
    (ivpComposedApprox A A_dag htail_cancel).toCLM (ν := ν)‖ ≤ _
  rw [ivpComposedApprox_defect_eq]
  exact ((defectOfBlockDiagOp A A_dag).norm_toCLM_le (ν := ν)).trans
    (by simp [defectOfBlockDiagOp, add_zero]; exact hZ₀)

/-! ## 3. Z₁ Finite-Mode Identity -/

/-- Z₁ finite-mode identity: `composedApprox = fderiv(ivpMap)` on modes ≤ N.
This is the generic version of Example83's `composedApprox_eq_fderiv_G_fin`.

The key hypothesis `hDF_block` connects the fderiv of `ivpCoeffs` (i.e., the Jacobian
of the IVP map) to the `A_dag.finBlock` action. This is equation-specific because
`A_dag` encodes the numerical Jacobian data. -/
lemma ivpComposedApprox_eq_fderiv_fin
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    (htail_diag_inv : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      lpWeighted.Mem ν 1 (A.action (ivpCoeffs φ x₀ a) l))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā : XL1 ν L)
    -- Equation-specific: fderiv of ivpCoeffs = A_dag.finBlock action
    (hDF_block : ∀ (h : XL1 ν L) (j : Fin L) (k : Fin (N + 1)),
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j ↑k) ā) h =
        ∑ m : Fin L, (A_dag.finBlock j m).mulVec
          (fun p => toCoeff (ν := ν) h m ↑p) k)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((ivpComposedApprox A A_dag htail_cancel).toCLM (ν := ν) h) l n =
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
  rw [SystemBlockDiagData.action_fin_eq_sum_mulVec
    (ivpComposedApprox A A_dag htail_cancel) _ l n']
  simp only [ivpComposedApprox]
  have hassoc := congr_fun (blockFinite_mulVec_assoc A.finBlock A_dag.finBlock
    (fun j k => toCoeff (ν := ν) h j ↑k) l) n'
  conv_lhs => rw [show (∑ x, (∑ m, A.finBlock l m * A_dag.finBlock m x).mulVec
    (fun k => toCoeff (ν := ν) h x ↑k) n') =
    (∑ x, (∑ m, A.finBlock l m * A_dag.finBlock m x).mulVec
      (fun k => toCoeff (ν := ν) h x ↑k)) n' from (Finset.sum_apply _ _ _).symm]
  rw [← hassoc]
  rw [SystemBlockDiagData.action_fin_eq_sum_mulVec A _ l n']
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  congr 1; ext m; congr 1; ext p; congr 1
  exact (hDF_block h m p).symm

/-! ## 4. Main Theorem (Theorem 8.2.2) -/

/-- **Theorem 8.2.2** (System-Level IVP Radii Polynomial Theorem).

Given a polynomial IVP system with:
- Nonlinearity `φ : XL1 → Fin L → l1Weighted`
- Approximate inverse `A : SystemBlockDiagData` with `tailDiag = 1/n`
- Approximate derivative `A† : BlockDiagOp` with `A.tail * A†.tail = 1`
- Approximate solution `ā ∈ XL1`

If the radii polynomial `p(r₀) = Z₂·r₀² - (1 - Z₀ - Z₁)·r₀ + Y₀ < 0`, then
there exists a unique zero of the composed IVP map in `closedBall ā r₀`. -/
theorem ivp_system_theorem
    -- Operator data
    (A : SystemBlockDiagData L N) (A_dag : BlockDiagOp L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (ā : XL1 ν L)
    -- Structural IVP hypotheses
    (htail_diag_inv : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (htail_cancel : ∀ l : Fin L, ∀ n, N < n →
      A.tailDiag l n * A_dag.tailDiag l n = 1)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    -- Z₁ finite-mode: fderiv of ivpCoeffs = A_dag.finBlock action
    (hDF_block : ∀ (h : XL1 ν L) (j : Fin L) (k : Fin (N + 1)),
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j ↑k) ā) h =
        ∑ m : Fin L, (A_dag.finBlock j m).mulVec
          (fun p => toCoeff (ν := ν) h m ↑p) k)
    -- Z₁ tail: Dφ per-component norm bound
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ_le : ∀ (h : XL1 ν L) (l : Fin L),
      ‖(fderiv ℝ (fun a => φ a l) ā) h‖ ≤ K * ‖h‖)
    -- Z₂: Dφ Lipschitz + block sparsity
    (active : Finset (Fin L))
    (hzero : ∀ (c : XL1 ν L) (h : XL1 ν L) (j : Fin L), j ∉ active →
      (fderiv ℝ (fun x => φ x j) c - fderiv ℝ (fun x => φ x j) ā) h = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hDφ_diff : ∀ (c : XL1 ν L) (h : XL1 ν L) (l : Fin L),
      ‖(fderiv ℝ (fun x => φ x l) c - fderiv ℝ (fun x => φ x l) ā) h‖ ≤
        C * ‖c - ā‖ * ‖h‖)
    -- Y₀: support bound + per-component finite sum
    (S : ℕ) (hSN : N ≤ S)
    (hsupport : ∀ l : Fin L, ∀ n, S < n → ivpCoeffs φ x₀ ā l n = 0)
    -- Numerical certificates
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀_nn : 0 ≤ Y₀)
    (hY₀ : ∀ l : Fin L,
      ∑ n ∈ Finset.Icc 0 S,
        |A.action (ivpCoeffs φ x₀ ā) l n| * (ν : ℝ) ^ n ≤ Y₀)
    (hZ₀ : finiteBlockMatrixNorm ν (defectOfBlockDiagOp A A_dag).finBlock ≤ Z₀)
    (hZ₁ : (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁)
    (hZ₂_nn : 0 ≤ Z₂_val)
    (hZ₂ : ∀ l : Fin L,
      C * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
        if l ∈ active then A.tailBound else 0) ≤ Z₂_val)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (ā : XL1 ν L) r₀,
      ivpMap A φ x₀ (ivpMap_mem_of_tailDiag_inv A φ x₀ htail_diag_inv) xTilde = 0 := by
  set hmem := ivpMap_mem_of_tailDiag_inv A φ x₀ htail_diag_inv
  set G := ivpMap A φ x₀ hmem
  set CA := ivpComposedApprox A A_dag htail_cancel
  have hG_diff : Differentiable ℝ G :=
    differentiable_ivpMap A φ x₀ htail_diag_inv hmem hφ_diff
  -- Assemble bounds
  have sub_seq : ∀ (f g : XL1 ν L →L[ℝ] XL1 ν L) (x : XL1 ν L) (l : Fin L) (n : ℕ),
      l1Weighted.toSeq (((f - g) x) l) n =
        l1Weighted.toSeq ((f x) l) n - l1Weighted.toSeq ((g x) l) n := by
    intros; simp [ContinuousLinearMap.sub_apply]
  have h_Y₀ := ivp_Y₀_le A φ x₀ hmem ā S hSN hsupport hY₀_nn hY₀
  have h_Z₀ := ivp_Z₀_le A A_dag htail_cancel hZ₀
  have h_Z₁ := ivp_Z₁_le CA G ā (fun h l => (fderiv ℝ (fun a => φ a l) ā) h)
    (fun h l n hn => by
      rw [sub_seq]
      have := ivpComposedApprox_eq_fderiv_fin A A_dag φ x₀ htail_cancel
        htail_diag_inv hmem hφ_diff ā hDF_block h l n hn
      simp only [toCoeff] at this; linarith)
    (fun h l n hn => by
      rw [sub_seq]
      have h1 : l1Weighted.toSeq (CA.toCLM (ν := ν) h l) n =
          l1Weighted.toSeq (h l) n := by
        show toCoeff (ν := ν) (CA.toCLM (ν := ν) h) l n = toCoeff h l n
        exact ivpComposedApprox_toCLM_tail A A_dag htail_cancel h l n hn
      rw [h1, fderiv_ivpMap_tail A φ x₀ htail_diag_inv hmem hφ_diff ā h l n hn,
        fderiv_ivpTail φ hφ_diff ā h l]
      simp)
    hK hDφ_le hZ₁
  have h_Z₂ : ∀ c ∈ Metric.closedBall ā r₀,
      ‖(ContinuousLinearMap.id ℝ (XL1 ν L)).comp
        (fderiv ℝ G c - fderiv ℝ G ā)‖ ≤ (fun _ => Z₂_val) r₀ * r₀ := by
    intro c hc; simp only [ContinuousLinearMap.id_comp]
    exact ivp_Z₂_le A G φ x₀ ā hG_diff hφ_diff
      (fun a l n => ivpMap_coeff A φ x₀ hmem a l n)
      active hzero hC hDφ_diff hZ₂_nn hZ₂ c hc
  -- Apply the abstract theorem
  exact general_radii_polynomial_theorem (A := ContinuousLinearMap.id ℝ _)
    (A_dagger := CA.toCLM (ν := ν))
    hr₀ h_Y₀ h_Z₀ h_Z₁ h_Z₂ hG_diff h_radii (fun _ _ h => h)

end IVP
