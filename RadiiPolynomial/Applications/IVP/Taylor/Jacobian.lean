import RadiiPolynomial.Applications.IVP.Taylor.Operator
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.WeightedL1

/-!
# Generic DF Block Verification for IVP Systems

The Jacobian bridge for the IVP zero-finding map. Each IVP example needs to
prove that the Fréchet derivative of `ivpCoeffs` agrees with the numerical
Jacobian stored in `A_dag.finBlock`. This file combines the coefficient
derivative formulas from `IVP.Setup`, `toSeq_fderiv_evalInBanach`, and the
Toeplitz row action into `ivp_hDF_block_nat`.

## Solution

`ivp_hDF_block_nat` provides the generic proof. The user supplies:
1. `φ_spec` — MvPolynomial specification of the nonlinearity
2. `Dφ_Q` — computable ℚ mirror of `pderiv(φ_spec)` evaluated at ābar
3. Proofs connecting these (`hφ_eq`, `habar`, `hDφ_Q`, `hDF`)

## Live consumer

The StdIVPData wrapper `IVP.StdIVPData.composedApprox_eq_fderiv_G_fin`
(`Applications/IVP/Taylor/Standard.lean`) calls `ivp_hDF_block_nat` and delivers the
toCoeff/G-side framing that the per-example Z₁ bound consumes (see
`composedApprox_eq_fderiv_G_fin` in each Taylor IVP example's `Algebra.lean`).
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-! ## 1. Computable DF Expected Formula -/

/-- Assemble the expected Jacobian entries from computable pderiv coefficients `Dφ_Q`.

For the IVP map F(a)_l_k:
- k = 0: F₀ = a_{l,0} - x₀_l  →  DF_{0,m,p} = δ_{l,m} · δ_{0,p}
- k = n+1: F_{n+1} = (n+1)·a_{l,n+1} - φ_l(a)_n
  → DF_{n+1,m,p} = (n+1)·δ_{l,m}·δ_{n+1,p} - Dφ_{l,n,m,p}

where `Dφ_{l,n,m,p} = Dφ_Q l m (n-p)` for `p ≤ n`, 0 otherwise (Toeplitz structure).

This natural-indexed form is canonical because certificates verify array entries by
`native_decide`; `ivp_DF_of_Dφ` below only restricts it to the finite block. -/
def ivp_DF_of_Dφ_nat (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (row col : ℕ) : ℚ :=
  match row with
  | 0 => if j = m ∧ col = 0 then 1 else 0
  | Nat.succ n =>
    (if j = m ∧ col = n + 1 then (n : ℚ) + 1 else 0) -
      (if col ≤ n then Dφ_Q j m (n - col) else 0)

/-- Finite-block restriction of the natural-indexed expected IVP Jacobian. -/
def ivp_DF_of_Dφ (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (k p : Fin (N + 1)) : ℚ :=
  ivp_DF_of_Dφ_nat Dφ_Q j m (k : ℕ) (p : ℕ)

omit [NeZero L] in
/-- `ivp_DF_of_Dφ_nat` agrees with `ivp_DF_of_Dφ` on `Fin` indices. -/
lemma ivp_DF_of_Dφ_nat_eq (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (k p : Fin (N + 1)) :
    ivp_DF_of_Dφ_nat Dφ_Q j m (k : ℕ) (p : ℕ) = ivp_DF_of_Dφ (N := N) Dφ_Q j m k p := by
  rfl

omit [NeZero L] in
/-- A rational Kronecker delta selects one matrix-vector coordinate after casting. -/
private lemma sum_delta_cast_mul {M : ℕ}
    (v : Fin L → Fin M → ℝ) (j : Fin L) (q : ℕ) (hq : q < M) (c : ℚ) :
    (∑ m : Fin L, ∑ p : Fin M,
      ((if j = m ∧ (p : ℕ) = q then c else 0 : ℚ) : ℝ) * v m p) =
        (c : ℝ) * v j ⟨q, hq⟩ := by
  classical
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single ⟨q, hq⟩]
    · simp
    · intro p _ hp
      simp [show (p : ℕ) ≠ q from fun hpq => hp (Fin.ext hpq)]
    · simp
  · intro m _ hm
    simp [Ne.symm hm]
  · simp

/-! ## 2. Bridge Lemma: Dφ_Q matches analytical pderiv -/

omit [NeZero L] in
/-- Internal bridge: if `Dφ_Q j m k` matches `toSeq(evalInBanach(pderiv m (spec j), ā)) k`,
then the Toeplitz extension matches `toSeq_fderiv_evalInBanach`. -/
private lemma ivp_Dφ_jacobian_bridge
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (ā : XL1 ν L)
    (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (hDφ_Q : ∀ (j m : Fin L) (k : ℕ),
      l1Weighted.toSeq (MvPolyBridge.evalInBanach
        (MvPolynomial.pderiv (↑m) (φ_spec j)) ā) k =
      ((Dφ_Q j m k : ℚ) : ℝ))
    (j : Fin L) (n : ℕ) (m : Fin L) (p : Fin (N + 1)) :
    ((if (p : ℕ) ≤ n then Dφ_Q j m (n - (p : ℕ)) else 0 : ℚ) : ℝ) =
      if (p : ℕ) ≤ n then
        l1Weighted.toSeq (MvPolyBridge.evalInBanach
          (MvPolynomial.pderiv (↑m) (φ_spec j)) ā) (n - (p : ℕ))
      else 0 := by
  split_ifs with hp
  · exact_mod_cast (hDφ_Q j m _).symm
  · simp

omit [NeZero L] in
/-- A positive expected-Jacobian row acts as the IVP diagonal minus its Toeplitz row. -/
private lemma sum_ivp_DF_succ
    (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (v : Fin L → Fin (N + 1) → ℝ) (j : Fin L)
    (n : ℕ) (hk : n + 1 < N + 1) :
    (∑ m : Fin L, ∑ p : Fin (N + 1),
      ((ivp_DF_of_Dφ (N := N) Dφ_Q j m ⟨n + 1, hk⟩ p : ℚ) : ℝ) * v m p) =
      ((n : ℝ) + 1) * v j ⟨n + 1, hk⟩ -
        ∑ m : Fin L, ∑ p : Fin (N + 1),
          ((if (p : ℕ) ≤ n then Dφ_Q j m (n - (p : ℕ)) else 0 : ℚ) : ℝ) * v m p := by
  simp only [ivp_DF_of_Dφ, ivp_DF_of_Dφ_nat, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  rw [sum_delta_cast_mul v j (n + 1) hk ((n : ℚ) + 1)]
  push_cast
  rfl

/-! ## 3. Main Generic Theorem -/

omit [NeZero L] in
/-- **Generic DF block correctness for IVP systems.**

Given:
- `φ_spec` — MvPolynomial specification of the nonlinearity
- `Dφ_Q` — computable ℚ coefficients of `pderiv(φ_spec)` at ābar
- `hDφ_Q` — bridge proving Dφ_Q matches the analytical pderiv evaluation
- `hDF` — numerical verification that A_dag.finBlock matches `ivp_DF_of_Dφ`

Proves that the Fréchet derivative of `ivpCoeffs` matches the `A_dag.finBlock` action.
This is the `hDF_block` hypothesis required by `ivp_system_theorem`. -/
theorem ivp_hDF_block
    (A_dag : BlockDiagOp L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (x₀ : Fin L → ℝ)
    (ā : XL1 ν L)
    -- Spec compatibility
    (hφ_eq : ∀ (a : XL1 ν L) (l : Fin L),
      φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    -- Computable pderiv mirror
    (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (hDφ_Q : ∀ (j m : Fin L) (k : ℕ),
      l1Weighted.toSeq (MvPolyBridge.evalInBanach
        (MvPolynomial.pderiv (↑m) (φ_spec j)) ā) k =
      ((Dφ_Q j m k : ℚ) : ℝ))
    -- Numerical DF verification
    (hDF : ∀ (j m : Fin L) (k p : Fin (N + 1)),
      A_dag.finBlock j m k p = ((ivp_DF_of_Dφ (N := N) Dφ_Q j m k p : ℚ) : ℝ))
    -- Output
    (h : XL1 ν L) (j : Fin L) (k : Fin (N + 1)) :
    (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j ↑k) ā) h =
      ∑ m : Fin L, (A_dag.finBlock j m).mulVec
        (fun p => toCoeff (ν := ν) h m ↑p) k := by
  -- Rewrite RHS: unfold mulVec/dotProduct, apply hDF
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [hDF]
  revert k
  intro ⟨k, hk⟩
  cases k with
  | zero =>
    rw [fderiv_ivpCoeffs_zero_apply φ x₀ ā h j]
    symm
    simpa only [ivp_DF_of_Dφ, ivp_DF_of_Dφ_nat, toCoeff, Rat.cast_one,
      one_mul] using
      sum_delta_cast_mul (fun m p => toCoeff (ν := ν) h m (p : ℕ)) j 0
        (Nat.zero_lt_succ N) (1 : ℚ)
  | succ n =>
    rw [fderiv_ivpCoeffs_succ_apply φ x₀ ā h j n (hφ_diff j ā),
      show (fun a : XL1 ν L => φ a j) =
        (fun a => evalInBanach (φ_spec j) a) from funext fun a => hφ_eq a j]
    rw [toSeq_fderiv_evalInBanach _ ā h (show n ≤ N from by omega)]
    simp_rw [← ivp_Dφ_jacobian_bridge φ_spec ā Dφ_Q hDφ_Q j n]
    symm
    simpa only [toCoeff] using
      sum_ivp_DF_succ Dφ_Q (fun m p => toCoeff (ν := ν) h m (p : ℕ)) j n hk

/-! ## 4. Generic Dφ Operator Norm Bound -/

omit [NeZero L] in
/-- **Generic Dφ operator norm bound for IVP systems.**

Given `φ_spec` and a per-component bound `K` on `Σ_m ‖pderiv_m(φ_spec l) at ā‖`,
proves `‖(fderiv φ l ā) h‖ ≤ K * ‖h‖`.

The user provides:
- `Dφ_norms : Fin L → Fin L → ℝ` — upper bounds on `‖evalInBanach(pderiv m (spec l), ā)‖`
- `hDφ_norms` — proofs of these bounds (e.g., via `finsum_bound`)
- `K` — overall bound: `Σ_m Dφ_norms l m ≤ K` for each `l`
-/
lemma ivp_Dφ_norm_le
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (ā : XL1 ν L)
    (hφ_eq : ∀ (a : XL1 ν L) (l : Fin L),
      φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    {K : ℝ}
    (hDφ_le : ∀ (l : Fin L),
      ∑ m : Fin L,
        ‖MvPolyBridge.evalInBanach (MvPolynomial.pderiv (↑m) (φ_spec l)) ā‖ ≤ K)
    (h : XL1 ν L) (l : Fin L) :
    ‖(fderiv ℝ (fun a => φ a l) ā) h‖ ≤ K * ‖h‖ := by
  rw [show (fun a : XL1 ν L => φ a l) =
      (fun a => evalInBanach (φ_spec l) a) from funext fun a => hφ_eq a l,
    fderiv_evalInBanach]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply]
  exact (norm_sum_mul_pi_le _ _).trans
    (mul_le_mul_of_nonneg_right (hDφ_le l) (norm_nonneg _))

/-! ## 5. Convenience: ivp_hDF_block_nat -/

omit [NeZero L] in
/-- Convenience version of `ivp_hDF_block` accepting a `Fin`-bounded `native_decide` proof.

The user provides:
```
hDF_nat : ∀ j m : Fin L, ∀ row col : Fin (N + 1),
    (DF_col j m (col : ℕ)).getD (row : ℕ) 0 = ivp_DF_of_Dφ_nat Dφ_Q j m (row : ℕ) (col : ℕ)
```
proved by `native_decide`, and this wraps it into the form needed internally. -/
theorem ivp_hDF_block_nat
    (A_dag : BlockDiagOp L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (x₀ : Fin L → ℝ)
    (ā : XL1 ν L)
    (hφ_eq : ∀ (a : XL1 ν L) (l : Fin L),
      φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (hDφ_Q : ∀ (j m : Fin L) (k : ℕ),
      l1Weighted.toSeq (MvPolyBridge.evalInBanach
        (MvPolynomial.pderiv (↑m) (φ_spec j)) ā) k =
      ((Dφ_Q j m k : ℚ) : ℝ))
    -- Fin-bounded DF verification (single native_decide)
    (DF_cols : Fin L → Fin L → ℕ → Array ℚ)
    (hDF_finBlock : ∀ (j m : Fin L) (k p : Fin (N + 1)),
      A_dag.finBlock j m k p = ((DF_cols j m (p : ℕ)).getD (k : ℕ) 0 : ℝ))
    (hDF_nat : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (DF_cols j m (col : ℕ)).getD (row : ℕ) 0 = ivp_DF_of_Dφ_nat Dφ_Q j m (row : ℕ) (col : ℕ))
    (h : XL1 ν L) (j : Fin L) (k : Fin (N + 1)) :
    (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j ↑k) ā) h =
      ∑ m : Fin L, (A_dag.finBlock j m).mulVec
        (fun p => toCoeff (ν := ν) h m ↑p) k :=
  ivp_hDF_block A_dag φ φ_spec x₀ ā hφ_eq hφ_diff Dφ_Q hDφ_Q
    (fun j m k p => by
      rw [hDF_finBlock j m k p, hDF_nat j m k p]
      rfl)
    h j k

end IVP
