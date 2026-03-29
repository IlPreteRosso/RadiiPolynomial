import RadiiPolynomial.source.IVP.Setup
import RadiiPolynomial.source.MvPolyBridge.Basic

/-!
# Generic DF Block Verification for IVP Systems

Eliminates the ~80-line `fderiv_F_coeffs_eq` boilerplate from each IVP example.

## Problem

Each IVP example must prove that the Fréchet derivative of `ivpCoeffs` matches the
numerical Jacobian data stored in `A_dag.finBlock`. This proof follows the same structure
every time:
- Zero case: fderiv of affine = coordinate projection
- Succ case: chain rule → HasFDerivAt decomposition → toSeq_fderiv_evalInBanach → Toeplitz sum

## Solution

`ivp_hDF_block` provides the generic proof. The user supplies:
1. `φ_spec` — MvPolynomial specification of the nonlinearity
2. `Dφ_Q` — computable ℚ mirror of `pderiv(φ_spec)` evaluated at ābar
3. Proofs connecting these (`hφ_eq`, `habar`, `hDφ_Q`, `hDF`)

The chain rule + HasFDerivAt decomposition (~60 lines) lives here, not in each example.

## Usage

```
-- In Algebra.lean, replace the 80-line fderiv_F_coeffs_eq with:
lemma fderiv_F_coeffs_eq ... :=
  IVP.ivp_hDF_block approxDeriv φ_scalar φ_scalar_spec x₀ abar (fun _ => abar_0)
    φ_scalar_eq_spec differentiable_φ_scalar_component abar_toSeq_eq
    Dφ_pderiv_Q Dφ_pderiv_bridge hDF_match h j k
```
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
- k = n+1: F_{n+1} = (n+1)·a_{l,n+1} - φ_l(a)_n  →  DF_{n+1,m,p} = (n+1)·δ_{l,m}·δ_{n+1,p} - Dφ_{l,n,m,p}

where `Dφ_{l,n,m,p} = Dφ_Q l m (n-p)` for `p ≤ n`, 0 otherwise (Toeplitz structure). -/
def ivp_DF_of_Dφ (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (k p : Fin (N + 1)) : ℚ :=
  match (k : ℕ) with
  | 0 => if j = m ∧ (p : ℕ) = 0 then 1 else 0
  | Nat.succ n =>
    (if j = m ∧ (p : ℕ) = n + 1 then (n : ℚ) + 1 else 0) -
      (if (p : ℕ) ≤ n then Dφ_Q j m (n - (p : ℕ)) else 0)

/-- ℕ-argument version of `ivp_DF_of_Dφ`, directly comparable to `DF_col.getD` entries
via `native_decide`. Avoids `Fin` coercion issues in the verification step. -/
def ivp_DF_of_Dφ_nat (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (row col : ℕ) : ℚ :=
  match row with
  | 0 => if j = m ∧ col = 0 then 1 else 0
  | Nat.succ n =>
    (if j = m ∧ col = n + 1 then (n : ℚ) + 1 else 0) -
      (if col ≤ n then Dφ_Q j m (n - col) else 0)

/-- `ivp_DF_of_Dφ_nat` agrees with `ivp_DF_of_Dφ` on `Fin` indices. -/
lemma ivp_DF_of_Dφ_nat_eq (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (j m : Fin L) (k p : Fin (N + 1)) :
    ivp_DF_of_Dφ_nat Dφ_Q j m (k : ℕ) (p : ℕ) = ivp_DF_of_Dφ (N := N) Dφ_Q j m k p := by
  simp [ivp_DF_of_Dφ_nat, ivp_DF_of_Dφ]

/-! ## 2. Bridge Lemma: Dφ_Q matches analytical pderiv -/

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

/-! ## 3. Main Generic Theorem -/

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
    (abar_Q : Fin L → Array ℚ)
    -- Spec compatibility
    (hφ_eq : ∀ (a : XL1 ν L) (l : Fin L),
      φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (habar : ∀ (l : Fin L) (n : ℕ),
      l1Weighted.toSeq (ā l) n = ((abar_Q l).getD n 0 : ℝ))
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
  revert k; intro ⟨k, hk⟩
  cases k with
  | zero =>
    -- F(a)_{j,0} = toSeq(a j) 0 - x₀ j  (affine → fderiv = coordinate projection)
    show (fderiv ℝ (fun a : XL1 ν L => ivpCoeffs φ x₀ a j 0) ā) h = _
    conv_lhs => rw [show (fun a : XL1 ν L => ivpCoeffs φ x₀ a j 0) =
      fun a => l1Weighted.toSeq (a j) 0 - x₀ j from funext fun a => rfl]
    rw [fderiv_sub_const,
      show (fun a : XL1 ν L => l1Weighted.toSeq (a j) 0) =
        ⇑((l1Weighted.toSeq_CLM (ν := ν) 0).comp (ContinuousLinearMap.proj j)) from rfl,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    -- RHS: Kronecker delta sum Σ_m Σ_p δ_{j,m}·δ_{0,p} · h_m_p = h_j_0
    simp only [ivp_DF_of_Dφ]
    change lpWeighted.toSeq (h j) 0 = _
    rw [Finset.sum_eq_single j
      (fun m _ hm => Finset.sum_eq_zero fun p _ => by
        simp [show ¬(j = m) from Ne.symm hm])
      (by simp),
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (N + 1))
      (fun p _ hp => by simp [show (p : ℕ) ≠ 0 from Fin.val_ne_of_ne hp])
      (by simp)]
    simp [toCoeff]
  | succ n =>
    -- F(a)_{j,n+1} = (n+1)·toSeq(a j)(n+1) - toSeq(φ a j) n
    show (fderiv ℝ (fun a : XL1 ν L =>
      ivpCoeffs φ x₀ a j ↑(⟨n + 1, hk⟩ : Fin (N + 1))) ā) h = _
    conv_lhs => rw [show (fun a : XL1 ν L => ivpCoeffs φ x₀ a j
        ↑(⟨n + 1, hk⟩ : Fin (N + 1))) =
      fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1) -
        l1Weighted.toSeq (φ a j) n from funext fun a => rfl]
    -- Chain rule decomposition
    set proj_j := ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin L => l1Weighted ν) j
    have hd1 : HasFDerivAt
        (fun a : XL1 ν L => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1))
        (((n : ℝ) + 1) • ((l1Weighted.toSeq_CLM (n + 1)).comp proj_j)) ā :=
      (((l1Weighted.toSeq_CLM (ν := ν) (n + 1)).comp proj_j).hasFDerivAt).const_mul _
    have hd2 : HasFDerivAt
        (fun a : XL1 ν L => l1Weighted.toSeq (φ a j) n)
        ((l1Weighted.toSeq_CLM (ν := ν) n).comp
          (fderiv ℝ (fun a => φ a j) ā)) ā := by
      have := ((l1Weighted.toSeq_CLM (ν := ν) n).hasFDerivAt
        (x := φ ā j)).comp ā (hφ_diff j ā).hasFDerivAt
      convert this using 1
    rw [show (fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1) -
        l1Weighted.toSeq (φ a j) n) =
      (fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1)) -
        (fun a => l1Weighted.toSeq (φ a j) n) from rfl,
      (hd1.sub hd2).fderiv, ContinuousLinearMap.sub_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul]
    -- Unfold toSeq_CLM to toSeq
    change ((n : ℝ) + 1) * l1Weighted.toSeq (h j) (n + 1) -
      l1Weighted.toSeq ((fderiv ℝ (fun a => φ a j) ā) h) n = _
    -- Rewrite fderiv(φ) using spec → toSeq_fderiv_evalInBanach
    have hfun_eq : (fun a : XL1 ν L => φ a j) = (fun a => evalInBanach (φ_spec j) a) :=
      funext (fun a => hφ_eq a j)
    conv_lhs => rw [hfun_eq]
    rw [toSeq_fderiv_evalInBanach _ ā h (show n ≤ N from by omega)]
    -- Now LHS = (n+1)*toCoeff(h,j,n+1) - Σ_m Σ_p (pderiv coeff)_{n-p} * toSeq(h m) p
    -- Apply Dφ_Q bridge
    simp_rw [← ivp_Dφ_jacobian_bridge φ_spec ā Dφ_Q hDφ_Q j n]
    -- Match with RHS
    simp only [ivp_DF_of_Dφ]
    simp only [show ∀ (m : Fin L) (p : Fin (N + 1)),
      (((if j = m ∧ (p : ℕ) = n + 1 then (↑n + 1 : ℚ) else 0) -
        (if (p : ℕ) ≤ n then Dφ_Q j m (n - (p : ℕ)) else 0) : ℚ) : ℝ) *
        toCoeff (ν := ν) h m ↑p =
      (if j = m ∧ (p : ℕ) = n + 1 then ((n : ℝ) + 1) * toCoeff (ν := ν) h m ↑p else 0) -
        ↑(if (p : ℕ) ≤ n then Dφ_Q j m (n - (p : ℕ)) else (0 : ℚ)) *
          toCoeff (ν := ν) h m ↑p
      from fun m p => by split_ifs <;> (push_cast; ring)]
    simp only [Finset.sum_sub_distrib]
    congr 1
    -- Collapse Kronecker delta: both sides = (n+1) * toCoeff h j (n+1)
    trans ((↑n + 1) * toCoeff (ν := ν) h j (n + 1))
    · simp [toCoeff]
    · symm
      have h_outer : ∀ m ∈ Finset.univ, m ≠ j →
          ∑ p : Fin (N + 1),
            (if j = m ∧ (↑p : ℕ) = n + 1 then ((↑n + 1) * toCoeff (ν := ν) h m ↑p) else 0) = 0 :=
        fun m _ hm => Finset.sum_eq_zero fun p _ => by simp [Ne.symm hm]
      have h_inner : ∀ p ∈ Finset.univ, p ≠ (⟨n + 1, hk⟩ : Fin (N + 1)) →
          (if j = j ∧ (↑p : ℕ) = n + 1 then ((↑n + 1) * toCoeff (ν := ν) h j ↑p) else 0) = 0 :=
        fun p _ hp => by simp [show (p : ℕ) ≠ n + 1 from fun h => hp (Fin.ext h)]
      rw [Finset.sum_eq_single j h_outer (by simp),
          Finset.sum_eq_single ⟨n + 1, hk⟩ h_inner (by simp)]
      simp [toCoeff]

/-! ## 4. Generic Dφ Operator Norm Bound -/

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
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ_le : ∀ (l : Fin L),
      ∑ m : Fin L,
        ‖MvPolyBridge.evalInBanach (MvPolynomial.pderiv (↑m) (φ_spec l)) ā‖ ≤ K)
    (h : XL1 ν L) (l : Fin L) :
    ‖(fderiv ℝ (fun a => φ a l) ā) h‖ ≤ K * ‖h‖ := by
  have hfun_eq : (fun a : XL1 ν L => φ a l) = (fun a => evalInBanach (φ_spec l) a) :=
    funext (fun a => hφ_eq a l)
  rw [hfun_eq, fderiv_evalInBanach]
  -- ‖Σ_i leftMul(g_i)(h_i)‖ ≤ Σ_i ‖g_i‖ * ‖h_i‖ ≤ (Σ_i ‖g_i‖) * ‖h‖
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply]
  calc ‖∑ i : Fin L, evalInBanach (MvPolynomial.pderiv (↑i) (φ_spec l)) ā * h i‖
      ≤ ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv (↑i) (φ_spec l)) ā * h i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv (↑i) (φ_spec l)) ā‖ * ‖h i‖ :=
        Finset.sum_le_sum fun i _ => norm_mul_le _ _
    _ ≤ ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv (↑i) (φ_spec l)) ā‖ * ‖h‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _)
    _ = (∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv (↑i) (φ_spec l)) ā‖) * ‖h‖ :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ K * ‖h‖ := mul_le_mul_of_nonneg_right (hDφ_le l) (norm_nonneg _)

/-! ## 5. Convenience: ivp_hDF_block_nat -/

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
    (abar_Q : Fin L → Array ℚ)
    (hφ_eq : ∀ (a : XL1 ν L) (l : Fin L),
      φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (habar : ∀ (l : Fin L) (n : ℕ),
      l1Weighted.toSeq (ā l) n = ((abar_Q l).getD n 0 : ℝ))
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
  ivp_hDF_block A_dag φ φ_spec x₀ ā abar_Q hφ_eq hφ_diff habar Dφ_Q hDφ_Q
    (fun j m k p => by
      rw [hDF_finBlock j m k p, show ((DF_cols j m (p : ℕ)).getD (k : ℕ) 0 : ℝ) =
        ((ivp_DF_of_Dφ (N := N) Dφ_Q j m k p : ℚ) : ℝ) from by
        rw [show (DF_cols j m (p : ℕ)).getD (k : ℕ) 0 =
          ivp_DF_of_Dφ_nat Dφ_Q j m (k : ℕ) (p : ℕ) from hDF_nat j m k p,
          ivp_DF_of_Dφ_nat_eq]])
    h j k

end IVP
