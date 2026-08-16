import RadiiPolynomial.Operators.BlockDiagonal.Scalar
import RadiiPolynomial.Tactic.AutoPolyFDeriv
import RadiiPolynomial.Core.AffineZ2

/-!
# Example 7.7 — Algebraic Infrastructure

Problem-specific algebra for the parameterized equilibrium `x² - λ = 0`.
Uses the `RadiiPolynomial/BlockDiagSystem` API exclusively.

## Contents

1. **Fréchet derivative**: `HasFDerivAt` via `auto_hasFDerivAt`, with `fderiv`/`Differentiable`
   derived from it. Affine fderiv form (`fderiv_F_sub_const_affine`) for Z₂.
2. **Problem data**: `paramSeq`, `ApproxSolution`, `F`, `F_toSeq`
3. **Operator construction**: `approxDeriv`, `approxInverse` as `ScalarBlockDiagData`
4. **Z₁ infrastructure**: `shiftedSeq`/`shiftedL1` (shifted coefficient sequence),
   `approxDeriv_finBlock_eq_cauchy` (Cauchy bridge for fin block),
   `approxDeriv_sub_fderiv_fin_kill` (fin modes vanish via `toScalarCLM_toSeq_fin_eq_cauchy`),
   `approxDeriv_sub_fderiv_tail_eq` (tail equals `-2•leftMul(shiftedL1)`),
   `Z₁_le_via_eval` (chains `Z₁_le_of_fin_kill_tail_dom`)
5. **Z₂**: via `Z₂_ball_bound_of_affine_leftMul` from `Z2Affine.lean`
6. **Main theorem**: `existsUnique` skeleton via `general_radii_polynomial_theorem`
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le
  leftMul_add leftMul_sub leftMul_smul smul_id_eq_leftMul)

noncomputable section

variable {ν : PosReal}

/-! ## 1. Fréchet Derivative for F(a) = a*a - c

`leftMul`, `smul_id_eq_leftMul`, and related lemmas are in
`RadiiPolynomial.l1Weighted` (LpOneBanachAlgebra.lean). -/

namespace Example77

/-! ### Squaring map and F = sq - c -/

def sq (a : l1Weighted ν) : l1Weighted ν := a * a

lemma sq_eq_pow (a : l1Weighted ν) : sq a = a ^ 2 := by
  simp [sq, _root_.sq]

lemma sq_eq_fun : (sq : l1Weighted ν → l1Weighted ν) = fun x => x ^ 2 := funext sq_eq_pow

def F_sub_const (c : l1Weighted ν) (a : l1Weighted ν) : l1Weighted ν := sq a - c

lemma F_sub_const_eq_fun (c : l1Weighted ν) :
    (F_sub_const c : l1Weighted ν → l1Weighted ν) = fun x => x ^ 2 - c :=
  funext (fun a => by simp [F_sub_const, sq_eq_pow])

/-! ### Fréchet derivative (via `auto_poly_fderiv`)

Pattern: `rw` unfolds the named def, then `auto_poly_fderiv` computes + normalizes
(Banach algebra bridge lemmas are built into the main simp phase). -/

theorem hasFDerivAt_sq (a : l1Weighted ν) :
    HasFDerivAt sq ((2 : ℝ) • leftMul a) a := by
  rw [sq_eq_fun]; auto_hasFDerivAt

theorem fderiv_sq (a : l1Weighted ν) :
    fderiv ℝ sq a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_sq a).fderiv

theorem differentiable_sq : Differentiable ℝ (sq : l1Weighted ν → l1Weighted ν) :=
  fun a => (hasFDerivAt_sq a).differentiableAt

theorem hasFDerivAt_F_sub_const (c a : l1Weighted ν) :
    HasFDerivAt (F_sub_const c) ((2 : ℝ) • leftMul a) a :=
  (hasFDerivAt_sq a).sub_const c

theorem fderiv_F_sub_const (c a : l1Weighted ν) :
    fderiv ℝ (F_sub_const c) a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_F_sub_const c a).fderiv

theorem differentiable_F_sub_const (c : l1Weighted ν) :
    Differentiable ℝ (F_sub_const c) :=
  fun a => (hasFDerivAt_F_sub_const c a).differentiableAt

/-- The fderiv of `F_sub_const c` is affine in `leftMul` with `α = 2, K = 0`.
This is the hypothesis needed by `Z₂_ball_bound_of_affine_leftMul`. -/
lemma fderiv_F_sub_const_affine (c : l1Weighted ν) :
    ∀ x, fderiv ℝ (F_sub_const c) x = (2 : ℝ) • leftMul x + 0 :=
  fun x => by rw [fderiv_F_sub_const, add_zero]

/-! ## 2. Problem Data -/

/-- The constant sequence c = (lam0, 1, 0, 0, ...) encoding λ = lam0 + t. -/
def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with | 0 => lam0 | 1 => 1 | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : l1Weighted.Mem ν (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

def c (lam0 : ℝ) : l1Weighted ν := l1Weighted.mk (paramSeq lam0) (paramSeq_mem lam0)

/-- The zero-finding map F(a) = a*a - c(lam0). -/
def F (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν := F_sub_const (c lam0) a

lemma F_eq (lam0 : ℝ) (a : l1Weighted ν) : F lam0 a = sq a - c lam0 := rfl

/-- Sequence-level formula for F(a): CauchyProduct(a,a) - paramSeq(λ₀).
Bridges the abstract `F` to computable form for certificates. -/
lemma F_toSeq (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (F lam0 a) n =
    CauchyProduct (l1Weighted.toSeq a) (l1Weighted.toSeq a) n - paramSeq lam0 n := by
  simp only [F, F_sub_const, sq, l1Weighted.sub_toSeq, l1Weighted.toSeq_mul, c,
    l1Weighted.mk_apply]

theorem differentiable_F (lam0 : ℝ) : Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  differentiable_F_sub_const _

theorem fderiv_F (lam0 : ℝ) (a : l1Weighted ν) :
    fderiv ℝ (F lam0) a = (2 : ℝ) • leftMul a :=
  fderiv_F_sub_const _ _

/-- Approximate solution: finite coefficients ā₀, ..., āₙ with ā₀ ≠ 0. -/
structure ApproxSolution (N : ℕ) where
  aBar_fin : Fin (N + 1) → ℝ
  aBar_zero_ne : aBar_fin 0 ≠ 0

/-- Zero-padded extension to ℕ. -/
def ApproxSolution.toSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ := fun n =>
  if h : n ≤ N then sol.aBar_fin ⟨n, Nat.lt_succ_of_le h⟩ else 0

lemma ApproxSolution.toSeq_zero_of_gt {N : ℕ} (sol : ApproxSolution N) (n : ℕ) (hn : N < n) :
    sol.toSeq n = 0 := by
  simp only [ApproxSolution.toSeq, not_le.mpr hn, ↓reduceDIte]

lemma ApproxSolution.toSeq_eq_fin {N : ℕ} (sol : ApproxSolution N) (n : Fin (N + 1)) :
    sol.toSeq n = sol.aBar_fin n := by
  simp only [ApproxSolution.toSeq, Fin.is_le, ↓reduceDIte]

lemma ApproxSolution.mem {N : ℕ} (sol : ApproxSolution N) : l1Weighted.Mem ν sol.toSeq := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp only [toSeq, mul_eq_zero, abs_eq_zero, dite_eq_right_iff, pow_eq_zero_iff',
    PosReal.coe_ne_zero, ne_eq, false_and, or_false]; intros; omega

def ApproxSolution.toL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  l1Weighted.mk sol.toSeq sol.mem

@[simp]
lemma ApproxSolution.toL1_toSeq {N : ℕ} (sol : ApproxSolution N) :
    l1Weighted.toSeq (sol.toL1 : l1Weighted ν) = sol.toSeq := rfl

/-! ## 3. Operators A and A† as ScalarBlockDiagData -/

/-- DF^(N)(ā): lower triangular with (DF)_{i,j} = 2*ā_{i-j} for j ≤ i. -/
def dfFin {N : ℕ} (sol : ApproxSolution N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) ≤ i then
    2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0

/-- A† as ScalarBlockDiagData: DF^(N)(ā) on finite, 2ā₀ on tail. -/
def approxDeriv {N : ℕ} (sol : ApproxSolution N) : ScalarBlockDiagData N :=
  ScalarBlockDiagData.ofParts
    (dfFin sol)
    (fun _ => 2 * sol.aBar_fin 0)
    |2 * sol.aBar_fin 0|
    (fun _ _ => le_refl _)

/-- A as ScalarBlockDiagData: A_mat on finite, 1/(2ā₀) on tail. -/
def approxInverse {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ScalarBlockDiagData N :=
  ScalarBlockDiagData.ofParts
    A_mat
    (fun _ => 1 / (2 * sol.aBar_fin 0))
    |1 / (2 * sol.aBar_fin 0)|
    (fun _ _ => le_refl _)

/-- Tail diagonals of A and A† multiply to 1. -/
lemma tailCancel {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n, N < n → (approxInverse sol A_mat).tailDiag0 n *
      (approxDeriv sol).tailDiag0 n = 1 := by
  intro n _
  simp only [approxInverse, approxDeriv, ScalarBlockDiagData.ofParts,
    ScalarBlockDiagData.tailDiag0]
  field_simp [sol.aBar_zero_ne]

/-- Tail diagonal of A is nonzero (for injectivity). -/
lemma approxInverse_tailDiag_ne_zero {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n, N < n → (approxInverse sol A_mat).tailDiag0 n ≠ 0 := by
  intro n _
  simp only [approxInverse, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.tailDiag0,
    ne_eq, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, sol.aBar_zero_ne,
    or_self, not_false_eq_true]

/-! ## 4. Structural Bound Reductions -/

/-! ### Z₀: reduces to finWeightedMatrixNorm of defect matrix -/

/-- Z₀ bound via tail cancellation. -/
lemma Z₀_structural {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Z₀_norm ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤
    FiniteWeightedNorm.finWeightedMatrixNorm ν
      (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) :=
  ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel
    (ν := ν) _ _ (tailCancel sol A_mat)

/-! ### Z₁: A†-DF kills finite modes, norm bounded by shifted convolution -/

/-- The finite block of `approxDeriv` is a Cauchy matrix with `a_seq = 2 * sol.toSeq`. -/
lemma approxDeriv_finBlock_eq_cauchy {N : ℕ} (sol : ApproxSolution N)
    (i j : Fin (N + 1)) :
    (approxDeriv sol).finBlock0 i j =
    if (j : ℕ) ≤ i then (fun k => 2 * sol.toSeq k) ((i : ℕ) - (j : ℕ)) else 0 := by
  simp only [approxDeriv, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.finBlock0,
    dfFin, Matrix.of_apply]
  split_ifs with h
  · rw [← sol.toSeq_eq_fin]
  · rfl

/-- A† - DF(ā) kills finite modes for x²-λ.
Uses `toScalarCLM_toSeq_fin_eq_cauchy`: on finite modes, the block-diagonal action
equals the Cauchy product, which is exactly 2·leftMul(ā). -/
lemma approxDeriv_sub_fderiv_fin_kill {N : ℕ}
    (sol : ApproxSolution N) (lam0 : ℝ) (h : l1Weighted ν)
    (n : ℕ) (hn : n ≤ N) :
    l1Weighted.toSeq (((approxDeriv sol).toScalarCLM (ν := ν) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν)) h) n = 0 := by
  rw [sub_apply, l1Weighted.sub_toSeq, fderiv_F,
    (approxDeriv sol).toScalarCLM_toSeq_fin_eq_cauchy (ν := ν)
      (fun k => 2 * sol.toSeq k) (approxDeriv_finBlock_eq_cauchy sol) h n hn,
    smul_apply, leftMul_apply, l1Weighted.smul_toSeq,
    l1Weighted.toSeq_mul, ApproxSolution.toL1_toSeq]
  have heq : (fun k => 2 * sol.toSeq k) = ((2 : ℝ) • sol.toSeq : ℕ → ℝ) := rfl
  rw [heq, CauchyProduct.smul_mul]
  simp [smul_eq_mul]

/-! ### Shifted coefficient sequence for Z₁ norm bound -/

/-- Shifted sequence: ā with 0th coefficient zeroed. Supported on [1,N]. -/
def shiftedSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ :=
  fun k => if k ∈ Finset.Icc 1 N then sol.toSeq k else 0

lemma shiftedSeq_mem {N : ℕ} (sol : ApproxSolution N) :
    l1Weighted.Mem ν (shiftedSeq sol) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
  intro n hn; simp [shiftedSeq, hn]

/-- Shifted sequence as element of ℓ¹_ν. -/
def shiftedL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  l1Weighted.mk (shiftedSeq sol) (shiftedSeq_mem sol)

lemma shiftedL1_norm {N : ℕ} (sol : ApproxSolution N) :
    ‖@shiftedL1 ν N sol‖ = ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n := by
  rw [l1Weighted.norm_eq_tsum]
  have h_eq : ∀ n, |l1Weighted.toSeq (@shiftedL1 ν N sol) n| * (ν : ℝ) ^ n =
      if n ∈ Finset.Icc 1 N then |sol.toSeq n| * (ν : ℝ) ^ n else 0 := by
    intro n; simp only [shiftedL1, l1Weighted.mk_apply, shiftedSeq]
    split_ifs <;> simp [abs_zero]
  simp_rw [h_eq]; rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl; intro n hn; simp [hn]
  · intro n hn; simp [hn]

/-- On tail modes n > N, the difference A†-DF acts as -2·leftMul(shiftedL1).
The tail diagonal of A† gives 2ā₀·h_n, while DF gives 2·CauchyProduct(ā,h)_n.
Since ā has support [0,N] and n > N, the Cauchy product splits as
ā₀·h_n + ∑_{k∈[1,N]} ā_k·h_{n-k}, so the difference is -2·∑_{k∈[1,N]} ā_k·h_{n-k}. -/
lemma approxDeriv_sub_fderiv_tail_eq {N : ℕ}
    (sol : ApproxSolution N) (lam0 : ℝ) (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (((approxDeriv sol).toScalarCLM (ν := ν) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν)) h) n =
    -(2 : ℝ) * l1Weighted.toSeq ((shiftedL1 sol : l1Weighted ν) * h) n := by
  have hsup : ∀ k, N < k → sol.toSeq k = 0 := fun k hk => sol.toSeq_zero_of_gt k hk
  have hShifted_sup : ∀ k, N < k → shiftedSeq sol k = 0 := by
    intro k hk
    simp only [shiftedSeq, Finset.mem_Icc, if_neg (show ¬(1 ≤ k ∧ k ≤ N) from by omega)]
  have hShifted0 : shiftedSeq sol 0 = 0 := by
    simp only [shiftedSeq, Finset.mem_Icc, if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ N) from by omega)]
  have hShifted_in : ∀ k ∈ Finset.Icc 1 N, shiftedSeq sol k = sol.toSeq k := by
    intro k hk
    simp only [shiftedSeq, if_pos hk]
  have hToSeq0_eq : sol.toSeq 0 = sol.aBar_fin 0 := by
    have := sol.toSeq_eq_fin ⟨0, Nat.succ_pos N⟩
    simpa using this
  have htail : (approxDeriv sol).tailDiag0 n = 2 * sol.aBar_fin 0 := rfl
  rw [sub_apply, l1Weighted.sub_toSeq, fderiv_F,
    (approxDeriv sol).toScalarCLM_toSeq_tail h n hn, htail,
    smul_apply, leftMul_apply, l1Weighted.smul_toSeq,
    l1Weighted.toSeq_mul, ApproxSolution.toL1_toSeq,
    CauchyProduct.apply_of_support_le_split hsup hn, ← hToSeq0_eq]
  -- RHS expansion
  show _ = -(2 : ℝ) * l1Weighted.toSeq ((shiftedL1 sol : l1Weighted ν) * h) n
  rw [l1Weighted.toSeq_mul]
  show _ = -(2 : ℝ) * CauchyProduct (shiftedSeq sol) (l1Weighted.toSeq h) n
  rw [CauchyProduct.apply_of_support_le_split hShifted_sup hn, hShifted0]
  have hSumEq : ∑ k ∈ Finset.Icc 1 N, shiftedSeq sol k * l1Weighted.toSeq h (n - k)
      = ∑ k ∈ Finset.Icc 1 N, sol.toSeq k * l1Weighted.toSeq h (n - k) :=
    Finset.sum_congr rfl (fun k hk => by rw [hShifted_in k hk])
  rw [hSumEq]
  ring

/-- **Z₁ pipeline**: Uses `Z₁_le_of_fin_kill_tail_dom` (general API) with
E = -2•leftMul(shiftedL1) as the dominating operator. Certificate provides C. -/
lemma Z₁_le_via_eval {N : ℕ} {ν : PosReal}
    (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam0 : ℝ)
    (C : ℝ)
    (hbound : (approxInverse sol A_mat).tailBound *
      (2 * ∑ m ∈ Finset.Icc 1 N, |sol.toSeq m| * (ν : ℝ) ^ m) ≤ C) :
    ‖((approxInverse sol A_mat).toScalarCLM (ν := ν)).comp
      ((approxDeriv sol).toScalarCLM (ν := ν) -
        fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν))‖ ≤ C :=
  ScalarBlockDiagData.Z₁_le_of_fin_kill_tail_dom N (approxInverse sol A_mat)
    _ ((-2 : ℝ) • leftMul (shiftedL1 sol))
    (fun h n hn => approxDeriv_sub_fderiv_fin_kill sol lam0 h n hn)
    (fun h n hn => by
      rw [approxDeriv_sub_fderiv_tail_eq sol lam0 h n hn]; simp; rfl)
    C (hbound.trans' (mul_le_mul_of_nonneg_left
      ((norm_smul (-2 : ℝ) (leftMul (shiftedL1 sol : l1Weighted ν)) ▸ by
        rw [norm_neg, Real.norm_ofNat]
        exact mul_le_mul_of_nonneg_left
          ((norm_leftMul_le _).trans_eq (shiftedL1_norm sol)) (by positivity)))
      (approxInverse sol A_mat).tailBound_nonneg))

/-! ### Z₂: via `Z₂_ball_bound_of_affine_leftMul` from Z2Affine.lean

The fderiv of F is affine in `leftMul` with α = 2, K = 0, so the generic
`Z₂_ball_bound_of_affine_leftMul` gives `Z₂_norm ≤ |2| * ‖A‖ * r₀ = 2 * ‖A‖ * r₀`. -/

lemma Z₂_ball_bound {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (lam0 : ℝ) (r₀ : ℝ) (Z₂_val : ℝ)
    (hA : 2 * ‖(approxInverse sol A_mat).toScalarCLM (ν := ν)‖ ≤ Z₂_val)
    (c_val : l1Weighted ν)
    (hc : c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀) :
    Z₂_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν)) c_val ≤
    Z₂_val * r₀ := by
  have h := Z₂_ball_bound_of_affine_leftMul (f := F lam0) (fderiv_F_sub_const_affine _)
    ((approxInverse sol A_mat).toScalarCLM (ν := ν)) sol.toL1 c_val hc
  simp only [abs_two] at h
  exact h.trans (mul_le_mul_of_nonneg_right hA
    (le_trans dist_nonneg (Metric.mem_closedBall.mp hc)))

/-! ### Main theorem skeleton -/

/-- Generic existence/uniqueness for Example 7.7 via `general_radii_polynomial_theorem`. -/
theorem existsUnique {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (lam0 : ℝ) {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν)) ≤ Y₀)
    (hZ₀ : Z₀_norm ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤ Z₀)
    (hZ₁ : Z₁_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      Z₂_norm (F lam0) sol.toL1
        ((approxInverse sol A_mat).toScalarCLM (ν := ν)) c_val ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (h_inj : Function.Injective
      ((approxInverse sol A_mat).toScalarCLM (ν := ν))) :
    ∃! xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 xTilde = 0 :=
  general_radii_polynomial_theorem
    hr₀ hY₀ hZ₀ hZ₁ hZ₂ (differentiable_F lam0) h_radii h_inj

end Example77
