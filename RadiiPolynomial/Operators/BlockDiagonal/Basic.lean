import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Scalar
import RadiiPolynomial.Analysis.Norm.FiniteSum
import RadiiPolynomial.Operators.Matrix.WeightedNorm
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Block-diagonal operator data (coefficient level)

Core structural layer for Section 8.2 operators:
- finite `L×L` block norm aggregation
- `FiniteBlockMatrix.toMatrix`: flatten block structure to single matrix on `Fin L × Fin (N+1)`
- `BlockDiagOp`: lightweight (finBlock + tailDiag, no tailBound) for unbounded operators (e.g. IVP A†)
- `SystemBlockDiagData`: full (+ tailBound) for bounded operators (A, defect)
- coefficient-level block-diagonal data and composition
-/

open scoped Topology Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

/-! ## 1. Finite Block-Matrix Norm Aggregation -/

section FiniteBlockNorm

variable {ν : PosReal} {L N : ℕ}

/-- Finite-dimensional `L × L` block matrix.
Each entry is an `(N+1)×(N+1)` real matrix acting on one component. -/
abbrev FiniteBlockMatrix (L N : ℕ) :=
  Fin L → Fin L → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ

/-- Norm of one block entry `(l,j)` in the weighted finite norm. -/
def blockEntryNorm (ν : PosReal) (A : FiniteBlockMatrix L N)
    (l j : Fin L) : ℝ :=
  FiniteWeightedNorm.finWeightedMatrixNorm ν (A l j)

/-- Row aggregation for system coupling:
`rowNorm l = ∑_j ‖A_{l,j}‖`. -/
def blockRowNorm (ν : PosReal) (A : FiniteBlockMatrix L N) (l : Fin L) : ℝ :=
  ∑ j : Fin L, blockEntryNorm ν A l j

/-- System finite block-matrix norm:
`max_l ∑_j ‖A_{l,j}‖`.

This is the natural aggregation for product-space estimates with component coupling
in Section 8.2. -/
def finiteBlockMatrixNorm [NeZero L] (ν : PosReal) (A : FiniteBlockMatrix L N) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun l => blockRowNorm ν A l)

lemma blockEntryNorm_nonneg (A : FiniteBlockMatrix L N) (l j : Fin L) :
    0 ≤ blockEntryNorm ν A l j :=
  FiniteWeightedNorm.finWeightedMatrixNorm_nonneg (ν := ν) (A l j)

lemma blockRowNorm_nonneg (A : FiniteBlockMatrix L N) (l : Fin L) :
    0 ≤ blockRowNorm ν A l := by
  unfold blockRowNorm
  exact Finset.sum_nonneg (fun j _ => blockEntryNorm_nonneg (ν := ν) A l j)

lemma finiteBlockMatrixNorm_nonneg [NeZero L] (A : FiniteBlockMatrix L N) :
    0 ≤ finiteBlockMatrixNorm ν A := by
  unfold finiteBlockMatrixNorm
  exact Finset.le_sup'_of_le (fun l : Fin L => blockRowNorm ν A l) (Finset.mem_univ 0)
    (blockRowNorm_nonneg (ν := ν) A 0)

lemma finiteBlockMatrixNorm_le_of_blockRowNorm_le
    [NeZero L] (A : FiniteBlockMatrix L N) (C : ℝ)
    (hrow : ∀ l : Fin L, blockRowNorm ν A l ≤ C) :
    finiteBlockMatrixNorm ν A ≤ C :=
  Finset.sup'_le _ _ fun l _ => hrow l

end FiniteBlockNorm

/-! ## 1b. Flattened Matrix API for Finite Block Matrices -/

section FiniteBlockMatrix

variable {L N : ℕ}

/-- Flatten an `L × L` system of `(N+1)×(N+1)` blocks into a single matrix
on `Fin L × Fin (N+1)`. -/
def FiniteBlockMatrix.toMatrix (A : FiniteBlockMatrix L N) :
    Matrix (Fin L × Fin (N + 1)) (Fin L × Fin (N + 1)) ℝ :=
  fun ⟨l, n⟩ ⟨j, k⟩ => A l j n k

@[simp] lemma FiniteBlockMatrix.toMatrix_apply (A : FiniteBlockMatrix L N)
    (l j : Fin L) (n k : Fin (N + 1)) :
    A.toMatrix (l, n) (j, k) = A l j n k := rfl

/-- The flattening is Mathlib's `Matrix.comp` (definitionally). -/
lemma FiniteBlockMatrix.toMatrix_eq_comp (A : FiniteBlockMatrix L N) :
    A.toMatrix = Matrix.comp (Fin L) (Fin L) (Fin (N + 1)) (Fin (N + 1)) ℝ A := rfl

/-- Block identity flattens to matrix identity (`Matrix.comp_one`). -/
lemma FiniteBlockMatrix.toMatrix_blockId :
    FiniteBlockMatrix.toMatrix
      (fun l j => if l = j then (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) else 0 :
        FiniteBlockMatrix L N) = 1 :=
  Matrix.comp_one

/-- Block-matrix product flattens to matrix product (`Matrix.compRingEquiv`). -/
lemma FiniteBlockMatrix.toMatrix_blockMul (A B : FiniteBlockMatrix L N) :
    FiniteBlockMatrix.toMatrix
      (fun l j => ∑ m : Fin L, A l m * B m j : FiniteBlockMatrix L N) =
    A.toMatrix * B.toMatrix :=
  (Matrix.compRingEquiv (Fin L) (Fin (N + 1)) ℝ).map_mul (Matrix.of A) (Matrix.of B)

end FiniteBlockMatrix

/-! ## 2. Coefficient-Level Block-Diagonal Data -/

section SystemBlockDiagData

variable {L N : ℕ}

/-- Coefficient representation of an `L`-component sequence object. -/
abbrev SystemCoeff (L : ℕ) := Fin L → ℕ → ℝ

/-- Extensionality for `SystemCoeff` by finite/tail mode split at cutoff `N`. -/
lemma SystemCoeff.ext_by_modes {f g : SystemCoeff L} {N : ℕ}
    (hfin : ∀ l n, n ≤ N → f l n = g l n)
    (htail : ∀ l n, N < n → f l n = g l n) : f = g :=
  funext fun l => funext fun n =>
    if hn : n ≤ N then hfin l n hn else htail l n (Nat.lt_of_not_ge hn)

/-- Lightweight block-diagonal operator data (no tail bound requirement).
Used for operators like A† in the IVP case where the tail diagonal `k·δ_{j,j'}`
is unbounded. Carries only the algebraic data needed for composition and
defect computation. -/
structure BlockDiagOp (L N : ℕ) where
  /-- Finite coupled block matrix (`L×L` blocks, each `(N+1)×(N+1)`). -/
  finBlock : FiniteBlockMatrix L N
  /-- Tail diagonal by component and mode. -/
  tailDiag : Fin L → ℕ → ℝ

/-- 8.2-style block operator data for Eq. (8.21):
- finite coupled `L×L` block on modes `0..N` (`A_N π_N`)
- componentwise diagonal tail on modes `N+1..∞` (`A_∞ π_{N,∞}`). -/
structure SystemBlockDiagData (L N : ℕ) where
  /-- Finite coupled block matrix (`L×L` blocks, each `(N+1)×(N+1)`). -/
  finBlock : FiniteBlockMatrix L N
  /-- Tail diagonal by component and mode. -/
  tailDiag : Fin L → ℕ → ℝ
  /-- Uniform tail bound for all components and tail modes. -/
  tailBound : ℝ
  /-- Tail bound certificate. -/
  tailBound_spec : ∀ l n, N < n → |tailDiag l n| ≤ tailBound

/-- Forget the tail bound, keeping only algebraic data. -/
def SystemBlockDiagData.toBlockDiagOp (A : SystemBlockDiagData L N) : BlockDiagOp L N :=
  ⟨A.finBlock, A.tailDiag⟩

instance : Coe (SystemBlockDiagData L N) (BlockDiagOp L N) :=
  ⟨SystemBlockDiagData.toBlockDiagOp⟩

@[simp] lemma SystemBlockDiagData.toBlockDiagOp_finBlock (A : SystemBlockDiagData L N) :
    (A : BlockDiagOp L N).finBlock = A.finBlock := rfl

@[simp] lemma SystemBlockDiagData.toBlockDiagOp_tailDiag (A : SystemBlockDiagData L N) :
    (A : BlockDiagOp L N).tailDiag = A.tailDiag := rfl

/-- Core finite block-matrix action at a single `Fin (N+1)` mode — no conditional.
The double sum `∑_j ∑_k A_{l,j,n,k} · b_{j,k}` that `actionFinite` wraps with
an `if n ≤ N` guard. -/
def finBlockAction (finBlock : FiniteBlockMatrix L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) : ℝ :=
  ∑ j : Fin L, ∑ k : Fin (N + 1), finBlock l j n k * b j k

/-- Finite-mode part (`A_N π_N b`) at coefficient level. -/
def SystemBlockDiagData.actionFinite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n =>
    if hn : n ≤ N then finBlockAction A.finBlock b l ⟨n, Nat.lt_succ_of_le hn⟩
    else 0

/-- Tail part (`A_∞ π_{N,∞} b`) at coefficient level. -/
def SystemBlockDiagData.actionTail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n =>
    if n ≤ N then
      0
    else
      A.tailDiag l n * b l n

lemma finBlockAction_add (finBlock : FiniteBlockMatrix L N)
    (c d : SystemCoeff L) (l : Fin L) (n : Fin (N + 1)) :
    finBlockAction finBlock (fun i k => c i k + d i k) l n =
      finBlockAction finBlock c l n + finBlockAction finBlock d l n := by
  simp only [finBlockAction]; simp_rw [mul_add, Finset.sum_add_distrib]

lemma finBlockAction_smul (finBlock : FiniteBlockMatrix L N)
    (r : ℝ) (c : SystemCoeff L) (l : Fin L) (n : Fin (N + 1)) :
    finBlockAction finBlock (fun i k => r * c i k) l n =
      r * finBlockAction finBlock c l n := by
  simp only [finBlockAction]
  rw [Finset.mul_sum]; congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext k; ring

lemma finBlockAction_eq_zero_of_coeff_zero (finBlock : FiniteBlockMatrix L N)
    (c : SystemCoeff L) (hc : ∀ j : Fin L, ∀ k : Fin (N + 1), c j k = 0)
    (l : Fin L) (n : Fin (N + 1)) :
    finBlockAction finBlock c l n = 0 :=
  Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by rw [hc j k, mul_zero]

/-- Full 8.2-style action `Ab = A_N π_N b + A_∞ π_{N,∞} b`. -/
def SystemBlockDiagData.action
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n => A.actionFinite b l n + A.actionTail b l n

@[simp]
lemma SystemBlockDiagData.actionFinite_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.actionFinite b l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b j k := by
  simp [SystemBlockDiagData.actionFinite, finBlockAction, hn]

@[simp] lemma finBlockAction_unfold (finBlock : FiniteBlockMatrix L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) :
    finBlockAction finBlock b l n = ∑ j : Fin L, ∑ k : Fin (N + 1), finBlock l j n k * b j k :=
  rfl

@[simp]
lemma SystemBlockDiagData.actionFinite_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.actionFinite b l n = 0 := by
  simp [SystemBlockDiagData.actionFinite, Nat.not_le.mpr hn]

lemma SystemBlockDiagData.actionFinite_eq_zero_of_coeff_fin_zero
    (A : SystemBlockDiagData L N) (c : SystemCoeff L)
    (hc : ∀ j : Fin L, ∀ k : Fin (N + 1), c j k = 0) :
    ∀ l n, A.actionFinite c l n = 0 := by
  intro l n; simp only [SystemBlockDiagData.actionFinite]; split
  · exact finBlockAction_eq_zero_of_coeff_zero _ _ hc _ _
  · rfl

@[simp]
lemma SystemBlockDiagData.actionTail_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.actionTail b l n = 0 := by
  simp [SystemBlockDiagData.actionTail, hn]

@[simp]
lemma SystemBlockDiagData.actionTail_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.actionTail b l n = A.tailDiag l n * b l n := by
  simp [SystemBlockDiagData.actionTail, Nat.not_le.mpr hn]

@[simp]
lemma SystemBlockDiagData.action_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.action b l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b j k := by
  simp [SystemBlockDiagData.action, hn, SystemBlockDiagData.actionFinite]

@[simp]
lemma SystemBlockDiagData.action_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action b l n = A.tailDiag l n * b l n := by
  simp [SystemBlockDiagData.action, Nat.not_le.mpr hn,
    SystemBlockDiagData.actionFinite, SystemBlockDiagData.actionTail]

@[simp]
lemma SystemBlockDiagData.action_fin
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) :
    A.action b l n = ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * b j k := by
  simp [SystemBlockDiagData.action, SystemBlockDiagData.actionFinite, Fin.is_le]

/-! ### mulVec bridge for finite-mode action

Expresses the finite-mode block action via `Matrix.mulVec`: per block, and through the
flattening `FiniteBlockMatrix.toMatrix`, where block-matrix associativity is Mathlib's
`Matrix.mulVec_mulVec`. -/

/-- Finite-mode action as sum of per-block `mulVec`.
`A.action b l n = ∑_j (A.finBlock l j *ᵥ b_j) n` for `n ≤ N`. -/
lemma SystemBlockDiagData.action_fin_eq_sum_mulVec
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) :
    A.action b l n = ∑ j : Fin L, (A.finBlock l j).mulVec (fun k => b j k) n := by
  simp [SystemBlockDiagData.action_fin, Matrix.mulVec, dotProduct]

/-- The finite-mode action is the flattened matrix `A.finBlock.toMatrix` acting on the
flattened coefficient vector `(j, k) ↦ b j k`. -/
lemma SystemBlockDiagData.action_fin_eq_toMatrix_mulVec
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) :
    A.action b l n =
      (A.finBlock.toMatrix *ᵥ fun p : Fin L × Fin (N + 1) => b p.1 p.2) (l, n) := by
  simp [SystemBlockDiagData.action_fin, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-! ### Coefficient-level decomposition and composition helpers -/

/-- Split form of the coefficient action into finite and tail parts. -/
lemma SystemBlockDiagData.action_eq_actionFinite_add_actionTail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) :
    A.action b = fun l n => A.actionFinite b l n + A.actionTail b l n := rfl

/-- `actionFinite` at a finite mode is differentiable when each coefficient `b(a) j k`
is differentiable. Reduces to `Differentiable.fun_sum` of `const * differentiable`. -/
lemma SystemBlockDiagData.differentiable_actionFinite {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : SystemBlockDiagData L N) (b : E → SystemCoeff L)
    (hb : ∀ j : Fin L, ∀ k : Fin (N + 1), Differentiable ℝ (fun a => b a j k))
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    Differentiable ℝ (fun a => A.actionFinite (b a) l n) := by
  simp_rw [show ∀ a, A.actionFinite (b a) l n =
    ∑ j, ∑ k, A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b a j k
    from fun a => A.actionFinite_finite (b a) l n hn]
  apply Differentiable.fun_sum; intro j _; apply Differentiable.fun_sum; intro k _
  exact (differentiable_const _).mul (hb j k)

/-- `action` at a finite mode is differentiable (actionTail vanishes for n ≤ N). -/
lemma SystemBlockDiagData.differentiable_action_fin {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : SystemBlockDiagData L N) (b : E → SystemCoeff L)
    (hb : ∀ j : Fin L, ∀ k : Fin (N + 1), Differentiable ℝ (fun a => b a j k))
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    Differentiable ℝ (fun a => A.action (b a) l n) := by
  have : (fun a => A.action (b a) l n) = (fun a => A.actionFinite (b a) l n) := by
    ext a; simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
      SystemBlockDiagData.actionTail_finite _ _ _ _ hn]
  rw [this]; exact A.differentiable_actionFinite b hb l n hn

/-- Fderiv of the action at a finite mode: linear in the coefficient fderiv.
When `b(a)` is a differentiable family of coefficients and `n ≤ N`, the fderiv of
`a ↦ A.action(b a) l n` equals `A.action` applied to the pointwise fderivs. -/
lemma SystemBlockDiagData.fderiv_action_fin {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : SystemBlockDiagData L N) (b : E → SystemCoeff L)
    (hb : ∀ j : Fin L, ∀ k : Fin (N + 1), Differentiable ℝ (fun a => b a j k))
    (l : Fin L) (n : ℕ) (hn : n ≤ N) (x h : E) :
    (fderiv ℝ (fun a => A.action (b a) l n) x) h =
      A.action (fun j k => (fderiv ℝ (fun a => b a j k) x) h) l n := by
  -- action = actionFinite on finite modes
  have hact : ∀ v, A.action v l n = A.actionFinite v l n := fun v => by
    simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
      SystemBlockDiagData.actionTail_finite _ _ _ _ hn]
  have hfn : (fun a => A.action (b a) l n) = fun a =>
      ∑ j, ∑ k : Fin (N + 1),
        A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b a j k :=
    funext fun a => (hact (b a)).trans (A.actionFinite_finite (b a) l n hn)
  -- HasFDerivAt via sum of const*differentiable
  have hfderiv : HasFDerivAt (fun a => A.action (b a) l n)
      (∑ j : Fin L, ∑ k : Fin (N + 1),
        A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k •
          fderiv ℝ (fun a => b a j k) x) x := by
    rw [hfn]
    have := HasFDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
      HasFDerivAt.sum fun k (_ : k ∈ Finset.univ) =>
        (hb j k x).hasFDerivAt.const_mul
          (A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k)
    have hsum :
        (fun a =>
          ∑ j : Fin L, ∑ k : Fin (N + 1),
            A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b a j k) =
          (∑ j : Fin L, ∑ k : Fin (N + 1),
            fun a => A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b a j k) := by
      funext a
      simp [Finset.sum_apply]
    rw [hsum]
    exact this
  rw [hfderiv.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  symm; exact (hact _).trans (A.actionFinite_finite _ l n hn)

/-- Pointwise nonnegativity witness for the uniform tail bound. -/
lemma SystemBlockDiagData.tailBound_nonneg_at
    (A : SystemBlockDiagData L N) (l : Fin L) :
    0 ≤ A.tailBound := by
  exact le_trans (abs_nonneg (A.tailDiag l (N + 1)))
    (A.tailBound_spec l (N + 1) (by omega))

/-- Coefficient-level composition of 8.2 block operators. -/
def SystemBlockDiagData.comp
    (A B : SystemBlockDiagData L N) : SystemBlockDiagData L N where
  finBlock := fun l i => ∑ j : Fin L, A.finBlock l j * B.finBlock j i
  tailDiag := fun l n => A.tailDiag l n * B.tailDiag l n
  tailBound := A.tailBound * B.tailBound
  tailBound_spec := by
    intro l n hn
    have hA0 : 0 ≤ A.tailBound := A.tailBound_nonneg_at l
    rw [abs_mul]
    exact mul_le_mul (A.tailBound_spec l n hn) (B.tailBound_spec l n hn)
      (abs_nonneg (B.tailDiag l n)) hA0

@[simp]
lemma SystemBlockDiagData.comp_finBlock
    (A B : SystemBlockDiagData L N) (l i : Fin L) :
    (A.comp B).finBlock l i = ∑ j : Fin L, A.finBlock l j * B.finBlock j i := rfl

@[simp]
lemma SystemBlockDiagData.comp_tailDiag
    (A B : SystemBlockDiagData L N) (l : Fin L) (n : ℕ) :
    (A.comp B).tailDiag l n = A.tailDiag l n * B.tailDiag l n := rfl

/-- The flattened finite block of a composition is the product of the flattened finite
blocks (`FiniteBlockMatrix.toMatrix_blockMul`). -/
lemma SystemBlockDiagData.comp_finBlock_toMatrix (A B : SystemBlockDiagData L N) :
    (A.comp B).finBlock.toMatrix = A.finBlock.toMatrix * B.finBlock.toMatrix :=
  FiniteBlockMatrix.toMatrix_blockMul A.finBlock B.finBlock

/-! ### Composition at coefficient level -/

/-! The next lemmas isolate finite-mode and tail-mode formulas for
composition before assembling the global identity. -/

/-- Finite-mode expansion of `A.action (B.action b)` for `n ≤ N`. -/
lemma SystemBlockDiagData.action_comp_finite
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.action (B.action b) l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1),
        A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * (B.action b j k) := by
  rw [SystemBlockDiagData.action_finite (A := A) (b := B.action b) (l := l) (n := n) hn]

/-- Tail-mode expansion of `A.action (B.action b)` for `N < n`. -/
lemma SystemBlockDiagData.action_comp_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action (B.action b) l n =
      (A.tailDiag l n * B.tailDiag l n) * b l n := by
  rw [SystemBlockDiagData.action_tail (A := A) (b := B.action b) (l := l) (n := n) hn]
  rw [SystemBlockDiagData.action_tail (A := B) (b := b) (l := l) (n := n) hn]
  ring

/-- Tail-mode formula for `(A.comp B).action`. -/
lemma SystemBlockDiagData.comp_action_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    (A.comp B).action b l n =
      (A.tailDiag l n * B.tailDiag l n) * b l n := by
  rw [SystemBlockDiagData.action_tail (A := A.comp B) (b := b) (l := l) (n := n) hn]
  simp [SystemBlockDiagData.comp, mul_assoc]

/-- Finite-mode compatibility for composition:
`(A.comp B).action = A.action ∘ B.action` on `n ≤ N`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp_finite
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    (A.comp B).action b l n = A.action (B.action b) l n := by
  set n' : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hB : (fun p : Fin L × Fin (N + 1) => B.action b p.1 p.2) =
      B.finBlock.toMatrix *ᵥ fun p => b p.1 p.2 :=
    funext fun p => B.action_fin_eq_toMatrix_mulVec b p.1 p.2
  rw [(A.comp B).action_fin_eq_toMatrix_mulVec b l n',
    A.action_fin_eq_toMatrix_mulVec (B.action b) l n', hB, A.comp_finBlock_toMatrix B,
    Matrix.mulVec_mulVec]

/-- Tail-mode compatibility for composition:
`(A.comp B).action = A.action ∘ B.action` on `N < n`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    (A.comp B).action b l n = A.action (B.action b) l n := by
  rw [SystemBlockDiagData.comp_action_tail (A := A) (B := B) (b := b) (l := l) (n := n) hn]
  rw [SystemBlockDiagData.action_comp_tail (A := A) (B := B) (b := b) (l := l) (n := n) hn]

/-- Full coefficient-level composition identity:
`(A.comp B).action = A.action ∘ B.action`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L) :
    (A.comp B).action b = A.action (B.action b) :=
  SystemCoeff.ext_by_modes
    (fun l n hn => A.comp_action_eq_action_comp_finite B b l n hn)
    (fun l n hn => A.comp_action_eq_action_comp_tail B b l n hn)

end SystemBlockDiagData

end RadiiPolynomial
