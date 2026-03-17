import RadiiPolynomial.source.BlockDiag.Concrete

/-!
# BlockDiagSystem Scalar

`L = 1` convenience layer on top of `SystemBlockDiagData`:
- scalar accessors and constructors
- scalar/operator injectivity transfer lemmas
- scalar coefficient API for `toScalarCLM`
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

/-! ## 7. Scalar (`L = 1`) Convenience Layer

This specialization exposes the `SystemBlockDiagData` API in a scalar shape.
It keeps the same underlying system operator, but removes `Fin 1` boilerplate
for the finite block and tail diagonal data.
-/

section ScalarSpecialization

variable {ν : PosReal} {N : ℕ}

/-- Scalar (`L = 1`) specialization of system block-diagonal data. -/
abbrev ScalarBlockDiagData (N : ℕ) := SystemBlockDiagData 1 N

/-- Scalar finite block accessor (`(N+1)×(N+1)` matrix). -/
def ScalarBlockDiagData.finBlock0 (A : ScalarBlockDiagData N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  A.finBlock 0 0

/-- Scalar tail diagonal accessor (`ℕ → ℝ`). -/
def ScalarBlockDiagData.tailDiag0 (A : ScalarBlockDiagData N) :
    ℕ → ℝ := fun n => A.tailDiag 0 n

/-- Build scalar data directly from one finite matrix and one tail diagonal. -/
def ScalarBlockDiagData.ofParts
    (finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (tailDiag : ℕ → ℝ)
    (tailBound : ℝ)
    (tailBound_spec : ∀ n, N < n → |tailDiag n| ≤ tailBound) :
    ScalarBlockDiagData N where
  finBlock := fun _ _ => finBlock
  tailDiag := fun _ n => tailDiag n
  tailBound := tailBound
  tailBound_spec := by
    intro _ n hn
    simpa using tailBound_spec n hn

@[simp] lemma ScalarBlockDiagData.finBlock0_ofParts
    (finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (tailDiag : ℕ → ℝ) (tailBound : ℝ)
    (tailBound_spec : ∀ n, N < n → |tailDiag n| ≤ tailBound) :
    (ScalarBlockDiagData.ofParts (N := N) finBlock tailDiag tailBound tailBound_spec).finBlock0 = finBlock := rfl

@[simp] lemma ScalarBlockDiagData.tailDiag0_ofParts
    (finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (tailDiag : ℕ → ℝ) (tailBound : ℝ)
    (tailBound_spec : ∀ n, N < n → |tailDiag n| ≤ tailBound) (n : ℕ) :
    (ScalarBlockDiagData.ofParts (N := N) finBlock tailDiag tailBound tailBound_spec).tailDiag0 n = tailDiag n := rfl

lemma ScalarBlockDiagData.finiteBlockMatrixNorm_eq
    (A : ScalarBlockDiagData N) :
    finiteBlockMatrixNorm ν A.finBlock = FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0 := by
  unfold finiteBlockMatrixNorm blockRowNorm blockEntryNorm ScalarBlockDiagData.finBlock0
  simp

/-- Scalar-form operator norm bound:
`‖A.toCLM‖ ≤ ‖A_fin‖_{1,ν} + tailBound`. -/
lemma ScalarBlockDiagData.norm_toCLM_le
    (A : ScalarBlockDiagData N) :
    ‖A.toCLM (ν := ν)‖ ≤ FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0 + A.tailBound := by
  have := SystemBlockDiagData.norm_toCLM_le (ν := ν) (L := 1) (N := N) (A := A)
  rwa [ScalarBlockDiagData.finiteBlockMatrixNorm_eq (A := A)] at this

/-- Scalar (`L=1`) `Z₀` transfer from defect identity to the canonical norm API. -/
lemma ScalarBlockDiagData.Z₀_norm_le_of_eq_defect
    (A B D : ScalarBlockDiagData N)
    (hD : ContinuousLinearMap.id ℝ (XL1 ν 1) -
        (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) = D.toCLM (ν := ν)) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
      FiniteWeightedNorm.finWeightedMatrixNorm ν D.finBlock0 + D.tailBound := by
  have hsys :
      Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
        finiteBlockMatrixNorm ν D.finBlock + D.tailBound := by
    exact SystemBlockDiagData.Z₀_norm_le_of_eq_defect
      (ν := ν) (L := 1) (N := N) (A := A) (B := B) (D := D) hD
  have hfb : finiteBlockMatrixNorm ν D.finBlock = FiniteWeightedNorm.finWeightedMatrixNorm ν D.finBlock0 :=
    ScalarBlockDiagData.finiteBlockMatrixNorm_eq (ν := ν) (A := D)
  simpa [hfb] using hsys

/-- Identify `(ℓ¹_ν)^1` with `ℓ¹_ν` via `ContinuousLinearEquiv.funUnique`. -/
abbrev scalarSpaceEquiv (ν : PosReal) : XL1 ν 1 ≃L[ℝ] l1Weighted ν :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ (l1Weighted ν)

/-- Scalar CLM view of `ScalarBlockDiagData`. -/
def ScalarBlockDiagData.toScalarCLM (A : ScalarBlockDiagData N) :
    l1Weighted ν →L[ℝ] l1Weighted ν :=
  let e : XL1 ν 1 →L[ℝ] l1Weighted ν := (scalarSpaceEquiv ν : XL1 ν 1 →L[ℝ] l1Weighted ν)
  let eInv : l1Weighted ν →L[ℝ] XL1 ν 1 := ((scalarSpaceEquiv ν).symm : l1Weighted ν →L[ℝ] XL1 ν 1)
  e.comp ((A.toCLM (ν := ν)).comp eInv)

@[simp] lemma ScalarBlockDiagData.toScalarCLM_apply
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) :
    A.toScalarCLM (ν := ν) x = (A.toCLM (ν := ν) (fun _ => x)) 0 := by
  have hconst : (Function.const (Fin 1) x) = (fun _ => x) := rfl
  simp [ScalarBlockDiagData.toScalarCLM, scalarSpaceEquiv, hconst]

/-- Scalar injectivity criterion for the underlying `L=1` system CLM:
invertible finite block + nonvanishing tail diagonal implies injectivity. -/
lemma ScalarBlockDiagData.injective_toCLM_of_parts
    (A : ScalarBlockDiagData N)
    (h_fin : Function.Injective A.finBlock0.mulVec)
    (h_tail : ∀ n, N < n → A.tailDiag0 n ≠ 0) :
    Function.Injective (A.toCLM (ν := ν)) := by
  have h_fin_coeff :
      ∀ d : SystemCoeff 1,
        (∀ l : Fin 1, ∀ n : Fin (N + 1),
          (∑ j : Fin 1, ∑ k : Fin (N + 1), A.finBlock l j n k * d j k) = 0) →
        (∀ l : Fin 1, ∀ n : Fin (N + 1), d l n = 0) := by
    intro d hd
    let v : Fin (N + 1) → ℝ := fun k => d 0 k
    have h_mulVec : A.finBlock0.mulVec v = 0 := by
      ext n
      have hcoeff : (∑ j : Fin 1, ∑ k : Fin (N + 1), A.finBlock 0 j n k * d j k) = 0 := hd 0 n
      simpa [ScalarBlockDiagData.finBlock0, v, Matrix.mulVec, dotProduct] using hcoeff
    have hv_zero : v = 0 := by
      refine h_fin ?_
      simpa using h_mulVec.trans (Matrix.mulVec_zero A.finBlock0).symm
    intro l n
    have hl : l = 0 := Fin.eq_zero l
    subst hl
    simpa [v] using congrFun hv_zero n
  have h_tail_coeff : ∀ l n, N < n → A.tailDiag l n ≠ 0 := by
    intro l n hn
    have hl : l = 0 := Fin.eq_zero l
    subst hl
    simpa [ScalarBlockDiagData.tailDiag0] using h_tail n hn
  exact SystemBlockDiagData.injective_toCLM_of_finite_part_injective
    (ν := ν) (A := A) h_fin_coeff h_tail_coeff

/-- Scalar injectivity criterion on `l1Weighted` via `toScalarCLM`. -/
lemma ScalarBlockDiagData.injective_toScalarCLM_of_toCLM_injective
    (A : ScalarBlockDiagData N)
    (h_inj : Function.Injective (A.toCLM (ν := ν))) :
    Function.Injective (A.toScalarCLM (ν := ν)) := by
  intro x y hxy
  have hxy_sys :
      A.toCLM (ν := ν) (fun _ => x) = A.toCLM (ν := ν) (fun _ => y) := by
    funext l
    have hl : l = 0 := Fin.eq_zero l
    simpa [hl, ScalarBlockDiagData.toScalarCLM_apply] using hxy
  have hin : (fun _ => x) = (fun _ => y) := h_inj hxy_sys
  exact congrArg (fun f => f 0) hin

/-- Scalar injectivity criterion on `l1Weighted` via `toScalarCLM`. -/
lemma ScalarBlockDiagData.injective_toScalarCLM_of_parts
    (A : ScalarBlockDiagData N)
    (h_fin : Function.Injective A.finBlock0.mulVec)
    (h_tail : ∀ n, N < n → A.tailDiag0 n ≠ 0) :
    Function.Injective (A.toScalarCLM (ν := ν)) := by
  exact A.injective_toScalarCLM_of_toCLM_injective (ν := ν)
    (A.injective_toCLM_of_parts (ν := ν) h_fin h_tail)

/-- Scalar Neumann-style injectivity criterion at `toCLM` level:
if `‖I - A.finBlock0 * B‖_{1,ν} < 1` and the tail diagonal is nonzero, then
`A.toCLM` is injective. -/
lemma ScalarBlockDiagData.injective_toCLM_of_finBlock_mul_close_to_one
    (A : ScalarBlockDiagData N)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h_norm : FiniteWeightedNorm.finWeightedMatrixNorm ν (1 - A.finBlock0 * B) < 1)
    (h_tail : ∀ n, N < n → A.tailDiag0 n ≠ 0) :
    Function.Injective (A.toCLM (ν := ν)) := by
  have h_prod_unit : IsUnit (A.finBlock0 * B) :=
    FinWeightedMatrix.matrix_invertible_of_norm_lt_one
      (ν := ν) (N := N) (M := A.finBlock0 * B) h_norm
  have h_fin_unit : IsUnit A.finBlock0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at h_prod_unit ⊢
    have h_det_prod : IsUnit (A.finBlock0 * B).det := h_prod_unit
    rw [Matrix.det_mul] at h_det_prod
    exact isUnit_of_mul_isUnit_left h_det_prod
  have h_fin_inj : Function.Injective A.finBlock0.mulVec :=
    Matrix.mulVec_injective_of_isUnit h_fin_unit
  exact A.injective_toCLM_of_parts (ν := ν) h_fin_inj h_tail

/-- Scalar Neumann-style injectivity criterion:
if `‖I - A.finBlock0 * B‖_{1,ν} < 1` and the tail diagonal is nonzero, then
`A.toScalarCLM` is injective. -/
lemma ScalarBlockDiagData.injective_toScalarCLM_of_finBlock_mul_close_to_one
    (A : ScalarBlockDiagData N)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h_norm : FiniteWeightedNorm.finWeightedMatrixNorm ν (1 - A.finBlock0 * B) < 1)
    (h_tail : ∀ n, N < n → A.tailDiag0 n ≠ 0) :
    Function.Injective (A.toScalarCLM (ν := ν)) := by
  exact A.injective_toScalarCLM_of_toCLM_injective (ν := ν)
    (A.injective_toCLM_of_finBlock_mul_close_to_one (ν := ν) B h_norm h_tail)

end ScalarSpecialization

/-! ## 8. Scalar CLM API: Coefficient Access And Theorem Entry Point

This section completes the scalar (`L = 1`) API by providing:
1. Coefficient-level access for `toScalarCLM` (finite/tail decomposition)
2. Z₀ residual coefficient identities and norm bounds
3. A scalar `existsUnique` theorem entry point

These enable the abstract RadiiPolynomial API to wrap scalar problems
(like Example 7.7) without routing through equation-specific wrappers.
-/

section ScalarCLMAPI

variable {ν : PosReal} {N : ℕ}

/-! ### XL1 ν 1 norm lemmas -/

/-- For `L = 1`, the product norm equals the single component norm. -/
lemma norm_XL1_fin1 (x : XL1 ν 1) : ‖x‖ = ‖x 0‖ := by
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hx, pi_norm_const]

/-- Embedding `l1Weighted ν` as a constant function in `XL1 ν 1` preserves the norm. -/
lemma norm_const_XL1_fin1 (a : l1Weighted ν) :
    ‖(fun _ : Fin 1 => a : XL1 ν 1)‖ = ‖a‖ :=
  norm_XL1_fin1 _

/-- Helper: for `L = 1`, any `x : XL1 ν 1` equals the constant function at `x 0`. -/
lemma XL1_fin1_eq_const (x : XL1 ν 1) : x = fun _ => x 0 :=
  funext fun i => congrArg x (Fin.eq_zero i)

/-! ### Coefficient access for `toScalarCLM` -/

/-- `toCoeff` of a constant `XL1 ν 1` family reduces to the sequence of the single element. -/
lemma toCoeff_const_fin1 (x : l1Weighted ν) :
    toCoeff (ν := ν) (fun _ : Fin 1 => x : XL1 ν 1) = fun _ k => lpWeighted.toSeq x k := by
  ext l k; simp [toCoeff]

@[simp]
lemma ScalarBlockDiagData.toScalarCLM_toSeq
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n =
      A.action (fun _ k => lpWeighted.toSeq x k) 0 n := by
  rw [ScalarBlockDiagData.toScalarCLM_apply]
  change toCoeff (ν := ν) (A.toCLM (ν := ν) (fun _ => x)) 0 n = _
  rw [SystemBlockDiagData.toCoeff_toCLM, toCoeff_const_fin1]

/-- Finite-mode specialization: for `n : Fin (N + 1)`, the action is a matrix-vector product. -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_fin
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n =
      ∑ k : Fin (N + 1), A.finBlock0 n k * lpWeighted.toSeq x k := by
  rw [toScalarCLM_toSeq]
  rw [SystemBlockDiagData.action_fin]
  simp [ScalarBlockDiagData.finBlock0]

/-- Tail-mode specialization: for `N < n`, the action is diagonal. -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_tail
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n =
      A.tailDiag0 n * lpWeighted.toSeq x n := by
  rw [toScalarCLM_toSeq]
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn]
  simp [ScalarBlockDiagData.tailDiag0]

/-- When the finite block is a lower-triangular Cauchy matrix from sequence `a_seq`,
the finite-mode action of `toScalarCLM` equals the Cauchy product.
This is the structural bridge between block-diagonal operators and ℓ¹ multiplication.
General enough for any polynomial nonlinearity (Chapter 8 systems). -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_fin_eq_cauchy
    (A : ScalarBlockDiagData N) (a_seq : ℕ → ℝ)
    (hfin : ∀ i j : Fin (N + 1), A.finBlock0 i j =
      if (j : ℕ) ≤ i then a_seq ((i : ℕ) - (j : ℕ)) else 0)
    (x : l1Weighted ν) (n : ℕ) (hn : n ≤ N) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n =
    CauchyProduct a_seq (lpWeighted.toSeq x) n := by
  rw [A.toScalarCLM_toSeq_fin (ν := ν) x ⟨n, Nat.lt_succ_of_le hn⟩]
  rw [CauchyProduct.apply_range]
  -- LHS: ∑ k : Fin(N+1), (if k≤n then a(n-k) else 0) * x(k)
  -- RHS: ∑ j ∈ range(n+1), a(n-j) * x(j)
  simp_rw [hfin]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (if k ≤ n then a_seq (n - k) else 0) * lpWeighted.toSeq x k) (N + 1)]
  symm; apply Finset.sum_subset_zero_on_sdiff
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range] at hk
    simp [show ¬(k ≤ n) from by omega]
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [show k ≤ n from by omega, ↓reduceIte]

/-! ### Z₀ residual at scalar CLM level -/

/-- The scalar residual `(id - A ∘ B) x` equals the system residual at component 0. -/
lemma ScalarBlockDiagData.id_sub_comp_toScalarCLM_apply_eq
    (A B : ScalarBlockDiagData N) (x : l1Weighted ν) :
    (ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (A.toScalarCLM (ν := ν)).comp (B.toScalarCLM (ν := ν))) x =
    ((ContinuousLinearMap.id ℝ (XL1 ν 1) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν))) (fun _ => x)) 0 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.sub_apply,
    ScalarBlockDiagData.toScalarCLM_apply]
  rw [← XL1_fin1_eq_const (B.toCLM (ν := ν) (fun _ => x))]

/-- Scalar-to-system norm transfer for the residual `id - A ∘ B`. -/
lemma ScalarBlockDiagData.norm_id_sub_comp_toScalarCLM_le
    (A B : ScalarBlockDiagData N) :
    Z₀_norm (A.toScalarCLM (ν := ν)) (B.toScalarCLM (ν := ν)) ≤
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) := by
  show ‖_‖ ≤ ‖_‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [id_sub_comp_toScalarCLM_apply_eq]
  refine (norm_le_pi_norm
    ((ContinuousLinearMap.id ℝ (XL1 ν 1) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν))) (fun _ : Fin 1 => x)) 0).trans ?_
  refine (ContinuousLinearMap.le_opNorm
    (ContinuousLinearMap.id ℝ (XL1 ν 1) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)))
    (fun _ : Fin 1 => x)).trans ?_
  rw [pi_norm_const]

/-! ### Scalar operator norm bound -/

/-- Scalar operator norm bound for `toScalarCLM`:
`‖A.toScalarCLM‖ ≤ finWeightedMatrixNorm + tailBound`. -/
lemma ScalarBlockDiagData.norm_toScalarCLM_le
    (A : ScalarBlockDiagData N) :
    ‖A.toScalarCLM (ν := ν)‖ ≤
    FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0 + A.tailBound := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (FiniteWeightedNorm.finWeightedMatrixNorm_nonneg (ν := ν) A.finBlock0)
      (A.tailBound_nonneg))
  intro x
  rw [ScalarBlockDiagData.toScalarCLM_apply]
  have h1 : ‖(A.toCLM (ν := ν) (fun _ => x)) 0‖ ≤ ‖A.toCLM (ν := ν) (fun _ => x)‖ :=
    norm_le_pi_norm _ 0
  have h2 : ‖A.toCLM (ν := ν) (fun _ => x)‖ ≤
      (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0 + A.tailBound) *
        ‖(fun _ : Fin 1 => x : XL1 ν 1)‖ := by
    have := A.norm_toCLM_le (ν := ν)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  rw [pi_norm_const] at h2
  exact h1.trans h2

/-- Tail action weighted bound: the weighted tail contribution of `A.toScalarCLM x`
is bounded by `tailBound` times the weighted tail of `x`. -/
lemma ScalarBlockDiagData.tailTsum_toScalarCLM_le
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) :
    ∑' n, |lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) (n + (N + 1))| *
      (ν : ℝ) ^ (n + (N + 1)) ≤
    A.tailBound * ∑' n, |lpWeighted.toSeq x (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) := by
  have hAx_shift : Summable (fun n => |lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) (n + (N + 1))| *
      (ν : ℝ) ^ (n + (N + 1))) :=
    ((l1Weighted.mem_iff (ν := ν)
      (a := lpWeighted.toSeq (A.toScalarCLM (ν := ν) x))).mp
      (A.toScalarCLM (ν := ν) x).2).comp_injective (add_left_injective (N + 1))
  have hx_shift : Summable (fun n => |lpWeighted.toSeq x (n + (N + 1))| *
      (ν : ℝ) ^ (n + (N + 1))) :=
    ((l1Weighted.mem_iff (ν := ν)
      (a := lpWeighted.toSeq x)).mp x.2).comp_injective (add_left_injective (N + 1))
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => by
    have hn : N < n + (N + 1) := by omega
    rw [A.toScalarCLM_toSeq_tail x _ hn, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec 0 _ hn)
      (mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _)))
    hAx_shift (hx_shift.mul_left A.tailBound)

/-- Finite action weighted bound: the weighted finite contribution of `A.toScalarCLM x`
is bounded by `finWeightedMatrixNorm` times the weighted finite part of `x`. -/
lemma ScalarBlockDiagData.finRangeSum_toScalarCLM_le
    (A : ScalarBlockDiagData N) (x : l1Weighted ν) :
    ∑ n ∈ Finset.range (N + 1),
      |lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n| * (ν : ℝ) ^ n ≤
    FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0 *
      ∑ n ∈ Finset.range (N + 1), |lpWeighted.toSeq x n| * (ν : ℝ) ^ n := by
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have hrewrite : ∀ n : Fin (N + 1),
      |lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n| =
      |∑ k : Fin (N + 1), A.finBlock0 n k * lpWeighted.toSeq x k| := by
    intro n
    rw [show lpWeighted.toSeq (A.toScalarCLM (ν := ν) x) n =
        ∑ k : Fin (N + 1), A.finBlock0 n k * lpWeighted.toSeq x k from
      A.toScalarCLM_toSeq_fin (ν := ν) x n]
  simp_rw [hrewrite]
  simpa [FiniteWeightedNorm.finl1WeightedNorm, Matrix.mulVec, dotProduct] using
    FiniteWeightedNorm.finWeightedMatrixNorm_mulVec_le (ν := ν) A.finBlock0 (fun k => lpWeighted.toSeq x k)

/-- Tighter scalar operator norm bound using `max` instead of `+`.
For block-diagonal operators on `ℓ¹_ν`, the operator norm is the max of column norms
over all columns (Exercise 2.7.2). Finite columns give `finWeightedMatrixNorm`,
tail columns give at most `tailBound`. -/
lemma ScalarBlockDiagData.norm_toScalarCLM_le_max
    (A : ScalarBlockDiagData N) :
    ‖A.toScalarCLM (ν := ν)‖ ≤
    max (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_max_of_le_left (FiniteWeightedNorm.finWeightedMatrixNorm_nonneg (ν := ν) A.finBlock0))
  intro x
  set C := max (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound
  -- Split ‖Ax‖ and ‖x‖ into finite + tail parts
  rw [l1Weighted.norm_eq_finRangeSum_add_tailTsum (A.toScalarCLM (ν := ν) x) (N + 1),
      l1Weighted.norm_eq_finRangeSum_add_tailTsum x (N + 1)]
  -- Use the finite and tail action bounds
  have h_fin := A.finRangeSum_toScalarCLM_le (ν := ν) x
  have h_tail := A.tailTsum_toScalarCLM_le (ν := ν) x
  have hf_fin_nn : 0 ≤ ∑ n ∈ Finset.range (N + 1), |lpWeighted.toSeq x n| * (ν : ℝ) ^ n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _))
  have hf_tail_nn : 0 ≤ ∑' n, |lpWeighted.toSeq x (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) :=
    tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _))
  linarith [le_max_left (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound,
            le_max_right (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound,
            mul_le_mul_of_nonneg_right (le_max_left (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound) hf_fin_nn,
            mul_le_mul_of_nonneg_right (le_max_right (FiniteWeightedNorm.finWeightedMatrixNorm ν A.finBlock0) A.tailBound) hf_tail_nn]

/-! ### Z₁ infrastructure: composition norm when inner operator kills finite modes

Three APIs for Z₁-type bounds:
- `norm_comp_of_fin_kill`: ‖A.comp T‖ ≤ tailBound * ‖T‖ when T kills finite modes
- `opNorm_le_of_fin_kill_tail_eq`: ‖D‖ ≤ ‖E‖ when D kills finite modes and matches E on tail
- `Z₁_le_of_fin_kill_tail_dom`: full pipeline chaining both into ‖A.comp T‖ ≤ C
-/

/-- Composition norm bound when the inner operator T kills finite modes.
If `T(h)[n] = 0` for all `n ≤ N`, then `A.toScalarCLM` acts on `T(h)` purely
via its tail diagonal, giving `‖A.comp T‖ ≤ A.tailBound * ‖T‖`. -/
lemma ScalarBlockDiagData.norm_comp_of_fin_kill
    (A : ScalarBlockDiagData N) (T : l1Weighted ν →L[ℝ] l1Weighted ν)
    (hfin : ∀ h, ∀ n, n ≤ N → lpWeighted.toSeq (T h) n = 0) :
    ‖(A.toScalarCLM (ν := ν)).comp T‖ ≤ A.tailBound * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg A.tailBound_nonneg (ContinuousLinearMap.opNorm_nonneg T))
  intro h
  show ‖A.toScalarCLM (ν := ν) (T h)‖ ≤ _
  -- Split ‖A(T(h))‖ into finite + tail
  rw [l1Weighted.norm_eq_finRangeSum_add_tailTsum (A.toScalarCLM (ν := ν) (T h)) (N + 1)]
  -- Finite part: T(h)[j] = 0 for j ≤ N, so A's finite action gives 0
  have h_fin_zero : ∑ n ∈ Finset.range (N + 1),
      |lpWeighted.toSeq (A.toScalarCLM (ν := ν) (T h)) n| * (ν : ℝ) ^ n = 0 := by
    apply Finset.sum_eq_zero; intro n hn
    rw [A.toScalarCLM_toSeq_fin (ν := ν) (T h) ⟨n, by
      simp only [Finset.mem_range] at hn; omega⟩]
    have hT_zero : ∀ k : Fin (N + 1), lpWeighted.toSeq (T h) k = 0 :=
      fun k => hfin h k (Nat.lt_succ_iff.mp k.2)
    simp_rw [hT_zero, mul_zero, Finset.sum_const_zero, abs_zero, zero_mul]
  rw [h_fin_zero, zero_add]
  -- Tail part: tailTsum ≤ tailBound * tail_of_T(h) ≤ tailBound * ‖T(h)‖ ≤ tailBound * ‖T‖ * ‖h‖
  have h_tail := A.tailTsum_toScalarCLM_le (ν := ν) (T h)
  have h_tail_le_norm : ∑' n, |lpWeighted.toSeq (T h) (n + (N + 1))| *
      (ν : ℝ) ^ (n + (N + 1)) ≤ ‖T h‖ := by
    rw [l1Weighted.norm_eq_finRangeSum_add_tailTsum (T h) (N + 1)]
    linarith [Finset.sum_nonneg (fun n (_ : n ∈ Finset.range (N + 1)) =>
      mul_nonneg (abs_nonneg (lpWeighted.toSeq (T h) n)) (pow_nonneg ν.coe_nonneg n))]
  linarith [mul_le_mul_of_nonneg_left h_tail_le_norm A.tailBound_nonneg,
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm T h) A.tailBound_nonneg]

/-! ### Z₀ defect construction (L=1 wrapper of general-L API in Concrete.lean) -/

/-- Z₀ bound for scalar pairs with tail cancellation.
Wrapper around `SystemBlockDiagData.Z₀_le_of_tailCancel`. -/
lemma ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel
    (A B : ScalarBlockDiagData N)
    (htail : ∀ n, N < n → A.tailDiag0 n * B.tailDiag0 n = 1) :
    Z₀_norm (A.toScalarCLM (ν := ν)) (B.toScalarCLM (ν := ν)) ≤
    FiniteWeightedNorm.finWeightedMatrixNorm ν (1 - A.finBlock0 * B.finBlock0) := by
  have htail_L : ∀ l : Fin 1, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1 := by
    intro l; rw [show l = 0 from Fin.eq_zero l]
    simpa [ScalarBlockDiagData.tailDiag0] using htail
  have hZ₀ := SystemBlockDiagData.Z₀_le_of_tailCancel (ν := ν) A B htail_L
  have hle := ScalarBlockDiagData.norm_id_sub_comp_toScalarCLM_le (ν := ν) A B
  refine hle.trans (hZ₀.trans ?_)
  -- finiteBlockMatrixNorm for L=1 = finWeightedMatrixNorm of the single block
  rw [show (A.defectOfTailCancel B htail_L).finBlock = fun _ _ =>
      (1 - A.finBlock0 * B.finBlock0) from by
    ext l j; simp [SystemBlockDiagData.defectOfTailCancel, ScalarBlockDiagData.finBlock0,
      show l = (0 : Fin 1) from Fin.eq_zero l, show j = (0 : Fin 1) from Fin.eq_zero j]]
  exact le_of_eq (ScalarBlockDiagData.finiteBlockMatrixNorm_eq (ν := ν)
    (A := ⟨fun _ _ => 1 - A.finBlock0 * B.finBlock0, fun _ _ => 0, 0, by intro l n _; simp⟩))

/-- Operator norm domination: if `D` kills finite modes and agrees with `E` on tail modes,
then `‖D‖ ≤ ‖E‖`. General (not scalar-specific); lives here for import reasons
(needs CLM operator norm API). Core pattern for Z₁-type bounds. -/
lemma l1Weighted.opNorm_le_of_fin_kill_tail_eq (N : ℕ)
    (D E : l1Weighted ν →L[ℝ] l1Weighted ν)
    (hfin : ∀ h, ∀ n, n ≤ N → lpWeighted.toSeq (D h) n = 0)
    (htail : ∀ h, ∀ n, N < n → lpWeighted.toSeq (D h) n = lpWeighted.toSeq (E h) n) :
    ‖D‖ ≤ ‖E‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg E)
  intro h
  rw [l1Weighted.norm_eq_tailTsum_of_fin_zero (D h) (N + 1) (fun n hn => hfin h n (by omega))]
  exact (l1Weighted.tailTsum_le_norm_of_eq (D h) (E h) (N + 1)
    (fun n hn => htail h n (by omega))).trans (ContinuousLinearMap.le_opNorm E h)

/-- Z₁ pipeline: if `T` kills finite modes and is dominated by `E` on tail,
then `‖A.comp T‖ ≤ A.tailBound * ‖E‖ ≤ C`. Equation-independent. -/
lemma ScalarBlockDiagData.Z₁_le_of_fin_kill_tail_dom (N : ℕ)
    (A : ScalarBlockDiagData N)
    (T E : l1Weighted ν →L[ℝ] l1Weighted ν)
    (hfin : ∀ h, ∀ n, n ≤ N → lpWeighted.toSeq (T h) n = 0)
    (htail : ∀ h, ∀ n, N < n → lpWeighted.toSeq (T h) n = lpWeighted.toSeq (E h) n)
    (C : ℝ) (hC : A.tailBound * ‖E‖ ≤ C) :
    ‖(A.toScalarCLM (ν := ν)).comp T‖ ≤ C :=
  (A.norm_comp_of_fin_kill T hfin).trans
    ((mul_le_mul_of_nonneg_left (l1Weighted.opNorm_le_of_fin_kill_tail_eq N T E hfin htail)
      A.tailBound_nonneg).trans hC)

end ScalarCLMAPI

end RadiiPolynomial
