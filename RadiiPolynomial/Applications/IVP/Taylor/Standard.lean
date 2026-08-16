import RadiiPolynomial.Applications.IVP.Taylor.Theorem
import RadiiPolynomial.Applications.IVP.Taylor.Jacobian

/-!
# Standard IVP Data Bundle

Packages the standard IVP numerical data (approximate inverse, approximate derivative,
approximate solution) into a single structure, with all generic constructions auto-derived.

## Architecture

Every polynomial IVP with the standard tail structure (A.tailDiag = 1/n, A†.tailDiag = n)
shares identical boilerplate for `approxInverse`, `approxDeriv`, `tailCancel`,
`htail_diag_inv`, `defect`, `composedApprox`, `abar`, `G`, `differentiable_G`, etc.

`StdIVPData` bundles the numerical arrays and auto-derives all of these in its namespace.
The user only needs to provide equation-specific data (φ, x₀, bounds).

## Usage

```lean
-- In Algebra.lean:
def data : IVP.StdIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := fun l => abar_l
  ν_q := 1
  hν := ν_val_eq_q

-- Then use: data.approxInverse, data.approxDeriv, data.tailCancel,
--           data.htail_diag_inv, data.abar, data.abar_toSeq_eq, etc.
```
-/

open scoped BigOperators Topology
open RadiiPolynomial

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- Standard IVP numerical data bundle.
Contains matrix arrays and approximate solution arrays from a numerical solver.
All standard IVP constructions are auto-derived in the `StdIVPData` namespace. -/
structure StdIVPData (ν : PosReal) (L N : ℕ) [NeZero L] where
  /-- Approximate inverse matrix columns: `A_col l j k` is column `k` of block `(l,j)`. -/
  A_col : Fin L → Fin L → ℕ → Array ℚ
  /-- Jacobian matrix columns: `DF_col l j k` is column `k` of block `(l,j)`. -/
  DF_col : Fin L → Fin L → ℕ → Array ℚ
  /-- Approximate solution coefficient arrays per component. -/
  abar_Q : Fin L → Array ℚ
  /-- Weight as ℚ (for `finsum_bound` / `native_decide`). -/
  ν_q : ℚ
  /-- Bridge: ν_val = ν_q cast to ℝ. -/
  hν : (ν : ℝ) = ((ν_q : ℚ) : ℝ)
  /-- Each abar_Q array has exactly N+1 entries. -/
  habar_size : ∀ l, (abar_Q l).size = N + 1

namespace StdIVPData

variable (d : StdIVPData ν L N)

/-! ## 1. Approximate Inverse A -/

/-- Finite block of the approximate inverse, cast from ℚ column arrays. -/
def A_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((d.A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate inverse with standard IVP tail structure:
tailDiag = 1/n, tailBound = 1/(N+1). -/
def approxInverse : SystemBlockDiagData L N where
  finBlock := d.A_finBlock
  tailDiag := fun _ n => if n = 0 then 0 else 1 / (n : ℝ)
  tailBound := 1 / ((N : ℝ) + 1)
  tailBound_spec := by
    intro _ n (hn : N < n)
    have hne : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hN1 : ((N : ℝ) + 1) ≤ n := by exact_mod_cast (show N + 1 ≤ n by omega)
    rw [if_neg hne, abs_of_pos (div_pos one_pos hpos)]
    exact one_div_le_one_div_of_le (by positivity) hN1

/-- Tail bound as ℚ. -/
abbrev approxInverse_tailBound_q : ℚ := 1 / (↑N + 1)

lemma approxInverse_tailBound_eq :
    d.approxInverse.tailBound = ((approxInverse_tailBound_q (N := N) : ℚ) : ℝ) := by
  simp [approxInverse, approxInverse_tailBound_q]

/-- Bridge: A_finBlock entries = ℚ cast of A_col data. -/
lemma A_finBlock_eq (l j : Fin L) (i k : Fin (N + 1)) :
    d.A_finBlock l j i k = ((d.A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) := rfl

/-! ## 2. Approximate Derivative A† -/

/-- Finite block of the Jacobian, cast from ℚ column arrays. -/
def DF_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((d.DF_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate derivative with standard IVP tail structure: tailDiag = n. -/
def approxDeriv : BlockDiagOp L N where
  finBlock := d.DF_finBlock
  tailDiag := fun _ n => (n : ℝ)

/-! ## 3. Structural IVP Hypotheses -/

/-- Tail cancellation: (1/n) * n = 1 for n > N. -/
lemma tailCancel (l : Fin L) (n : ℕ) (hn : N < n) :
    d.approxInverse.tailDiag l n * d.approxDeriv.tailDiag l n = 1 := by
  simp only [approxInverse, approxDeriv]
  rw [if_neg (by omega : n ≠ 0)]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- A.tailDiag = 1/n for n > N. -/
lemma htail_diag_inv (l : Fin L) (n : ℕ) (hn : N < n) :
    d.approxInverse.tailDiag l n = 1 / (↑n : ℝ) := by
  simp only [approxInverse, if_neg (by omega : n ≠ 0)]

/-- Defect D = I - A·A†. -/
def defect : SystemBlockDiagData L N :=
  defectOfBlockDiagOp d.approxInverse d.approxDeriv

/-- Composed approximate derivative A·A†. -/
def composedApprox : SystemBlockDiagData L N :=
  d.approxInverse.composedApprox d.approxDeriv d.tailCancel

/-! ## 4. Approximate Solution ābar -/

/-- ābar coefficient sequence: finite support (modes 0..N), zero beyond. -/
def abar_seq (l : Fin L) (n : ℕ) : ℝ :=
  if n ≤ N then ((d.abar_Q l).getD n 0 : ℝ) else 0

lemma abar_seq_support (l : Fin L) (n : ℕ) (hn : N < n) :
    d.abar_seq l n = 0 := by
  simp [abar_seq, show ¬(n ≤ N) from by omega]

/-- ābar toSeq = raw ℚ getD. -/
lemma abar_seq_eq_getD (l : Fin L) (k : ℕ) :
    d.abar_seq l k = ((d.abar_Q l).getD k 0 : ℝ) := by
  simp only [abar_seq]
  by_cases hk : k ≤ N
  · simp [hk]
  · simp only [show ¬(k ≤ N) from hk, ↓reduceIte]
    symm; simp only [Array.getD]
    rw [dif_neg (by rw [d.habar_size l]; omega)]; simp

/-- Approximate solution as XL1. -/
def abar : XL1 ν L := fun l =>
  l1Weighted.mk (d.abar_seq l) (by
    rw [l1Weighted.mem_iff]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) fun n hn => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp [d.abar_seq_support l n (by omega)])

/-- Bridge: toSeq(abar l) k = (abar_Q l).getD k 0. -/
lemma abar_toSeq_eq (l : Fin L) (k : ℕ) :
    l1Weighted.toSeq (d.abar l) k = ((d.abar_Q l).getD k 0 : ℝ) :=
  d.abar_seq_eq_getD l k

/-! ## 5. Composed Map G (needs φ, x₀) -/

/-- The composed IVP map G = A ∘ F. -/
def G (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ) :
    XL1 ν L → XL1 ν L :=
  ivpMap d.approxInverse φ x₀ (ivpMap_mem_of_tailDiag_inv _ _ _ d.htail_diag_inv)

lemma G_coeff (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (a : XL1 ν L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (d.G φ x₀ a l) n =
      d.approxInverse.action (ivpCoeffs φ x₀ a) l n :=
  ivpMap_coeff _ _ _ _ a l n

/-- G is differentiable (generic). -/
lemma differentiable_G (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l)) :
    Differentiable ℝ (d.G φ x₀) :=
  differentiable_ivpMap d.approxInverse φ x₀ d.htail_diag_inv _ hφ_diff

/-! ## 6. Fderiv Infrastructure (needs φ data) -/

/-- composedApprox tail: identity on modes > N. -/
lemma composedApprox_toCLM_tail (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) h l n :=
  d.approxInverse.composedApprox_toCLM_tail d.approxDeriv d.tailCancel h l n hn

/-- Fderiv of G on tail modes. -/
lemma fderiv_G_tail (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (Dφ : (Fin L → l1Weighted ν) → Fin L → l1Weighted ν)
    (hDφ : ∀ h l, Dφ h l = (fderiv ℝ (fun a => φ a l) d.abar) h)
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((fderiv ℝ (d.G φ x₀) d.abar h)) l n =
      toCoeff (ν := ν) h l n -
        toCoeff (ν := ν) (fun l => shiftDivN_CLM (Dφ h l)) l n := by
  show l1Weighted.toSeq _ n = _
  change l1Weighted.toSeq ((fderiv ℝ (ivpMap d.approxInverse φ x₀ _) d.abar h) l) n = _
  rw [fderiv_ivpMap_tail d.approxInverse φ x₀ d.htail_diag_inv _ hφ_diff d.abar h l n hn]
  rw [fderiv_ivpTail φ hφ_diff d.abar h l]
  simp only [toCoeff, l1Weighted.sub_toSeq, shiftDivN_CLM_apply]
  congr 1; congr 1
  exact congrArg shiftDivN (hDφ h l).symm

end StdIVPData

/-- composedApprox = fderiv(G) on finite modes (for StdIVPData). -/
lemma StdIVPData.composedApprox_eq_fderiv_G_fin
    {ν : PosReal} {L N : ℕ} [NeZero L]
    (d : StdIVPData ν L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (x₀ : Fin L → ℝ)
    (hφ_eq : ∀ a l, φ a l = MvPolyBridge.evalInBanach (φ_spec l) a)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (Dφ_Q : Fin L → Fin L → ℕ → ℚ)
    (hDφ_Q : ∀ j m k, l1Weighted.toSeq (MvPolyBridge.evalInBanach
      (MvPolynomial.pderiv (↑m) (φ_spec j)) d.abar) k = ((Dφ_Q j m k : ℚ) : ℝ))
    (hDF_nat : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 = ivp_DF_of_Dφ_nat Dφ_Q j m (row : ℕ) (col : ℕ))
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) ((fderiv ℝ (d.G φ x₀) d.abar) h) l n :=
  ivpComposedApprox_eq_fderiv_fin d.approxInverse d.approxDeriv φ x₀ d.tailCancel
    d.htail_diag_inv _ hφ_diff d.abar
    (ivp_hDF_block_nat d.approxDeriv φ φ_spec x₀ d.abar
      hφ_eq hφ_diff Dφ_Q hDφ_Q
      d.DF_col (fun _ _ _ _ => rfl) hDF_nat)
    h l n hn

namespace StdIVPData

variable {ν : PosReal} {L N : ℕ} [NeZero L] (d : StdIVPData ν L N)

/-! ## 7. Z₀ Bound -/

/-- Z₀ bound via generic `IVP.ivp_Z₀_le`. -/
lemma Z₀_le {Z₀ : ℝ} (hZ₀ : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀) :
    Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₀ :=
  IVP.ivp_Z₀_le d.approxInverse d.approxDeriv d.tailCancel hZ₀

/-! ## 7'. F-Zero Bridge (for the f-F bridge / `analytic_solution_unique`) -/

/-- `data.G φ x₀ a = 0` implies `ivpCoeffs φ x₀ a` is identically zero, provided the
defect's finite block has operator norm strictly less than 1. The radii polynomial's
Z₀-bound gives precisely this strict inequality (Z₀ < 1 is part of the radii polynomial
condition `generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0`).

Proof structure:
1. `G = approxInverse.action ∘ ivpCoeffs` (via `ivpMap_coeff`), so `G a = 0` gives
   `approxInverse.action (ivpCoeffs ...) l n = 0` per coefficient.
2. `approxInverse` has finite block injective (by `finite_block_injective_of_defect_norm_lt_one`)
   and tail-diagonal `1/n ≠ 0` (by `htail_diag_inv`).
3. `seq_zero_of_action_zero` upgrades action-zero to coefficient-zero. -/
lemma ivpCoeffs_zero_of_G_zero
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {a : XL1 ν L} (hG : d.G φ x₀ a = 0) :
    ∀ l n, ivpCoeffs φ x₀ a l n = 0 := by
  -- Step 1: convert XL1-zero to per-coefficient action-zero.
  have h_action : ∀ l n, d.approxInverse.action (ivpCoeffs φ x₀ a) l n = 0 := fun l n => by
    rw [← d.G_coeff φ x₀ a l n, congrFun hG l]
    rfl
  -- Step 2: apply the per-coefficient injectivity bridge.
  refine SystemBlockDiagData.seq_zero_of_action_zero d.approxInverse ?_ ?_ h_action
  · exact finite_block_injective_of_defect_norm_lt_one d.approxInverse d.approxDeriv hZ₀_lt_one
  · intro l n hn
    rw [d.htail_diag_inv l n hn]
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega))

/-- A vanishing IVP coefficient residual is sent to zero by the composed map `G`. -/
lemma G_zero_of_ivpCoeffs_zero
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    {a : XL1 ν L} (hF : ∀ l n, ivpCoeffs φ x₀ a l n = 0) :
    d.G φ x₀ a = 0 := by
  funext l
  apply l1Weighted.ext
  intro n
  change l1Weighted.toSeq (d.G φ x₀ a l) n = 0
  rw [d.G_coeff φ x₀ a l n]
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.action_finite _ _ _ _ hn]
    simp [hF]
  · rw [SystemBlockDiagData.action_tail _ _ _ _ (by omega), hF, mul_zero]

/-- The preconditioned map `G` vanishes exactly when the underlying IVP coefficient
residual vanishes, provided the finite defect certifies injectivity of the approximate
inverse. -/
lemma G_eq_zero_iff_ivpCoeffs_eq_zero
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hdefect : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {a : XL1 ν L} :
    d.G φ x₀ a = 0 ↔ ∀ l n, ivpCoeffs φ x₀ a l n = 0 :=
  ⟨d.ivpCoeffs_zero_of_G_zero φ x₀ hdefect,
    d.G_zero_of_ivpCoeffs_zero φ x₀⟩

/-- Radii-polynomial negativity makes the finite defect strictly smaller than one.
This is the injectivity fact needed to transport `G = 0` back to the source IVP
coefficient residual. -/
lemma defect_finBlockNorm_lt_one_of_radii
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤
        Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    finiteBlockMatrixNorm ν d.defect.finBlock < 1 := by
  have hY₀_nonneg : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
  have hZ₁_nonneg : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁
  have hZ₂r_nonneg : 0 ≤ Z₂ r₀ * r₀ :=
    (norm_nonneg _).trans (hZ₂ d.abar (Metric.mem_closedBall_self hr₀.le))
  have hZ_lt_one :=
    general_radii_poly_neg_implies_Z_lt_one hY₀_nonneg hr₀ h_radii
  unfold Z_bound_general at hZ_lt_one
  have hZ₀_lt_one : Z₀ < 1 := by nlinarith
  exact hZ₀fin.trans_lt hZ₀_lt_one

/-! ## 8. Main Existence/Uniqueness Skeleton -/

/-- Main existence/uniqueness theorem for standard IVP systems.
The user provides equation-specific bounds; all structural hypotheses are auto-derived. -/
theorem existsUnique
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀ : Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      d.G φ x₀ xTilde = 0 :=
  general_radii_polynomial_theorem hr₀ hY₀ hZ₀ hZ₁ hZ₂
    (d.differentiable_G φ x₀ hφ_diff) h_radii Function.injective_id

/-- Preferred existence/uniqueness theorem for standard IVP systems, stated at the
source coefficient residual rather than only at the preconditioned map `G`.

The finite `Z₀` certificate is used both for the canonical radii-polynomial bound and
for the injectivity bridge `G = 0 ↔ ivpCoeffs = 0`. -/
theorem existsUnique_ivpCoeffs
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hφ_diff : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G φ x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤
        Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      ∀ l n, ivpCoeffs φ x₀ xTilde l n = 0 := by
  have hdefect := d.defect_finBlockNorm_lt_one_of_radii φ x₀
    hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii
  rcases d.existsUnique φ x₀ hφ_diff hr₀ hY₀ (d.Z₀_le hZ₀fin)
      hZ₁ hZ₂ h_radii with ⟨xTilde, hxTilde, hunique⟩
  refine ⟨xTilde, ⟨hxTilde.1,
    (d.G_eq_zero_iff_ivpCoeffs_eq_zero φ x₀ hdefect).mp hxTilde.2⟩, ?_⟩
  intro y hy
  exact hunique y ⟨hy.1,
    (d.G_eq_zero_iff_ivpCoeffs_eq_zero φ x₀ hdefect).mpr hy.2⟩

end StdIVPData

end IVP
