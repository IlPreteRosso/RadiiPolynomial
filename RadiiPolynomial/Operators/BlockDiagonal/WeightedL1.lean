import RadiiPolynomial.Core.Bounds
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Operators.BlockDiagonal.Basic
import RadiiPolynomial.Operators.BlockDiagonal.Lift

/-!
# Block-diagonal operators on (ℓ¹_ν)^L

Concrete `l1Weighted` realization of `SystemBlockDiagData`:
- coefficient extraction/reconstruction (`toCoeff`, `ofCoeff`)
- linearity and summability helpers
- `toLinearMap` / `toCLM` with explicit norm bound (`finiteBlockMatrixNorm + tailBound`)
- residual and `Z₀` bridge lemmas (`defectOfTailCancel`, `Z₀_le_of_tailCancel`)
- `defectOfBlockDiagOp`: defect from bounded A + unbounded B (for IVP case), with the
  composed-derivative identity `defect_of_composed_toCLM_eq`
- injectivity: `injective_toCLM_of_finite_part_injective`
- system Neumann criterion: `isUnit_toMatrix_of_blockNorm_lt_one` (analogous to
  `FinWeightedMatrix.matrix_invertible_of_norm_lt_one` for the scalar case)
- `finite_block_injective_of_defect_norm_lt_one`: bridges block defect norm to
  the `h_fin` hypothesis of `injective_toCLM_of_finite_part_injective`
-/

open scoped Topology Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

/-! ## 1. Concrete `ℓ¹_ν` Realization And CLM Lift -/

section SystemBlockDiagConcrete

variable {ν : PosReal} {L N : ℕ}

/-- Concrete system space `(ℓ¹_ν)^L`. -/
abbrev XL1 (ν : PosReal) (L : ℕ) := Fin L → l1Weighted ν

/-- Extract coefficient functions from a concrete system state. -/
def toCoeff (x : XL1 ν L) : SystemCoeff L :=
  fun l n => l1Weighted.toSeq (x l) n

/-- Build a concrete system state from coefficients with per-component membership proofs. -/
def ofCoeff (c : SystemCoeff L) (hc : ∀ l : Fin L, l1Weighted.Mem ν (c l)) : XL1 ν L :=
  fun l => l1Weighted.mk (c l) (hc l)

lemma toCoeff_mem (x : XL1 ν L) (l : Fin L) :
    l1Weighted.Mem ν (toCoeff x l) := by
  change Memℓp (fun n => ScaledReal.ofReal (l1Weighted.toSeq (x l) n)) 1
  exact lp.memℓp (x l).toLp

lemma toCoeff_eq_zero {x : XL1 ν L} {j : Fin L} (h : x j = 0) (n : ℕ) :
    toCoeff (ν := ν) x j n = 0 := by
  exact (congrArg (fun y : l1Weighted ν => l1Weighted.toSeq y n) h).trans rfl

@[simp] lemma toCoeff_ofCoeff
    (c : SystemCoeff L) (hc : ∀ l : Fin L, l1Weighted.Mem ν (c l))
    (l : Fin L) (n : ℕ) :
    toCoeff (ofCoeff (ν := ν) c hc) l n = c l n := by
  simp [toCoeff, ofCoeff, l1Weighted.mk]; rfl


/-- `toCoeff` is injective: elements of `(ℓ¹_ν)^L` are determined by their coefficients. -/
lemma toCoeff_injective : Function.Injective (toCoeff (ν := ν) (L := L)) := by
  intro x y h
  funext l
  apply l1Weighted.ext
  exact fun n => congr_fun (congr_fun h l) n

/-- Extensionality for `XL1`: two elements are equal iff their coefficients agree. -/
lemma XL1.ext {x y : XL1 ν L} (h : ∀ l n, toCoeff x l n = toCoeff y l n) : x = y :=
  toCoeff_injective (funext fun l => funext fun n => h l n)

@[simp] lemma toCoeff_zero (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) (0 : XL1 ν L) l n = 0 := rfl

@[simp] lemma toCoeff_add (x y : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) (x + y) l n = toCoeff x l n + toCoeff y l n := rfl




@[simp] lemma toCoeff_smul (r : ℝ) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) (r • x) l n = r * toCoeff x l n := rfl


lemma SystemBlockDiagData.actionFinite_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) :
    l1Weighted.Mem ν (A.actionFinite c l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) fun n hn => by
    have : N < n := by simp [Finset.mem_Icc] at hn; omega
    simp [SystemBlockDiagData.actionFinite, Nat.not_le.mpr this]

/-- Pointwise weighted tail estimate used in summability/norm bounds. -/
lemma SystemBlockDiagData.tail_weighted_term_le
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) (n : ℕ) :
    |A.actionTail c l n| * (ν : ℝ) ^ n ≤
      A.tailBound * (|c l n| * (ν : ℝ) ^ n) := by
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.actionTail_finite (A := A) (b := c) (l := l) (n := n) hn]
    have hnonneg :
        0 ≤ A.tailBound * (|c l n| * (ν : ℝ) ^ n) := by
      exact mul_nonneg (A.tailBound_nonneg_at l) (FiniteWeightedNorm.weighted_term_nonneg (c l n) n)
    simpa using hnonneg
  · have hlt : N < n := Nat.lt_of_not_ge hn
    rw [SystemBlockDiagData.actionTail_tail (A := A) (b := c) (l := l) (n := n) hlt]
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec l n hlt)
      (FiniteWeightedNorm.weighted_term_nonneg (c l n) n)

/-- If a component is in `ℓ¹_ν`, its tail-transformed component is also in `ℓ¹_ν`. -/
lemma SystemBlockDiagData.actionTail_mem_of_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L)
    (hc : l1Weighted.Mem ν (c l)) :
    l1Weighted.Mem ν (A.actionTail c l) := by
  rw [l1Weighted.mem_iff] at hc ⊢
  have h_rhs : Summable (fun n => A.tailBound * (|c l n| * (ν : ℝ) ^ n)) :=
    (hc.mul_left A.tailBound)
  refine h_rhs.of_nonneg_of_le ?_ ?_
  · intro n
    exact FiniteWeightedNorm.weighted_term_nonneg (A.actionTail c l n) n
  · intro n
    exact A.tail_weighted_term_le (ν := ν) c l n

/-! ### Linearity helpers for finite/tail decomposition -/

/-- Additivity of the finite-mode action. -/
lemma SystemBlockDiagData.actionFinite_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.actionFinite (fun l n => c l n + d l n) =
      fun l n => A.actionFinite c l n + A.actionFinite d l n := by
  funext l n; simp only [SystemBlockDiagData.actionFinite]; split
  · exact finBlockAction_add _ _ _ _ _
  · simp

/-- Additivity of the tail action. -/
lemma SystemBlockDiagData.actionTail_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.actionTail (fun l n => c l n + d l n) =
      fun l n => A.actionTail c l n + A.actionTail d l n := by
  funext l n; simp only [SystemBlockDiagData.actionTail]; split <;> simp [mul_add]

/-- Homogeneity of the finite-mode action. -/
lemma SystemBlockDiagData.actionFinite_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.actionFinite (fun l n => r * c l n) =
      fun l n => r * A.actionFinite c l n := by
  funext l n; simp only [SystemBlockDiagData.actionFinite]; split
  · exact finBlockAction_smul _ _ _ _ _
  · simp

/-- Homogeneity of the tail action. -/
lemma SystemBlockDiagData.actionTail_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.actionTail (fun l n => r * c l n) =
      fun l n => r * A.actionTail c l n := by
  funext l n; simp only [SystemBlockDiagData.actionTail]; split <;> simp [mul_left_comm]

lemma SystemBlockDiagData.action_mem_of_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L)
    (hc : ∀ l : Fin L, l1Weighted.Mem ν (c l)) :
    ∀ l : Fin L, l1Weighted.Mem ν (A.action c l) := by
  intro l
  rw [l1Weighted.mem_iff]
  have hfin := (l1Weighted.mem_iff _).mp (A.actionFinite_mem (ν := ν) c l)
  have htail := (l1Weighted.mem_iff _).mp (A.actionTail_mem_of_mem (ν := ν) c l (hc l))
  exact (hfin.add htail).of_nonneg_of_le
    (fun n => FiniteWeightedNorm.weighted_term_nonneg _ n) fun n =>
    (mul_le_mul_of_nonneg_right
      (by simpa [SystemBlockDiagData.action_eq_actionFinite_add_actionTail] using
        abs_add_le (A.actionFinite c l n) (A.actionTail c l n))
      (pow_nonneg ν.coe_nonneg n)).trans_eq (add_mul _ _ _)

/-- Concrete action of `SystemBlockDiagData` on `(ℓ¹_ν)^L`. -/
def SystemBlockDiagData.applyX
    (A : SystemBlockDiagData L N) (x : XL1 ν L) : XL1 ν L :=
  ofCoeff (ν := ν) (A.action (toCoeff x))
    (A.action_mem_of_mem (ν := ν) (toCoeff x) (toCoeff_mem (ν := ν) x))

@[simp]
lemma SystemBlockDiagData.toCoeff_applyX
    (A : SystemBlockDiagData L N) (x : XL1 ν L) :
    toCoeff (A.applyX (ν := ν) x) = A.action (toCoeff x) := by
  funext l n; simp [SystemBlockDiagData.applyX, toCoeff, ofCoeff, l1Weighted.mk]; rfl

lemma SystemBlockDiagData.action_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.action (fun l n => c l n + d l n) =
      fun l n => A.action c l n + A.action d l n := by
  ext l n
  simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
    SystemBlockDiagData.actionFinite_add, SystemBlockDiagData.actionTail_add, add_assoc, add_left_comm]

lemma SystemBlockDiagData.action_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.action (fun l n => r * c l n) =
      fun l n => r * A.action c l n := by
  ext l n
  simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
    SystemBlockDiagData.actionFinite_smul, SystemBlockDiagData.actionTail_smul, left_distrib]

lemma SystemBlockDiagData.applyX_add
    (A : SystemBlockDiagData L N) (x y : XL1 ν L) :
    A.applyX (ν := ν) (x + y) = A.applyX (ν := ν) x + A.applyX (ν := ν) y :=
  XL1.ext fun l n => by
    simp only [toCoeff_applyX, toCoeff_add]
    exact congr_fun (congr_fun (A.action_add (toCoeff (ν := ν) x) (toCoeff (ν := ν) y)) l) n

lemma SystemBlockDiagData.applyX_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (x : XL1 ν L) :
    A.applyX (ν := ν) (r • x) = r • A.applyX (ν := ν) x :=
  XL1.ext fun l n => by
    simp only [toCoeff_applyX, toCoeff_smul]
    exact congr_fun (congr_fun (A.action_smul r (toCoeff (ν := ν) x)) l) n

/-- Linear-map lift of the 8.2 block operator data on `(ℓ¹_ν)^L`. -/
def SystemBlockDiagData.toLinearMap
    (A : SystemBlockDiagData L N) : XL1 ν L →ₗ[ℝ] XL1 ν L where
  toFun := A.applyX (ν := ν)
  map_add' := A.applyX_add (ν := ν)
  map_smul' := A.applyX_smul (ν := ν)

/-- Bridge `‖mk (actionFinite c l) ...‖` to expanded double-sum form. -/
lemma SystemBlockDiagData.norm_mk_actionFinite_eq
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) :
    ‖l1Weighted.mk (A.actionFinite c l)
      (A.actionFinite_mem (ν := ν) c l)‖ =
      ∑ n : Fin (N + 1),
        |finBlockAction A.finBlock c l n| * (ν : ℝ) ^ (n : ℕ) := by
  have hsupp := l1Weighted.norm_eq_Icc_sum_of_support
    (a := l1Weighted.mk (A.actionFinite c l) (A.actionFinite_mem (ν := ν) c l))
    (M := N) (fun n hn => A.actionFinite_tail c l n hn)
  rw [hsupp, ← (by simpa [Nat.add_sub_cancel] using
    Nat.range_eq_Icc_zero_sub_one (n := N + 1) (Nat.succ_ne_zero N) :
    Finset.range (N + 1) = Finset.Icc (0 : ℕ) N)]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ => by
    simp only [l1Weighted.mk_apply, SystemBlockDiagData.actionFinite, Fin.is_le,
      dite_true, finBlockAction]

/-- General finite block action norm bound. For ANY coefficient function `c` satisfying
`∀ j, ∑ k, |c j k| * ν^k ≤ C`, the weighted double-sum norm at row `l` is
bounded by `blockRowNorm(l) * C`. Shared by Taylor and Chebyshev IVP norm proofs. -/
lemma SystemBlockDiagData.actionFinite_weighted_norm_le
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) {C : ℝ}
    (hcoeff : ∀ j : Fin L,
      ∑ k : Fin (N + 1), |c j k| * (ν : ℝ) ^ (k : ℕ) ≤ C) :
    ∑ n : Fin (N + 1),
      |finBlockAction A.finBlock c l n| * (ν : ℝ) ^ (n : ℕ) ≤
      blockRowNorm ν A.finBlock l * C := by
  simp only [finBlockAction]
  refine (NormHelpers.weighted_sum_abs_sum_le (fun n => (ν : ℝ) ^ (n : ℕ))
    (fun _ => pow_nonneg ν.coe_nonneg _)
    (fun j n => ∑ k, A.finBlock l j n k * c j k)).trans ?_
  refine (Finset.sum_le_sum fun j _ => by
    simpa [blockEntryNorm, FiniteWeightedNorm.finl1WeightedNorm, Matrix.mulVec, dotProduct] using
      FiniteWeightedNorm.finWeightedMatrixNorm_mulVec_le (ν := ν) (A := A.finBlock l j)
        (v := fun k => c j k)).trans ?_
  exact (NormHelpers.sum_mul_le_sum_mul_const
    (a := fun j => blockEntryNorm ν A.finBlock l j)
    (b := fun j => ∑ k : Fin (N + 1), |c j k| * (ν : ℝ) ^ (k : ℕ))
    (ha := fun j => blockEntryNorm_nonneg (ν := ν) A.finBlock l j)
    (hb := hcoeff)).trans_eq rfl

lemma SystemBlockDiagData.actionFinite_component_norm_le_row
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖l1Weighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
      (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l)‖ ≤
      blockRowNorm ν A.finBlock l * ‖x‖ := by
  rw [A.norm_mk_actionFinite_eq (ν := ν)]
  exact A.actionFinite_weighted_norm_le (ν := ν) (toCoeff x) l fun j =>
    (by simpa [toCoeff, l1Weighted.toSeq] using
      l1Weighted.finSum_weighted_toSeq_le_norm (ν := ν) (a := x j) (N := N) :
      ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖x j‖).trans
      (norm_le_pi_norm x j)

/-- Restricted finite block norm: when components outside `active` vanish, the finite
block norm sum can be restricted to active components only. -/
lemma SystemBlockDiagData.actionFinite_component_norm_le_restricted
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L)
    (active : Finset (Fin L)) (hzero : ∀ j, j ∉ active → x j = 0) :
    ‖l1Weighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
      (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l)‖ ≤
      (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) * ‖x‖ := by
  rw [A.norm_mk_actionFinite_eq (ν := ν)]
  refine (NormHelpers.weighted_sum_abs_sum_le (fun n => (ν : ℝ) ^ (n : ℕ))
    (fun _ => pow_nonneg ν.coe_nonneg _)
    (fun j n => ∑ k, A.finBlock l j n k * toCoeff (ν := ν) x j k)).trans ?_
  refine (Finset.sum_le_sum fun j _ => by
    simpa [blockEntryNorm, FiniteWeightedNorm.finl1WeightedNorm, Matrix.mulVec, dotProduct] using
      FiniteWeightedNorm.finWeightedMatrixNorm_mulVec_le (ν := ν) (A := A.finBlock l j)
        (v := fun k => toCoeff (ν := ν) x j k)).trans ?_
  refine (Finset.sum_le_sum (g := fun j =>
      if j ∈ active then blockEntryNorm ν A.finBlock l j * ‖x‖ else 0) fun j _ => ?_).trans_eq ?_
  · by_cases hj : j ∈ active
    · rw [ite_eq_left hj]; exact mul_le_mul_of_nonneg_left
        ((by simpa [toCoeff, l1Weighted.toSeq] using
          l1Weighted.finSum_weighted_toSeq_le_norm (ν := ν) (a := x j) (N := N) :
          ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖x j‖).trans
          (norm_le_pi_norm x j))
        (blockEntryNorm_nonneg (ν := ν) A.finBlock l j)
    · rw [ite_eq_right hj]; simp [toCoeff_eq_zero (hzero j hj)]
  · rw [← Finset.sum_filter (p := (· ∈ active))]
    exact (Finset.sum_congr (by ext; simp) fun _ _ => rfl).trans (Finset.sum_mul ..).symm

lemma SystemBlockDiagData.actionTail_component_norm_le
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖l1Weighted.mk (A.actionTail (toCoeff (ν := ν) x) l)
      (A.actionTail_mem_of_mem (ν := ν) (toCoeff (ν := ν) x) l (toCoeff_mem (ν := ν) x l))‖ ≤
      A.tailBound * ‖x l‖ := by
  refine l1Weighted.norm_mk_le_of_pointwise _ _ (x l) A.tailBound (fun n => ?_)
  change |A.actionTail (toCoeff (ν := ν) x) l n| ≤ A.tailBound * |toCoeff (ν := ν) x l n|
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.actionTail_finite A _ l n hn, abs_zero]
    exact mul_nonneg (A.tailBound_nonneg_at l) (abs_nonneg _)
  · rw [SystemBlockDiagData.actionTail_tail A _ l n (Nat.lt_of_not_ge hn), abs_mul]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec l n (Nat.lt_of_not_ge hn)) (abs_nonneg _)

lemma SystemBlockDiagData.applyX_component_eq_finite_add_tail
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    A.applyX (ν := ν) x l =
      l1Weighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
        (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l) +
      l1Weighted.mk (A.actionTail (toCoeff (ν := ν) x) l)
        (A.actionTail_mem_of_mem (ν := ν) (toCoeff (ν := ν) x) l (toCoeff_mem (ν := ν) x l)) := by
  apply l1Weighted.ext
  intro n
  exact congr_fun (congr_fun (A.action_eq_actionFinite_add_actionTail (toCoeff (ν := ν) x)) l) n

lemma SystemBlockDiagData.applyX_component_norm_le
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖A.applyX (ν := ν) x l‖ ≤ (blockRowNorm ν A.finBlock l + A.tailBound) * ‖x‖ := by
  rw [A.applyX_component_eq_finite_add_tail (ν := ν) x l]
  have hfin := A.actionFinite_component_norm_le_row (ν := ν) x l
  have htail := (A.actionTail_component_norm_le (ν := ν) x l).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm x l) (A.tailBound_nonneg_at l))
  exact ((norm_add_le _ _).trans (add_le_add hfin htail)).trans_eq (by ring)

lemma SystemBlockDiagData.tailBound_nonneg [NeZero L] (A : SystemBlockDiagData L N) :
    0 ≤ A.tailBound := by
  let l0 : Fin L := ⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩
  exact A.tailBound_nonneg_at l0

lemma SystemBlockDiagData.toLinearMap_bound [NeZero L]
    (A : SystemBlockDiagData L N) :
    ∀ x : XL1 ν L,
      ‖A.toLinearMap (ν := ν) x‖ ≤
        (finiteBlockMatrixNorm ν A.finBlock + A.tailBound) * ‖x‖ := by
  intro x
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg
    (add_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) A.finBlock) A.tailBound_nonneg)
    (norm_nonneg x))).2 fun l => ?_
  exact (A.applyX_component_norm_le (ν := ν) x l).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add (Finset.le_sup' _ (Finset.mem_univ l)) le_rfl) (norm_nonneg x))

/-- Continuous-linear lift of the 8.2 block operator data on `(ℓ¹_ν)^L`,
with explicit operator bound `max_l Σ_j ‖A_{l,j}‖ + tailBound`. -/
def SystemBlockDiagData.toCLM [NeZero L]
    (A : SystemBlockDiagData L N) : XL1 ν L →L[ℝ] XL1 ν L :=
  LinearMap.mkContinuous (A.toLinearMap (ν := ν))
    (finiteBlockMatrixNorm ν A.finBlock + A.tailBound)
    (A.toLinearMap_bound (ν := ν))

@[simp]
lemma SystemBlockDiagData.toCLM_apply [NeZero L]
    (A : SystemBlockDiagData L N) (x : XL1 ν L) :
    A.toCLM (ν := ν) x = A.applyX (ν := ν) x := by
  simp [SystemBlockDiagData.toCLM, SystemBlockDiagData.toLinearMap]

/-- Per-component norm of `A.toCLM(w)` with active set restriction.
When `w j = 0` for `j ∉ active`, the finite block sum restricts to `active` and the
tail contribution vanishes for `l ∉ active`. Composes `applyX_component_eq_finite_add_tail`,
`actionFinite_component_norm_le_restricted`, and `actionTail_component_norm_le`. -/
lemma SystemBlockDiagData.norm_toCLM_component_le_restricted [NeZero L]
    (A : SystemBlockDiagData L N) (w : XL1 ν L) (l : Fin L)
    (active : Finset (Fin L)) (hzero : ∀ j, j ∉ active → w j = 0) :
    ‖A.toCLM (ν := ν) w l‖ ≤
      ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
        if l ∈ active then A.tailBound else 0) * ‖w‖ := by
  rw [SystemBlockDiagData.toCLM_apply, A.applyX_component_eq_finite_add_tail (ν := ν) w l]
  have hfin := A.actionFinite_component_norm_le_restricted (ν := ν) w l active hzero
  have htail := A.actionTail_component_norm_le (ν := ν) w l
  have htail_restricted : A.tailBound * ‖w l‖ ≤
      (if l ∈ active then A.tailBound else 0) * ‖w‖ := by
    by_cases hl : l ∈ active
    · rw [ite_eq_left hl]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w l) (A.tailBound_nonneg_at l)
    · rw [ite_eq_right hl, zero_mul]
      exact le_of_eq (by rw [hzero l hl, norm_zero, mul_zero])
  exact ((norm_add_le _ _).trans (add_le_add hfin htail)).trans
    ((add_le_add le_rfl htail_restricted).trans_eq (by ring))

@[simp]
lemma SystemBlockDiagData.toCoeff_toCLM [NeZero L]
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) (A.toCLM (ν := ν) x) l n = A.action (toCoeff (ν := ν) x) l n := by
  simp

@[simp]
lemma SystemBlockDiagData.toCoeff_comp_toCLM [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) ((A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) x) l n =
      A.action (B.action (toCoeff (ν := ν) x)) l n := by
  simp

/-! ## 2. CLM Composition And Residual Bridges -/





lemma SystemBlockDiagData.norm_toCLM_le [NeZero L]
    (A : SystemBlockDiagData L N) :
    ‖A.toCLM (ν := ν)‖ ≤ finiteBlockMatrixNorm ν A.finBlock + A.tailBound := by
  exact LinearMap.mkContinuous_norm_le _
    (add_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) A.finBlock) (A.tailBound_nonneg))
    (A.toLinearMap_bound (ν := ν))

lemma toCLM_ext_of_toCoeff_eq
    (T S : XL1 ν L →L[ℝ] XL1 ν L)
    (hcoeff : ∀ x : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ,
      toCoeff (ν := ν) (T x) l n = toCoeff (ν := ν) (S x) l n) :
    T = S :=
  ContinuousLinearMap.ext fun x => XL1.ext fun l n => hcoeff x l n


/-- Per-coefficient zero-input recovery from zero-action. Given `A`'s
finite-block injectivity and tail nonvanishing, `A.action c = 0` (pointwise)
implies `c = 0` (pointwise) — even when `c` is just a `SystemCoeff` and not
necessarily `toCoeff` of any `XL1` element.

This is the per-`SystemCoeff` analogue of
`injective_toCLM_of_finite_part_injective`, used to bridge `G a = 0` to
`ivpCoeffs ... = 0` in the f-F bridge: `G = approxInverse.action ∘ ivpCoeffs`,
so `G a = 0` gives `action (ivpCoeffs ...) = 0`, and this lemma upgrades to
`ivpCoeffs ... = 0`. -/
lemma SystemBlockDiagData.seq_zero_of_action_zero
    (A : SystemBlockDiagData L N)
    (h_fin :
      ∀ d : SystemCoeff L,
        (∀ l : Fin L, ∀ n : Fin (N + 1),
          (∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * d j k) = 0) →
        (∀ l : Fin L, ∀ n : Fin (N + 1), d l n = 0))
    (h_tail : ∀ l n, N < n → A.tailDiag l n ≠ 0)
    {c : SystemCoeff L} (h : ∀ l n, A.action c l n = 0) :
    ∀ l n, c l n = 0 := by
  have h_tail_zero : ∀ l n, N < n → c l n = 0 := fun l n hn =>
    (mul_eq_zero.mp ((A.action_tail c l n hn).symm.trans (h l n))).resolve_left
      (h_tail l n hn)
  have h_fin_zero := h_fin c fun l n => (A.action_fin c l n).symm.trans (h l ↑n)
  intro l n
  by_cases hn : n ≤ N
  · exact h_fin_zero l ⟨n, Nat.lt_succ_of_le hn⟩
  · exact h_tail_zero l n (Nat.lt_of_not_ge hn)

/-- General injectivity transfer from coefficient-level finite/tail hypotheses.

`h_fin` states injectivity of the finite-mode block action on coefficients `0..N`.
`h_tail` states nonvanishing tail diagonal on modes `N+1..∞`.
Together they imply injectivity of the lifted CLM `A.toCLM`. -/
lemma SystemBlockDiagData.injective_toCLM_of_finite_part_injective [NeZero L]
    (A : SystemBlockDiagData L N)
    (h_fin :
      ∀ d : SystemCoeff L,
        (∀ l : Fin L, ∀ n : Fin (N + 1),
          (∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * d j k) = 0) →
        (∀ l : Fin L, ∀ n : Fin (N + 1), d l n = 0))
    (h_tail : ∀ l n, N < n → A.tailDiag l n ≠ 0) :
    Function.Injective (A.toCLM (ν := ν)) :=
  (injective_iff_map_eq_zero _).2 fun x hx => toCoeff_injective (ν := ν) <| funext₂
    (A.seq_zero_of_action_zero h_fin h_tail (c := toCoeff (ν := ν) x) fun l n => by
      rw [← A.toCoeff_toCLM (ν := ν), hx, toCoeff_zero])

/-! ## 3. Block Identity Action

Helper: `x_{l,n} = ∑_j ∑_k (if l = j then I else 0)_{n,k} * x_{j,k}`. -/

private lemma block_identity_action
    (c : SystemCoeff L) (l : Fin L) (n : Fin (N + 1)) :
    c l n = ∑ j : Fin L, ∑ k : Fin (N + 1),
      (if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) n k * c j k := by
  rw [Finset.sum_eq_single l]
  · simp [Matrix.one_apply]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- Defect construction for A (bounded `SystemBlockDiagData`) composed with B (`BlockDiagOp`,
possibly unbounded tail). The finite block is `δ_{l,j}·I - ∑_m A_{l,m} B_{m,j}` and
the tail is zero (the tail of `I - A∘B` when the tail diagonals cancel; no cancellation
hypothesis enters the definition). Used for the IVP case where A† has unbounded tail
diagonal `k·δ_{j,j'}`.

The definition does not relate the defect to any operator: the caller proves separately
that `I - G_CLM = defect.toCLM` for a composed derivative (`defect_of_composed_toCLM_eq`). -/
def defectOfBlockDiagOp
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N) :
    SystemBlockDiagData L N where
  finBlock := fun l j =>
    (if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) -
      ∑ m, A.finBlock l m * B.finBlock m j
  tailDiag := fun _ _ => 0
  tailBound := 0
  tailBound_spec := by intro l n _; simp

/-! ## 4. Z₀ Bridge For Composed CLM (IVP Case)

When `A†` has unbounded tail (e.g., tail diagonal = `n`), no `DF_CLM : XL1 →L[ℝ] XL1`
with matching structure exists. Instead, the certificate provides the *composed*
`G_CLM = fderiv ℝ (A ∘ F) x̄ : XL1 →L[ℝ] XL1` whose coefficients match `A·B`
algebraically (finite block = `∑_m A_{l,m}*B_{m,j}`, tail = `A.tailDiag*B.tailDiag`).

This avoids materializing the intermediate unbounded operator. -/

/-- CLM-level identity for the *composed* derivative (IVP pattern):
`I - G_CLM = (defectOfBlockDiagOp A B).toCLM` when `G_CLM`'s coefficients match
the algebraic product `A·B` on both finite and tail modes. -/
lemma defect_of_composed_toCLM_eq [NeZero L]
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (G_CLM : XL1 ν L →L[ℝ] XL1 ν L)
    (hfin : ∀ x : XL1 ν L, ∀ l : Fin L, ∀ n : Fin (N + 1),
      toCoeff (ν := ν) (G_CLM x) l n =
        ∑ j : Fin L, ∑ k : Fin (N + 1),
          (∑ m : Fin L, A.finBlock l m * B.finBlock m j) n k *
            toCoeff (ν := ν) x j k)
    (htail : ∀ x : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      toCoeff (ν := ν) (G_CLM x) l n =
        (A.tailDiag l n * B.tailDiag l n) * toCoeff (ν := ν) x l n)
    (hcancel : ∀ l : Fin L, ∀ n : ℕ, N < n →
      A.tailDiag l n * B.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) - G_CLM =
    (defectOfBlockDiagOp A B).toCLM (ν := ν) := by
  apply toCLM_ext_of_toCoeff_eq; intro x l n
  simp only [sub_apply, ContinuousLinearMap.coe_id', id_eq,
    SystemBlockDiagData.toCoeff_toCLM]
  show toCoeff (ν := ν) x l n - toCoeff (ν := ν) (G_CLM x) l n =
    (defectOfBlockDiagOp A B).action (toCoeff (ν := ν) x) l n
  by_cases hn : n ≤ N
  · -- Finite modes: defect.action = (δI - ∑A*B) applied to toCoeff(x)
    set n' : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    rw [hfin x l n',
      SystemBlockDiagData.action_fin_eq_sum_mulVec (defectOfBlockDiagOp A B) _ l n']
    simp only [defectOfBlockDiagOp, Matrix.mulVec, dotProduct,
      Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    linarith [block_identity_action (toCoeff (ν := ν) x) l n']
  · -- Tail modes: A.tailDiag * B.tailDiag = 1 implies G_CLM(x) = x, so defect = 0
    rw [htail x l n (Nat.lt_of_not_ge hn),
      SystemBlockDiagData.action_tail (defectOfBlockDiagOp A B) _ l n (Nat.lt_of_not_ge hn)]
    show toCoeff (ν := ν) x l n -
      (A.tailDiag l n * B.tailDiag l n) * toCoeff (ν := ν) x l n =
      (defectOfBlockDiagOp A B).tailDiag l n * toCoeff (ν := ν) x l n
    simp only [defectOfBlockDiagOp, hcancel l n (Nat.lt_of_not_ge hn), one_mul, sub_self,
      zero_mul]

/-! ## 5. Defect Construction For Tail-Canceling Pairs (General L) -/

/-- Defect data for pairs where componentwise tail diagonals multiply to 1: the defect
`defectOfBlockDiagOp A B` of `A` with `↑B`. The residual `I - A∘B` has zero tail, so
`tailBound = 0`. The cancellation hypothesis does not enter the data; it is kept because
`Z₀_le_of_tailCancel` and `id_sub_comp_eq_defect_toCLM` are stated with it. -/
def SystemBlockDiagData.defectOfTailCancel
    (A B : SystemBlockDiagData L N)
    (_ : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    SystemBlockDiagData L N :=
  defectOfBlockDiagOp A B

/-- The defect CLM equals `I - A.toCLM ∘ B.toCLM` when tail diagonals cancel. -/
lemma SystemBlockDiagData.id_sub_comp_eq_defect_toCLM [NeZero L]
    (A B : SystemBlockDiagData L N)
    (htail : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) =
    (A.defectOfTailCancel B htail).toCLM (ν := ν) :=
  defect_of_composed_toCLM_eq A B _
    (fun x l n => by
      rw [SystemBlockDiagData.toCoeff_comp_toCLM, ← SystemBlockDiagData.comp_action_eq_action_comp,
        SystemBlockDiagData.action_fin]
      rfl)
    (fun x l n hn => by
      rw [SystemBlockDiagData.toCoeff_comp_toCLM,
        SystemBlockDiagData.action_comp_tail _ _ _ _ _ hn]
      rfl)
    htail

/-- Z₀ bound for tail-canceling pairs (general L):
`‖I - A.toCLM ∘ B.toCLM‖ ≤ finiteBlockMatrixNorm(defect.finBlock)`.

Design note. This lemma (both factors bounded) and `IVP.ivp_Z₀_le` (`A†` a `BlockDiagOp` with
unbounded tail) are faces of the carrier-generic `BlockDiagLift.composedApprox_Z₀`; on `XL1`,
`(A.composedApprox B h).toCLM = BlockDiagLift.composedApproxCLM (defectOfBlockDiagOp A B)`
(`SystemBlockDiagData.composedApprox_toCLM_eq_lift`). `A†` stays `BlockDiagOp` data: its tail
`Λ_n = n` is unbounded on `ℓ¹_ν`. Typing `A†` as a bounded map `ℓ¹_ν → ℓ¹_ω` would need block
realizations over a general weight function: `ω_n = ν^(n+1)/(n+1)` is not geometric, and
`l1Omega ν = lp (OmegaScaledReal ν) 1` (`Analysis/SequenceSpace/Geometric/Omega.lean`) is not an
`XL1` at another `PosReal`. -/
lemma SystemBlockDiagData.Z₀_le_of_tailCancel [NeZero L]
    (A B : SystemBlockDiagData L N)
    (htail : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
    finiteBlockMatrixNorm ν (A.defectOfTailCancel B htail).finBlock := by
  have hD := A.id_sub_comp_eq_defect_toCLM (ν := ν) B htail
  show ‖_‖ ≤ _; rw [hD]
  have h := (A.defectOfTailCancel B htail).norm_toCLM_le (ν := ν)
  have htb : (A.defectOfTailCancel B htail).tailBound = 0 := rfl
  rwa [htb, add_zero] at h

/-! ## 6. Finite Block Injectivity From Defect Norm < 1

If `‖I - A·B‖ < 1` as a block matrix norm, then the block product `A·B` is close to
the identity, so `A` is injective on finite modes. This bridges the numerical defect
bound to the `h_fin` hypothesis of `injective_toCLM_of_finite_part_injective`. -/

/-- System-level Neumann criterion: if the block defect `‖δI - ∑ A*B‖_{block,ν} < 1`,
then `A.toMatrix` is a unit (invertible as a flat matrix).
Analogous to `FinWeightedMatrix.matrix_invertible_of_norm_lt_one`. -/
lemma FiniteBlockMatrix.isUnit_toMatrix_of_blockNorm_lt_one [NeZero L]
    {ν : PosReal} (A B : FiniteBlockMatrix L N)
    (hlt : finiteBlockMatrixNorm ν
      (fun l j => (if l = j then (1 : Matrix _ _ ℝ) else 0) - ∑ m, A l m * B m j) < 1) :
    IsUnit (FiniteBlockMatrix.toMatrix A) := by
  -- The defect as zero-tail block data; its CLM has norm `< 1`, so it fixes only `0`.
  let D : SystemBlockDiagData L N :=
    defectOfBlockDiagOp ⟨A, fun _ _ => 0, 0, fun _ _ _ => by simp⟩ ⟨B, fun _ _ => 0⟩
  have hD : ‖D.toCLM (ν := ν)‖ < 1 := (D.norm_toCLM_le (ν := ν)).trans_lt (by
    show finiteBlockMatrixNorm ν _ + 0 < 1
    rwa [add_zero])
  have hfix : ∀ x : XL1 ν L, D.toCLM (ν := ν) x = x → x = 0 := fun x hx =>
    norm_le_zero_iff.mp <| by
      nlinarith [hx ▸ (D.toCLM (ν := ν)).le_opNorm x, norm_nonneg x, norm_nonneg (D.toCLM (ν := ν))]
  -- Step 1: the flattened block product `M_A * M_B` has injective `mulVec`.
  have h_prod : IsUnit (A.toMatrix * B.toMatrix) := by
    rw [← FiniteBlockMatrix.toMatrix_blockMul]
    refine Matrix.mulVec_injective_iff_isUnit.mp <|
      (injective_iff_map_eq_zero (Matrix.mulVecLin _)).2 fun v hv => ?_
    let c : SystemCoeff L := fun l n => if h : n < N + 1 then v (l, ⟨n, h⟩) else 0
    have hc_mem : ∀ l : Fin L, l1Weighted.Mem ν (c l) := fun l => by
      rw [l1Weighted.mem_iff]
      exact summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
        simp [c, show ¬ n ≤ N from by simp at hn; omega]
    have hx := hfix (ofCoeff (ν := ν) c hc_mem) <| XL1.ext fun l n => by
      rw [SystemBlockDiagData.toCoeff_toCLM, toCoeff_ofCoeff]
      have hc : toCoeff (ν := ν) (ofCoeff c hc_mem) = c := funext₂ (toCoeff_ofCoeff c hc_mem)
      rw [hc]
      by_cases hn : n ≤ N
      · have h0 := congr_fun hv (l, ⟨n, Nat.lt_succ_of_le hn⟩)
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
          FiniteBlockMatrix.toMatrix_apply, Pi.zero_apply] at h0
        rw [SystemBlockDiagData.action_finite _ _ _ _ hn]
        simp only [D, defectOfBlockDiagOp, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
        have h2 : ∑ j : Fin L, ∑ k : Fin (N + 1),
            (∑ m, A l m * B m j) ⟨n, Nat.lt_succ_of_le hn⟩ k * c j k = 0 := by
          simpa only [c, Fin.is_lt, ↓reduceDIte, Fin.eta] using h0
        linarith [block_identity_action c l ⟨n, Nat.lt_succ_of_le hn⟩]
      · rw [SystemBlockDiagData.action_tail _ _ _ _ (Nat.lt_of_not_ge hn)]
        simp [D, defectOfBlockDiagOp, c, hn]
    funext ⟨l, k⟩
    have := congr_fun (congr_fun (congrArg (toCoeff (ν := ν)) hx) l) k
    simpa [c, toCoeff_ofCoeff, Nat.lt_succ_iff.mp k.2] using this
  -- Step 2: `det (M_A * M_B) = det M_A * det M_B` is a unit, so `det M_A` is.
  rw [Matrix.isUnit_iff_isUnit_det] at h_prod ⊢
  exact isUnit_of_mul_isUnit_left (by rwa [Matrix.det_mul] at h_prod)

/-- If the finite-block defect `‖δI - ∑ A*B‖ < 1`, then `A` is injective on finite
coefficients: `∀ d, (∀ l n, ∑ A*d = 0) → (∀ l n, d = 0)`.

Uses `FiniteBlockMatrix.isUnit_toMatrix_of_blockNorm_lt_one` to get
`IsUnit (FiniteBlockMatrix.toMatrix A.finBlock)`, then extracts `mulVec` injectivity. -/
lemma finite_block_injective_of_defect_norm_lt_one [NeZero L]
    {ν : PosReal}
    (A : SystemBlockDiagData L N) (B : BlockDiagOp L N)
    (hlt : finiteBlockMatrixNorm ν (defectOfBlockDiagOp A B).finBlock < 1) :
    ∀ d : SystemCoeff L,
      (∀ l : Fin L, ∀ n : Fin (N + 1),
        (∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * d j k) = 0) →
      (∀ l : Fin L, ∀ n : Fin (N + 1), d l n = 0) := by
  -- The defect finBlock matches the signature of isUnit_toMatrix_of_blockNorm_lt_one
  have h_A_unit : IsUnit (FiniteBlockMatrix.toMatrix A.finBlock) :=
    FiniteBlockMatrix.isUnit_toMatrix_of_blockNorm_lt_one A.finBlock B.finBlock hlt
  have h_A_inj : Function.Injective (FiniteBlockMatrix.toMatrix A.finBlock).mulVec :=
    Matrix.mulVec_injective_of_isUnit h_A_unit
  intro d hd l n
  let v : Fin L × Fin (N + 1) → ℝ := fun ⟨j, k⟩ => d j ↑k
  have hv : (FiniteBlockMatrix.toMatrix A.finBlock).mulVec v = 0 := by
    ext ⟨l', n'⟩
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, FiniteBlockMatrix.toMatrix]
    rw [show ∑ x : Fin L × Fin (N + 1),
        A.finBlock l' x.1 n' x.2 * d x.1 ↑x.2 =
        ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l' j n' k * d j ↑k from
      Fintype.sum_prod_type _]
    exact hd l' n'
  exact congr_fun (h_A_inj (hv.trans (Matrix.mulVec_zero _).symm)) ⟨l, n⟩

end SystemBlockDiagConcrete

/-! ## 7. BlockDiagLift Instance for XL1 -/

section BlockDiagLiftXL1

variable {ν : PosReal} {L : ℕ} [NeZero L]

/-- The Taylor system space `XL1 ν L = (ℓ¹_ν)^L` lifts a block defect by applying
`D.actionFinite` to the coefficients `toCoeff x` and rebuilding with `ofCoeff`. -/
instance instBlockDiagLiftXL1 : BlockDiagLift (XL1 ν L) L ν where
  liftDefect D x :=
    ofCoeff (D.actionFinite (toCoeff (ν := ν) x))
      (fun l => D.actionFinite_mem (ν := ν) (toCoeff x) l)
  liftDefect_add D x y := by
    apply XL1.ext; intro l n
    simp only [toCoeff_ofCoeff, toCoeff_add]
    exact congr_fun (congr_fun (D.actionFinite_add (toCoeff x) (toCoeff y)) l) n
  liftDefect_smul D r x := by
    apply XL1.ext; intro l n
    simp only [toCoeff_ofCoeff, toCoeff_smul]
    exact congr_fun (congr_fun (D.actionFinite_smul r (toCoeff x)) l) n
  liftDefect_norm_le D x := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) _)
      (norm_nonneg _))).2 fun l => ?_
    exact (D.actionFinite_component_norm_le_row x l).trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ l)) (norm_nonneg x))

end BlockDiagLiftXL1

end RadiiPolynomial
