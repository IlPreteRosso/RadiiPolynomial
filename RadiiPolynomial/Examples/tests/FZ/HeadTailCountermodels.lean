import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift

/-!
# L001 tests (T43): countermodels for the decision-bearing hypotheses of the column layer

Ported S027 checker tests (`tmp/units/S027-HeadTailColumns/evidence/checker/c1/tests.lean`,
sha256 81d0377d…, cited by name and line) restated on the library API of
`WeightedL1/Columns.lean` and `WeightedL1/Diagonal.lean`, plus the decisive tests of
TARGET_SHEET §7 for T25, T32 and T33 and the positive sides (falsity witnesses) of the
mathematical-negative controls CTL-C1, CTL-D1, CTL-D2 and CTL-D3.

Old → new symbols: `P_H (H N)` ↦ `lpOneAlg.headProj (Finset.Icc (-N) N)`
(`{0}` for `N = 0`), `1 - P_H` / `Q_H` ↦ `lpOneAlg.tailProj`, `D_r` ↦ `lpOneAlg.diagCLM`,
`colRatio` ↦ `lpOneAlg.colRatio`. The S027 composition tests `mixedComposition` /
`mixedCompositeNonzero` need `Operators/HeadTail` and live in `HeadTailVacuity.lean`.

Every countermodel states the retained hypotheses, the failure of the dropped hypothesis and
the failure of the conclusion. Kernel-only; imported by nothing.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.HeadTail

open RadiiPolynomial lpOneAlg

/-! ### The unit-weight carrier and rank-one maps (S027T :466–:488) -/

/-- The unit weight `ν = 1`. -/
def nuOne : PosReal := ⟨1, by norm_num⟩

/-- The unit-weight bilateral carrier `ℓ¹(ℤ)`. -/
abbrev X := lpOneAlg ℤ (geomFiberZ ℝ nuOne)

/-- The head `{0}`. -/
abbrev H0 : Finset ℤ := {0}

/-- Every weight of the unit carrier is `1`. -/
theorem oneWeight (j : ℤ) : FiberTrivialization.weight (E := geomFiberZ ℝ nuOne) j = 1 := by
  rw [geomFiberZ_weight]; change (1 : ℝ) ^ j.natAbs = 1; exact one_pow _

/-- Every unit atom of the unit carrier has norm `1`. -/
theorem atomNorm (j : ℤ) : ‖(single j (1 : ℝ) : X)‖ = 1 := by
  rw [norm_single, norm_one, one_mul, oneWeight]

/-- Every unit atom is nonzero. -/
theorem atom_ne_zero (j : ℤ) : (single j (1 : ℝ) : X) ≠ 0 := fun h =>
  zero_ne_one ((norm_zero (E := X)).symm.trans ((congrArg norm h).symm.trans (atomNorm j)))

/-- Column domination of the rank-one family `e_j ↦ [j = k] e_l`. -/
theorem rankBound (k l j : ℤ) :
    ‖(if j = k then single l (1 : ℝ) else 0 : X)‖ ≤
      1 * FiberTrivialization.weight (E := geomFiberZ ℝ nuOne) j := by
  rw [oneWeight, one_mul]; split_ifs
  · rw [atomNorm]
  · rw [norm_zero]; norm_num

/-- The rank-one map `e_k ↦ e_l` (S027T `rank k` is `rk k k`). -/
def rk (k l : ℤ) : X →L[ℝ] X :=
  liftCLM (fun j => if j = k then single l 1 else 0) 1 (rankBound k l)

theorem rkAtom (k l j : ℤ) : rk k l (single j (1 : ℝ)) = if j = k then single l 1 else 0 := by
  rw [rk, liftCLM_single, one_smul]

theorem rkRatio (k l j : ℤ) : colRatio (rk k l) j = if j = k then 1 else 0 := by
  rw [colRatio, rkAtom, oneWeight, div_one]; split_ifs
  · rw [atomNorm]
  · exact norm_zero

theorem negRatio {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y) (j : ℤ) :
    colRatio (-A) j = colRatio A j := by
  simp only [colRatio, neg_apply, norm_neg]

theorem zeroRatio {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (j : ℤ) :
    colRatio (0 : X →L[ℝ] Y) j = 0 := by
  rw [colRatio, zero_apply, norm_zero, zero_div]

/-- A one-point supremum. -/
theorem iSup_indicator (k : ℤ) (c : ℝ) (hc : 0 ≤ c) : (⨆ j : ℤ, if j = k then c else 0) = c := by
  refine le_antisymm (Real.iSup_le (fun j => by split_ifs <;> linarith) hc) ?_
  refine le_ciSup_of_le ⟨c, ?_⟩ k (by simp)
  rintro _ ⟨j, rfl⟩; dsimp only; split_ifs <;> linarith

theorem head_atom_mem (j : ℤ) (hj : j ∈ H0) :
    (headProj H0 : X →L[ℝ] X) (single j (1 : ℝ) : X) = single j 1 := by
  rw [headProj_single, ite_eq_left hj]

theorem head_atom_not_mem (j : ℤ) (hj : j ∉ H0) :
    (headProj H0 : X →L[ℝ] X) (single j (1 : ℝ) : X) = 0 := by
  rw [headProj_single, ite_eq_right hj]

theorem tail_atom_mem (j : ℤ) (hj : j ∈ H0) :
    (tailProj H0 : X →L[ℝ] X) (single j (1 : ℝ) : X) = 0 := by
  rw [tailProj_single, ite_eq_left hj]

theorem tail_atom_not_mem (j : ℤ) (hj : j ∉ H0) :
    (tailProj H0 : X →L[ℝ] X) (single j (1 : ℝ) : X) = single j 1 := by
  rw [tailProj_single, ite_eq_right hj]

/-- A rank-one map into the head is head-valued. -/
theorem rk_head (k : ℤ) : (headProj H0 : X →L[ℝ] X) ∘L rk k 0 = rk k 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, rkAtom]; split_ifs
  · exact head_atom_mem 0 (Finset.mem_singleton_self 0)
  · exact map_zero _

/-- A rank-one map into the tail is tail-valued. -/
theorem rk_tail (k l : ℤ) (hl : l ≠ 0) : (tailProj H0 : X →L[ℝ] X) ∘L rk k l = rk k l := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, rkAtom]; split_ifs
  · exact tail_atom_not_mem l (by simpa using hl)
  · exact map_zero _

/-- A rank-one map out of the head kills the source tail. -/
theorem rk_kill_tail (l : ℤ) : rk 0 l ∘L (tailProj H0 : X →L[ℝ] X) = 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, zero_apply]
  by_cases hj : j ∈ H0
  · rw [tail_atom_mem j hj, map_zero]
  · rw [tail_atom_not_mem j hj, rkAtom, ite_eq_right (by simpa using hj)]

/-- A rank-one map out of the tail kills the source head. -/
theorem rk_kill_head (k l : ℤ) (hk : k ≠ 0) : rk k l ∘L (headProj H0 : X →L[ℝ] X) = 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, zero_apply]
  by_cases hj : j ∈ H0
  · rw [head_atom_mem j hj, rkAtom, ite_eq_right]
    rintro rfl; exact hk (by simpa using hj)
  · rw [head_atom_not_mem j hj, map_zero]

/-- A rank-one map into the tail is not head-valued. -/
theorem rk_not_head (k l : ℤ) (hl : l ≠ 0) : (headProj H0 : X →L[ℝ] X) ∘L rk k l ≠ rk k l := by
  intro h
  have hk := DFunLike.congr_fun h (single k (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, rkAtom, ite_eq_left rfl,
    head_atom_not_mem l (by simpa using hl)] at hk
  exact atom_ne_zero l hk.symm

/-- A rank-one map into the head is not tail-valued. -/
theorem rk_not_tail (k : ℤ) : (tailProj H0 : X →L[ℝ] X) ∘L rk k 0 ≠ rk k 0 := by
  intro h
  have hk := DFunLike.congr_fun h (single k (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, rkAtom, ite_eq_left rfl,
    tail_atom_mem 0 (Finset.mem_singleton_self 0)] at hk
  exact atom_ne_zero 0 hk.symm

/-- A rank-one map out of the tail does not kill the source tail. -/
theorem rk_not_kill_tail (k l : ℤ) (hk : k ≠ 0) : rk k l ∘L (tailProj H0 : X →L[ℝ] X) ≠ 0 := by
  intro h
  have hk' := DFunLike.congr_fun h (single k (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, tail_atom_not_mem k (by simpa using hk), rkAtom,
    ite_eq_left rfl, zero_apply] at hk'
  exact atom_ne_zero l hk'

/-- A rank-one map out of the head does not kill the source head. -/
theorem rk_not_kill_head (l : ℤ) : rk 0 l ∘L (headProj H0 : X →L[ℝ] X) ≠ 0 := by
  intro h
  have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, head_atom_mem 0 (Finset.mem_singleton_self 0), rkAtom,
    ite_eq_left rfl, zero_apply] at h0
  exact atom_ne_zero l h0

/-- A two-term column sum concentrated at one source atom with value `2`. -/
theorem iSup_pair2 (k : ℤ) (A B : X →L[ℝ] X)
    (h : ∀ j, colRatio A j + colRatio B j = if j = k then 2 else 0) :
    (⨆ j, (colRatio A j + colRatio B j)) = 2 := by
  rw [iSup_congr h, iSup_indicator k 2 (by norm_num)]

/-- A three-term column sum concentrated at one source atom with value `2`. -/
theorem iSup_triple (k : ℤ) (A B C : X →L[ℝ] X)
    (h : ∀ j, colRatio A j + colRatio B j + colRatio C j = if j = k then 2 else 0) :
    (⨆ j, (colRatio A j + colRatio B j + colRatio C j)) = 2 := by
  rw [iSup_congr h, iSup_indicator k 2 (by norm_num)]

/-! ### T28/T29 `hS`, `hT` (S027T :489–:516, :647–:660) -/

theorem rankHead : (headProj H0 : X →L[ℝ] X) ∘L rk 0 0 = rk 0 0 := rk_head 0

theorem rankTail : (tailProj H0 : X →L[ℝ] X) ∘L rk 1 1 = rk 1 1 := rk_tail 1 1 one_ne_zero

theorem drop_hS_column :
    colRatio (-rk 1 1 + rk 1 1) 1 ≠ colRatio (-rk 1 1) 1 + colRatio (rk 1 1) 1 := by
  rw [neg_add_cancel, negRatio, rkRatio, zeroRatio]; norm_num

theorem rankSumSup (k : ℤ) : (⨆ j, colRatio (-rk k k) j + colRatio (rk k k) j) = 2 :=
  iSup_pair2 k _ _ fun j => by simp only [negRatio, rkRatio]; split_ifs <;> norm_num

theorem drop_hS_norm : ‖-rk 1 1 + rk 1 1‖ ≠ ⨆ j, colRatio (-rk 1 1) j + colRatio (rk 1 1) j := by
  rw [neg_add_cancel, norm_zero, rankSumSup]; norm_num

theorem drop_hT_column :
    colRatio (rk 0 0 + -rk 0 0) 0 ≠ colRatio (rk 0 0) 0 + colRatio (-rk 0 0) 0 := by
  rw [add_neg_cancel, negRatio, rkRatio, zeroRatio]; norm_num

theorem drop_hT_norm : ‖rk 0 0 + -rk 0 0‖ ≠ ⨆ j, colRatio (rk 0 0) j + colRatio (-rk 0 0) j := by
  rw [add_neg_cancel, norm_zero,
    iSup_pair2 0 _ _ fun j => by simp only [negRatio, rkRatio]; split_ifs <;> norm_num]
  norm_num

theorem drop_hS_retained : (tailProj H0 : X →L[ℝ] X) ∘L rk 1 1 = rk 1 1 := rankTail

theorem drop_hS_fails : (headProj H0 : X →L[ℝ] X) ∘L (-rk 1 1) ≠ -rk 1 1 := by
  rw [ContinuousLinearMap.comp_neg]
  exact fun h => rk_not_head 1 1 one_ne_zero (neg_inj.mp h)

theorem drop_hT_retained : (headProj H0 : X →L[ℝ] X) ∘L rk 0 0 = rk 0 0 := rankHead

theorem drop_hT_fails : (tailProj H0 : X →L[ℝ] X) ∘L (-rk 0 0) ≠ -rk 0 0 := by
  rw [ContinuousLinearMap.comp_neg]
  exact fun h => rk_not_tail 0 (neg_inj.mp h)

/-! ### T26 `hx`, `hy` (S027T :532) -/

/-- Dropping `hy` (S027T `drop_support`): `x = e₀` is head-supported, `y = -e₀` is not
tail-supported, and the norms do not add. -/
theorem drop_support :
    (headProj H0 : X →L[ℝ] X) (single 0 (1 : ℝ) : X) = single 0 1 ∧
      (tailProj H0 : X →L[ℝ] X) (-(single 0 (1 : ℝ)) : X) ≠ -(single 0 1) ∧
      ‖(single 0 (1 : ℝ) : X) + -(single 0 (1 : ℝ) : X)‖ ≠
        ‖(single 0 (1 : ℝ) : X)‖ + ‖-(single 0 (1 : ℝ) : X)‖ := by
  refine ⟨head_atom_mem 0 (Finset.mem_singleton_self 0), ?_, ?_⟩
  · rw [map_neg, tail_atom_mem 0 (Finset.mem_singleton_self 0), neg_zero]
    exact fun h => atom_ne_zero 0 (neg_eq_zero.mp h.symm)
  · rw [add_neg_cancel, norm_zero, norm_neg, atomNorm]; norm_num

/-- Dropping `hx`: `x = e₁` is not head-supported, `y = -e₁` is tail-supported, and the
norms do not add. -/
theorem drop_hx_support :
    (headProj H0 : X →L[ℝ] X) (single 1 (1 : ℝ) : X) ≠ single 1 1 ∧
      (tailProj H0 : X →L[ℝ] X) (-(single 1 (1 : ℝ)) : X) = -(single 1 1) ∧
      ‖(single 1 (1 : ℝ) : X) + -(single 1 (1 : ℝ) : X)‖ ≠
        ‖(single 1 (1 : ℝ) : X)‖ + ‖-(single 1 (1 : ℝ) : X)‖ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [head_atom_not_mem 1 (by decide)]; exact fun h => atom_ne_zero 1 h.symm
  · rw [map_neg, tail_atom_not_mem 1 (by decide)]
  · rw [add_neg_cancel, norm_zero, norm_neg, atomNorm]; norm_num

/-! ### T6/T7 `hC` and T9 on an empty index (S027T :537–:549) -/

/-- The empty index type carries a (vacuous) positive weight. -/
local instance emptyPos : PosWeight (fun _ : Empty => (1 : ℝ)) := ⟨fun i => nomatch i⟩

/-- The weighted ℓ¹ space over the empty index type. -/
abbrev EmptyX := lpOneAlg Empty (WeightedScalar ℝ (fun _ : Empty => (1 : ℝ)))

/-- Without `0 ≤ C`, the column bound holds vacuously at `C = -1` while `‖0‖ ≤ -1` fails. -/
theorem empty_bad_bound :
    (∀ i : Empty, ‖(0 : EmptyX →L[ℝ] ℝ) (single i 1)‖ ≤
      (-1 : ℝ) * FiberTrivialization.weight (E := WeightedScalar ℝ (fun _ : Empty => (1 : ℝ))) i) ∧
      ¬ ‖(0 : EmptyX →L[ℝ] ℝ)‖ ≤ (-1 : ℝ) := by
  constructor
  · intro i; exact nomatch i
  · rw [norm_zero]; norm_num

/-- The `hC`-free iff of T7 is false (T = 0, C = -1, empty index). -/
theorem drop_hC_iff :
    ¬ (‖(0 : EmptyX →L[ℝ] ℝ)‖ ≤ (-1 : ℝ) ↔ ∀ i : Empty, ‖(0 : EmptyX →L[ℝ] ℝ) (single i 1)‖ ≤
      (-1 : ℝ) * FiberTrivialization.weight (E := WeightedScalar ℝ (fun _ : Empty => (1 : ℝ))) i) :=
  fun h => empty_bad_bound.2 (h.mpr empty_bad_bound.1)

/-- T9 needs no `Nonempty`: on the empty index both sides are `0`. -/
theorem empty_iSup :
    ‖(0 : EmptyX →L[ℝ] ℝ)‖ = 0 ∧ (⨆ i : Empty, colRatio (0 : EmptyX →L[ℝ] ℝ) i) = 0 :=
  ⟨norm_zero, Real.iSup_of_isEmpty (ι := Empty) (f := colRatio (0 : EmptyX →L[ℝ] ℝ))⟩

/-- T9 applies on the empty index. -/
theorem empty_opNorm_eq_iSup :
    ‖(0 : EmptyX →L[ℝ] ℝ)‖ = ⨆ i : Empty, colRatio (0 : EmptyX →L[ℝ] ℝ) i :=
  opNorm_eq_iSup_cols _

/-- CTL-C1 positive side: T7 with `<` for `≤` is false at `T = 0`, `C = 0`. -/
theorem ctl_C1_witness :
    ¬ (‖(0 : X →L[ℝ] X)‖ < 0 ↔ ∀ i, ‖(0 : X →L[ℝ] X) (single i (1 : ℝ))‖ ≤
      0 * FiberTrivialization.weight (E := geomFiberZ ℝ nuOne) i) := by
  rw [norm_zero]
  exact fun h => lt_irrefl _ (h.mpr fun i => by rw [zero_apply, norm_zero, zero_mul])

/-! ### Mixed weights (S027T :553–:605) -/

/-- Source weight `2`. -/
def muTwo : PosReal := ⟨2, by norm_num⟩

/-- Target weight `3`. -/
def nuThree : PosReal := ⟨3, by norm_num⟩

theorem muTwo_coe : (muTwo : ℝ) = 2 := rfl

theorem nuThree_coe : (nuThree : ℝ) = 3 := rfl

abbrev Source2 := lpOneAlg ℤ (geomFiberZ ℝ muTwo)

abbrev Target3 := lpOneAlg ℤ (geomFiberZ ℝ nuThree)

/-- The head `[-1, 1]`. -/
abbrev H1 : Finset ℤ := Finset.Icc (-1) 1

def mixedP : Target3 →L[ℝ] Target3 := headProj H1

def mixedQ : Target3 →L[ℝ] Target3 := tailProj H1

def mixedVector : Target3 := single 0 1 + single 2 1

theorem mixedBound (j : ℤ) : ‖(if j = 1 then mixedVector else 0 : Target3)‖ ≤
    10 * FiberTrivialization.weight (E := geomFiberZ ℝ muTwo) j := by
  rw [geomFiberZ_weight]
  by_cases hj : j = 1
  · subst j; rw [ite_eq_left rfl]
    refine (norm_add_le _ _).trans ?_
    rw [norm_single, norm_single, geomFiberZ_weight, geomFiberZ_weight]
    norm_num [nuThree_coe, muTwo_coe]
  · rw [ite_eq_right hj, norm_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg muTwo.coe_nonneg _)

def mixedL : Source2 →L[ℝ] Target3 :=
  liftCLM (fun j => if j = 1 then mixedVector else 0) 10 mixedBound

def mixedS : Source2 →L[ℝ] Target3 := mixedP ∘L mixedL

def mixedT : Source2 →L[ℝ] Target3 := mixedQ ∘L mixedL

theorem weightsDistinct : (muTwo : ℝ) ≠ (nuThree : ℝ) := by norm_num [nuThree_coe, muTwo_coe]

theorem mixedSupports : mixedP ∘L mixedS = mixedS ∧ mixedQ ∘L mixedT = mixedT := by
  constructor
  · rw [mixedS, ← ContinuousLinearMap.comp_assoc, mixedP, headProj_comp_headProj]
  · rw [mixedT, ← ContinuousLinearMap.comp_assoc, mixedQ, tailProj_comp_tailProj]

theorem mixedAtom : mixedL (single 1 (1 : ℝ)) = mixedVector := by
  rw [mixedL, liftCLM_single, one_smul, ite_eq_left rfl]

theorem mixedSAtom : mixedS (single 1 (1 : ℝ)) = single 0 1 := by
  rw [mixedS, ContinuousLinearMap.comp_apply, mixedAtom, mixedVector, map_add, mixedP,
    headProj_single, headProj_single, ite_eq_left (by decide), ite_eq_right (by decide), add_zero]

theorem mixedTAtom : mixedT (single 1 (1 : ℝ)) = single 2 1 := by
  rw [mixedT, ContinuousLinearMap.comp_apply, mixedAtom, mixedVector, map_add, mixedQ,
    tailProj_single, tailProj_single, ite_eq_left (by decide), ite_eq_right (by decide), zero_add]

theorem mixedColumns : colRatio mixedS 1 = (1 : ℝ) / 2 ∧ colRatio mixedT 1 = (9 : ℝ) / 2 := by
  constructor <;> rw [colRatio]
  · rw [mixedSAtom, norm_single, geomFiberZ_weight, geomFiberZ_weight]
    norm_num [nuThree_coe, muTwo_coe]
  · rw [mixedTAtom, norm_single, geomFiberZ_weight, geomFiberZ_weight]
    norm_num [nuThree_coe, muTwo_coe]

/-- Distinct source/target weights: the aggregate column is the sum `1/2 + 9/2`. -/
theorem mixedAggregateColumn : colRatio (mixedS + mixedT) 1 = 5 := by
  rw [colRatio_add_of_head_tail H1 _ _ mixedSupports.1 mixedSupports.2,
    mixedColumns.1, mixedColumns.2]; norm_num

theorem mixedAggregateNorm : ‖mixedS + mixedT‖ = ⨆ i, (colRatio mixedS i + colRatio mixedT i) :=
  opNorm_add_eq_iSup H1 _ _ mixedSupports.1 mixedSupports.2

/-! ### Empty head (S027T :611–:645) -/

theorem emptyHead : (headProj (𝕜 := ℝ) (∅ : Finset ℤ) : Target3 →L[ℝ] Target3) = 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [headProj_single, ite_eq_right (Finset.notMem_empty j)]
  rfl

theorem emptyHeadComplement : (tailProj (𝕜 := ℝ) (∅ : Finset ℤ) : Target3 →L[ℝ] Target3) = 1 := by
  rw [tailProj_eq_one_sub, emptyHead, sub_zero]

def emptyP : Target3 →L[ℝ] Target3 := headProj ∅

def emptyQ : Target3 →L[ℝ] Target3 := tailProj ∅

def emptyL : EmptyX →L[ℝ] Target3 := 0

def emptyS : EmptyX →L[ℝ] Target3 := emptyP ∘L emptyL

def emptyT : EmptyX →L[ℝ] Target3 := emptyQ ∘L emptyL

def emptyM : Target3 →L[ℝ] Target3 := 1

def emptyR : Target3 →L[ℝ] Target3 := emptyQ

def emptyInternalL : Target3 →L[ℝ] Target3 := 1

def emptyComposite : Target3 →L[ℝ] Target3 :=
  (emptyM ∘L emptyP + emptyR) ∘L (emptyP ∘L emptyInternalL ∘L emptyQ + emptyQ ∘L emptyInternalL)

theorem emptyComposition : emptyComposite = 1 := by
  rw [emptyComposite, emptyM, emptyR, emptyInternalL, emptyQ, emptyP, emptyHeadComplement,
    emptyHead]
  simp only [zero_add, ← ContinuousLinearMap.mul_def, one_mul, zero_mul]

theorem emptyReconstruction :
    ‖emptyS + emptyT‖ = ⨆ i : Empty, (colRatio emptyS i + colRatio emptyT i) := by
  apply opNorm_add_eq_iSup (∅ : Finset ℤ)
  · rw [emptyS, ← ContinuousLinearMap.comp_assoc, emptyP, headProj_comp_headProj]
  · rw [emptyT, ← ContinuousLinearMap.comp_assoc, emptyQ, tailProj_comp_tailProj]

/-! ### T25 `hr0` (TARGET_SHEET §7) -/

/-- The constant symbol `1`. -/
def rOne : ℤ → ℝ := fun _ => 1

theorem rOne_bound (j : ℤ) : ‖rOne j‖ ≤ 1 := by simp [rOne]

/-- Dropping `hr0`: `r ≡ 1` does not vanish on `H = {0}`, `P_H ∘ D_r = P_H ≠ 0`, and
`Q_H ∘ D_r ≠ D_r`. -/
theorem drop_hr0 :
    ¬ (∀ j ∈ H0, rOne j = 0) ∧
      (headProj H0 : X →L[ℝ] X) ∘L (diagCLM rOne 1 rOne_bound : X →L[ℝ] X) ≠ 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (diagCLM rOne 1 rOne_bound : X →L[ℝ] X) ≠
        diagCLM rOne 1 rOne_bound := by
  have hD : (diagCLM rOne 1 rOne_bound : X →L[ℝ] X) (single 0 1) = single 0 1 := by
    rw [diagCLM_single, rOne, one_mul]
  refine ⟨fun h => one_ne_zero (h 0 (Finset.mem_singleton_self 0)), fun h => ?_, fun h => ?_⟩
  · have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply, hD, head_atom_mem 0 (Finset.mem_singleton_self 0),
      zero_apply] at h0
    exact atom_ne_zero 0 h0
  · have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply, hD, tail_atom_mem 0 (Finset.mem_singleton_self 0)] at h0
    exact atom_ne_zero 0 h0.symm

/-! ### T32 `hZ`, `hS`, `hi` (TARGET_SHEET §7) -/

theorem idRatio (j : ℤ) : colRatio (1 : X →L[ℝ] X) j = 1 := by
  rw [colRatio, one_apply_eq_self, atomNorm, oneWeight, div_one]

theorem headRatio_mem : colRatio (headProj H0 : X →L[ℝ] X) 0 = 1 := by
  rw [colRatio, head_atom_mem 0 (Finset.mem_singleton_self 0), atomNorm, oneWeight, div_one]

theorem tailRatio_not_mem : colRatio (tailProj H0 : X →L[ℝ] X) 1 = 1 := by
  rw [colRatio, tail_atom_not_mem 1 (by decide), atomNorm, oneWeight, div_one]

theorem id_comp_tail_ne_zero : (1 : X →L[ℝ] X) ∘L (tailProj H0 : X →L[ℝ] X) ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (single 1 (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, tail_atom_not_mem 1 (by decide), one_apply_eq_self,
    zero_apply] at h1
  exact atom_ne_zero 1 h1

theorem id_comp_head_ne_zero : (1 : X →L[ℝ] X) ∘L (headProj H0 : X →L[ℝ] X) ≠ 0 := by
  intro h
  have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, head_atom_mem 0 (Finset.mem_singleton_self 0),
    one_apply_eq_self, zero_apply] at h0
  exact atom_ne_zero 0 h0

/-- `colRatio_eq_zero_of_comp_tailProj`, dropping `hZ`: `Z = 1`, `i = 1 ∉ H`. -/
theorem drop_hZ_tail : (1 ∉ H0) ∧ (1 : X →L[ℝ] X) ∘L tailProj H0 ≠ 0 ∧
    colRatio (1 : X →L[ℝ] X) 1 ≠ 0 :=
  ⟨by decide, id_comp_tail_ne_zero, by rw [idRatio]; norm_num⟩

/-- `colRatio_eq_zero_of_comp_tailProj`, dropping `hi`: `Z = P_H` kills the tail, `i = 0 ∈ H`. -/
theorem drop_hi_tail : (headProj H0 : X →L[ℝ] X) ∘L tailProj H0 = 0 ∧ (0 : ℤ) ∈ H0 ∧
    colRatio (headProj H0 : X →L[ℝ] X) 0 ≠ 0 :=
  ⟨headProj_comp_tailProj H0, Finset.mem_singleton_self 0, by rw [headRatio_mem]; norm_num⟩

/-- `colRatio_eq_zero_of_comp_headProj`, dropping `hS`: `S = 1`, `i = 0 ∈ H`. -/
theorem drop_hS_head : (0 : ℤ) ∈ H0 ∧ (1 : X →L[ℝ] X) ∘L headProj H0 ≠ 0 ∧
    colRatio (1 : X →L[ℝ] X) 0 ≠ 0 :=
  ⟨Finset.mem_singleton_self 0, id_comp_head_ne_zero, by rw [idRatio]; norm_num⟩

/-- `colRatio_eq_zero_of_comp_headProj`, dropping `hi`: `S = Q_H` kills the head, `i = 1 ∉ H`. -/
theorem drop_hi_head : (tailProj H0 : X →L[ℝ] X) ∘L headProj H0 = 0 ∧ (1 : ℤ) ∉ H0 ∧
    colRatio (tailProj H0 : X →L[ℝ] X) 1 ≠ 0 :=
  ⟨tailProj_comp_headProj H0, by decide, by rw [tailRatio_not_mem]; norm_num⟩

/-- `colRatio_add_of_comp_split`, dropping `hZ`: `Z = -Q_H`, `S = Q_H`, column `1`. -/
theorem drop_hZ_split :
    (-tailProj H0 : X →L[ℝ] X) ∘L tailProj H0 ≠ 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L headProj H0 = 0 ∧
      colRatio (-(tailProj H0 : X →L[ℝ] X) + tailProj H0 : X →L[ℝ] X) 1 ≠
        colRatio (-tailProj H0 : X →L[ℝ] X) 1 +
          colRatio (tailProj H0 : X →L[ℝ] X) 1 := by
  refine ⟨?_, tailProj_comp_headProj H0, ?_⟩
  · rw [ContinuousLinearMap.neg_comp, tailProj_comp_tailProj, neg_ne_zero]
    intro h
    have h1 := DFunLike.congr_fun h (single 1 (1 : ℝ))
    rw [tail_atom_not_mem 1 (by decide), zero_apply] at h1
    exact atom_ne_zero 1 h1
  · rw [neg_add_cancel, negRatio, tailRatio_not_mem, zeroRatio]; norm_num

/-- `colRatio_add_of_comp_split`, dropping `hS`: `Z = P_H`, `S = -P_H`, column `0`. -/
theorem drop_hS_split :
    (headProj H0 : X →L[ℝ] X) ∘L tailProj H0 = 0 ∧
      (-headProj H0 : X →L[ℝ] X) ∘L headProj H0 ≠ 0 ∧
      colRatio ((headProj H0 : X →L[ℝ] X) + -headProj H0 : X →L[ℝ] X) 0 ≠
        colRatio (headProj H0 : X →L[ℝ] X) 0 +
          colRatio (-headProj H0 : X →L[ℝ] X) 0 := by
  refine ⟨headProj_comp_tailProj H0, ?_, ?_⟩
  · rw [ContinuousLinearMap.neg_comp, headProj_comp_headProj, neg_ne_zero]
    intro h
    have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
    rw [head_atom_mem 0 (Finset.mem_singleton_self 0), zero_apply] at h0
    exact atom_ne_zero 0 h0
  · rw [add_neg_cancel, negRatio, headRatio_mem, zeroRatio]; norm_num

/-! ### T33: one countermodel per hypothesis (TARGET_SHEET §7); `I = J = ℤ`, weights `1`,
`Hs = H = {0}`. -/

/-- Dropping `hPZ`: `Z = (e₀ ↦ e₁)`, `S = 0`, `T = -Z`; `0` against `2`. -/
theorem T33_drop_hPZ :
    (headProj H0 : X →L[ℝ] X) ∘L rk 0 1 ≠ rk 0 1 ∧ rk 0 1 ∘L (tailProj H0 : X →L[ℝ] X) = 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧ (0 : X →L[ℝ] X) ∘L
        (headProj H0 : X →L[ℝ] X) = 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (-rk 0 1) = -rk 0 1 ∧
      ‖rk 0 1 + 0 + -rk 0 1‖ ≠ ⨆ i, (colRatio (rk 0 1) i + colRatio (0 : X →L[ℝ] X) i +
        colRatio (-rk 0 1) i) := by
  refine ⟨rk_not_head 0 1 one_ne_zero, rk_kill_tail 1, ContinuousLinearMap.comp_zero _,
    ContinuousLinearMap.zero_comp _, by rw [ContinuousLinearMap.comp_neg, rk_tail 0 1 one_ne_zero],
    ?_⟩
  rw [add_zero, add_neg_cancel, norm_zero, iSup_triple 0 _ _ _ fun j => by
    simp only [negRatio, rkRatio, zeroRatio]; split_ifs <;> norm_num]
  norm_num

/-- Dropping `hZQ`: `Z = (e₁ ↦ e₀)`, `S = -Z`, `T = 0`; `0` against `2`. -/
theorem T33_drop_hZQ :
    (headProj H0 : X →L[ℝ] X) ∘L rk 1 0 = rk 1 0 ∧ rk 1 0 ∘L (tailProj H0 : X →L[ℝ] X) ≠ 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L (-rk 1 0) = -rk 1 0 ∧ (-rk 1 0) ∘L
        (headProj H0 : X →L[ℝ] X) = 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧
      ‖rk 1 0 + -rk 1 0 + 0‖ ≠ ⨆ i, (colRatio (rk 1 0) i + colRatio (-rk 1 0) i +
        colRatio (0 : X →L[ℝ] X) i) := by
  refine ⟨rk_head 1, rk_not_kill_tail 1 0 one_ne_zero,
    by rw [ContinuousLinearMap.comp_neg, rk_head 1],
    by rw [ContinuousLinearMap.neg_comp, rk_kill_head 1 0 one_ne_zero, neg_zero],
    ContinuousLinearMap.comp_zero _, ?_⟩
  rw [add_zero, add_neg_cancel, norm_zero, iSup_triple 1 _ _ _ fun j => by
    simp only [negRatio, rkRatio, zeroRatio]; split_ifs <;> norm_num]
  norm_num

/-- Dropping `hPS`: `Z = 0`, `S = (e₁ ↦ e₁)`, `T = -S`; `0` against `2`. -/
theorem T33_drop_hPS :
    (headProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧ (0 : X →L[ℝ] X) ∘L
      (tailProj H0 : X →L[ℝ] X) = 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L rk 1 1 ≠ rk 1 1 ∧ rk 1 1 ∘L (headProj H0 : X →L[ℝ] X) = 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (-rk 1 1) = -rk 1 1 ∧
      ‖0 + rk 1 1 + -rk 1 1‖ ≠ ⨆ i, (colRatio (0 : X →L[ℝ] X) i + colRatio (rk 1 1) i +
        colRatio (-rk 1 1) i) := by
  refine ⟨ContinuousLinearMap.comp_zero _, ContinuousLinearMap.zero_comp _,
    rk_not_head 1 1 one_ne_zero, rk_kill_head 1 1 one_ne_zero,
    by rw [ContinuousLinearMap.comp_neg, rk_tail 1 1 one_ne_zero], ?_⟩
  rw [zero_add, add_neg_cancel, norm_zero, iSup_triple 1 _ _ _ fun j => by
    simp only [negRatio, rkRatio, zeroRatio]; split_ifs <;> norm_num]
  norm_num

/-- Dropping `hSP`: `Z = -S`, `S = (e₀ ↦ e₀)`, `T = 0`; `0` against `2`. -/
theorem T33_drop_hSP :
    (headProj H0 : X →L[ℝ] X) ∘L (-rk 0 0) = -rk 0 0 ∧ (-rk 0 0) ∘L (tailProj H0 : X →L[ℝ] X) = 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L rk 0 0 = rk 0 0 ∧ rk 0 0 ∘L (headProj H0 : X →L[ℝ] X) ≠ 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧
      ‖-rk 0 0 + rk 0 0 + 0‖ ≠ ⨆ i, (colRatio (-rk 0 0) i + colRatio (rk 0 0) i +
        colRatio (0 : X →L[ℝ] X) i) := by
  refine ⟨by rw [ContinuousLinearMap.comp_neg, rk_head 0],
    by rw [ContinuousLinearMap.neg_comp, rk_kill_tail 0, neg_zero], rk_head 0,
    rk_not_kill_head 0, ContinuousLinearMap.comp_zero _, ?_⟩
  rw [add_zero, neg_add_cancel, norm_zero, iSup_triple 0 _ _ _ fun j => by
    simp only [negRatio, rkRatio, zeroRatio]; split_ifs <;> norm_num]
  norm_num

/-- Dropping `hT`: `Z = -T`, `S = 0`, `T = (e₀ ↦ e₀)`; `0` against `2`. -/
theorem T33_drop_hT :
    (headProj H0 : X →L[ℝ] X) ∘L (-rk 0 0) = -rk 0 0 ∧ (-rk 0 0) ∘L (tailProj H0 : X →L[ℝ] X) = 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧ (0 : X →L[ℝ] X) ∘L
        (headProj H0 : X →L[ℝ] X) = 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L rk 0 0 ≠ rk 0 0 ∧
      ‖-rk 0 0 + 0 + rk 0 0‖ ≠ ⨆ i, (colRatio (-rk 0 0) i + colRatio (0 : X →L[ℝ] X) i +
        colRatio (rk 0 0) i) := by
  refine ⟨by rw [ContinuousLinearMap.comp_neg, rk_head 0],
    by rw [ContinuousLinearMap.neg_comp, rk_kill_tail 0, neg_zero],
    ContinuousLinearMap.comp_zero _, ContinuousLinearMap.zero_comp _, rk_not_tail 0, ?_⟩
  rw [add_zero, neg_add_cancel, norm_zero, iSup_triple 0 _ _ _ fun j => by
    simp only [negRatio, rkRatio, zeroRatio]; split_ifs <;> norm_num]
  norm_num

/-! ### Positive sides of the mathematical-negative controls CTL-D1, CTL-D2, CTL-D3 -/

/-- CTL-D1: `P_H ∘ P_H = Q_H` is false (`H = {0}`; at `e₀` the sides are `e₀` and `0`). -/
theorem ctl_D1_witness :
    (headProj H0 : X →L[ℝ] X) ∘L headProj H0 ≠ tailProj H0 := by
  intro h
  have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
  rw [ContinuousLinearMap.comp_apply, head_atom_mem 0 (Finset.mem_singleton_self 0),
    head_atom_mem 0 (Finset.mem_singleton_self 0),
      tail_atom_mem 0 (Finset.mem_singleton_self 0)] at h0
  exact atom_ne_zero 0 h0

/-- CTL-D2: T33 without the summand `colRatio S i` is false (`Z = T = 0`, `S = (e₁ ↦ e₀)`):
the hypotheses hold and `‖S‖ = 1` against `0`. -/
theorem ctl_D2_witness :
    (headProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧ (0 : X →L[ℝ] X) ∘L
      (tailProj H0 : X →L[ℝ] X) = 0 ∧
      (headProj H0 : X →L[ℝ] X) ∘L rk 1 0 = rk 1 0 ∧ rk 1 0 ∘L (headProj H0 : X →L[ℝ] X) = 0 ∧
      (tailProj H0 : X →L[ℝ] X) ∘L (0 : X →L[ℝ] X) = 0 ∧
      ‖(0 : X →L[ℝ] X) + rk 1 0 + 0‖ ≠
        ⨆ i, (colRatio (0 : X →L[ℝ] X) i + colRatio (0 : X →L[ℝ] X) i) := by
  refine ⟨ContinuousLinearMap.comp_zero _, ContinuousLinearMap.zero_comp _, rk_head 1,
    rk_kill_head 1 0 one_ne_zero, ContinuousLinearMap.comp_zero _, ?_⟩
  simp only [zeroRatio, add_zero, zero_add, ciSup_const]
  rw [opNorm_eq_iSup_cols, iSup_congr (rkRatio 1 0), iSup_indicator 1 1 zero_le_one]
  norm_num

/-- CTL-D3: the value law `Q_H = 1 + P_H` is false (`H = {0}`; at `e₀`: `0` against `2 e₀`). -/
theorem ctl_D3_witness : (tailProj H0 : X →L[ℝ] X) ≠ 1 + headProj H0 := by
  intro h
  have h0 := DFunLike.congr_fun h (single 0 (1 : ℝ))
  rw [tail_atom_mem 0 (Finset.mem_singleton_self 0), add_apply, one_apply_eq_self,
    head_atom_mem 0 (Finset.mem_singleton_self 0)] at h0
  have h2 := congrArg norm h0
  rw [norm_zero, ← two_smul ℝ, norm_smul, atomNorm] at h2
  norm_num at h2

end RadiiPolynomial.Tests.FZ.HeadTail
