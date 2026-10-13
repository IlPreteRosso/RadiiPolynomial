import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import RadiiPolynomial.Algebra.Ring.HeadTailIdentities
import RadiiPolynomial.Operators.HeadTail
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis

/-!
# L001 tests (T42): nonvacuity of the head/tail layer

* The eleven S027 `Vacuity` theorems (`HeadTailColumns.lean` :388–:455, sha256 614b7107…)
  ported to the library API: carrier `lpOneAlg ℤ (geomFiberZ ℝ ν)`, head
  `Finset.Icc (-1) 1`. Old → new symbols: `P_H (H 1)` ↦ `lpOneAlg.headProj (Finset.Icc (-1) 1)`,
  `1 - P_H` ↦ `1 - headProj` (`= tailProj` by `tailProj_eq_one_sub`),
  `composition_identity` ↦ `HeadTail.composition_identity` (hypothesis `IsIdempotentElem P`).
* Nonvacuity witnesses for T33 (all five hypotheses with `Z, S, T ≠ 0`), T25 (a nonzero symbol
  vanishing on the head), T35 and T36 (all hypotheses with both sides nonzero, 2×2 matrices).
* The S027 checker composition tests `mixedComposition` (:606) and `mixedCompositeNonzero`
  (:632), which need `Operators/HeadTail`.

Kernel-only; imported by nothing.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.HeadTail

open RadiiPolynomial lpOneAlg HeadTail

/-! ### The eleven S027 vacuity theorems -/

section Vacuity

variable (ν : PosReal)

/-- Every Fourier unit atom is nonzero. -/
theorem vacuity_single_ne_zero (j : ℤ) :
    (single j (1 : ℝ) : lpOneAlg ℤ (geomFiberZ ℝ ν)) ≠ 0 := by
  intro h
  have h1 := congr_arg (fun z : lpOneAlg ℤ (geomFiberZ ℝ ν) => toRealSeq z j) h
  rw [toRealSeq_single, ite_eq_left rfl, toRealSeq_zero, Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem vacuity_one_ne_zero :
    (1 : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν)) ≠ 0 := by
  intro h
  apply vacuity_single_ne_zero ν 0
  exact DFunLike.congr_fun h (single 0 1)

/-- Nontrivial T4 data with a nonempty head and a nonzero total. -/
theorem vacuity_T4 :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    P ∘L P = P ∧ (1 - P) ∘L (1 - P) = 1 - P ∧ P + (1 - P) = 1 ∧ P + (1 - P) ≠ 0 := by
  dsimp only
  exact ⟨headProj_comp_headProj _, tailProj_comp_tailProj _, headProj_add_tailProj _,
    fun h => vacuity_one_ne_zero ν ((headProj_add_tailProj _).symm.trans h)⟩

/-- A tail atom witnesses that the complement is nonzero. -/
theorem vacuity_tail_atom :
    (1 - headProj (Finset.Icc (-1) 1) : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] _)
      (single 2 (1 : ℝ)) = single 2 1 :=
  (tailProj_single _ 2 1).trans (ite_eq_right (by decide))

theorem vacuity_tail_ne_zero :
    (1 - headProj (Finset.Icc (-1) 1) :
      lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν)) ≠ 0 := by
  intro h
  apply vacuity_single_ne_zero ν 2
  exact (vacuity_tail_atom ν).symm.trans (DFunLike.congr_fun h (single 2 1))

/-- The T5 composite with `M = L = 1` is the nonzero complement. -/
theorem vacuity_T5_composite :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    ((1 ∘L P + (1 - P)) ∘L (P ∘L 1 ∘L (1 - P) + (1 - P) ∘L 1)) = 1 - P := by
  dsimp only
  rw [composition_identity (headProj _) 1 (1 - headProj _) 1 (isIdempotentElem_headProj _)
    (tailProj_comp_headProj _)]
  simp only [← ContinuousLinearMap.mul_def, one_mul, mul_one]
  rw [ContinuousLinearMap.mul_def, ← tailProj_eq_one_sub, headProj_comp_tailProj, zero_add]

/-- The hypotheses of T5 hold for the nontrivial split. -/
theorem vacuity_T5_hypotheses :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    IsIdempotentElem P ∧ (1 - P) ∘L P = 0 :=
  ⟨isIdempotentElem_headProj _, tailProj_comp_headProj _⟩

theorem vacuity_T5_composite_ne_zero :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    ((1 ∘L P + (1 - P)) ∘L (P ∘L 1 ∘L (1 - P) + (1 - P) ∘L 1)) ≠ 0 := by
  dsimp only
  rw [vacuity_T5_composite ν]
  exact vacuity_tail_ne_zero ν

omit ν in
theorem vacuity_sigma_unit : ‖(-1 : ℝ)‖ = 1 := by
  rw [norm_neg, norm_one]

/-- The model-discrepancy hypothesis is inhabited by the signed case `σ = -1`. -/
theorem vacuity_T5_signed_hZ :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    let composite := (1 ∘L P + (1 - P)) ∘L (P ∘L 1 ∘L (1 - P) + (1 - P) ∘L 1)
    (-1 : ℝ) • composite = (-1 : ℝ) • composite := rfl

theorem vacuity_T5_signed_norm :
    let P : lpOneAlg ℤ (geomFiberZ ℝ ν) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ ν) :=
      headProj (Finset.Icc (-1) 1)
    ‖(-1 : ℝ) • ((1 ∘L P + (1 - P)) ∘L (P ∘L 1 ∘L (1 - P) + (1 - P) ∘L 1))‖ = ‖1 - P‖ := by
  dsimp only
  rw [vacuity_T5_composite ν, norm_smul, vacuity_sigma_unit, one_mul]

end Vacuity

/-! ### Unit-weight carrier and rank-one maps (vacuity-local copies) -/

/-- The unit weight. -/
def vacNuOne : PosReal := ⟨1, by norm_num⟩

/-- The unit-weight carrier `ℓ¹(ℤ)`. -/
abbrev VacX := lpOneAlg ℤ (geomFiberZ ℝ vacNuOne)

theorem vacOneWeight (j : ℤ) :
    FiberTrivialization.weight (E := geomFiberZ ℝ vacNuOne) j = 1 := by
  rw [geomFiberZ_weight]; change (1 : ℝ) ^ j.natAbs = 1; exact one_pow _

theorem vacAtomNorm (j : ℤ) : ‖(single j (1 : ℝ) : VacX)‖ = 1 := by
  rw [norm_single, norm_one, one_mul, vacOneWeight]

theorem vacRankBound (k l j : ℤ) :
    ‖(if j = k then single l (1 : ℝ) else 0 : VacX)‖ ≤
      1 * FiberTrivialization.weight (E := geomFiberZ ℝ vacNuOne) j := by
  rw [vacOneWeight, one_mul]; split_ifs
  · rw [vacAtomNorm]
  · rw [norm_zero]; norm_num

/-- The rank-one map `e_k ↦ e_l`. -/
def vacRk (k l : ℤ) : VacX →L[ℝ] VacX :=
  liftCLM (fun j => if j = k then single l 1 else 0) 1 (vacRankBound k l)

theorem vacRkAtom (k l j : ℤ) :
    vacRk k l (single j (1 : ℝ)) = if j = k then single l 1 else 0 := by
  rw [vacRk, liftCLM_single, one_smul]

theorem vacRkRatio (k l j : ℤ) : colRatio (vacRk k l) j = if j = k then 1 else 0 := by
  rw [colRatio, vacRkAtom, vacOneWeight, div_one]; split_ifs
  · rw [vacAtomNorm]
  · exact norm_zero

theorem vacRk_ne_zero (k l : ℤ) : vacRk k l ≠ 0 := by
  intro h
  have hk := DFunLike.congr_fun h (single k (1 : ℝ))
  rw [vacRkAtom, ite_eq_left rfl, zero_apply] at hk
  exact vacuity_single_ne_zero vacNuOne l hk

/-- The head `{0}`. -/
abbrev vacH0 : Finset ℤ := {0}

theorem vacRk_head (k : ℤ) : (headProj vacH0 : VacX →L[ℝ] VacX) ∘L vacRk k 0 = vacRk k 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, vacRkAtom]; split_ifs
  · rw [headProj_single, ite_eq_left (Finset.mem_singleton_self 0)]
  · exact map_zero _

theorem vacRk_tail (k : ℤ) : (tailProj vacH0 : VacX →L[ℝ] VacX) ∘L vacRk k 1 = vacRk k 1 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, vacRkAtom]; split_ifs
  · rw [tailProj_single, ite_eq_right (by decide)]
  · exact map_zero _

theorem vacRk_kill_tail (l : ℤ) : vacRk 0 l ∘L (tailProj vacH0 : VacX →L[ℝ] VacX) = 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, zero_apply, tailProj_single]
  split_ifs with hj
  · exact map_zero _
  · rw [vacRkAtom, ite_eq_right (by simpa using hj)]

theorem vacRk_kill_head (l : ℤ) : vacRk 1 l ∘L (headProj vacH0 : VacX →L[ℝ] VacX) = 0 := by
  refine continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, zero_apply, headProj_single]
  split_ifs with hj
  · rw [vacRkAtom, ite_eq_right]; rintro rfl; exact absurd hj (by decide)
  · exact map_zero _

/-! ### T33 nonvacuity: all five hypotheses with `Z, S, T ≠ 0` -/

/-- `Z = (e₀ ↦ e₀)`, `S = (e₁ ↦ e₀)`, `T = (e₀ ↦ e₁)`, `Hs = H = {0}`: every hypothesis of
`opNorm_joint_eq_iSup` holds and all three maps are nonzero. -/
theorem vacuity_T33_hypotheses :
    (headProj vacH0 : VacX →L[ℝ] VacX) ∘L vacRk 0 0 = vacRk 0 0 ∧
      vacRk 0 0 ∘L (tailProj vacH0 : VacX →L[ℝ] VacX) = 0 ∧
      (headProj vacH0 : VacX →L[ℝ] VacX) ∘L vacRk 1 0 = vacRk 1 0 ∧
      vacRk 1 0 ∘L (headProj vacH0 : VacX →L[ℝ] VacX) = 0 ∧
      (tailProj vacH0 : VacX →L[ℝ] VacX) ∘L vacRk 0 1 = vacRk 0 1 ∧
      vacRk 0 0 ≠ 0 ∧ vacRk 1 0 ≠ 0 ∧ vacRk 0 1 ≠ 0 :=
  ⟨vacRk_head 0, vacRk_kill_tail 0, vacRk_head 1, vacRk_kill_head 0, vacRk_tail 0,
    vacRk_ne_zero 0 0, vacRk_ne_zero 1 0, vacRk_ne_zero 0 1⟩

/-- The T33 conclusion on the witness: `‖Z + S + T‖ = 2`. -/
theorem vacuity_T33_value : ‖vacRk 0 0 + vacRk 1 0 + vacRk 0 1‖ = 2 := by
  obtain ⟨hPZ, hZQ, hPS, hSP, hT, -⟩ := vacuity_T33_hypotheses
  rw [opNorm_joint_eq_iSup vacH0 vacH0 _ _ _ hPZ hZQ hPS hSP hT]
  simp only [vacRkRatio]
  refine le_antisymm (Real.iSup_le (fun j => by split_ifs <;> first | omega | norm_num)
    (by norm_num)) ?_
  refine le_ciSup_of_le ⟨2, ?_⟩ 0 (by norm_num)
  rintro _ ⟨j, rfl⟩; dsimp only; split_ifs <;> first | omega | norm_num

/-! ### T25 nonvacuity: a nonzero symbol vanishing on the head -/

/-- The symbol `r = 1 - 1_{0}`. -/
def vacR : ℤ → ℝ := fun j => if j = 0 then 0 else 1

theorem vacR_bound (j : ℤ) : ‖vacR j‖ ≤ 1 := by
  unfold vacR; split_ifs <;> simp

/-- `r` vanishes on `H = {0}`, `r ≠ 0`, `D_r ≠ 0`, and both faces of T25 hold with the
tail face nonzero. -/
theorem vacuity_T25 :
    (∀ j ∈ vacH0, vacR j = 0) ∧ vacR ≠ 0 ∧
      (diagCLM vacR 1 vacR_bound : VacX →L[ℝ] VacX) ≠ 0 ∧
      (headProj vacH0 : VacX →L[ℝ] VacX) ∘L diagCLM vacR 1 vacR_bound = 0 ∧
      (tailProj vacH0 : VacX →L[ℝ] VacX) ∘L diagCLM vacR 1 vacR_bound =
        diagCLM vacR 1 vacR_bound := by
  have hr0 : ∀ j ∈ vacH0, vacR j = 0 := fun j hj => by
    rw [Finset.mem_singleton] at hj; subst hj; rfl
  refine ⟨hr0, fun h => ?_, fun h => ?_, headProj_comp_diagCLM _ _ _ _ hr0,
    tailProj_comp_diagCLM _ _ _ _ hr0⟩
  · have h1 := congrFun h 1
    simp [vacR] at h1
  · have h1 := DFunLike.congr_fun h (single 1 (1 : ℝ))
    rw [diagCLM_single, zero_apply, vacR, ite_eq_right (by decide), one_mul] at h1
    exact vacuity_single_ne_zero vacNuOne 1 h1

/-! ### T35/T36 nonvacuity in `Matrix (Fin 2) (Fin 2) ℚ` -/

/-- `E₁₁`. -/
def vacE11 : Matrix (Fin 2) (Fin 2) ℚ := Matrix.single 0 0 1

/-- `E₁₂`. -/
def vacE12 : Matrix (Fin 2) (Fin 2) ℚ := Matrix.single 0 1 1

/-- `E₂₂`. -/
def vacE22 : Matrix (Fin 2) (Fin 2) ℚ := Matrix.single 1 1 1

theorem vacE11_idem : IsIdempotentElem vacE11 := by
  rw [IsIdempotentElem, vacE11, Matrix.single_mul_single_same, mul_one]

theorem vac_one_sub_E11 : (1 : Matrix (Fin 2) (Fin 2) ℚ) - vacE11 = vacE22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vacE11, vacE22]

theorem vacE12_ne_zero : vacE12 ≠ 0 := fun h => by
  simpa [vacE12] using congrFun (congrFun h 0) 1

theorem vacE11_ne_zero : vacE11 ≠ 0 := fun h => by
  simpa [vacE11] using congrFun (congrFun h 0) 0

/-- T35 with `P = E₁₁`, `Λ = 1`, `G = E₂₂`, `M = 1`, `L = E₁₂`: all hypotheses hold and both
sides equal `-E₁₂ ≠ 0`. -/
theorem vacuity_T35 :
    IsIdempotentElem vacE11 ∧ Commute (1 : Matrix (Fin 2) (Fin 2) ℚ) vacE11 ∧
      vacE22 * vacE11 = 0 ∧
      -(1 * vacE11 * vacE12 * (1 - vacE11) + vacE22 * (1 - vacE11) * vacE12) ≠ 0 ∧
      (1 * vacE11 + vacE22) * ((vacE11 * (1 + vacE12) * vacE11 +
        (1 - vacE11) * 1 * (1 - vacE11)) - (1 + vacE12)) ≠ 0 := by
  have hG : vacE22 * vacE11 = 0 := by simp [vacE22, vacE11]
  have hR : -(1 * vacE11 * vacE12 * (1 - vacE11) + vacE22 * (1 - vacE11) * vacE12) ≠ 0 := by
    have e : 1 * vacE11 * vacE12 * (1 - vacE11) + vacE22 * (1 - vacE11) * vacE12 = vacE12 := by
      rw [vac_one_sub_E11]; simp [vacE11, vacE12, vacE22]
    rw [e, neg_ne_zero]
    exact vacE12_ne_zero
  refine ⟨vacE11_idem, Commute.one_left _, hG, hR, ?_⟩
  rw [defect_identity_ring _ _ _ _ _ vacE11_idem (Commute.one_left _) hG]
  exact hR

/-- T36 with `P = E₁₁`, `G = E₂₂`, `Λ = 1`, `M = L = 0`: all hypotheses hold and both sides
equal `E₁₁ ≠ 0`. -/
theorem vacuity_T36 :
    IsIdempotentElem vacE11 ∧ vacE22 * vacE11 = 0 ∧
      vacE22 * 1 * (1 - vacE11) = 1 - vacE11 ∧
      vacE11 - 0 * vacE11 * (1 + 0) * vacE11 ≠ 0 ∧
      1 - (0 * vacE11 + vacE22) * (vacE11 * (1 + 0) * vacE11 +
        (1 - vacE11) * 1 * (1 - vacE11)) ≠ 0 := by
  have hG : vacE22 * vacE11 = 0 := by simp [vacE22, vacE11]
  have hGΛ : vacE22 * 1 * (1 - vacE11) = 1 - vacE11 := by
    rw [vac_one_sub_E11, mul_one, vacE22, Matrix.single_mul_single_same, mul_one]
  have hR : vacE11 - 0 * vacE11 * (1 + 0) * vacE11 ≠ 0 := by
    rw [zero_mul, zero_mul, zero_mul, sub_zero]; exact vacE11_ne_zero
  refine ⟨vacE11_idem, hG, hGΛ, hR, ?_⟩
  rw [inverse_defect_ring _ _ _ _ _ vacE11_idem hG hGΛ]
  exact hR

/-! ### S027 checker composition tests (S027T :574–:579, :606, :632) -/

/-- Target weight `3` (vacuity-local copy of the checker's `nuThree`). -/
def vacNuThree : PosReal := ⟨3, by norm_num⟩

abbrev VacTarget3 := lpOneAlg ℤ (geomFiberZ ℝ vacNuThree)

def vacMixedP : VacTarget3 →L[ℝ] VacTarget3 := headProj (Finset.Icc (-1) 1)

def vacMixedQ : VacTarget3 →L[ℝ] VacTarget3 := tailProj (Finset.Icc (-1) 1)

def mixedM : VacTarget3 →L[ℝ] VacTarget3 := 1

def mixedR : VacTarget3 →L[ℝ] VacTarget3 := vacMixedQ

def mixedInternalL : VacTarget3 →L[ℝ] VacTarget3 := 1

def mixedComposite : VacTarget3 →L[ℝ] VacTarget3 :=
  (mixedM ∘L vacMixedP + mixedR) ∘L
    (vacMixedP ∘L mixedInternalL ∘L vacMixedQ + vacMixedQ ∘L mixedInternalL)

theorem mixedComposition : mixedComposite = vacMixedQ := by
  rw [mixedComposite, mixedM, mixedR, mixedInternalL, vacMixedQ, vacMixedP, tailProj_eq_one_sub,
    composition_identity (headProj _) 1 (1 - headProj _) 1 (isIdempotentElem_headProj _)
      (tailProj_comp_headProj _)]
  simp only [← ContinuousLinearMap.mul_def, one_mul, mul_one]
  rw [ContinuousLinearMap.mul_def, ← tailProj_eq_one_sub, headProj_comp_tailProj, zero_add]

theorem mixedCompositeNonzero : mixedComposite ≠ 0 := by
  rw [mixedComposition]
  intro h
  have hi := DFunLike.congr_fun h (single 2 (1 : ℝ))
  rw [vacMixedQ, tailProj_single, ite_eq_right (by decide), zero_apply] at hi
  exact vacuity_single_ne_zero vacNuThree 2 hi

end RadiiPolynomial.Tests.FZ.HeadTail
