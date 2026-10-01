import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Columns
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import Mathlib.Algebra.Ring.Idempotent

/-!
# Bounded scalar diagonals, finite-head projections and head/tail aggregation

On a weighted ℓ¹ space `lpOneAlg J G` (any fibers, no completeness), a scalar symbol
`r : J → 𝕜` with `‖r j‖ ≤ C` acts fiberwise, `(D_r y)_j = r_j • y_j`, as a bounded
operator `diagCLM r C hr` with `‖D_r y‖ ≤ C ‖y‖`. The indicator symbol of a finite head
`H : Finset J` gives the head projection `headProj H = D_{1_H}` and its complement
`tailProj H = 1 - headProj H`: complementary idempotents whose ranges are the vectors
supported on `H`, respectively off `H`.

Head-supported and tail-supported vectors add in norm (ℓ¹ additivity). Through the column
principle of `WeightedL1/Columns.lean` this gives the exact aggregation laws: a head-valued
`S` and a tail-valued `T` add column-wise, `colRatio (S + T) i = colRatio S i + colRatio T i`,
and `‖S + T‖ = ⨆ i, (colRatio S i + colRatio T i)`; the joint form adds a head block `Z`
that vanishes on the source tail and an `S` that vanishes on the source head.

Main declarations:
* `lpOneAlg.diagCLM`, `diagCLM_apply`, `norm_diagCLM_apply_le`, `norm_diagCLM_le`,
  `toRealSeq_diagCLM`, `diagCLM_single` — the bounded diagonal and its faces.
* `lpOneAlg.headSymbol`, `headProj`, `tailProj` (with the simp face `tailProj_eq_one_sub`).
* `lpOneAlg.isIdempotentElem_headProj` and the projection identities.
* `lpOneAlg.headProj_apply_eq_self_iff`, `tailProj_apply_eq_self_iff` — the ranges.
* `lpOneAlg.norm_add_of_head_tail` — ℓ¹ additivity of head + tail.
* `lpOneAlg.opNorm_add_eq_iSup`, `opNorm_add_eq_iSup_of_head_zero`,
  `opNorm_joint_eq_iSup` — the exact aggregate operator norms.
-/

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

/-! ### The bounded diagonal -/

/-- Fiberwise multiplication by a bounded symbol preserves `ℓ¹` membership
(construction internal of `diagCLM`). -/
private theorem memℓp_smul_diag {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) :
    Memℓp (fun j => r j • x j) 1 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact ((summable_norm x).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun j => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hr j) (norm_nonneg _))

/-- The norm bound of the fiberwise product (construction internal of `diagCLM`). -/
private theorem norm_smul_diag_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) :
    ‖(⟨⟨fun j => r j • x j, memℓp_smul_diag r C hr x⟩⟩ : lpOneAlg J G)‖ ≤ C * ‖x‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, ← tsum_mul_left]
  exact (summable_norm _).tsum_le_tsum
    (fun j => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hr j) (norm_nonneg _)))
    ((summable_norm x).mul_left C)

/-- **(T10, L001.)** The bounded scalar diagonal `(D_r y)_j = r_j • y_j` on `lpOneAlg J G`,
for a symbol with `‖r j‖ ≤ C`. Any fibers; no completeness, no scalar trivialization. -/
def diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  LinearMap.mkContinuous
    { toFun := fun x : lpOneAlg J G => ⟨⟨fun j => r j • x j, memℓp_smul_diag r C hr x⟩⟩
      map_add' := fun x y => ext fun j => smul_add (r j) (x j) (y j)
      map_smul' := fun c x => ext fun j => smul_comm (r j) c (x j) }
    C (norm_smul_diag_le r C hr)

/-- **(T11, L001.)** The fiber action of the diagonal (the value contract of `diagCLM`). -/
theorem diagCLM_apply {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) (j : J) :
    diagCLM r C hr x j = r j • x j :=
  rfl

/-- **(T12, L001.)** Pointwise bound of the diagonal: `‖D_r x‖ ≤ C ‖x‖`. -/
theorem norm_diagCLM_apply_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) :
    ‖diagCLM r C hr x‖ ≤ C * ‖x‖ :=
  norm_smul_diag_le r C hr x

/-- **(T13, L001.)** Operator-norm bound of the diagonal: `‖D_r‖ ≤ C` for `0 ≤ C`. -/
theorem norm_diagCLM_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hC : 0 ≤ C) :
    ‖(diagCLM r C hr : lpOneAlg J G →L[𝕜] lpOneAlg J G)‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_diagCLM_apply_le r C hr)

/-- **(T14, L001.)** Coefficient face of the diagonal: `(D_r x)_j = r_j x_j` in the scalar
trivialization. -/
theorem toRealSeq_diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) (j : J) :
    toRealSeq (diagCLM r C hr x) j = r j * toRealSeq x j :=
  lpAlgSmulCompat.toReal_smul j (r j) (x j)

/-- **(T15, L001.)** Atom face of the diagonal: `D_r (x e_j) = (r_j x) e_j`. -/
theorem diagCLM_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (j : J) (x : 𝕜) :
    diagCLM r C hr (single j x : lpOneAlg J G) = single j (r j * x) := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_diagCLM, toRealSeq_single, toRealSeq_single]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-! ### Finite-head projections -/

/-- **(T16, L001.)** The indicator symbol of a finite head `H`. -/
def headSymbol {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
    (H : Finset J) (j : J) : 𝕜 :=
  if j ∈ H then 1 else 0

/-- **(T16, L001.)** The head symbol has norm at most one. -/
theorem norm_headSymbol_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
    (H : Finset J) (j : J) : ‖(headSymbol H j : 𝕜)‖ ≤ 1 := by
  unfold headSymbol
  split_ifs <;> simp

/-- **(T16, L001.)** The head symbol is the `Set.indicator` of the head. -/
theorem headSymbol_eq_indicator {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
    (H : Finset J) : (headSymbol H : J → 𝕜) = Set.indicator (↑H : Set J) (fun _ => (1 : 𝕜)) := by
  funext j
  simp only [headSymbol, Set.indicator_apply, Finset.mem_coe]

/-- **(T17, L001.)** The head projection `P_H = D_{1_H}`: keep the coordinates in `H`. -/
def headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  diagCLM (headSymbol H) 1 (norm_headSymbol_le H)

/-- **(T18, L001.)** The tail projection `Q_H = 1 - P_H`. -/
def tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  1 - headProj H

/-- **(T18, L001.)** The tail projection is the literal complement of the head projection
(the simp normal form). -/
@[simp] theorem tailProj_eq_one_sub {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) = 1 - headProj H :=
  rfl

/-- **(T19, L001.)** Coefficient face of the head projection. -/
theorem toRealSeq_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) (j : J) :
    toRealSeq (headProj (𝕜 := 𝕜) H x) j = if j ∈ H then toRealSeq x j else 0 := by
  rw [headProj, toRealSeq_diagCLM, headSymbol]
  split_ifs <;> simp only [one_mul, zero_mul]

/-- **(T19, L001.)** Coefficient face of the tail projection. -/
theorem toRealSeq_tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) (j : J) :
    toRealSeq (tailProj (𝕜 := 𝕜) H x) j = if j ∈ H then 0 else toRealSeq x j := by
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, toRealSeq_sub, Pi.sub_apply,
    toRealSeq_headProj]
  split_ifs <;> simp only [sub_self, sub_zero]

/-- **(T20, L001.)** Atom face of the head projection. -/
theorem headProj_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (j : J) (x : 𝕜) :
    headProj (𝕜 := 𝕜) H (single j x : lpOneAlg J G) = if j ∈ H then single j x else 0 := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_headProj, toRealSeq_single]
  by_cases hkj : k = j
  · subst hkj
    split_ifs <;> simp_all [toRealSeq_single, toRealSeq_zero]
  · split_ifs <;> simp [hkj, toRealSeq_single, toRealSeq_zero]

/-- **(T20, L001.)** Atom face of the tail projection. -/
theorem tailProj_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (j : J) (x : 𝕜) :
    tailProj (𝕜 := 𝕜) H (single j x : lpOneAlg J G) = if j ∈ H then 0 else single j x := by
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, headProj_single]
  split_ifs <;> simp only [sub_self, sub_zero]

/-- **(T21, L001.)** The head projection is an idempotent of the operator ring. -/
theorem isIdempotentElem_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : IsIdempotentElem (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) := by
  refine ContinuousLinearMap.ext fun x => ext fun j => ?_
  rw [mul_apply_eq_comp, headProj, diagCLM_apply, diagCLM_apply, smul_smul, headSymbol]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- **(T22, L001.)** `P_H ∘ P_H = P_H`. -/
theorem headProj_comp_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L headProj H = headProj H :=
  (ContinuousLinearMap.mul_def _ _).symm.trans (isIdempotentElem_headProj H).eq

/-- **(T22, L001.)** `P_H ∘ Q_H = 0`. -/
theorem headProj_comp_tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L tailProj H = 0 :=
  (ContinuousLinearMap.mul_def _ _).symm.trans (isIdempotentElem_headProj H).mul_one_sub_self

/-- **(T22, L001.)** `Q_H ∘ P_H = 0`. -/
theorem tailProj_comp_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) :
    (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L headProj H = 0 :=
  (ContinuousLinearMap.mul_def _ _).symm.trans (isIdempotentElem_headProj H).one_sub_mul_self

/-- **(T22, L001.)** `Q_H ∘ Q_H = Q_H`. -/
theorem tailProj_comp_tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) :
    (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L tailProj H = tailProj H :=
  (ContinuousLinearMap.mul_def _ _).symm.trans (isIdempotentElem_headProj H).one_sub.eq

/-- **(T22, L001.)** `P_H + Q_H = 1`. -/
theorem headProj_add_tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) + tailProj H = 1 :=
  add_sub_cancel _ _

/-- **(T24, L001; optional.)** Range of the head projection, fiber form: the vectors
vanishing off `H`. -/
theorem headProj_apply_eq_self_iff_fiber {𝕜 : Type*} [NormedField 𝕜] {J : Type*}
    {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [DecidableEq J] (H : Finset J) (x : lpOneAlg J G) :
    headProj (𝕜 := 𝕜) H x = x ↔ ∀ j ∉ H, x j = 0 := by
  constructor
  · intro h j hj
    rw [← h, headProj, diagCLM_apply, headSymbol, ite_eq_right hj, zero_smul]
  · intro h
    refine ext fun j => ?_
    rw [headProj, diagCLM_apply, headSymbol]
    split_ifs with hj
    · exact one_smul _ _
    · rw [h j hj, smul_zero]

/-- **(T24, L001; optional.)** Range of the tail projection, fiber form: the vectors
vanishing on `H`. -/
theorem tailProj_apply_eq_self_iff_fiber {𝕜 : Type*} [NormedField 𝕜] {J : Type*}
    {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [DecidableEq J] (H : Finset J) (x : lpOneAlg J G) :
    tailProj (𝕜 := 𝕜) H x = x ↔ ∀ j ∈ H, x j = 0 := by
  constructor
  · intro h j hj
    rw [← h, tailProj_eq_one_sub, sub_apply, one_apply_eq_self]
    change x j - headSymbol H j • x j = 0
    rw [headSymbol, ite_eq_left hj, one_smul, sub_self]
  · intro h
    refine ext fun j => ?_
    rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self]
    change x j - headSymbol H j • x j = x j
    rw [headSymbol]
    split_ifs with hj
    · rw [h j hj, smul_zero, sub_zero]
    · rw [zero_smul, sub_zero]

/-- **(T23, L001.)** Range of the head projection, coefficient form. -/
theorem headProj_apply_eq_self_iff {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) :
    headProj (𝕜 := 𝕜) H x = x ↔ ∀ j ∉ H, toRealSeq x j = 0 := by
  constructor
  · intro h j hj
    rw [← h, toRealSeq_headProj, ite_eq_right hj]
  · intro h
    refine ext_toRealSeq (funext fun j => ?_)
    rw [toRealSeq_headProj]
    split_ifs with hj
    · rfl
    · exact (h j hj).symm

/-- **(T23, L001.)** Range of the tail projection, coefficient form. -/
theorem tailProj_apply_eq_self_iff {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) :
    tailProj (𝕜 := 𝕜) H x = x ↔ ∀ j ∈ H, toRealSeq x j = 0 := by
  constructor
  · intro h j hj
    rw [← h, toRealSeq_tailProj, ite_eq_left hj]
  · intro h
    refine ext_toRealSeq (funext fun j => ?_)
    rw [toRealSeq_tailProj]
    split_ifs with hj
    · exact (h j hj).symm
    · rfl

/-- **(T25, L001.)** A diagonal vanishing on the head has zero head part. -/
theorem headProj_comp_diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hr0 : ∀ j ∈ H, r j = 0) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L diagCLM r C hr = 0 := by
  refine ContinuousLinearMap.ext fun x => ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, headProj, diagCLM_apply, diagCLM_apply, headSymbol]
  split_ifs with hj
  · rw [hr0 j hj, zero_smul, smul_zero]; rfl
  · rw [zero_smul]; rfl

/-- **(T25, L001.)** A diagonal vanishing on the head is tail-valued. -/
theorem tailProj_comp_diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hr0 : ∀ j ∈ H, r j = 0) :
    (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L diagCLM r C hr = diagCLM r C hr := by
  rw [tailProj_eq_one_sub, ContinuousLinearMap.sub_comp, headProj_comp_diagCLM H r C hr hr0,
    sub_zero]
  rfl

/-- **(T26, L001.)** ℓ¹ additivity: a head-supported and a tail-supported vector have
additive norms. -/
theorem norm_add_of_head_tail {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (x y : lpOneAlg J G) (hx : headProj (𝕜 := 𝕜) H x = x)
    (hy : tailProj (𝕜 := 𝕜) H y = y) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rw [headProj_apply_eq_self_iff_fiber] at hx
  rw [tailProj_apply_eq_self_iff_fiber] at hy
  rw [norm_eq_tsum, norm_eq_tsum x, norm_eq_tsum y,
    ← (summable_norm x).tsum_add (summable_norm y)]
  refine tsum_congr fun j => ?_
  change ‖x j + y j‖ = ‖x j‖ + ‖y j‖
  by_cases hj : j ∈ H
  · rw [hy j hj, add_zero, norm_zero, add_zero]
  · rw [hx j hj, zero_add, norm_zero, zero_add]

/-- **(T27, L001; optional.)** The head projection is a contraction. -/
theorem norm_headProj_apply_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) : ‖headProj (𝕜 := 𝕜) H x‖ ≤ ‖x‖ :=
  (norm_diagCLM_apply_le _ _ (norm_headSymbol_le H) x).trans_eq (one_mul _)

/-- **(T27, L001; optional.)** The tail projection is a contraction. -/
theorem norm_tailProj_apply_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) : ‖tailProj (𝕜 := 𝕜) H x‖ ≤ ‖x‖ := by
  rw [norm_eq_tsum, norm_eq_tsum]
  refine (summable_norm _).tsum_le_tsum (fun j => ?_) (summable_norm x)
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self]
  change ‖x j - headSymbol H j • x j‖ ≤ ‖x j‖
  rw [headSymbol]
  split_ifs
  · rw [one_smul, sub_self, norm_zero]; exact norm_nonneg _
  · rw [zero_smul, sub_zero]

/-! ### Head/tail aggregation of column ratios -/

/-- **(T28, L001.)** A head-valued `S` and a tail-valued `T` add column-wise. -/
theorem colRatio_add_of_head_tail {𝕜 : Type*} [NormedField 𝕜] {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [lpAlgSmulCompat 𝕜 I E]
    {J : Type*} {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (S T : lpOneAlg I E →L[𝕜] lpOneAlg J G)
    (hS : headProj H ∘L S = S) (hT : tailProj H ∘L T = T) (i : I) :
    colRatio (S + T) i = colRatio S i + colRatio T i := by
  rw [colRatio, colRatio, colRatio, add_apply,
    norm_add_of_head_tail H (S (single i 1)) (T (single i 1)) (DFunLike.congr_fun hS _)
      (DFunLike.congr_fun hT _), add_div]

/-- **(T29, L001.)** Exact aggregate operator norm of a head-valued plus a tail-valued map:
`‖S + T‖ = ⨆ i, (colRatio S i + colRatio T i)`. -/
theorem opNorm_add_eq_iSup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [lpAlgSmulCompat 𝕜 I E]
    {J : Type*} {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (S T : lpOneAlg I E →L[𝕜] lpOneAlg J G)
    (hS : headProj H ∘L S = S) (hT : tailProj H ∘L T = T) :
    ‖S + T‖ = ⨆ i, (colRatio S i + colRatio T i) :=
  (opNorm_eq_iSup_cols _).trans (iSup_congr fun i => colRatio_add_of_head_tail H S T hS hT i)

/-- **(T30, L001.)** A map into `lpOneAlg J G` has zero head part iff it is tail-valued. -/
theorem head_comp_eq_zero_iff_tail_comp_eq_self {𝕜 : Type*} [NormedField 𝕜] {J : Type*}
    {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [DecidableEq J] (H : Finset J) {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] lpOneAlg J G) : headProj H ∘L T = 0 ↔ tailProj H ∘L T = T := by
  rw [tailProj_eq_one_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]
  exact ⟨fun h => by rw [h, sub_zero], fun h => sub_eq_self.mp h⟩

/-- **(T31, L001.)** Column additivity when the second map has zero head part. -/
theorem colRatio_add_of_head_zero {𝕜 : Type*} [NormedField 𝕜] {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [lpAlgSmulCompat 𝕜 I E]
    {J : Type*} {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (S T : lpOneAlg I E →L[𝕜] lpOneAlg J G)
    (hS : headProj H ∘L S = S) (hT0 : headProj H ∘L T = 0) (i : I) :
    colRatio (S + T) i = colRatio S i + colRatio T i :=
  colRatio_add_of_head_tail H S T hS ((head_comp_eq_zero_iff_tail_comp_eq_self H T).mp hT0) i

/-- **(T31, L001.)** Exact aggregate operator norm when the second map has zero head part. -/
theorem opNorm_add_eq_iSup_of_head_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [lpAlgSmulCompat 𝕜 I E]
    {J : Type*} {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (H : Finset J) (S T : lpOneAlg I E →L[𝕜] lpOneAlg J G)
    (hS : headProj H ∘L S = S) (hT0 : headProj H ∘L T = 0) :
    ‖S + T‖ = ⨆ i, (colRatio S i + colRatio T i) :=
  opNorm_add_eq_iSup H S T hS ((head_comp_eq_zero_iff_tail_comp_eq_self H T).mp hT0)

/-- A vanishing column ratio means a vanishing column (the weight is positive). -/
private theorem apply_single_eq_zero_of_colRatio_eq_zero {𝕜 : Type*} [NormedField 𝕜]
    {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E]
    [DecidableEq I] [∀ i, NormedSpace 𝕜 (E i)] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {T : lpOneAlg I E →L[𝕜] F} {i : I} (h : colRatio T i = 0) :
    T (single i (1 : 𝕜)) = 0 := by
  rw [colRatio, div_eq_zero_iff] at h
  exact norm_eq_zero.mp (h.resolve_right (norm_ofReal_one_pos i).ne')

/-- **(T32, L001.)** A map killing the source tail has zero tail columns. -/
theorem colRatio_eq_zero_of_comp_tailProj {𝕜 : Type*} [NormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [lpAlgSmulCompat 𝕜 I E] (Hs : Finset I) (Z : lpOneAlg I E →L[𝕜] F)
    (hZ : Z ∘L tailProj Hs = 0) (i : I) (hi : i ∉ Hs) : colRatio Z i = 0 := by
  have h := DFunLike.congr_fun hZ (single i (1 : 𝕜))
  rw [ContinuousLinearMap.comp_apply, tailProj_single, ite_eq_right hi, zero_apply] at h
  rw [colRatio, h, norm_zero, zero_div]

/-- **(T32, L001.)** A map killing the source head has zero head columns. -/
theorem colRatio_eq_zero_of_comp_headProj {𝕜 : Type*} [NormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [lpAlgSmulCompat 𝕜 I E] (Hs : Finset I) (S : lpOneAlg I E →L[𝕜] F)
    (hS : S ∘L headProj Hs = 0) (i : I) (hi : i ∈ Hs) : colRatio S i = 0 := by
  have h := DFunLike.congr_fun hS (single i (1 : 𝕜))
  rw [ContinuousLinearMap.comp_apply, headProj_single, ite_eq_left hi, zero_apply] at h
  rw [colRatio, h, norm_zero, zero_div]

/-- **(T32, L001.)** Column additivity of a source-split pair: each column carries only one
of `Z` (killing the source tail) and `S` (killing the source head). -/
theorem colRatio_add_of_comp_split {𝕜 : Type*} [NormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [lpAlgSmulCompat 𝕜 I E] (Hs : Finset I) (Z S : lpOneAlg I E →L[𝕜] F)
    (hZ : Z ∘L tailProj Hs = 0) (hS : S ∘L headProj Hs = 0) (i : I) :
    colRatio (Z + S) i = colRatio Z i + colRatio S i := by
  by_cases hi : i ∈ Hs
  · have h := colRatio_eq_zero_of_comp_headProj Hs S hS i hi
    rw [h, add_zero, colRatio, colRatio, add_apply,
      apply_single_eq_zero_of_colRatio_eq_zero h, add_zero]
  · have h := colRatio_eq_zero_of_comp_tailProj Hs Z hZ i hi
    rw [h, zero_add, colRatio, colRatio, add_apply,
      apply_single_eq_zero_of_colRatio_eq_zero h, zero_add]

/-- **(T33, L001.)** Joint exact aggregate: for a head block `Z` (head-valued, killing the
source tail), a head-valued `S` killing the source head and a tail-valued `T`,
`‖Z + S + T‖ = ⨆ i, (colRatio Z i + colRatio S i + colRatio T i)`. -/
theorem opNorm_joint_eq_iSup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [lpAlgRingData 𝕜 I E] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [lpAlgSmulCompat 𝕜 I E]
    {J : Type*} {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G] [DecidableEq J]
    (Hs : Finset I) (H : Finset J) (Z S T : lpOneAlg I E →L[𝕜] lpOneAlg J G)
    (hPZ : headProj H ∘L Z = Z) (hZQ : Z ∘L tailProj Hs = 0)
    (hPS : headProj H ∘L S = S) (hSP : S ∘L headProj Hs = 0) (hT : tailProj H ∘L T = T) :
    ‖Z + S + T‖ = ⨆ i, (colRatio Z i + colRatio S i + colRatio T i) := by
  have hZS : headProj H ∘L (Z + S) = Z + S := by rw [ContinuousLinearMap.comp_add, hPZ, hPS]
  rw [opNorm_add_eq_iSup H (Z + S) T hZS hT]
  exact iSup_congr fun i => by rw [colRatio_add_of_comp_split Hs Z S hZQ hSP i]

end lpOneAlg

end RadiiPolynomial
