import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bounded scalar diagonals and finite-head projections

On `lpOneAlg J G`, a bounded scalar symbol `r : J → 𝕜` acts fiberwise as
`diagCLM r C hr`, with `‖diagCLM r C hr x‖ ≤ C * ‖x‖`. The construction needs no
chosen frame and no completeness hypothesis. Its coefficient and atom computation faces
are `toRealSeq_diagCLM` and `diagCLM_single`.

The indicator of `H : Finset J` defines `headProj H`; `tailProj H` is its complement
`1 - headProj H`. The coefficient formulas `toRealSeq_headProj` and `toRealSeq_tailProj`
describe their support, and `norm_tailProj_apply_le` gives `‖tailProj H x‖ ≤ ‖x‖` over a
`NormedField`.

The head/tail faces reached by a finite-head certificate: the atom faces `headProj_single` and
`tailProj_single`, idempotence `isIdempotentElem_headProj`, the head expansion
`headProj_eq_sum` (`P_H x = ∑_(j ∈ H) x_j e_j`) with the instance
`finiteDimensional_range_headProj`, the head norm identity `norm_headProj`
(`‖P_H y‖ = ∑_(k ∈ H) ‖y k‖`) and the tail bound of a diagonal
`norm_tailProj_diagCLM_apply_le` (`‖Q_H D_r w‖ ≤ C' ‖w‖` when `‖r k‖ ≤ C'` off `H`).
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

/-- The bounded scalar diagonal `(D_r y)_j = r_j • y_j` on `lpOneAlg J G`,
for a symbol with `‖r j‖ ≤ C`. Any fibers; no completeness, no scalar trivialization. -/
def diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  LinearMap.mkContinuous
    { toFun := fun x : lpOneAlg J G => ⟨⟨fun j => r j • x j, memℓp_smul_diag r C hr x⟩⟩
      map_add' := fun x y => ext fun j => smul_add (r j) (x j) (y j)
      map_smul' := fun c x => ext fun j => smul_comm (r j) c (x j) }
    C (norm_smul_diag_le r C hr)

/-- The fiber action of the diagonal (the value contract of `diagCLM`). -/
theorem diagCLM_apply {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) (j : J) :
    diagCLM r C hr x j = r j • x j :=
  rfl

/-- Pointwise bound of the diagonal: `‖D_r x‖ ≤ C ‖x‖`. -/
theorem norm_diagCLM_apply_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) :
    ‖diagCLM r C hr x‖ ≤ C * ‖x‖ :=
  norm_smul_diag_le r C hr x

/-- Operator-norm bound of the diagonal: `‖D_r‖ ≤ C` for `0 ≤ C`. -/
theorem norm_diagCLM_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hC : 0 ≤ C) :
    ‖(diagCLM r C hr : lpOneAlg J G →L[𝕜] lpOneAlg J G)‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_diagCLM_apply_le r C hr)

/-- Coefficient face of the diagonal: `(D_r x)_j = r_j x_j` in the chosen frame
(`map_smul` of `θ_j⁻¹`). -/
theorem toRealSeq_diagCLM {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (x : lpOneAlg J G) (j : J) :
    toRealSeq (diagCLM r C hr x) j = r j * toRealSeq x j :=
  map_smul (FiberTrivialization.equiv (E := G) j).symm (r j) (x j)

/-- Atom face of the diagonal: `D_r (x e_j) = (r_j x) e_j`. -/
theorem diagCLM_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (j : J) (x : 𝕜) :
    diagCLM r C hr (single j x : lpOneAlg J G) = single j (r j * x) := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_diagCLM, toRealSeq_single, toRealSeq_single]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-! ### Finite-head projections -/

/-- The indicator symbol of a finite head `H`. -/
def headSymbol {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
    (H : Finset J) (j : J) : 𝕜 :=
  if j ∈ H then 1 else 0

/-- The head symbol has norm at most one. -/
theorem norm_headSymbol_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
    (H : Finset J) (j : J) : ‖(headSymbol H j : 𝕜)‖ ≤ 1 := by
  unfold headSymbol
  split_ifs <;> simp


/-- The head projection `P_H = D_{1_H}`: keep the coordinates in `H`. -/
def headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  diagCLM (headSymbol H) 1 (norm_headSymbol_le H)

/-- The tail projection `Q_H = 1 - P_H`. -/
def tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : lpOneAlg J G →L[𝕜] lpOneAlg J G :=
  1 - headProj H

/-- The tail projection is the literal complement of the head projection
(the simp normal form). -/
@[simp] theorem tailProj_eq_one_sub {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) = 1 - headProj H :=
  rfl

/-- Coefficient face of the head projection. -/
theorem toRealSeq_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) (j : J) :
    toRealSeq (headProj (𝕜 := 𝕜) H x) j = if j ∈ H then toRealSeq x j else 0 := by
  rw [headProj, toRealSeq_diagCLM, headSymbol]
  split_ifs <;> simp only [one_mul, zero_mul]

/-- Coefficient face of the tail projection. -/
theorem toRealSeq_tailProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) (j : J) :
    toRealSeq (tailProj (𝕜 := 𝕜) H x) j = if j ∈ H then 0 else toRealSeq x j := by
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, toRealSeq_sub, Pi.sub_apply,
    toRealSeq_headProj]
  split_ifs <;> simp only [sub_self, sub_zero]

/-- Atom face of the head projection. -/
theorem headProj_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (j : J) (x : 𝕜) :
    headProj (𝕜 := 𝕜) H (single j x : lpOneAlg J G) = if j ∈ H then single j x else 0 := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_headProj, toRealSeq_single]
  by_cases hkj : k = j
  · subst hkj
    split_ifs <;> simp_all [toRealSeq_single, toRealSeq_zero]
  · split_ifs <;> simp [hkj, toRealSeq_single, toRealSeq_zero]

/-- Atom face of the tail projection. -/
theorem tailProj_single {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (j : J) (x : 𝕜) :
    tailProj (𝕜 := 𝕜) H (single j x : lpOneAlg J G) = if j ∈ H then 0 else single j x := by
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, headProj_single]
  split_ifs <;> simp only [sub_self, sub_zero]

/-- The head projection is an idempotent of the operator ring. -/
theorem isIdempotentElem_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) : IsIdempotentElem (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) := by
  refine ContinuousLinearMap.ext fun x => ext fun j => ?_
  rw [mul_apply_eq_comp, headProj, diagCLM_apply, diagCLM_apply, smul_smul, headSymbol]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- **The head expansion** `P_H x = ∑_(j ∈ H) x_j e_j` in the chosen frame. -/
theorem headProj_eq_sum {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x : lpOneAlg J G) :
    headProj (𝕜 := 𝕜) H x = ∑ j ∈ H, toRealSeq x j • (single j (1 : 𝕜) : lpOneAlg J G) :=
  ext_toRealSeq (funext fun k => by
    rw [toRealSeq_headProj, toRealSeq_finset_sum]
    simp only [toRealSeq_smul, Pi.smul_apply, toRealSeq_single, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq])

/-- The range of the head projection lies in the span of the head atoms (construction internal
of `finiteDimensional_range_headProj`). -/
private theorem range_headProj_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J] (H : Finset J) :
    LinearMap.range (headProj (𝕜 := 𝕜) (G := G) H).toLinearMap ≤
      Submodule.span 𝕜 (Set.range fun j : H => (single (j : J) (1 : 𝕜) : lpOneAlg J G)) := by
  rintro _ ⟨x, rfl⟩
  rw [ContinuousLinearMap.coe_coe, headProj_eq_sum]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)

/-- **The head range is finite-dimensional** (spanned by the atoms `e_j`, `j ∈ H`). -/
instance finiteDimensional_range_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*}
    {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]
    [FiberTrivialization 𝕜 J G] [DecidableEq J] (H : Finset J) :
    FiniteDimensional 𝕜 (LinearMap.range (headProj (𝕜 := 𝕜) (G := G) H).toLinearMap) :=
  haveI := FiniteDimensional.span_of_finite 𝕜
    (Set.finite_range fun j : H => (single (j : J) (1 : 𝕜) : lpOneAlg J G))
  Submodule.finiteDimensional_of_le (range_headProj_le H)

/-- The tail projection is a contraction. -/
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

/-- **The head norm identity** `‖P_H y‖ = ∑_(k ∈ H) ‖y k‖` (fiber norms; no frame). -/
theorem norm_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (y : lpOneAlg J G) : ‖headProj (𝕜 := 𝕜) H y‖ = ∑ k ∈ H, ‖y k‖ := by
  rw [norm_eq_tsum, tsum_eq_sum (s := H) fun k hk => by
    rw [headProj, diagCLM_apply, headSymbol, ite_eq_right hk, zero_smul, norm_zero]]
  exact Finset.sum_congr rfl fun k hk => by
    rw [headProj, diagCLM_apply, headSymbol, ite_eq_left hk, one_smul]

/-- **The tail bound of a diagonal**: if `‖r k‖ ≤ C'` off the head, then
`‖Q_H D_r w‖ ≤ C' ‖w‖` (`0 ≤ C'` covers the modes of `H`). -/
theorem norm_tailProj_diagCLM_apply_le {𝕜 : Type*} [NormedField 𝕜] {J : Type*}
    {G : J → Type*} [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) {C' : ℝ} (hC' : 0 ≤ C')
    (htail : ∀ k ∉ H, ‖r k‖ ≤ C') (w : lpOneAlg J G) :
    ‖tailProj (𝕜 := 𝕜) H (diagCLM r C hr w)‖ ≤ C' * ‖w‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, ← tsum_mul_left]
  refine (summable_norm _).tsum_le_tsum (fun k => ?_) ((summable_norm w).mul_left _)
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self]
  change ‖r k • w k - headSymbol H k • (r k • w k)‖ ≤ C' * ‖w k‖
  rw [headSymbol]
  split_ifs with hk
  · rw [one_smul, sub_self, norm_zero]; exact mul_nonneg hC' (norm_nonneg _)
  · rw [zero_smul, sub_zero]
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (htail k hk) (norm_nonneg _))

end lpOneAlg

end RadiiPolynomial
