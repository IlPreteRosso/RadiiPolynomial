import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Ring.Idempotent

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











end lpOneAlg

end RadiiPolynomial
