import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Weighted column ratios: the one-slot column principle

A continuous linear map `T` out of a weighted ℓ¹ space `lpOneAlg I E` with a chosen frame
`θ` is determined in norm by its columns `T e_i`, `e_i = single i 1 = fiberSingle i (θ_i 1)`.
With the fiber weight `ω_i = FiberTrivialization.weight i = ‖θ_i 1‖ > 0`, the weighted column
ratio is
`colRatio T i = ‖T e_i‖ / ω_i`, and the operator norm is exactly the supremum of
these ratios. This file states the one-slot member of the column-principle family
whose two- and three-slot members live in `WeightedL1/Multilinear.lean`.

The upper bound reuses the pointwise bound `lpOneAlg.norm_le_of_cols`
(`WeightedL1/Carrier.lean`); the lower bound is the operator-norm inequality on
one unit single, divided by the positive weight `FiberTrivialization.weight_pos`
(`WeightedL1/FiberTrivialization.lean`). The operator norm needs `[NontriviallyNormedField 𝕜]`; the ratio
itself and its nonnegativity hold over any `[NormedField 𝕜]`.

Main declarations:
* `lpOneAlg.colRatio` — the weighted column ratio `‖T e_i‖ / ω_i`.
* `lpOneAlg.opNorm_le_of_cols`, `lpOneAlg.cols_le_opNorm`,
  `lpOneAlg.opNorm_le_iff_cols` — the two directions of the column principle.
* `lpOneAlg.opNorm_eq_iSup_cols` — `‖T‖ = ⨆ i, colRatio T i`, with no
  `Nonempty` hypothesis (both sides vanish on an empty index type).
-/

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

/-- The weighted column ratio `‖T e_i‖ / ω_i` of a continuous linear
map out of `lpOneAlg I E`, with `e_i = single i 1` and `ω_i = FiberTrivialization.weight i`. -/
def colRatio {𝕜 : Type*} [NormedField 𝕜] {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) (i : I) : ℝ :=
  ‖T (single i (1 : 𝕜))‖ / FiberTrivialization.weight (E := E) i

/-- Column ratios are nonnegative. -/
theorem colRatio_nonneg {𝕜 : Type*} [NormedField 𝕜] {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) (i : I) : 0 ≤ colRatio T i :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Each column is bounded by the operator norm times its weight:
`‖T e_i‖ ≤ ‖T‖ · ω_i`. -/
theorem cols_le_opNorm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) (i : I) :
    ‖T (single i (1 : 𝕜))‖ ≤ ‖T‖ * FiberTrivialization.weight (E := E) i := by
  simpa only [norm_single, norm_one, one_mul] using T.le_opNorm (single i (1 : 𝕜))

/-- Every column ratio is a lower bound of the operator norm. -/
theorem colRatio_le_opNorm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) (i : I) : colRatio T i ≤ ‖T‖ :=
  (div_le_iff₀ (FiberTrivialization.weight_pos i)).mpr (cols_le_opNorm T i)

/-- One-slot column principle, operator norm: if every column satisfies
`‖T e_i‖ ≤ C · ω_i` and `0 ≤ C`, then `‖T‖ ≤ C`. The pointwise bound is
`lpOneAlg.norm_le_of_cols`. -/
theorem opNorm_le_of_cols {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ i, ‖T (single i (1 : 𝕜))‖ ≤ C * FiberTrivialization.weight (E := E) i) :
    ‖T‖ ≤ C :=
  T.opNorm_le_bound hC (norm_le_of_cols T hcol)

/-- One-slot column principle, iff form: for `0 ≤ C`, `‖T‖ ≤ C` iff
every column satisfies `‖T e_i‖ ≤ C · ω_i`. The bound `C` is implicit, as in the
two- and three-slot members `opNorm_le_iff_cols₂/₃`. -/
theorem opNorm_le_iff_cols {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ i, ‖T (single i (1 : 𝕜))‖ ≤ C * FiberTrivialization.weight (E := E) i :=
  ⟨fun h i => (cols_le_opNorm T i).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)),
    opNorm_le_of_cols T hC⟩

/-- The column ratios are bounded above (by `‖T‖`). -/
theorem colRatio_bddAbove {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) : BddAbove (Set.range (colRatio T)) :=
  ⟨‖T‖, by rintro _ ⟨i, rfl⟩; exact colRatio_le_opNorm T i⟩

/-- The operator norm out of a weighted ℓ¹ space is the supremum of the
weighted column ratios. No `Nonempty I` hypothesis: on an empty index type both sides
are `0`. -/
theorem opNorm_eq_iSup_cols {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : lpOneAlg I E →L[𝕜] F) : ‖T‖ = ⨆ i, colRatio T i := by
  refine le_antisymm ?_ (Real.iSup_le (colRatio_le_opNorm T) (norm_nonneg _))
  refine (opNorm_le_iff_cols T (Real.iSup_nonneg (colRatio_nonneg T))).mpr fun i => ?_
  exact (div_le_iff₀ (FiberTrivialization.weight_pos i)).mp (le_ciSup (colRatio_bddAbove T) i)

end lpOneAlg

end RadiiPolynomial
