import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Bilinear and trilinear maps out of weighted ℓ¹ spaces: the curried column principle

A continuous linear map out of `lpOneAlg M E` is controlled by its values on
the unit singles (`lpOneAlg.norm_le_of_cols`). This file curries that
principle: a continuous bilinear (resp. trilinear) map out of two (resp.
three) weighted ℓ¹ spaces is controlled by its values on pairs (resp. triples)
of unit singles, each atom weighted by the product of the fiber weights
`ω_m = FiberTrivialization.weight m = ‖θ_m 1‖` of each slot's chosen frame. The three carriers
are independent: each slot has its own index type, its own fibers, its own frame and its own
weight.

The proof applies the one-slot bound once per slot. Partial evaluation
`x ↦ B x y` is assembled as a continuous linear map from
`continuous_eval_const` (a private helper), because Mathlib's
`ContinuousLinearMap.flip` needs a `NontriviallyNormedField`.

Main declarations:
* `lpOneAlg.norm_le_of_cols₂`, `lpOneAlg.norm_le_of_cols₃` — pointwise
  bounds `‖B f g‖ ≤ C ‖f‖ ‖g‖` and `‖T f g h‖ ≤ C ‖f‖ ‖g‖ ‖h‖` from the atom
  bounds, over any `NormedField`, with no sign hypothesis on `C`.
* `lpOneAlg.opNorm_le_of_cols₂`, `lpOneAlg.opNorm_le_of_cols₃` — the same
  bounds on the operator norm, for `0 ≤ C`.
* `lpOneAlg.cols_le_opNorm₂`, `lpOneAlg.cols_le_opNorm₃` — conversely, every
  atom is bounded by the operator norm times its weights.
* `lpOneAlg.opNorm_le_iff_cols₂`, `lpOneAlg.opNorm_le_iff_cols₃` — the two
  directions as one iff, for `0 ≤ C`.
* `lpOneAlg.opNorm_eq_iSup_cols₂`, `lpOneAlg.opNorm_eq_iSup_cols₃` — the
  operator norm IS the supremum of the weighted atom ratios, with no hypothesis
  beyond the carrier context.

Specializations, declared in `Geometric/Basic.lean` and `Chebyshev/Algebra.lean`:
* `l1Weighted.single_eq_lpOneAlg_single` — the geometric single is the generic
  single.
* `l1Weighted.opNorm_eq_iSup_cols₂/₃` and `l1Chebyshev.opNorm_eq_iSup_cols₂/₃`
  — the supremum formulas with the weights `νⁿ` on `ℕ` and `ν^{|k|}` on `ℤ`,
  for every `ν : PosReal` (no `1 ≤ ν`).

Field hypotheses. The pointwise forms need only `[NormedField 𝕜]`, like
`lpOneAlg.norm_le_of_cols`. The operator-norm forms need
`[NontriviallyNormedField 𝕜]`, the setting in which Mathlib defines the
operator norm (`ContinuousLinearMap.hasOpNorm`) and its bilinear API
(`ContinuousLinearMap.opNorm_le_bound₂`, `ContinuousLinearMap.le_opNorm₂`).

Sign of `C`. The pointwise forms carry no sign hypothesis. A negative `C` is
not false there, only vacuous on the usual carriers: the weights are always
positive (next paragraph), so if every index type is inhabited, the atom
hypothesis at one atom gives `0 ≤ C`. That deduction needs inhabited index
types, so the operator-norm and iff forms keep `0 ≤ C` as an explicit
hypothesis; on inhabited carriers it costs nothing.

Positivity of the weights. Every fiber weight `FiberTrivialization.weight m` is
positive (`FiberTrivialization.weight_pos`), because `θ_m` is injective, so `θ_m 1 ≠ 0`.
The supremum formulas `lpOneAlg.opNorm_eq_iSup_cols₂/₃` therefore need no hypothesis beyond the
context of the iff forms: the ratios never have a zero denominator. No
`Nonempty` hypothesis is needed either, since `Real.iSup_le` handles an empty
index type.

Instance path. With the pinned Mathlib, `Norm` on a three-level curried type
`X →L[𝕜] Y →L[𝕜] Z →L[𝕜] F` does not synthesize at the default
`maxSynthPendingDepth` of downstream projects (Mathlib itself builds with 3).
Over a general `𝕜` a section-local `RingHomIsometric (RingHom.id 𝕜)` instance
repairs it; for the concrete `𝕜 = ℝ` statements that instance does not, and
`set_option maxSynthPendingDepth 2 in` is used on the two trilinear
specializations, which live in `Geometric/Basic.lean` and `Chebyshev/Algebra.lean`.

Scope. These are the faces for weighted ℓ¹ spaces whose fibers are trivialized
by a chosen frame `FiberTrivialization` (scalar fibers carrying a weight). Nothing here
concerns arbitrary Banach-valued fibers or products of blocks.

Placement. This module holds the generic faces; it imports only
`WeightedL1.UniversalProperty` and `Mathlib.Analysis.Normed.Operator.Bilinear`.
The ℕ-side supremum formulas live in `Geometric/Basic.lean` and the ℤ-side ones
in `Chebyshev/Algebra.lean`.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

namespace lpOneAlg

section Multilinear

variable {𝕜 : Type*}
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable {M' : Type*} {E' : M' → Type*} [∀ m, NormedAddCommGroup (E' m)]
variable {M'' : Type*} {E'' : M'' → Type*} [∀ m, NormedAddCommGroup (E'' m)]
variable {F : Type*} [NormedAddCommGroup F]

section Pointwise

variable [NormedField 𝕜]
variable [DecidableEq M] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
variable [DecidableEq M'] [∀ m, NormedSpace 𝕜 (E' m)] [FiberTrivialization 𝕜 M' E']
variable [DecidableEq M''] [∀ m, NormedSpace 𝕜 (E'' m)] [FiberTrivialization 𝕜 M'' E'']
variable [NormedSpace 𝕜 F]

/-- Partial evaluation in the second slot, `x ↦ B x y`, as a continuous linear
map. Over a general `NormedField` Mathlib's `ContinuousLinearMap.flip` is not
available (it needs a `NontriviallyNormedField`), so the map is assembled from
`continuous_eval_const`. -/
private def applyRight {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
    (B : X →L[𝕜] Y →L[𝕜] G) (y : Y) : X →L[𝕜] G where
  toFun x := B x y
  map_add' x x' := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl
  cont := (continuous_eval_const y).comp B.continuous

/-- Evaluation of the private partial evaluation `applyRight`. -/
private theorem applyRight_apply {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
    (B : X →L[𝕜] Y →L[𝕜] G) (y : Y) (x : X) : applyRight B y x = B x y := rfl

/-- **Bilinear column principle, pointwise.** Out of two weighted ℓ¹ spaces, a
continuous bilinear map satisfies `‖B f g‖ ≤ C · ‖f‖ · ‖g‖` as soon as every
pair of unit singles satisfies `‖B e_i e_j‖ ≤ C · ω_i · ω'_j` (`ω` the fiber
weights).

There is no sign hypothesis on `C`. With `C < 0` the statement is vacuous
when both index types are inhabited (the weights are positive, so the atom
hypothesis at one pair forces `0 ≤ C`), never false. -/
theorem norm_le_of_cols₂ (B : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] F) {C : ℝ}
    (hcol : ∀ i j, ‖B (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j)
    (f : lpOneAlg M E) (g : lpOneAlg M' E') : ‖B f g‖ ≤ C * ‖f‖ * ‖g‖ := by
  have h1 : ∀ j : M', ‖B f (lpOneAlg.single j (1 : 𝕜))‖
      ≤ (C * ‖f‖) * FiberTrivialization.weight (E := E') j := fun j => by
    have := lpOneAlg.norm_le_of_cols (𝕜 := 𝕜) (applyRight B (lpOneAlg.single j (1 : 𝕜)))
      (C := C * FiberTrivialization.weight (E := E') j)
      (fun i => by
        rw [applyRight_apply]
        exact (hcol i j).trans_eq (by ring)) f
    rw [applyRight_apply] at this
    exact this.trans_eq (by ring)
  exact lpOneAlg.norm_le_of_cols (𝕜 := 𝕜) (B f) h1 g

/-- **Trilinear column principle, pointwise.** Out of three weighted ℓ¹ spaces,
a continuous trilinear map satisfies `‖T f g h‖ ≤ C · ‖f‖ · ‖g‖ · ‖h‖` as soon
as every triple of unit singles satisfies `‖T e_i e_j e_k‖ ≤ C · ω_i · ω'_j · ω''_k`.

There is no sign hypothesis on `C`; as for `norm_le_of_cols₂`, a negative `C`
makes the statement vacuous on inhabited carriers, never false. -/
theorem norm_le_of_cols₃
    (T : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] lpOneAlg M'' E'' →L[𝕜] F) {C : ℝ}
    (hcol : ∀ i j k, ‖T (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))
        (lpOneAlg.single k (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k)
    (f : lpOneAlg M E) (g : lpOneAlg M' E') (h : lpOneAlg M'' E'') :
    ‖T f g h‖ ≤ C * ‖f‖ * ‖g‖ * ‖h‖ := by
  have h1 : ∀ j k, ‖T f (lpOneAlg.single j (1 : 𝕜)) (lpOneAlg.single k (1 : 𝕜))‖
      ≤ (C * ‖f‖) * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k := fun j k => by
    have := lpOneAlg.norm_le_of_cols (𝕜 := 𝕜)
      (applyRight (applyRight T (lpOneAlg.single j (1 : 𝕜))) (lpOneAlg.single k (1 : 𝕜)))
      (C := C * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k)
      (fun i => by
        rw [applyRight_apply, applyRight_apply]
        exact (hcol i j k).trans_eq (by ring)) f
    rw [applyRight_apply, applyRight_apply] at this
    exact this.trans_eq (by ring)
  exact norm_le_of_cols₂ (T f) h1 g h

end Pointwise

section OpNorm

variable [NontriviallyNormedField 𝕜]
variable [DecidableEq M] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
variable [DecidableEq M'] [∀ m, NormedSpace 𝕜 (E' m)] [FiberTrivialization 𝕜 M' E']
variable [DecidableEq M''] [∀ m, NormedSpace 𝕜 (E'' m)] [FiberTrivialization 𝕜 M'' E'']
variable [NormedSpace 𝕜 F]

/-- Section-local instance, not exported. With the pinned Mathlib, `Norm` on a
three-level curried type `X →L[𝕜] Y →L[𝕜] Z →L[𝕜] F` does not synthesize at the
default `maxSynthPendingDepth` of downstream projects (Mathlib builds with 3);
registering the identity `RingHomIsometric` instance directly repairs the
synthesis over a general `𝕜`. It is a `Prop` instance proved by Mathlib's own
`RingHomIsometric.ids`, so it adds no hypothesis. -/
private local instance ringHomIsometric_id' : RingHomIsometric (RingHom.id 𝕜) :=
  RingHomIsometric.ids

/-- **Bilinear column principle, operator norm.** If every pair of unit singles
satisfies `‖B e_i e_j‖ ≤ C · ω_i · ω'_j` and `0 ≤ C`, then `‖B‖ ≤ C`.

The hypothesis `0 ≤ C` is kept: it follows from the atom bounds only when
both index types are inhabited. -/
theorem opNorm_le_of_cols₂ (B : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C)
    (hcol : ∀ i j, ‖B (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j) : ‖B‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound₂ _ hC (norm_le_of_cols₂ B hcol)

/-- **Atoms under the bilinear operator norm.** Every pair of unit singles
satisfies `‖B e_i e_j‖ ≤ ‖B‖ · ω_i · ω'_j`. -/
theorem cols_le_opNorm₂ (B : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] F) (i : M) (j : M') :
    ‖B (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))‖
      ≤ ‖B‖ * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j := by
  have h := B.le_opNorm₂ (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))
  rwa [lpOneAlg.norm_single, lpOneAlg.norm_single, norm_one, one_mul, one_mul] at h

/-- **Bilinear column principle, iff form.** For `0 ≤ C`, `‖B‖ ≤ C` holds iff
every pair of unit singles satisfies `‖B e_i e_j‖ ≤ C · ω_i · ω'_j`. -/
theorem opNorm_le_iff_cols₂ (B : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C) :
    ‖B‖ ≤ C ↔ ∀ i j, ‖B (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j :=
  ⟨fun h i j => (cols_le_opNorm₂ B i j).trans
      (by gcongr <;> exact FiberTrivialization.weight_nonneg _),
    fun h => opNorm_le_of_cols₂ B hC h⟩

/-- **Trilinear column principle, operator norm.** If every triple of unit
singles satisfies `‖T e_i e_j e_k‖ ≤ C · ω_i · ω'_j · ω''_k` and `0 ≤ C`, then
`‖T‖ ≤ C`. -/
theorem opNorm_le_of_cols₃
    (T : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] lpOneAlg M'' E'' →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C)
    (hcol : ∀ i j k, ‖T (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))
        (lpOneAlg.single k (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k) : ‖T‖ ≤ C :=
  T.opNorm_le_bound hC fun f =>
    (T f).opNorm_le_bound₂ (mul_nonneg hC (norm_nonneg f)) fun g h =>
      norm_le_of_cols₃ T hcol f g h

/-- **Atoms under the trilinear operator norm.** Every triple of unit singles
satisfies `‖T e_i e_j e_k‖ ≤ ‖T‖ · ω_i · ω'_j · ω''_k`. -/
theorem cols_le_opNorm₃
    (T : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] lpOneAlg M'' E'' →L[𝕜] F)
    (i : M) (j : M') (k : M'') :
    ‖T (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜)) (lpOneAlg.single k (1 : 𝕜))‖
      ≤ ‖T‖ * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k := by
  have h1 := (T (lpOneAlg.single i (1 : 𝕜))).le_opNorm₂ (lpOneAlg.single j (1 : 𝕜))
    (lpOneAlg.single k (1 : 𝕜))
  have h2 := T.le_opNorm (lpOneAlg.single i (1 : 𝕜))
  have h3 : ‖T (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))
      (lpOneAlg.single k (1 : 𝕜))‖
      ≤ ‖T‖ * ‖(lpOneAlg.single i (1 : 𝕜) : lpOneAlg M E)‖
        * ‖(lpOneAlg.single j (1 : 𝕜) : lpOneAlg M' E')‖
        * ‖(lpOneAlg.single k (1 : 𝕜) : lpOneAlg M'' E'')‖ :=
    h1.trans (by gcongr)
  rwa [lpOneAlg.norm_single, lpOneAlg.norm_single, lpOneAlg.norm_single, norm_one, one_mul,
    one_mul, one_mul] at h3

/-- **Trilinear column principle, iff form.** For `0 ≤ C`, `‖T‖ ≤ C` holds iff
every triple of unit singles satisfies `‖T e_i e_j e_k‖ ≤ C · ω_i · ω'_j · ω''_k`. -/
theorem opNorm_le_iff_cols₃
    (T : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] lpOneAlg M'' E'' →L[𝕜] F) {C : ℝ}
    (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ i j k, ‖T (lpOneAlg.single i (1 : 𝕜)) (lpOneAlg.single j (1 : 𝕜))
        (lpOneAlg.single k (1 : 𝕜))‖
      ≤ C * FiberTrivialization.weight (E := E) i
        * FiberTrivialization.weight (E := E') j
        * FiberTrivialization.weight (E := E'') k :=
  ⟨fun h i j k => (cols_le_opNorm₃ T i j k).trans
      (by gcongr <;> exact FiberTrivialization.weight_nonneg _),
    fun h => opNorm_le_of_cols₃ T hC h⟩

/-- **The bilinear operator norm as an atom supremum.** `‖B‖` is the supremum
over index pairs of the weighted atom ratios `‖B e_i e_j‖ / (ω_i · ω'_j)`.

Every weight is positive (`FiberTrivialization.weight_pos`), so the formula needs no hypothesis
beyond the context of
`opNorm_le_iff_cols₂`. No `Nonempty` hypothesis: on an empty index type both
sides are `0`. -/
theorem opNorm_eq_iSup_cols₂ (B : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] F) :
    ‖B‖ = ⨆ p : M × M', ‖B (lpOneAlg.single p.1 (1 : 𝕜)) (lpOneAlg.single p.2 (1 : 𝕜))‖
      / (FiberTrivialization.weight (E := E) p.1
        * FiberTrivialization.weight (E := E') p.2) := by
  have hpos : ∀ p : M × M', 0 < FiberTrivialization.weight (E := E) p.1
      * FiberTrivialization.weight (E := E') p.2 := fun p =>
    mul_pos (FiberTrivialization.weight_pos p.1) (FiberTrivialization.weight_pos p.2)
  have hle : ∀ p : M × M',
      ‖B (lpOneAlg.single p.1 (1 : 𝕜)) (lpOneAlg.single p.2 (1 : 𝕜))‖
        / (FiberTrivialization.weight (E := E) p.1
          * FiberTrivialization.weight (E := E') p.2) ≤ ‖B‖ := fun p =>
    (div_le_iff₀ (hpos p)).mpr ((cols_le_opNorm₂ B p.1 p.2).trans_eq (mul_assoc _ _ _))
  have hbdd : BddAbove (Set.range fun p : M × M' =>
      ‖B (lpOneAlg.single p.1 (1 : 𝕜)) (lpOneAlg.single p.2 (1 : 𝕜))‖
        / (FiberTrivialization.weight (E := E) p.1
          * FiberTrivialization.weight (E := E') p.2)) :=
    ⟨‖B‖, by rintro _ ⟨p, rfl⟩; exact hle p⟩
  refine le_antisymm ?_ (Real.iSup_le hle (norm_nonneg _))
  refine opNorm_le_of_cols₂ B
    (Real.iSup_nonneg fun p => div_nonneg (norm_nonneg _) (hpos p).le) fun i j => ?_
  rw [mul_assoc]
  exact (div_le_iff₀ (hpos (i, j))).mp (le_ciSup hbdd (i, j))

/-- **The trilinear operator norm as an atom supremum.** `‖T‖` is the
supremum over index triples of the weighted atom ratios
`‖T e_i e_j e_k‖ / (ω_i · ω'_j · ω''_k)`. As for `opNorm_eq_iSup_cols₂`, the
weights are always positive, so the formula needs no hypothesis beyond the
context of `opNorm_le_iff_cols₃`, and no `Nonempty` hypothesis. A consumer who
restates `‖T‖` for a three-level curried map needs
`set_option maxSynthPendingDepth 2 in` (the identity `RingHomIsometric` instance
used in this section is local). -/
theorem opNorm_eq_iSup_cols₃
    (T : lpOneAlg M E →L[𝕜] lpOneAlg M' E' →L[𝕜] lpOneAlg M'' E'' →L[𝕜] F) :
    ‖T‖ = ⨆ p : M × M' × M'', ‖T (lpOneAlg.single p.1 (1 : 𝕜))
        (lpOneAlg.single p.2.1 (1 : 𝕜)) (lpOneAlg.single p.2.2 (1 : 𝕜))‖
      / (FiberTrivialization.weight (E := E) p.1
        * FiberTrivialization.weight (E := E') p.2.1
        * FiberTrivialization.weight (E := E'') p.2.2) := by
  have hpos : ∀ p : M × M' × M'', 0 < FiberTrivialization.weight (E := E) p.1
      * FiberTrivialization.weight (E := E') p.2.1
      * FiberTrivialization.weight (E := E'') p.2.2 := fun p =>
    mul_pos (mul_pos (FiberTrivialization.weight_pos p.1) (FiberTrivialization.weight_pos p.2.1))
      (FiberTrivialization.weight_pos p.2.2)
  have hle : ∀ p : M × M' × M'', ‖T (lpOneAlg.single p.1 (1 : 𝕜))
        (lpOneAlg.single p.2.1 (1 : 𝕜)) (lpOneAlg.single p.2.2 (1 : 𝕜))‖
      / (FiberTrivialization.weight (E := E) p.1
        * FiberTrivialization.weight (E := E') p.2.1
        * FiberTrivialization.weight (E := E'') p.2.2) ≤ ‖T‖ := fun p =>
    (div_le_iff₀ (hpos p)).mpr ((cols_le_opNorm₃ T p.1 p.2.1 p.2.2).trans_eq (by ring))
  have hbdd : BddAbove (Set.range fun p : M × M' × M'' => ‖T (lpOneAlg.single p.1 (1 : 𝕜))
        (lpOneAlg.single p.2.1 (1 : 𝕜)) (lpOneAlg.single p.2.2 (1 : 𝕜))‖
      / (FiberTrivialization.weight (E := E) p.1
        * FiberTrivialization.weight (E := E') p.2.1
        * FiberTrivialization.weight (E := E'') p.2.2)) :=
    ⟨‖T‖, by rintro _ ⟨p, rfl⟩; exact hle p⟩
  refine le_antisymm ?_ (Real.iSup_le hle T.opNorm_nonneg)
  refine opNorm_le_of_cols₃ T
    (Real.iSup_nonneg fun p => div_nonneg (norm_nonneg _) (hpos p).le) fun i j k => ?_
  refine ((div_le_iff₀ (hpos (i, j, k))).mp (le_ciSup hbdd (i, j, k))).trans_eq ?_
  ring

end OpNorm

end Multilinear

end lpOneAlg

end RadiiPolynomial
