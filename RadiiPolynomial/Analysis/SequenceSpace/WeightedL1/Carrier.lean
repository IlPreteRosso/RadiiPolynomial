import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.FiberTrivialization
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# The weighted ℓ¹ carrier `lpOneAlg M E`

`lpOneAlg M E` wraps `lp E 1`: the families `f m ∈ E m` with `∑' m, ‖f m‖ < ∞`, normed by that
sum. This file is the carrier half of the weighted ℓ¹ API; it uses no operation on the index type
and no convolution. The convolution ring structure is in `WeightedL1/Algebra.lean`.

## Contents

* The fiber classes: the legacy trivialization data `lpAlgRingData` with its weight
  `lpAlgRingData.weight`, the scalar-compatibility class `lpAlgSmulCompat`, and the Beurling-weight
  classes `lpOneAlgWeightMul`, `lpOneAlgWeightSubMul`.
* The one-way compatibility layer from `FiberTrivialization` to `lpAlgRingData`.
* The structure `lpOneAlg`, its normed-group, complete-space and normed-space instances, and the
  norm faces `norm_eq_tsum`, `summable_norm`, `norm_apply_le_norm`.
* The coefficient sequence `toRealSeq` with extensionality `ext_toRealSeq` and its additive faces,
  bundled as the injective additive monoid hom `toRealSeqAddHom` (`toRealSeq_injective`,
  `toRealSeq_finset_sum`); the positivity of the fiber weights `norm_ofReal_one_pos`; and the
  bound `abs_toRealSeq_le` under weight ≥ 1.
* Over the index `ℤ` with any fibers: the sign split `norm_eq_tsum_natCast_add_tsum_neg`, its
  vanishing-negative form `norm_eq_tsum_natCast_of_neg`, and the finite-support sums
  `norm_eq_bilatFinSum`, `norm_eq_natFinSum_of_finSupp`.
* The singles `single` (coefficient atom `toRealSeq_single_eq_piSingle`), the mode expansion
  `hasSum_single`, coordinate evaluation `evalCLM`, and the column-norm bounds
  `norm_le_of_cols`, `finsum_norm_le_of_cols`.

## Typeclass convention

The fiber data `lpAlgRingData` and the scalar-compatibility class `lpAlgSmulCompat` are
monoid-independent and have no additive versions. The weight classes come in pairs: the additive
classes (`lpOneAlgWeightMul`, `lpOneAlgWeightSubMul`) are declared directly, and the multiplicative
ones (`lpOneMulAlgWeightMul`, `lpOneMulAlgWeightSubMul`) are linked to them by
`@[to_additive existing]`. Helper definitions and lemmas are stated in multiplicative spelling and
generate their additive versions via `@[to_additive]` (`mulToRealSeq` ↦ `toRealSeq`);
`mulToRealSeq` itself needs no monoid structure on `M`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### Typeclasses -/

/-- **Legacy (deprecated interface; prefer `FiberTrivialization`).** Ten-field trivialization
of each fiber `E m` as a weighted copy of the scalar field `𝕜`.

For each `m : M`, the maps `toReal m` and `ofReal m` are mutually inverse additive-group
isomorphisms between `E m` and `𝕜`. The norm is scaled by the weight
`ω_m := ‖ofReal m 1‖`, giving `‖ofReal m r‖ = ‖r‖ * ω_m`, so each fiber is isometric
to `(𝕜, ω_m · ‖·‖)`. Together, these data identify `lpOneAlg M E` with the weighted
ℓ¹ space of `𝕜`-valued sequences on `M`, with weight `ω`.

Kept as a one-way compatibility layer: every `FiberTrivialization 𝕜 M E` provides an instance
(`FiberTrivialization.toLpAlgRingData`); there is no instance in the reverse direction (use the
explicit constructor `FiberTrivialization.ofLpAlgRingData`, which also needs `lpAlgSmulCompat`).

Monoid-independent — the same data works for both `[Monoid M]` and `[AddMonoid M]`. -/
class lpAlgRingData (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [∀ m, NormedAddCommGroup (E m)] where
  toReal : ∀ m, E m → 𝕜
  ofReal : ∀ m, 𝕜 → E m
  toReal_ofReal : ∀ m r, toReal m (ofReal m r) = r
  ofReal_toReal : ∀ m x, ofReal m (toReal m x) = x
  ofReal_add : ∀ m a b, ofReal m (a + b) = ofReal m a + ofReal m b
  ofReal_zero : ∀ m, ofReal m 0 = 0
  toReal_add : ∀ m x y, toReal m (x + y) = toReal m x + toReal m y
  toReal_zero : ∀ m, toReal m 0 = 0
  toReal_neg : ∀ m x, toReal m (-x) = -(toReal m x)
  norm_ofReal_eq : ∀ m r, ‖ofReal m r‖ = ‖r‖ * ‖ofReal m 1‖

/-- **Legacy (deprecated interface; prefer `FiberTrivialization`).** Upgrades the fiber
trivialization from `lpAlgRingData` to a `𝕜`-module isomorphism.

The additive isomorphism `toReal m : E m → 𝕜` from `lpAlgRingData` intertwines scalar
multiplication: `toReal m (r • x) = r * toReal m x`. Combined with `lpAlgRingData`, each
fiber `E m` becomes a one-dimensional `𝕜`-module isomorphic to `𝕜` itself, with norm
scaled by the weight `ω_m`. For data derived from a `FiberTrivialization` this witness is
the instance `FiberTrivialization.toLpAlgSmulCompat` (it is `map_smul` of `θ_m⁻¹`), indexed by
the derived data only.

Monoid-independent — separated from `lpAlgRingData` because it requires `NormedSpace 𝕜`. -/
class lpAlgSmulCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [lpAlgRingData 𝕜 M E] where
  toReal_smul : ∀ m (r : 𝕜) (x : E m),
    lpAlgRingData.toReal m (r • x) = r * lpAlgRingData.toReal m x

/-- The weight `ω_m = ‖ofReal m 1‖` of legacy fiber data. For data derived from a
`FiberTrivialization` it is definitionally `FiberTrivialization.weight m`. -/
def lpAlgRingData.weight {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
    [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] (m : M) : ℝ :=
  ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖

lemma lpAlgRingData.weight_def {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
    [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] (m : M) :
    lpAlgRingData.weight (E := E) m = ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ := rfl

/-- Every fiber weight `‖ofReal m 1‖` of a scalar-trivialized fiber family is positive:
`ofReal m` has the left inverse `toReal m`, so `ofReal m 1 ≠ 0`. -/
theorem lpOneAlg.norm_ofReal_one_pos {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
    [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] (m : M) :
    0 < ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ := by
  rw [norm_pos_iff]
  intro h
  have h1 := congr_arg (lpAlgRingData.toReal (E := E) m) h
  rw [lpAlgRingData.toReal_ofReal, lpAlgRingData.toReal_zero] at h1
  exact one_ne_zero h1

/-- Beurling weight (additive index monoid): `ω_{j+l} ≤ ω_j ω_l` and `ω_0 = 1`, stated on the
weight alone. The old two-scalar inequality is the derived lemma `norm_ofReal_mul_le`. -/
class lpOneAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  weight_add_le : ∀ j l : M,
    lpAlgRingData.weight (E := E) (j + l) ≤
      lpAlgRingData.weight (E := E) j * lpAlgRingData.weight (E := E) l
  weight_zero : lpAlgRingData.weight (E := E) (0 : M) = 1

/-- Beurling weight (multiplicative index monoid): `ω_{j*l} ≤ ω_j ω_l` and `ω_1 = 1`.
Sufficient for Ring on `lpOneAlg` when `[HasMulAntidiagonal M]` (finite fibers,
`lpOneAlg.instMulConvCompatOfAntidiag`) or when `𝕜` is complete
(`lpOneAlg.instMulConvCompatOfWeightMul`). -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgWeightMul]
class lpOneMulAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  weight_mul_le : ∀ j l : M,
    lpAlgRingData.weight (E := E) (j * l) ≤
      lpAlgRingData.weight (E := E) j * lpAlgRingData.weight (E := E) l
  /-- Weight at identity = 1: ensures `‖1‖ = 1` (NormOneClass). -/
  weight_one : lpAlgRingData.weight (E := E) (1 : M) = 1

class lpOneAlgWeightSubMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E]
    extends lpOneAlgWeightMul 𝕜 M E where
  /-- Weight ≥ 1: provides the fiberwise bound `‖toRealSeq f m‖ ≤ ‖f m‖`,
  embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
  one_le_weight : ∀ m, 1 ≤ lpAlgRingData.weight (E := E) m

/-- Submultiplicative weight with weight ≥ 1.
Extends `lpOneMulAlgWeightMul`. The weight ≥ 1 axiom is not used for Cauchy
sum convergence (submultiplicativity alone suffices, see
`instMulConvCompatOfWeightMul`); it provides the fiberwise bound
`‖mulToRealSeq f m‖ ≤ ‖f m‖` (see `abs_mulToRealSeq_le`), which embeds the
extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgWeightSubMul]
class lpOneMulAlgWeightSubMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E]
    extends lpOneMulAlgWeightMul 𝕜 M E where
  /-- Weight ≥ 1: provides the fiberwise bound `‖mulToRealSeq f m‖ ≤ ‖f m‖`,
  embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
  one_le_weight : ∀ m, 1 ≤ lpAlgRingData.weight (E := E) m

/-! ### Retained two-scalar forms of the Beurling hypotheses (derived) -/

section BeurlingWrappers

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E]

/-- Old two-scalar form: `‖ofReal (j*l) (a*b)‖ ≤ ‖ofReal j a‖ * ‖ofReal l b‖`
(derived from `weight_mul_le` and the scaling identity). -/
@[to_additive (dont_translate := E 𝕜) lpOneAlgWeightMul.norm_ofReal_mul_le]
theorem lpOneMulAlgWeightMul.norm_ofReal_mul_le [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E]
    (j l : M) (a b : 𝕜) :
    ‖lpAlgRingData.ofReal (E := E) (j * l) (a * b)‖ ≤
      ‖lpAlgRingData.ofReal (E := E) j a‖ * ‖lpAlgRingData.ofReal (E := E) l b‖ := by
  rw [lpAlgRingData.norm_ofReal_eq, lpAlgRingData.norm_ofReal_eq (E := E) j,
    lpAlgRingData.norm_ofReal_eq (E := E) l, norm_mul]
  have h := lpOneMulAlgWeightMul.weight_mul_le (E := E) j l
  simp only [lpAlgRingData.weight] at h
  exact (mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg a) (norm_nonneg b))).trans_eq
    (by ring)

/-- Old form of the unit-weight hypothesis: `‖ofReal 1 1‖ = 1`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlgWeightMul.norm_ofReal_one_zero]
theorem lpOneMulAlgWeightMul.norm_ofReal_one_one [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] :
    ‖lpAlgRingData.ofReal (E := E) (1 : M) (1 : 𝕜)‖ = 1 :=
  lpOneMulAlgWeightMul.weight_one (E := E)

/-- Old form of the weight ≥ 1 hypothesis: `1 ≤ ‖ofReal m 1‖`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlgWeightSubMul.norm_ofReal_one_ge]
theorem lpOneMulAlgWeightSubMul.norm_ofReal_one_ge [Monoid M] [lpOneMulAlgWeightSubMul 𝕜 M E]
    (m : M) : 1 ≤ ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ :=
  lpOneMulAlgWeightSubMul.one_le_weight m

end BeurlingWrappers

/-! ### Compatibility layer: `FiberTrivialization` → legacy data (one-way) -/

namespace FiberTrivialization

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]

/-- The legacy ten-field data of a fiber trivialization: `toReal m = θ_m⁻¹`,
`ofReal m = θ_m`. This is the ONLY instance between the two interfaces (one-way). -/
instance toLpAlgRingData [FiberTrivialization 𝕜 M E] : lpAlgRingData 𝕜 M E where
  toReal m := (equiv (E := E) m).symm
  ofReal m := equiv (E := E) m
  toReal_ofReal m r := LinearEquiv.symm_apply_apply _ r
  ofReal_toReal m x := LinearEquiv.apply_symm_apply _ x
  ofReal_add m a b := map_add _ a b
  ofReal_zero m := map_zero _
  toReal_add m x y := map_add _ x y
  toReal_zero m := map_zero _
  toReal_neg m x := map_neg _ x
  norm_ofReal_eq m r := by
    rw [norm_equiv_apply, norm_equiv_apply, norm_one, one_mul]

/-- The scalar-compatibility witness, indexed specifically by the derived data
`toLpAlgRingData` (never synthesized for independently supplied legacy data). -/
instance toLpAlgSmulCompat [FiberTrivialization 𝕜 M E] :
    @lpAlgSmulCompat 𝕜 _ M E _ _ (toLpAlgRingData (𝕜 := 𝕜)) where
  toReal_smul m r x := map_smul (equiv (E := E) m).symm r x

lemma toLpAlgRingData_toReal [FiberTrivialization 𝕜 M E] (m : M) (x : E m) :
    lpAlgRingData.toReal (𝕜 := 𝕜) m x = (equiv (E := E) m).symm x := rfl

lemma toLpAlgRingData_ofReal [FiberTrivialization 𝕜 M E] (m : M) (r : 𝕜) :
    lpAlgRingData.ofReal (E := E) m r = equiv (E := E) m r := rfl

lemma toLpAlgRingData_weight [FiberTrivialization 𝕜 M E] (m : M) :
    lpAlgRingData.weight (E := E) m = weight (E := E) m := rfl

/-- Explicit constructor (NOT an instance) of a fiber trivialization from a particular legacy
data instance together with its matching scalar-compatibility witness. -/
@[instance_reducible]
def ofLpAlgRingData (d : lpAlgRingData 𝕜 M E) [@lpAlgSmulCompat 𝕜 _ M E _ _ d] :
    FiberTrivialization 𝕜 M E where
  equiv m :=
    { toFun := d.ofReal m
      invFun := d.toReal m
      map_add' := d.ofReal_add m
      map_smul' := fun r a => by
        show d.ofReal m (r * a) = r • d.ofReal m a
        conv_rhs => rw [← d.ofReal_toReal m (r • d.ofReal m a)]
        rw [lpAlgSmulCompat.toReal_smul m r (d.ofReal m a), d.toReal_ofReal]
      left_inv := d.toReal_ofReal m
      right_inv := d.ofReal_toReal m }

/-- Not `@[simp]`: as a simp lemma it would unify any `FiberTrivialization` instance with
`ofLpAlgRingData ?d` and rewrite the primary datum `equiv` into the legacy projection. -/
lemma ofLpAlgRingData_equiv_apply (d : lpAlgRingData 𝕜 M E)
    [@lpAlgSmulCompat 𝕜 _ M E _ _ d] (m : M) (r : 𝕜) :
    (ofLpAlgRingData d).equiv m r = d.ofReal m r := rfl

/-- Not `@[simp]`; see `ofLpAlgRingData_equiv_apply`. -/
lemma ofLpAlgRingData_equiv_symm_apply (d : lpAlgRingData 𝕜 M E)
    [@lpAlgSmulCompat 𝕜 _ M E _ _ d] (m : M) (x : E m) :
    ((ofLpAlgRingData d).equiv m).symm x = d.toReal m x := rfl

end FiberTrivialization

/-! ### lpOneAlg Structure -/

structure lpOneAlg (M : Type*) (E : M → Type*) [∀ m, NormedAddCommGroup (E m)] where
  toLp : lp E 1

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

protected def equiv : lpOneAlg M E ≃ lp E 1 where
  toFun := toLp
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instNormedAddCommGroup : NormedAddCommGroup (lpOneAlg M E) :=
  lpOneAlg.equiv.normedAddCommGroup

instance instCompleteSpace [∀ m, CompleteSpace (E m)] : CompleteSpace (lpOneAlg M E) :=
  (completeSpace_congr (Isometry.isUniformEmbedding
    (show Isometry lpOneAlg.equiv from fun _ _ => rfl))).mpr inferInstance

instance : CoeFun (lpOneAlg M E) (fun _ => ∀ m, E m) where
  coe f := f.toLp

/-- NormedSpace 𝕜 for lpOneAlg, transferred from lp. No algebraic constraint on M needed. -/
instance instNormedSpaceBase {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)] :
    NormedSpace 𝕜 (lpOneAlg M E) :=
  { lpOneAlg.equiv.addEquiv.module 𝕜 with
    norm_smul_le := fun r f => by
      show ‖r • f.toLp‖ ≤ _; exact norm_smul_le r f.toLp }

@[simp] theorem toLp_zero : (0 : lpOneAlg M E).toLp = 0 := rfl
@[simp] theorem toLp_add (f g : lpOneAlg M E) : (f + g).toLp = f.toLp + g.toLp := rfl
@[simp] theorem toLp_neg (f : lpOneAlg M E) : (-f).toLp = -f.toLp := rfl
@[simp] theorem toLp_sub (f g : lpOneAlg M E) : (f - g).toLp = f.toLp - g.toLp := rfl

@[simp] theorem toLp_smul {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)]
    (r : 𝕜) (f : lpOneAlg M E) : (r • f).toLp = r • f.toLp := rfl

theorem ext {f g : lpOneAlg M E} (h : ∀ m, f m = g m) : f = g := by
  have : f.toLp = g.toLp := lp.ext (funext h)
  cases f; cases g; simpa using this

theorem norm_def (f : lpOneAlg M E) : ‖f‖ = ‖f.toLp‖ := rfl

theorem norm_eq_tsum (f : lpOneAlg M E) : ‖f‖ = ∑' m, ‖f m‖ := by
  rw [norm_def, lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

theorem summable_norm (f : lpOneAlg M E) : Summable (fun m => ‖f m‖) := by
  have hf := lp.memℓp f.toLp
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf
  simpa using hf

/-- Shifted norm sums are summable: `∑ ‖f(m + s)‖ < ∞` for any `s`. -/
theorem summable_norm_shift [AddRightCancelMonoid M] (f : lpOneAlg M E) (s : M) :
    Summable (fun m => ‖f (m + s)‖) :=
  (summable_norm f).comp_injective (add_left_injective s)

/-- Product norm summability: `∑ ‖f a‖ * ‖g b‖ < ∞` over `M × M`. -/
theorem summable_norm_prod (f g : lpOneAlg M E) :
    Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) := by
  have := (summable_norm f).mul_of_nonneg (summable_norm g)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact this

/-! ### Underlying 𝕜-valued Sequence (monoid-independent) -/

section AlgHelpers

variable {𝕜 : Type*} [NormedField 𝕜] [lpAlgRingData 𝕜 M E]

/-- The underlying 𝕜-valued sequence. Monoid-independent. -/
@[to_additive (dont_translate := E 𝕜) toRealSeq]
def mulToRealSeq (f : lpOneAlg M E) : M → 𝕜 :=
  fun m => lpAlgRingData.toReal m (f m)

@[to_additive (dont_translate := E 𝕜) norm_eq_abs_toReal_mul_weight]
theorem norm_eq_abs_mulToReal_mul_weight (f : lpOneAlg M E) (m : M) :
    ‖f m‖ = ‖mulToRealSeq f m‖ * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ := by
  conv_lhs => rw [show f m = lpAlgRingData.ofReal (E := E) m (mulToRealSeq f m)
    from (lpAlgRingData.ofReal_toReal m (f m)).symm]
  exact lpAlgRingData.norm_ofReal_eq m _

/-- Extensionality via toRealSeq. -/
@[to_additive (dont_translate := E 𝕜) ext_toRealSeq]
theorem ext_mulToRealSeq {f g : lpOneAlg M E}
    (h : mulToRealSeq f = mulToRealSeq g) : f = g :=
  ext fun m => (lpAlgRingData.ofReal_toReal m (f m)).symm ▸
    (lpAlgRingData.ofReal_toReal m (g m)).symm ▸ congr_arg _ (congr_fun h m)

@[to_additive (dont_translate := E 𝕜) toRealSeq_add]
theorem mulToRealSeq_add (f g : lpOneAlg M E) :
    mulToRealSeq (f + g) = mulToRealSeq f + mulToRealSeq g :=
  funext fun m => lpAlgRingData.toReal_add m _ _

@[to_additive (dont_translate := E 𝕜) toRealSeq_zero]
theorem mulToRealSeq_zero : mulToRealSeq (0 : lpOneAlg M E) = 0 :=
  funext fun m => lpAlgRingData.toReal_zero m

@[to_additive (dont_translate := E 𝕜) toRealSeq_neg]
theorem mulToRealSeq_neg (f : lpOneAlg M E) :
    mulToRealSeq (-f) = -(mulToRealSeq f) := by
  funext m
  show lpAlgRingData.toReal m ((-f).toLp m) = -(lpAlgRingData.toReal m (f.toLp m))
  rw [toLp_neg, lp.coeFn_neg, Pi.neg_apply, lpAlgRingData.toReal_neg]

@[to_additive (dont_translate := E 𝕜) toRealSeq_sub]
theorem mulToRealSeq_sub (f g : lpOneAlg M E) :
    mulToRealSeq (f - g) = mulToRealSeq f - mulToRealSeq g := by
  rw [sub_eq_add_neg, mulToRealSeq_add, mulToRealSeq_neg, sub_eq_add_neg]

/-- The coefficient map `toRealSeq` as an additive monoid hom (injective: `toRealSeq_injective`). -/
def toRealSeqAddHom : lpOneAlg M E →+ (M → 𝕜) where
  toFun := toRealSeq
  map_zero' := toRealSeq_zero
  map_add' := toRealSeq_add

@[simp] theorem toRealSeqAddHom_apply (f : lpOneAlg M E) :
    toRealSeqAddHom (𝕜 := 𝕜) f = toRealSeq f := rfl

/-- The coefficient map `toRealSeq` is injective: two elements of `lpOneAlg M E` with the same
coefficients in every fiber are equal. -/
theorem toRealSeq_injective : Function.Injective (toRealSeq : lpOneAlg M E → M → 𝕜) :=
  fun _ _ h => ext_toRealSeq h

/-- Coefficient extraction commutes with finite sums (`map_sum` of `toRealSeqAddHom`). -/
theorem toRealSeq_finset_sum {ι : Type*} (s : Finset ι) (a : ι → lpOneAlg M E) (k : M) :
    toRealSeq (∑ i ∈ s, a i) k = ∑ i ∈ s, toRealSeq (a i) k := by
  rw [← toRealSeqAddHom_apply, map_sum, Finset.sum_apply]
  rfl

end AlgHelpers

/-! ### Weight-dependent summability (needs [Monoid M] for to_additive) -/

section MulWeightHelpers

variable {𝕜 : Type*} [NormedField 𝕜] [Monoid M] [lpAlgRingData 𝕜 M E]
variable [lpOneMulAlgWeightSubMul 𝕜 M E]

/-- `‖mulToRealSeq f m‖ ≤ ‖f m‖` (from weight ≥ 1). -/
@[to_additive (dont_translate := E 𝕜) abs_toRealSeq_le]
theorem abs_mulToRealSeq_le (f : lpOneAlg M E) (m : M) :
    ‖mulToRealSeq f m‖ ≤ ‖f m‖ := by
  rw [norm_eq_abs_mulToReal_mul_weight f m]
  exact le_mul_of_one_le_right (norm_nonneg _) (lpOneMulAlgWeightSubMul.norm_ofReal_one_ge m)

@[to_additive (dont_translate := E 𝕜) summable_abs_toRealSeq]
theorem summable_abs_mulToRealSeq (f : lpOneAlg M E) :
    Summable (fun m => ‖mulToRealSeq f m‖) :=
  (summable_norm f).of_nonneg_of_le (fun _ => norm_nonneg _) (abs_mulToRealSeq_le f)

end MulWeightHelpers

end lpOneAlg

/-! ### The sign split of the norm over `ℤ` (any fibers)

For `lpOneAlg ℤ E` with arbitrary normed fibers, the norm splits along `ℤ = ℕ ⊔ (-(ℕ + 1))`; the
negative modes are written `-((n : ℤ) + 1)`, the normal form of Mathlib's
`tsum_of_nat_of_neg_add_one`. -/

section IntSplit

/-- Sign split of the bilateral norm: `‖f‖ = ∑' n, ‖f n‖ + ∑' n, ‖f (-(n + 1))‖`. -/
theorem lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg {E : ℤ → Type*}
    [∀ k, NormedAddCommGroup (E k)] (f : lpOneAlg ℤ E) :
    ‖f‖ = (∑' n : ℕ, ‖f (n : ℤ)‖) + ∑' n : ℕ, ‖f (-((n : ℤ) + 1))‖ := by
  have hs := lpOneAlg.summable_norm f
  rw [lpOneAlg.norm_eq_tsum f]
  exact tsum_of_nat_of_neg_add_one (hs.comp_injective fun _ _ h => by omega)
    (hs.comp_injective fun _ _ h => by omega)

/-- With vanishing negative modes the norm is the sum over the nonnegative modes. -/
theorem lpOneAlg.norm_eq_tsum_natCast_of_neg {E : ℤ → Type*} [∀ k, NormedAddCommGroup (E k)]
    (f : lpOneAlg ℤ E) (h : ∀ n : ℕ, f (-((n : ℤ) + 1)) = 0) :
    ‖f‖ = ∑' n : ℕ, ‖f (n : ℤ)‖ := by
  rw [lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg f,
    (tsum_congr fun n => by rw [h n, norm_zero] : (∑' n : ℕ, ‖f (-((n : ℤ) + 1))‖) = _),
    tsum_zero, add_zero]

/-- The norm of an element supported in `|k| ≤ N` as a finite bilateral sum. -/
theorem lpOneAlg.norm_eq_bilatFinSum {E : ℤ → Type*} [∀ k, NormedAddCommGroup (E k)]
    (f : lpOneAlg ℤ E) (N : ℕ)
    (h_tail : ∀ n : ℕ, N < n → ‖f (↑n : ℤ)‖ = 0)
    (h_negtail : ∀ n : ℕ, N < n + 1 → ‖f (Int.negSucc n)‖ = 0) :
    ‖f‖ = (∑ n : Fin (N + 1), ‖f (↑(n : ℕ) : ℤ)‖)
      + ∑ n : Fin N, ‖f (Int.negSucc (n : ℕ))‖ := by
  have hidx : ∀ n : ℕ, -((n : ℤ) + 1) = Int.negSucc n := fun n => by omega
  rw [lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg f]
  congr 1
  · rw [tsum_eq_sum (s := Finset.range (N + 1))
      (fun n hn => h_tail n (by simp [Finset.mem_range] at hn; omega)),
      ← Fin.sum_univ_eq_sum_range]
  · rw [tsum_eq_sum (f := fun n : ℕ => ‖f (-((n : ℤ) + 1))‖) (s := Finset.range N)
      (fun n hn => by
        rw [hidx n]
        exact h_negtail n (by simp [Finset.mem_range] at hn; omega)),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun n _ => by rw [hidx n]

/-- The norm of an element vanishing at the negative modes and supported in `0 ≤ k ≤ N`, as a
finite sum over the nonnegative modes. -/
theorem lpOneAlg.norm_eq_natFinSum_of_finSupp {E : ℤ → Type*} [∀ k, NormedAddCommGroup (E k)]
    (f : lpOneAlg ℤ E) (N : ℕ)
    (h_neg : ∀ m : ℕ, (f : ∀ k : ℤ, E k) (Int.negSucc m) = 0)
    (h_tail : ∀ n : ℕ, N < n → ‖(f : ∀ k : ℤ, E k) (↑n : ℤ)‖ = 0) :
    ‖f‖ = ∑ n : Fin (N + 1), ‖(f : ∀ k : ℤ, E k) (↑(n : ℕ) : ℤ)‖ := by
  rw [lpOneAlg.norm_eq_bilatFinSum f N h_tail (fun n _ => by rw [h_neg, norm_zero])]
  simp only [h_neg, norm_zero, Finset.sum_const_zero, add_zero]

end IntSplit

/-! ### Scalar Multiplication Compatibility -/

section lpOneAlgSmul

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [lpAlgRingData 𝕜 M E]
variable [∀ m, NormedSpace 𝕜 (E m)]
variable [lpAlgSmulCompat 𝕜 M E]

theorem lpOneAlg.toRealSeq_smul (r : 𝕜) (f : lpOneAlg M E) :
    lpOneAlg.toRealSeq (r • f) = r • lpOneAlg.toRealSeq f := by
  ext m; simp only [lpOneAlg.toRealSeq, Pi.smul_apply, smul_eq_mul]
  exact lpAlgSmulCompat.toReal_smul m r (f m)

end lpOneAlgSmul

/-! ### Singles, mode expansion, and column-norm bounds

Monoid-independent API (the index `M` needs no algebraic structure except where
stated). Sequence-mentioning statements use the additive `toRealSeq` spelling,
matching `toRealSeq_smul` above; both production index types (ℕ, ℤ) are additive.

The column-norm bounds realize the ℓ¹ principle: out of a weighted ℓ¹ space, an
operator's norm is controlled by the sup of its weighted column norms. Promoted
from the Example 14.2.1 toolkit (2026-08-25). -/

namespace lpOneAlg

section Single

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

theorem norm_apply_le_norm (f : lpOneAlg M E) (m : M) : ‖f m‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm one_ne_zero f.toLp m

theorem isometry_mk : Isometry (mk : lp E 1 → lpOneAlg M E) :=
  fun _ _ => rfl

/-- The wrapper `lp E 1 → lpOneAlg M E` as an additive monoid hom. -/
def mkAddHom : lp E 1 →+ lpOneAlg M E where
  toFun := mk
  map_zero' := rfl
  map_add' _ _ := rfl

variable [lpAlgRingData 𝕜 M E] [DecidableEq M]

/-- The element with value `x` at index `j` and `0` elsewhere. -/
def single (j : M) (x : 𝕜) : lpOneAlg M E :=
  ⟨lp.single 1 j (lpAlgRingData.ofReal (E := E) j x)⟩

theorem toRealSeq_single (j : M) (x : 𝕜) (k : M) :
    toRealSeq (single (E := E) j x) k = if k = j then x else 0 := by
  show lpAlgRingData.toReal k ((single (E := E) j x) k) = _
  by_cases h : k = j
  · subst h
    show lpAlgRingData.toReal k
      (Pi.single k (lpAlgRingData.ofReal (E := E) k x) k) = _
    rw [Pi.single_eq_same, lpAlgRingData.toReal_ofReal, ite_eq_left rfl]
  · show lpAlgRingData.toReal k
      (Pi.single j (lpAlgRingData.ofReal (E := E) j x) k) = _
    rw [Pi.single_eq_of_ne h, lpAlgRingData.toReal_zero, ite_eq_right h]

/-- The coefficient sequence of an atom is the atom `Pi.single j x`. -/
theorem toRealSeq_single_eq_piSingle (j : M) (x : 𝕜) :
    toRealSeq (single (E := E) j x) = Pi.single j x :=
  funext fun k => (toRealSeq_single j x k).trans (Pi.single_apply j x k).symm

theorem norm_single (j : M) (x : 𝕜) :
    ‖(single (E := E) j x : lpOneAlg M E)‖
      = ‖x‖ * ‖lpAlgRingData.ofReal (E := E) j (1 : 𝕜)‖ := by
  show ‖lp.single 1 j (lpAlgRingData.ofReal (E := E) j x)‖ = _
  rw [lp.norm_single (by norm_num), lpAlgRingData.norm_ofReal_eq]

/-- Every element is the norm-convergent sum of its singles (transfer of
`lp.hasSum_single` through the wrapper). -/
theorem hasSum_single (h : lpOneAlg M E) :
    HasSum (fun m : M => single (E := E) m (toRealSeq h m)) h := by
  have h0 : HasSum (fun m : M => lp.single 1 m (h.toLp m)) h.toLp :=
    lp.hasSum_single (by norm_num) h.toLp
  have h1 := h0.map (mkAddHom (E := E)) (isometry_mk (E := E)).continuous
  have heq : (⇑(mkAddHom (E := E)) ∘ fun m : M => lp.single 1 m (h.toLp m))
      = fun m : M => single (E := E) m (toRealSeq h m) := by
    funext m
    show mk (lp.single 1 m (h.toLp m)) = single (E := E) m (toRealSeq h m)
    unfold single
    rw [show lpAlgRingData.ofReal (E := E) m (toRealSeq h m)
      = h.toLp m from lpAlgRingData.ofReal_toReal m (h.toLp m)]
  rw [heq] at h1
  exact h1

variable [∀ m, NormedSpace 𝕜 (E m)]

/-- Mode expansion pushed through a continuous linear map. -/
theorem hasSum_single_mapCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (W : lpOneAlg M E →L[𝕜] F) (h : lpOneAlg M E) :
    HasSum (fun m : M => W (single m (toRealSeq h m))) (W h) :=
  (hasSum_single h).mapL W

variable [lpAlgSmulCompat 𝕜 M E]

theorem single_smul (j : M) (x : 𝕜) :
    single (E := E) j x = x • single j 1 := by
  apply ext_toRealSeq
  funext k
  rw [show toRealSeq (x • single (E := E) j 1) k
      = x * toRealSeq (single (E := E) j 1) k from
    congr_fun (toRealSeq_smul x _) k]
  rw [toRealSeq_single, toRealSeq_single]
  split_ifs <;> ring

end Single

section EvalCLM

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)]

/-- Coordinate evaluation as a continuous linear map (norm ≤ 1). -/
def evalCLM (m : M) : lpOneAlg M E →L[𝕜] E m :=
  LinearMap.mkContinuous
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by rw [one_mul]; exact norm_apply_le_norm f m)

@[simp] theorem evalCLM_apply (m : M) (f : lpOneAlg M E) :
    evalCLM (𝕜 := 𝕜) m f = f m := rfl

end EvalCLM

section ColumnNorm

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [lpAlgRingData 𝕜 M E] [DecidableEq M]
variable [∀ m, NormedSpace 𝕜 (E m)] [lpAlgSmulCompat 𝕜 M E]

/-- **Column-norm bound.** Out of a weighted ℓ¹ space, an operator norm is
controlled by the weighted column norms: if `‖W (single m 1)‖ ≤ C · ω_m` for
every `m` (with `ω_m = ‖ofReal m 1‖` the weight), then `‖W h‖ ≤ C · ‖h‖`. -/
theorem norm_le_of_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (W : lpOneAlg M E →L[𝕜] F) {C : ℝ}
    (hcol : ∀ m : M, ‖W (single m 1)‖
      ≤ C * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖)
    (h : lpOneAlg M E) : ‖W h‖ ≤ C * ‖h‖ := by
  have hexp := hasSum_single_mapCLM W h
  have hterm : ∀ m : M, ‖W (single m (toRealSeq h m))‖
      ≤ ‖toRealSeq h m‖ * (C * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖) := by
    intro m
    rw [single_smul, map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hcol m) (norm_nonneg _)
  have hmaj : Summable (fun m : M =>
      ‖toRealSeq h m‖ * (C * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖)) := by
    refine ((summable_norm h).mul_left C).congr fun m => ?_
    rw [norm_eq_abs_toReal_mul_weight h m]
    ring
  have hsumm : Summable (fun m : M => ‖W (single m (toRealSeq h m))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  rw [← hexp.tsum_eq]
  refine (norm_tsum_le_tsum_norm hsumm).trans ?_
  refine (Summable.tsum_le_tsum hterm hsumm hmaj).trans (le_of_eq ?_)
  rw [norm_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [norm_eq_abs_toReal_mul_weight h m]; ring

/-- **Finite-part column-norm bound.** A finite family of output coordinates
`g : ι → M'` of `W h` is controlled by the same finite sums on the columns:
if `∑_{n ∈ s} ‖(W (single m 1)) (g n)‖ ≤ ε · ω_m` for every `m`, then
`∑_{n ∈ s} ‖(W h) (g n)‖ ≤ ε · ‖h‖`. -/
theorem finsum_norm_le_of_cols {M' : Type*} {E' : M' → Type*}
    [∀ n, NormedAddCommGroup (E' n)] [∀ n, NormedSpace 𝕜 (E' n)]
    {ι : Type*} (W : lpOneAlg M E →L[𝕜] lpOneAlg M' E')
    (s : Finset ι) (g : ι → M') {ε : ℝ}
    (hcol : ∀ m : M, ∑ n ∈ s, ‖(W (single m 1)) (g n)‖
      ≤ ε * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖)
    (h : lpOneAlg M E) :
    ∑ n ∈ s, ‖(W h) (g n)‖ ≤ ε * ‖h‖ := by
  have hterm : ∀ (n : ι) (m : M),
      ‖(W (single m (toRealSeq h m))) (g n)‖
        = ‖toRealSeq h m‖ * ‖(W (single (E := E) m 1)) (g n)‖ := by
    intro n m
    rw [single_smul, map_smul]
    show ‖((toRealSeq h m • W (single (E := E) m 1)).toLp : ∀ k, E' k) (g n)‖ = _
    rw [toLp_smul, lp.coeFn_smul, Pi.smul_apply, norm_smul]
  have hmaj : Summable (fun m : M =>
      ‖toRealSeq h m‖ * (ε * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖)) := by
    refine ((summable_norm h).mul_left ε).congr fun m => ?_
    rw [norm_eq_abs_toReal_mul_weight h m]
    ring
  have hsumm : ∀ n ∈ s, Summable
      (fun m : M => ‖(W (single m (toRealSeq h m))) (g n)‖) := by
    intro n hn
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hmaj
    rw [hterm n m]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (Finset.single_le_sum
      (f := fun i => ‖(W (single (E := E) m 1)) (g i)‖)
      (fun i _ => norm_nonneg _) hn).trans (hcol m)
  have hfib : ∀ n : ι, HasSum
      (fun m : M => (W (single m (toRealSeq h m))) (g n)) ((W h) (g n)) := fun n =>
    (hasSum_single_mapCLM W h).mapL (evalCLM (𝕜 := 𝕜) (g n))
  have hn_le : ∀ n ∈ s, ‖(W h) (g n)‖
      ≤ ∑' m : M, ‖(W (single m (toRealSeq h m))) (g n)‖ := by
    intro n hn
    rw [← (hfib n).tsum_eq]
    exact norm_tsum_le_tsum_norm (hsumm n hn)
  refine (Finset.sum_le_sum hn_le).trans ?_
  rw [← Summable.tsum_finsetSum fun n hn => hsumm n hn]
  have hcol' : ∀ m : M, ∑ n ∈ s, ‖(W (single m (toRealSeq h m))) (g n)‖
      ≤ ‖toRealSeq h m‖ * (ε * ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖) := by
    intro m
    rw [Finset.sum_congr rfl fun n _ => hterm n m, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol m) (norm_nonneg _)
  refine (Summable.tsum_le_tsum hcol'
    (summable_sum fun n hn => hsumm n hn) hmaj).trans (le_of_eq ?_)
  rw [norm_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [norm_eq_abs_toReal_mul_weight h m]; ring

end ColumnNorm

end lpOneAlg

end RadiiPolynomial

end
