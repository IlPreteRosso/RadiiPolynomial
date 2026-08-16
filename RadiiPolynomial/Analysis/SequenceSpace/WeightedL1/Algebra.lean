import RadiiPolynomial.Algebra.Convolution.Ring
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Generalized ℓ¹ Banach Algebra with Non-Uniform Fibers

`lpOneAlg M E` wraps `lp E 1` with convolution as multiplication.

## Typeclass convention

Multiplicative typeclasses (`lpAlgRingData`, `lpOneMulAlgWeightSubMul`,
`lpAlgSmulCompat`, `lpOneMulAlgConvCompat`) are primary; additive versions
(`lpAlgRingData`, `lpOneAlgWeightSubMul`, `lpAlgSmulCompat`,
`lpOneAlgConvCompat`) are registered via `@[to_additive]`.

Helper definitions and summability lemmas (`mulToRealSeq`, `mulConvSummable`, etc.)
are defined with `[Monoid M]` and auto-generate additive versions (`toRealSeq`,
`convSummable`, etc.) via `@[to_additive]`.

Ring infrastructure helper lemmas (`mul_memℓp_mul`, `norm_mul_le_mul'`,
`mulConv_assoc`, etc.) are defined with `[Monoid M]` and auto-generate additive
versions via `@[to_additive]`. Ring *instances* (`instMul`, `instRing`, etc.) are
defined manually for both `[Monoid M]` and `[AddMonoid M]` because `to_additive`
cannot distinguish ring multiplication on `lpOneAlg` from monoid multiplication on `M`.
-/

open scoped BigOperators Topology NNReal ENNReal DiscreteConvolution

noncomputable section

namespace RadiiPolynomial

/-! ### Typeclasses -/

/-- Canonical trivialization of each fiber `E m` as a weighted copy of the scalar field `𝕜`.

For each `m : M`, the maps `toReal m` and `ofReal m` are mutually inverse additive-group
isomorphisms between `E m` and `𝕜`. The norm is scaled by the weight
`ω_m := ‖ofReal m 1‖`, giving `‖ofReal m r‖ = ‖r‖ * ω_m`, so each fiber is isometric
to `(𝕜, ω_m · ‖·‖)`. Together, these data identify `lpOneAlg M E` with the weighted
ℓ¹ space of `𝕜`-valued sequences on `M`, with weight `ω`.

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

/-- Upgrades the fiber trivialization from `lpAlgRingData` to a `𝕜`-module isomorphism.

The additive isomorphism `toReal m : E m → 𝕜` from `lpAlgRingData` intertwines scalar
multiplication: `toReal m (r • x) = r * toReal m x`. Combined with `lpAlgRingData`, each
fiber `E m` becomes a one-dimensional `𝕜`-module isomorphic to `𝕜` itself, with norm
scaled by the weight `ω_m`.

Monoid-independent — separated from `lpAlgRingData` because it requires `NormedSpace 𝕜`. -/
class lpAlgSmulCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [lpAlgRingData 𝕜 M E] where
  toReal_smul : ∀ m (r : 𝕜) (x : E m),
    lpAlgRingData.toReal m (r • x) = r * lpAlgRingData.toReal m x

class lpOneAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  norm_ofReal_mul_le : ∀ (j l : M) (a b : 𝕜),
    ‖lpAlgRingData.ofReal (E := E) (j + l) (a * b)‖ ≤
    ‖lpAlgRingData.ofReal (E := E) j a‖ * ‖lpAlgRingData.ofReal (E := E) l b‖
  norm_ofReal_one_zero : ‖lpAlgRingData.ofReal (E := E) (0 : M) (1 : 𝕜)‖ = 1

/-- Submultiplicative weight (no weight ≥ 1 requirement).
Sufficient for Ring on `lpOneAlg` when `[HasAntidiagonal M]` (finite fibers). -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgWeightMul]
class lpOneMulAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  norm_ofReal_mul_le : ∀ (j l : M) (a b : 𝕜),
    ‖lpAlgRingData.ofReal (E := E) (j * l) (a * b)‖ ≤
    ‖lpAlgRingData.ofReal (E := E) j a‖ * ‖lpAlgRingData.ofReal (E := E) l b‖
  /-- Weight at identity = 1: ensures `‖1‖ = 1` (NormOneClass). -/
  norm_ofReal_one_one : ‖lpAlgRingData.ofReal (E := E) (1 : M) (1 : 𝕜)‖ = 1

class lpOneAlgWeightSubMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E]
    extends lpOneAlgWeightMul 𝕜 M E where
  /-- Weight ≥ 1: provides the fiberwise bound `‖toRealSeq f m‖ ≤ ‖f m‖`,
  embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
  norm_ofReal_one_ge : ∀ m, 1 ≤ ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖

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
  norm_ofReal_one_ge : ∀ m, 1 ≤ ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖

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
  { lpOneAlg.equiv.module 𝕜 with
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

/-- Weight at any index is positive (from ofReal/toReal injectivity). -/
private theorem norm_mulOfReal_one_pos (m : M) :
    0 < ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ := by
  rw [norm_pos_iff]; intro h
  have h1 := congr_arg (lpAlgRingData.toReal (E := E) m) h
  rw [lpAlgRingData.toReal_ofReal, lpAlgRingData.toReal_zero] at h1
  exact one_ne_zero h1

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

/-- `ofReal` preserves negation (derived from toReal_neg + injectivity). -/
private theorem ofReal_neg (m : M) (r : 𝕜) :
    lpAlgRingData.ofReal (E := E) m (-r) = -(lpAlgRingData.ofReal m r) := by
  rw [← lpAlgRingData.ofReal_toReal (E := E) m (-(lpAlgRingData.ofReal m r))]
  congr 1; rw [lpAlgRingData.toReal_neg, lpAlgRingData.toReal_ofReal]

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

/-! ### Convolution compatibility: abstraction over summability path -/

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (additive).
Two instances: from `[lpOneAlgWeightMul]` (tsum path, submultiplicativity alone) or
from `[HasAntidiagonal M] + [lpOneAlgWeightMul 𝕜 M E]` (finite sum path, priority 1100). -/
class lpOneAlgConvCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  convSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : DiscreteConvolution.addFiber k =>
      lpOneAlg.toRealSeq f ab.1.1 * lpOneAlg.toRealSeq g ab.1.2
  tripleConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    DiscreteConvolution.AddTripleConvolutionSummable
      (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) (lpOneAlg.toRealSeq h) x
  norm_conv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution (lpOneAlg.toRealSeq f)
        (lpOneAlg.toRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.addFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (multiplicative).
Two instances: from `[lpOneMulAlgWeightMul]` (tsum path, submultiplicativity alone) or
from `[HasMulAntidiagonal M] + [lpOneMulAlgWeightMul 𝕜 M E]` (finite sum path, priority 1100). -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgConvCompat]
class lpOneMulAlgConvCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E] where
  mulConvSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2
  tripleMulConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    DiscreteConvolution.TripleConvolutionSummable
      (lpOneAlg.mulToRealSeq f) (lpOneAlg.mulToRealSeq g) (lpOneAlg.mulToRealSeq h) x
  norm_mulConv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

/-- Pointwise weighted bound for two extracted scalar coefficients. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.norm_toRealSeq_add_weight_le]
private theorem lpOneAlg.norm_mulToRealSeq_mul_weight_le
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) {j l k : M} (hjl : j * l = k) :
    ‖lpOneAlg.mulToRealSeq f j‖ * ‖lpOneAlg.mulToRealSeq g l‖ *
        ‖lpAlgRingData.ofReal (E := E) k (1 : 𝕜)‖ ≤
      ‖f j‖ * ‖g l‖ := by
  subst k
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f j,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g l]
  have hw := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) j l (1 : 𝕜) 1
  simp only [mul_one] at hw
  exact (mul_le_mul_of_nonneg_left hw
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

/-- Generic per-index bound: given fiber summability, proves the norm bound
via triangle inequality + submultiplicativity. Shared by both convolution paths. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.norm_conv_le_fiber_generic]
private theorem lpOneAlg.norm_mulConv_le_fiber_generic
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M)
    (habs : Summable fun ab : DiscreteConvolution.mulFiber k =>
      ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖) :
    ‖lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
  rw [lpAlgRingData.norm_ofReal_eq, DiscreteConvolution.ringConvolution_apply_eq]
  have hnorm_fiber : Summable (fun ab : DiscreteConvolution.mulFiber k =>
      ‖f ab.1.1‖ * ‖g ab.1.2‖) := (lpOneAlg.summable_norm_prod f g).subtype _
  have h_elem (ab : DiscreteConvolution.mulFiber k) :=
    lpOneAlg.norm_mulToRealSeq_mul_weight_le f g
      (DiscreteConvolution.mem_mulFiber.mp ab.2)
  have h_tri : ‖∑' ab : DiscreteConvolution.mulFiber k,
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2‖ ≤
      ∑' ab : DiscreteConvolution.mulFiber k,
        ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖ :=
    tsum_of_norm_bounded habs.hasSum
      fun ab => le_of_eq (norm_mul _ _)
  refine (mul_le_mul_of_nonneg_right h_tri (norm_nonneg _)).trans ?_
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum h_elem
    (Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      h_elem hnorm_fiber) hnorm_fiber

/-- Absolute convolution fiber summability from `lpOneMulAlgWeightMul` alone (no weight ≥ 1).
Key bound: `|f_a|·|g_b|·w(k) ≤ ‖f a‖·‖g b‖` via submultiplicativity `w(k) ≤ w(a)·w(b)`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.abs_convSummable_of_weightMul]
private theorem lpOneAlg.abs_mulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖ := by
  have hnorm : Summable (fun ab : DiscreteConvolution.mulFiber k => ‖f ab.1.1‖ * ‖g ab.1.2‖) :=
    (lpOneAlg.summable_norm_prod f g).subtype _
  have hw := lpOneAlg.norm_mulOfReal_one_pos (E := E) k
  refine (hnorm.const_smul (‖lpAlgRingData.ofReal (E := E) k (1 : 𝕜)‖⁻¹)).of_norm_bounded
    fun ab => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [smul_eq_mul]
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact lpOneAlg.norm_mulToRealSeq_mul_weight_le f g
    (DiscreteConvolution.mem_mulFiber.mp ab.2)

@[to_additive (dont_translate := E 𝕜) lpOneAlg.convSummable_of_weightMul]
private theorem lpOneAlg.mulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2 :=
  (lpOneAlg.abs_mulConvSummable_of_weightMul f g k).of_norm_bounded
    fun ⟨⟨_, _⟩, _⟩ => norm_mul_le _ _

/-- Triple convolution summability from `lpOneMulAlgWeightMul` alone.
Applies submultiplicativity twice: `w(a·b·c) ≤ w(a·b)·w(c) ≤ w(a)·w(b)·w(c)`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.tripleConvSummable_of_weightMul]
private theorem lpOneAlg.tripleMulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g h : lpOneAlg M E) (x : M) :
    Summable fun p : DiscreteConvolution.tripleMulFiber x =>
      lpOneAlg.mulToRealSeq f p.1.1 * lpOneAlg.mulToRealSeq g p.1.2.1 *
        lpOneAlg.mulToRealSeq h p.1.2.2 := by
  have h3 : Summable (fun abc : M × M × M =>
      ‖f abc.1‖ * ‖g abc.2.1‖ * ‖h abc.2.2‖) :=
    ((lpOneAlg.summable_norm f).mul_of_nonneg (lpOneAlg.summable_norm_prod g h)
      (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).congr
      fun _ => (mul_assoc _ _ _).symm
  have hnorm3 : Summable (fun p : DiscreteConvolution.tripleMulFiber x =>
      ‖f p.1.1‖ * ‖g p.1.2.1‖ * ‖h p.1.2.2‖) := h3.subtype _
  have hw := lpOneAlg.norm_mulOfReal_one_pos (E := E) x
  refine (hnorm3.const_smul (‖lpAlgRingData.ofReal (E := E) x (1 : 𝕜)‖⁻¹)).of_norm_bounded
    fun p => ?_
  have hmem := p.2; rw [DiscreteConvolution.mem_tripleMulFiber] at hmem
  simp only [smul_eq_mul]
  rw [norm_mul, norm_mul]
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f p.1.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g p.1.2.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight h p.1.2.2]
  have hsub1 := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) (p.1.1 * p.1.2.1) p.1.2.2 (1 : 𝕜) 1
  have hsub2 := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) p.1.1 p.1.2.1 (1 : 𝕜) 1
  simp only [mul_one] at hsub1 hsub2
  rw [hmem] at hsub1
  have hsub : ‖lpAlgRingData.ofReal (E := E) x (1 : 𝕜)‖ ≤
      ‖lpAlgRingData.ofReal (E := E) p.1.1 (1 : 𝕜)‖ *
      ‖lpAlgRingData.ofReal (E := E) p.1.2.1 (1 : 𝕜)‖ *
      ‖lpAlgRingData.ofReal (E := E) p.1.2.2 (1 : 𝕜)‖ :=
    hsub1.trans (mul_le_mul_of_nonneg_right hsub2 (norm_nonneg _))
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).trans_eq (by ring)

/-- Instance from `[lpOneMulAlgWeightMul]`: tsum path using submultiplicativity alone
(no weight ≥ 1 needed). -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.instConvCompatOfWeightMul]
instance lpOneAlg.instMulConvCompatOfWeightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpAlgRingData 𝕜 M E]
    [lpOneMulAlgWeightMul 𝕜 M E] : lpOneMulAlgConvCompat 𝕜 M E where
  mulConvSummable := lpOneAlg.mulConvSummable_of_weightMul
  tripleMulConvSummable := lpOneAlg.tripleMulConvSummable_of_weightMul
  norm_mulConv_le_fiber f g k :=
    lpOneAlg.norm_mulConv_le_fiber_generic f g k
      (lpOneAlg.abs_mulConvSummable_of_weightMul f g k)

/-- Finiteness of `mulFiber k` from `HasMulAntidiagonal`. -/
@[to_additive]
private theorem lpOneAlg.mulFiber_finite
    {M : Type*} [Monoid M] [Finset.HasMulAntidiagonal M] (k : M) :
    Set.Finite (DiscreteConvolution.mulFiber k) :=
  (Finset.mulAntidiagonal k).finite_toSet.subset fun ⟨_, _⟩ h =>
    Finset.mem_coe.mpr (Finset.mem_mulAntidiagonal.mpr (DiscreteConvolution.mem_mulFiber.mp h))

/-- Instance from `[HasMulAntidiagonal M] + [lpOneMulAlgWeightMul M E]`:
finite sum path (antidiagonal gives finite fibers, no weight ≥ 1 needed). -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.instConvCompatOfAntidiag]
instance (priority := 1100) lpOneAlg.instMulConvCompatOfAntidiag
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [DecidableEq M]
    [Finset.HasMulAntidiagonal M] [lpAlgRingData 𝕜 M E]
    [lpOneMulAlgWeightMul 𝕜 M E] : lpOneMulAlgConvCompat 𝕜 M E where
  mulConvSummable f g k := by
    exact (lpOneAlg.mulFiber_finite k).summable (fun p : M × M =>
      lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2)
  tripleMulConvSummable f g h x := by
    have : ∀ k : M, Finite ↑(DiscreteConvolution.mulFiber k) :=
      fun k => (lpOneAlg.mulFiber_finite k).to_subtype
    have : Finite ↑(DiscreteConvolution.tripleMulFiber x) :=
      (DiscreteConvolution.leftMulAssocEquiv x).finite_iff.mp inferInstance
    exact (Set.toFinite _).summable
      (fun p : M × M × M =>
        lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2.1 *
          lpOneAlg.mulToRealSeq h p.2.2)
  norm_mulConv_le_fiber f g k := by
    have : Finite ↑(DiscreteConvolution.mulFiber k) :=
      (lpOneAlg.mulFiber_finite k).to_subtype
    exact lpOneAlg.norm_mulConv_le_fiber_generic f g k
      ((lpOneAlg.mulFiber_finite k).summable (fun p : M × M =>
        ‖lpOneAlg.mulToRealSeq f p.1‖ * ‖lpOneAlg.mulToRealSeq g p.2‖))

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-! ### Ring Infrastructure (multiplicative primary, additive via @[to_additive]) -/

section MulRingInfrastructure

variable {𝕜 : Type*} [NormedField 𝕜]
variable [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgConvCompat 𝕜 M E] [DecidableEq M]

/-! ### Mul Membership and Norm -/

omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) mul_memℓp]
theorem mul_memℓp_mul (f g : lpOneAlg M E) :
    Memℓp (fun k => lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    (DiscreteConvolution.sigmaMulFiberEquiv.summable_iff.mpr (summable_norm_prod f g)).sigma

omit [lpOneMulAlgConvCompat 𝕜 M E] in
/-- `delta r` belongs to ℓ¹. Used by the identity and scalar casts. -/
@[to_additive (dont_translate := E 𝕜) delta_memℓp]
private theorem delta_memℓp_mul (r : 𝕜) :
    Memℓp (fun m => lpAlgRingData.ofReal (E := E) m
      (DiscreteConvolution.delta r m)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact summable_of_ne_finset_zero (s := {1}) (fun b hb => by
    rw [Finset.mem_singleton] at hb
    rw [DiscreteConvolution.delta_ne r hb, lpAlgRingData.ofReal_zero, norm_zero])

omit [lpOneMulAlgConvCompat 𝕜 M E] in
@[to_additive (dont_translate := E 𝕜) one_memℓp]
theorem one_memℓp_mul :
    Memℓp (fun m => lpAlgRingData.ofReal (E := E) m
      (DiscreteConvolution.delta (1 : 𝕜) m)) 1 := by
  exact delta_memℓp_mul (1 : 𝕜)

omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) norm_mul_le']
private theorem norm_mul_le_mul' (f g : lpOneAlg M E) :
    ‖(⟨⟨fun k => lpAlgRingData.ofReal (E := E) k
        (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
      mul_memℓp_mul f g⟩⟩ : lpOneAlg M E)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum]
  have hsigma := DiscreteConvolution.sigmaMulFiberEquiv.summable_iff.mpr (summable_norm_prod f g)
  have hmem : Summable (fun k => ‖lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)‖) := by
    simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp (mul_memℓp_mul f g)
  refine (Summable.tsum_le_tsum (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    hmem hsigma.sigma).trans (le_of_eq ?_)
  exact (hsigma.tsum_sigma' hsigma.sigma_factor) ▸
    (summable_norm f).tsum_mul_tsum (summable_norm g) (summable_norm_prod f g) ▸
    DiscreteConvolution.sigmaMulFiberEquiv.tsum_eq (fun p => ‖f p.1‖ * ‖g p.2‖)

end MulRingInfrastructure

/-! ### Mul / One / Ring / NormedRing instances (multiplicative index monoid) -/

section MulRingInstances

variable {𝕜 : Type*} [NormedField 𝕜]
variable [Monoid M] [lpAlgRingData 𝕜 M E] [lpOneMulAlgConvCompat 𝕜 M E] [DecidableEq M]

@[to_additive (dont_translate := E 𝕜) instMul]
instance instMulMul : Mul (lpOneAlg M E) where
  mul f g := ⟨⟨fun k => lpAlgRingData.ofReal (E := E) k
    (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
    mul_memℓp_mul f g⟩⟩

@[to_additive (dont_translate := E 𝕜) instOne]
instance instMulOne : One (lpOneAlg M E) where
  one := ⟨⟨fun m => lpAlgRingData.ofReal (E := E) m
    (DiscreteConvolution.delta (1 : 𝕜) m), one_memℓp_mul⟩⟩

-- Key rewrites: mulToRealSeq of product/one = convolution/delta of mulToRealSeqs
omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) (attr := simp) toRealSeq_mul_fun]
theorem mulToRealSeq_mul_fun (f g : lpOneAlg M E) :
    mulToRealSeq (f * g) =
      DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) := by
  ext k; unfold mulToRealSeq
  show lpAlgRingData.toReal k
    (lpAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution
        (fun m => lpAlgRingData.toReal m (f m))
        (fun m => lpAlgRingData.toReal m (g m)) k)) = _
  rw [lpAlgRingData.toReal_ofReal]

omit [lpOneMulAlgConvCompat 𝕜 M E] in
@[to_additive (dont_translate := E 𝕜) (attr := simp) toRealSeq_one_fun]
theorem mulToRealSeq_one_fun :
    mulToRealSeq (1 : lpOneAlg M E) = DiscreteConvolution.delta (1 : 𝕜) := by
  ext m; unfold mulToRealSeq
  show lpAlgRingData.toReal m
    (lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta (1 : 𝕜) m)) = _
  rw [lpAlgRingData.toReal_ofReal]

@[to_additive (dont_translate := E 𝕜) instRing]
instance instMulRing : Ring (lpOneAlg M E) where
  mul_assoc f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun]
    exact congr_fun (DiscreteConvolution.ringConvolution_assoc _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f g)
      (lpOneMulAlgConvCompat.mulConvSummable g h)
      (lpOneMulAlgConvCompat.tripleMulConvSummable f g h)) k
  one_mul f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [DiscreteConvolution.delta_ringConvolution' (1 : 𝕜) _ k, one_mul]
  mul_one f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [DiscreteConvolution.ringConvolution_delta' _ (1 : 𝕜) k, mul_one]
  left_distrib f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_add]
    exact congr_fun (DiscreteConvolution.ringConvolution_add _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f g)
      (lpOneMulAlgConvCompat.mulConvSummable f h)) k
  right_distrib f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_add]
    exact congr_fun (DiscreteConvolution.add_ringConvolution _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f h)
      (lpOneMulAlgConvCompat.mulConvSummable g h)) k
  zero_mul f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_zero]
    exact congr_fun (DiscreteConvolution.zero_ringConvolution _) k
  mul_zero f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_zero]
    exact congr_fun (DiscreteConvolution.ringConvolution_zero _) k
  natCast n := ⟨⟨fun m => lpAlgRingData.ofReal (E := E) m
    (DiscreteConvolution.delta ((n : 𝕜)) m), delta_memℓp_mul (n : 𝕜)⟩⟩
  natCast_zero := ext fun m => by
    show lpAlgRingData.ofReal (E := E) m
      (DiscreteConvolution.delta ((0 : ℕ) : 𝕜) m) = 0
    simp [Nat.cast_zero, DiscreteConvolution.delta, Pi.single_apply,
      lpAlgRingData.ofReal_zero]
  natCast_succ n := ext fun m => by
    show lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta ((↑(n + 1) : 𝕜)) m) =
      lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta ((n : 𝕜)) m) +
      lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta ((1 : 𝕜)) m)
    rw [← lpAlgRingData.ofReal_add, Nat.cast_succ]
    congr 1; simp [DiscreteConvolution.delta, Pi.single_apply]; split_ifs <;> ring
  intCast n := ⟨⟨fun m => lpAlgRingData.ofReal (E := E) m
    (DiscreteConvolution.delta ((n : 𝕜)) m), delta_memℓp_mul (n : 𝕜)⟩⟩
  intCast_ofNat n := ext fun m => by
    simp only [Int.cast_natCast]; rfl
  intCast_negSucc n := ext fun m => by
    show lpAlgRingData.ofReal (E := E) m
        (DiscreteConvolution.delta ((Int.negSucc n : 𝕜)) m) =
      -(lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta ((↑(n + 1) : 𝕜)) m))
    simp only [Int.cast_negSucc]
    rw [show DiscreteConvolution.delta (-↑(n + 1) : 𝕜) m =
      -(DiscreteConvolution.delta ((↑(n + 1) : 𝕜)) m) from by
        simp [DiscreteConvolution.delta, Pi.single_apply]; split_ifs <;> ring]
    exact ofReal_neg m _

@[to_additive (dont_translate := E 𝕜) instNormedRing]
instance instMulNormedRing : NormedRing (lpOneAlg M E) :=
  fast_instance% { lpOneAlg.instNormedAddCommGroup, lpOneAlg.instMulRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g => norm_mul_le_mul' f g }

end MulRingInstances

end lpOneAlg

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

/-! ### CommRing, Algebra (separate section to avoid AddGroup/AddCommGroup diamond) -/

section lpOneAlgCommAlgebra

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddCommMonoid M] [DecidableEq M]
variable [lpAlgRingData 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]

instance lpOneAlg.instCommRing : CommRing (lpOneAlg M E) where
  mul_comm f g := by
    apply lpOneAlg.ext_toRealSeq
    simp only [lpOneAlg.toRealSeq_mul_fun]
    exact DiscreteConvolution.addRingConvolution_comm _ _

instance lpOneAlg.instNormedCommRing : NormedCommRing (lpOneAlg M E) where
  mul_comm := lpOneAlg.instCommRing.mul_comm

variable [∀ m, NormedSpace 𝕜 (E m)]
variable [lpAlgSmulCompat 𝕜 M E]

instance lpOneAlg.instAlgebra : Algebra 𝕜 (lpOneAlg M E) :=
  Algebra.ofModule
    (fun r f g => by
      apply lpOneAlg.ext_toRealSeq
      simp only [lpOneAlg.toRealSeq_mul_fun, lpOneAlg.toRealSeq_smul]
      exact DiscreteConvolution.smul_addRingConvolution r _ _
        (lpOneAlgConvCompat.convSummable f g))
    (fun r f g => by
      apply lpOneAlg.ext_toRealSeq
      simp only [lpOneAlg.toRealSeq_mul_fun, lpOneAlg.toRealSeq_smul]
      exact DiscreteConvolution.addRingConvolution_smul r _ _
        (lpOneAlgConvCompat.convSummable f g))

instance lpOneAlg.instNormedAlgebra : NormedAlgebra 𝕜 (lpOneAlg M E) where
  norm_smul_le := lpOneAlg.instNormedSpaceBase.norm_smul_le

end lpOneAlgCommAlgebra

namespace lpOneAlg

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [AddMonoid M] [lpAlgRingData 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]
variable [lpOneAlgWeightMul 𝕜 M E] [DecidableEq M]

/-! ### Norm of Identity -/

omit [lpOneAlgWeightMul 𝕜 M E] in
theorem norm_one_eq :
    ‖(1 : lpOneAlg M E)‖ = ‖lpAlgRingData.ofReal (E := E) (0 : M) (1 : 𝕜)‖ := by
  rw [norm_eq_tsum]
  have h : (fun m => ‖(1 : lpOneAlg M E) m‖) =
      fun m => if m = 0 then ‖lpAlgRingData.ofReal (E := E) (0 : M) (1 : 𝕜)‖ else 0 := by
    ext m; by_cases hm : m = 0
    · subst hm
      change ‖lpAlgRingData.ofReal (E := E) 0 (DiscreteConvolution.addDelta (1 : 𝕜) 0)‖ = _
      rw [DiscreteConvolution.addDelta_zero_eq]; simp
    · rw [if_neg hm]
      show ‖lpAlgRingData.ofReal (E := E) m (DiscreteConvolution.addDelta (1 : 𝕜) m)‖ = 0
      rw [DiscreteConvolution.addDelta_ne (1 : 𝕜) hm, lpAlgRingData.ofReal_zero, norm_zero]
  rw [h, tsum_ite_eq]

instance instNormOneClass : NormOneClass (lpOneAlg M E) where
  norm_one := norm_one_eq.trans (lpOneAlgWeightMul.norm_ofReal_one_zero)

end lpOneAlg

end RadiiPolynomial

end
