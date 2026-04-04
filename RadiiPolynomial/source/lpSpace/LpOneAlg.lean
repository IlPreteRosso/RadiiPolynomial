import RadiiPolynomial.source.lpSpace.DiscreteConvolutionRing
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Generalized ℓ¹ Banach Algebra with Non-Uniform Fibers

`lpOneAlg M E` wraps `lp E 1` with convolution as multiplication.

## Typeclass convention

Multiplicative typeclasses (`lpOneMulAlgRingData`, `lpOneMulAlgWeightSubMul`,
`lpOneMulAlgSmulCompat`, `lpOneMulAlgConvCompat`) are primary; additive versions
(`lpOneAlgRingData`, `lpOneAlgWeightSubMul`, `lpOneAlgSmulCompat`,
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

class lpOneMulAlgRingData (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] where
  toReal : ∀ m, E m → ℝ
  ofReal : ∀ m, ℝ → E m
  toReal_ofReal : ∀ m r, toReal m (ofReal m r) = r
  ofReal_toReal : ∀ m x, ofReal m (toReal m x) = x
  ofReal_add : ∀ m a b, ofReal m (a + b) = ofReal m a + ofReal m b
  ofReal_zero : ∀ m, ofReal m 0 = 0
  toReal_add : ∀ m x y, toReal m (x + y) = toReal m x + toReal m y
  toReal_zero : ∀ m, toReal m 0 = 0
  toReal_neg : ∀ m x, toReal m (-x) = -(toReal m x)
  norm_ofReal_eq : ∀ m r, ‖ofReal m r‖ = |r| * ‖ofReal m 1‖

class lpOneAlgRingData (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] where
  toReal : ∀ m, E m → ℝ
  ofReal : ∀ m, ℝ → E m
  toReal_ofReal : ∀ m r, toReal m (ofReal m r) = r
  ofReal_toReal : ∀ m x, ofReal m (toReal m x) = x
  ofReal_add : ∀ m a b, ofReal m (a + b) = ofReal m a + ofReal m b
  ofReal_zero : ∀ m, ofReal m 0 = 0
  toReal_add : ∀ m x y, toReal m (x + y) = toReal m x + toReal m y
  toReal_zero : ∀ m, toReal m 0 = 0
  toReal_neg : ∀ m x, toReal m (-x) = -(toReal m x)
  norm_ofReal_eq : ∀ m r, ‖ofReal m r‖ = |r| * ‖ofReal m 1‖

attribute [to_additive existing lpOneAlgRingData] lpOneMulAlgRingData

/-- Scalar compatibility: `toReal` respects ℝ-scalar multiplication.
Needed for Algebra ℝ instance. Separated from `lpOneMulAlgRingData` because it
requires `NormedSpace ℝ (E m)` which not all ring applications need. -/
class lpOneMulAlgSmulCompat (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℝ (E m)]
    [lpOneMulAlgRingData M E] where
  toReal_smul : ∀ m (r : ℝ) (x : E m),
    lpOneMulAlgRingData.toReal m (r • x) = r * lpOneMulAlgRingData.toReal m x

/-- Scalar compatibility: `toReal` respects ℝ-scalar multiplication.
Needed for Algebra ℝ instance. Separated from `lpOneAlgRingData` because it
requires `NormedSpace ℝ (E m)` which not all ring applications need. -/
class lpOneAlgSmulCompat (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℝ (E m)]
    [lpOneAlgRingData M E] where
  toReal_smul : ∀ m (r : ℝ) (x : E m),
    lpOneAlgRingData.toReal m (r • x) = r * lpOneAlgRingData.toReal m x

attribute [to_additive existing lpOneAlgSmulCompat] lpOneMulAlgSmulCompat

/-- Submultiplicative weight (no weight ≥ 1 requirement).
Sufficient for Ring on `lpOneAlg` when `[HasAntidiagonal M]` (finite fibers). -/
class lpOneMulAlgWeightMul (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneMulAlgRingData M E] where
  norm_ofReal_mul_le : ∀ (j l : M) (a b : ℝ),
    ‖lpOneMulAlgRingData.ofReal (E := E) (j * l) (a * b)‖ ≤
    ‖lpOneMulAlgRingData.ofReal (E := E) j a‖ * ‖lpOneMulAlgRingData.ofReal (E := E) l b‖
  /-- Weight at identity = 1: ensures `‖1‖ = 1` (NormOneClass). -/
  norm_ofReal_one_one : ‖lpOneMulAlgRingData.ofReal (E := E) (1 : M) (1 : ℝ)‖ = 1

class lpOneAlgWeightMul (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneAlgRingData M E] where
  norm_ofReal_mul_le : ∀ (j l : M) (a b : ℝ),
    ‖lpOneAlgRingData.ofReal (E := E) (j + l) (a * b)‖ ≤
    ‖lpOneAlgRingData.ofReal (E := E) j a‖ * ‖lpOneAlgRingData.ofReal (E := E) l b‖
  norm_ofReal_one_zero : ‖lpOneAlgRingData.ofReal (E := E) (0 : M) (1 : ℝ)‖ = 1

attribute [to_additive existing lpOneAlgWeightMul] lpOneMulAlgWeightMul

/-- Full weight condition: submultiplicative + weight ≥ 1.
Needed for tsum-based Ring on general M (infinite fibers).
Extends `lpOneMulAlgWeightMul`. -/
class lpOneMulAlgWeightSubMul (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneMulAlgRingData M E]
    extends lpOneMulAlgWeightMul M E where
  /-- Weight ≥ 1: ensures `|mulToRealSeq f m| ≤ ‖f m‖`, needed for tsum summability. -/
  norm_ofReal_one_ge : ∀ m, 1 ≤ ‖lpOneMulAlgRingData.ofReal (E := E) m 1‖

class lpOneAlgWeightSubMul (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneAlgRingData M E]
    extends lpOneAlgWeightMul M E where
  /-- Weight ≥ 1: ensures `|toRealSeq f m| ≤ ‖f m‖`, needed for tsum summability. -/
  norm_ofReal_one_ge : ∀ m, 1 ≤ ‖lpOneAlgRingData.ofReal (E := E) m 1‖

attribute [to_additive existing lpOneAlgWeightSubMul] lpOneMulAlgWeightSubMul

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

/-- NormedSpace ℝ for lpOneAlg, transferred from lp. No algebraic constraint on M needed. -/
instance instNormedSpaceBase [∀ m, NormedSpace ℝ (E m)] : NormedSpace ℝ (lpOneAlg M E) :=
  { lpOneAlg.equiv.module ℝ with
    norm_smul_le := fun r f => by
      show ‖r • f.toLp‖ ≤ _; exact norm_smul_le r f.toLp }

@[simp] theorem toLp_zero : (0 : lpOneAlg M E).toLp = 0 := rfl
@[simp] theorem toLp_add (f g : lpOneAlg M E) : (f + g).toLp = f.toLp + g.toLp := rfl
@[simp] theorem toLp_neg (f : lpOneAlg M E) : (-f).toLp = -f.toLp := rfl
@[simp] theorem toLp_sub (f g : lpOneAlg M E) : (f - g).toLp = f.toLp - g.toLp := rfl
@[simp] theorem toLp_smul [∀ m, NormedSpace ℝ (E m)] (r : ℝ) (f : lpOneAlg M E) :
    (r • f).toLp = r • f.toLp := rfl

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
    Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
  (summable_norm f).mul_of_nonneg (summable_norm g)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-! ### Underlying ℝ Sequence and Summability (multiplicative, with @[to_additive]) -/

section MulHelpers

variable [Monoid M] [lpOneMulAlgRingData M E]

/-- The underlying ℝ-valued sequence for multiplicative index monoid. -/
@[to_additive (dont_translate := E) toRealSeq]
def mulToRealSeq (f : lpOneAlg M E) : M → ℝ :=
  fun m => lpOneMulAlgRingData.toReal m (f m)

@[to_additive (dont_translate := E) norm_eq_abs_toReal_mul_weight]
theorem norm_eq_abs_mulToReal_mul_weight (f : lpOneAlg M E) (m : M) :
    ‖f m‖ = |mulToRealSeq f m| * ‖lpOneMulAlgRingData.ofReal (E := E) m 1‖ := by
  conv_lhs => rw [show f m = lpOneMulAlgRingData.ofReal (E := E) m (mulToRealSeq f m)
    from (lpOneMulAlgRingData.ofReal_toReal m (f m)).symm]
  exact lpOneMulAlgRingData.norm_ofReal_eq m _

/-- Weight at any index is positive (from ofReal/toReal injectivity). -/
@[to_additive (dont_translate := E) norm_ofReal_one_pos]
private theorem norm_mulOfReal_one_pos (m : M) :
    0 < ‖lpOneMulAlgRingData.ofReal (E := E) m 1‖ := by
  rw [norm_pos_iff]; intro h
  have h1 := congr_arg (lpOneMulAlgRingData.toReal (E := E) m) h
  rw [lpOneMulAlgRingData.toReal_ofReal, lpOneMulAlgRingData.toReal_zero] at h1
  exact one_ne_zero h1

variable [lpOneMulAlgWeightSubMul M E]

/-- `|mulToRealSeq f m| ≤ ‖f m‖` (from weight ≥ 1). -/
@[to_additive (dont_translate := E) abs_toRealSeq_le]
theorem abs_mulToRealSeq_le (f : lpOneAlg M E) (m : M) :
    |mulToRealSeq f m| ≤ ‖f m‖ := by
  rw [norm_eq_abs_mulToReal_mul_weight f m]
  exact le_mul_of_one_le_right (abs_nonneg _) (lpOneMulAlgWeightSubMul.norm_ofReal_one_ge m)

@[to_additive (dont_translate := E) summable_abs_toRealSeq]
theorem summable_abs_mulToRealSeq (f : lpOneAlg M E) :
    Summable (fun m => |mulToRealSeq f m|) :=
  (summable_norm f).of_nonneg_of_le (fun _ => abs_nonneg _) (abs_mulToRealSeq_le f)

omit [lpOneMulAlgWeightSubMul M E] in
/-- Extensionality via toRealSeq. -/
@[to_additive (dont_translate := E) ext_toRealSeq]
theorem ext_mulToRealSeq {f g : lpOneAlg M E}
    (h : mulToRealSeq f = mulToRealSeq g) : f = g :=
  ext fun m => (lpOneMulAlgRingData.ofReal_toReal m (f m)).symm ▸
    (lpOneMulAlgRingData.ofReal_toReal m (g m)).symm ▸ congr_arg _ (congr_fun h m)

omit [lpOneMulAlgWeightSubMul M E] in
@[to_additive (dont_translate := E) toRealSeq_add]
theorem mulToRealSeq_add (f g : lpOneAlg M E) :
    mulToRealSeq (f + g) = mulToRealSeq f + mulToRealSeq g :=
  funext fun m => lpOneMulAlgRingData.toReal_add m _ _

omit [lpOneMulAlgWeightSubMul M E] in
@[to_additive (dont_translate := E) toRealSeq_zero]
theorem mulToRealSeq_zero : mulToRealSeq (0 : lpOneAlg M E) = 0 :=
  funext fun m => lpOneMulAlgRingData.toReal_zero m

end MulHelpers

end lpOneAlg

/-! ### Convolution compatibility: abstraction over summability path -/

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (multiplicative).
Two instances: from `[lpOneMulAlgWeightMul]` (tsum path, submultiplicativity alone) or
from `[HasMulAntidiagonal M] + [lpOneMulAlgWeightMul M E]` (finite sum path, priority 1100). -/
class lpOneMulAlgConvCompat (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneMulAlgRingData M E] where
  mulConvSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2
  tripleMulConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    DiscreteConvolution.TripleConvolutionSummable
      (lpOneAlg.mulToRealSeq f) (lpOneAlg.mulToRealSeq g) (lpOneAlg.mulToRealSeq h) x
  norm_mulConv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖lpOneMulAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (additive).
Two instances: from `[lpOneAlgWeightMul]` (tsum path, submultiplicativity alone) or
from `[HasAntidiagonal M] + [lpOneAlgWeightMul M E]` (finite sum path, priority 1100). -/
class lpOneAlgConvCompat (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [lpOneAlgRingData M E] where
  convSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : DiscreteConvolution.addFiber k =>
      lpOneAlg.toRealSeq f ab.1.1 * lpOneAlg.toRealSeq g ab.1.2
  tripleConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    Summable fun p : DiscreteConvolution.tripleAddFiber x =>
      lpOneAlg.toRealSeq f p.1.1 * lpOneAlg.toRealSeq g p.1.2.1 *
        lpOneAlg.toRealSeq h p.1.2.2
  norm_conv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖lpOneAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution (lpOneAlg.toRealSeq f)
        (lpOneAlg.toRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.addFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

attribute [to_additive existing lpOneAlgConvCompat] lpOneMulAlgConvCompat

/-- Generic per-index bound: given fiber summability, proves the norm bound
via triangle inequality + submultiplicativity. Shared by both convolution paths. -/
@[to_additive (dont_translate := E) lpOneAlg.norm_conv_le_fiber_generic]
private theorem lpOneAlg.norm_mulConv_le_fiber_generic
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgWeightMul M E]
    (f g : lpOneAlg M E) (k : M)
    (habs : Summable fun ab : DiscreteConvolution.mulFiber k =>
      |lpOneAlg.mulToRealSeq f ab.1.1| * |lpOneAlg.mulToRealSeq g ab.1.2|) :
    ‖lpOneMulAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
  rw [lpOneMulAlgRingData.norm_ofReal_eq, DiscreteConvolution.ringConvolution_apply_eq]
  have hnorm_fiber : Summable (fun ab : DiscreteConvolution.mulFiber k =>
      ‖f ab.1.1‖ * ‖g ab.1.2‖) := (lpOneAlg.summable_norm_prod f g).subtype _
  have h_elem (ab : DiscreteConvolution.mulFiber k) :
      |lpOneAlg.mulToRealSeq f ab.1.1| * |lpOneAlg.mulToRealSeq g ab.1.2| *
        ‖lpOneMulAlgRingData.ofReal (E := E) k 1‖ ≤
      ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
    obtain ⟨⟨j, l⟩, hjl⟩ := ab
    rw [DiscreteConvolution.mem_mulFiber] at hjl; subst hjl
    rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f j,
      lpOneAlg.norm_eq_abs_mulToReal_mul_weight g l]
    have hw := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) j l 1 1
    simp only [mul_one] at hw
    exact (mul_le_mul_of_nonneg_left hw
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)
  have h_tri : ‖∑' ab : DiscreteConvolution.mulFiber k,
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2‖ ≤
      ∑' ab : DiscreteConvolution.mulFiber k,
        |lpOneAlg.mulToRealSeq f ab.1.1| * |lpOneAlg.mulToRealSeq g ab.1.2| :=
    tsum_of_norm_bounded habs.hasSum
      fun ab => le_of_eq (by rw [Real.norm_eq_abs, abs_mul])
  rw [Real.norm_eq_abs] at h_tri
  refine (mul_le_mul_of_nonneg_right h_tri (norm_nonneg _)).trans ?_
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum h_elem
    (Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))
      h_elem hnorm_fiber) hnorm_fiber

/-- Absolute convolution fiber summability from `lpOneMulAlgWeightMul` alone (no weight ≥ 1).
Key bound: `|f_a|·|g_b|·w(k) ≤ ‖f a‖·‖g b‖` via submultiplicativity `w(k) ≤ w(a)·w(b)`. -/
@[to_additive (dont_translate := E) lpOneAlg.abs_convSummable_of_weightMul]
private theorem lpOneAlg.abs_mulConvSummable_of_weightMul
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgWeightMul M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      |lpOneAlg.mulToRealSeq f ab.1.1| * |lpOneAlg.mulToRealSeq g ab.1.2| := by
  have hnorm : Summable (fun ab : DiscreteConvolution.mulFiber k => ‖f ab.1.1‖ * ‖g ab.1.2‖) :=
    (lpOneAlg.summable_norm_prod f g).subtype _
  have hw := lpOneAlg.norm_mulOfReal_one_pos (E := E) k
  refine (hnorm.const_smul (‖lpOneMulAlgRingData.ofReal (E := E) k 1‖⁻¹)).of_norm_bounded
    fun ab => ?_
  have hmem := ab.2; rw [DiscreteConvolution.mem_mulFiber] at hmem
  simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_abs]
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f ab.1.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g ab.1.2]
  have hsub := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) ab.1.1 ab.1.2 1 1
  simp only [mul_one] at hsub; rw [hmem] at hsub
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)

@[to_additive (dont_translate := E) lpOneAlg.convSummable_of_weightMul]
private theorem lpOneAlg.mulConvSummable_of_weightMul
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgWeightMul M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : DiscreteConvolution.mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2 :=
  (lpOneAlg.abs_mulConvSummable_of_weightMul f g k).of_norm_bounded
    fun ⟨⟨_, _⟩, _⟩ => by simp [Real.norm_eq_abs]

/-- Triple convolution summability from `lpOneMulAlgWeightMul` alone.
Applies submultiplicativity twice: `w(a·b·c) ≤ w(a·b)·w(c) ≤ w(a)·w(b)·w(c)`. -/
@[to_additive (dont_translate := E) lpOneAlg.tripleConvSummable_of_weightMul]
private theorem lpOneAlg.tripleMulConvSummable_of_weightMul
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgWeightMul M E]
    (f g h : lpOneAlg M E) (x : M) :
    Summable fun p : DiscreteConvolution.tripleMulFiber x =>
      lpOneAlg.mulToRealSeq f p.1.1 * lpOneAlg.mulToRealSeq g p.1.2.1 *
        lpOneAlg.mulToRealSeq h p.1.2.2 := by
  have hnorm3 : Summable (fun p : DiscreteConvolution.tripleMulFiber x =>
      ‖f p.1.1‖ * ‖g p.1.2.1‖ * ‖h p.1.2.2‖) := by
    have h3 : Summable (fun abc : M × M × M =>
        ‖f abc.1‖ * ‖g abc.2.1‖ * ‖h abc.2.2‖) :=
      (Equiv.prodAssoc M M M).symm.summable_iff.mpr
        ((lpOneAlg.summable_norm_prod f g).mul_of_nonneg (lpOneAlg.summable_norm h)
          (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _))
    exact h3.subtype _
  have hw := lpOneAlg.norm_mulOfReal_one_pos (E := E) x
  refine (hnorm3.const_smul (‖lpOneMulAlgRingData.ofReal (E := E) x 1‖⁻¹)).of_norm_bounded
    fun p => ?_
  have hmem := p.2; rw [DiscreteConvolution.mem_tripleMulFiber] at hmem
  simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul]
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f p.1.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g p.1.2.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight h p.1.2.2]
  have hsub1 := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) (p.1.1 * p.1.2.1) p.1.2.2 1 1
  have hsub2 := lpOneMulAlgWeightMul.norm_ofReal_mul_le (E := E) p.1.1 p.1.2.1 1 1
  simp only [mul_one] at hsub1 hsub2
  rw [hmem] at hsub1
  have hsub : ‖lpOneMulAlgRingData.ofReal (E := E) x 1‖ ≤
      ‖lpOneMulAlgRingData.ofReal (E := E) p.1.1 1‖ *
      ‖lpOneMulAlgRingData.ofReal (E := E) p.1.2.1 1‖ *
      ‖lpOneMulAlgRingData.ofReal (E := E) p.1.2.2 1‖ :=
    hsub1.trans (mul_le_mul_of_nonneg_right hsub2 (norm_nonneg _))
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))).trans_eq (by ring)

/-- Instance from `[lpOneMulAlgWeightMul]`: tsum path using submultiplicativity alone
(no weight ≥ 1 needed). -/
@[to_additive (dont_translate := E) lpOneAlg.instConvCompatOfWeightMul]
instance lpOneAlg.instMulConvCompatOfWeightMul
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [lpOneMulAlgRingData M E]
    [lpOneMulAlgWeightMul M E] : lpOneMulAlgConvCompat M E where
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
@[to_additive (dont_translate := E) lpOneAlg.instConvCompatOfAntidiag]
instance (priority := 1100) lpOneAlg.instMulConvCompatOfAntidiag
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
    [Monoid M] [DecidableEq M]
    [Finset.HasMulAntidiagonal M] [lpOneMulAlgRingData M E]
    [lpOneMulAlgWeightMul M E] : lpOneMulAlgConvCompat M E where
  mulConvSummable f g k := by
    exact (lpOneAlg.mulFiber_finite k).summable (fun p : M × M =>
      lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2)
  tripleMulConvSummable f g h x := by
    haveI : ∀ k : M, Finite ↑(DiscreteConvolution.mulFiber k) :=
      fun k => (lpOneAlg.mulFiber_finite k).to_subtype
    haveI : Finite ↑(DiscreteConvolution.tripleMulFiber x) :=
      (DiscreteConvolution.leftMulAssocEquiv x).finite_iff.mp inferInstance
    exact (Set.toFinite _).summable
      (fun p : M × M × M =>
        lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2.1 *
          lpOneAlg.mulToRealSeq h p.2.2)
  norm_mulConv_le_fiber f g k := by
    haveI : Finite ↑(DiscreteConvolution.mulFiber k) :=
      (lpOneAlg.mulFiber_finite k).to_subtype
    exact lpOneAlg.norm_mulConv_le_fiber_generic f g k
      ((lpOneAlg.mulFiber_finite k).summable (fun p : M × M =>
        |lpOneAlg.mulToRealSeq f p.1| * |lpOneAlg.mulToRealSeq g p.2|))

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-! ### Ring Infrastructure (multiplicative primary, additive via @[to_additive]) -/

section MulRingInfrastructure

variable [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgConvCompat M E] [DecidableEq M]

/-! ### Mul Membership and Norm -/

omit [DecidableEq M] in
@[to_additive (dont_translate := E) mul_memℓp]
theorem mul_memℓp_mul (f g : lpOneAlg M E) :
    Memℓp (fun k => lpOneMulAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    (DiscreteConvolution.sigmaMulFiberEquiv.summable_iff.mpr (summable_norm_prod f g)).sigma

omit [lpOneMulAlgConvCompat M E] in
@[to_additive (dont_translate := E) one_memℓp]
theorem one_memℓp_mul :
    Memℓp (fun m => lpOneMulAlgRingData.ofReal (E := E) m
      (DiscreteConvolution.delta (1 : ℝ) m)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact summable_of_ne_finset_zero (s := {1}) (fun b hb => by
    rw [Finset.mem_singleton] at hb
    rw [DiscreteConvolution.delta_ne 1 hb, lpOneMulAlgRingData.ofReal_zero, norm_zero])

omit [DecidableEq M] in
@[to_additive (dont_translate := E) norm_mul_le']
theorem norm_mul_le_mul' (f g : lpOneAlg M E) :
    ‖(⟨⟨fun k => lpOneMulAlgRingData.ofReal (E := E) k
        (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
      mul_memℓp_mul f g⟩⟩ : lpOneAlg M E)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum]
  have hsigma := DiscreteConvolution.sigmaMulFiberEquiv.summable_iff.mpr (summable_norm_prod f g)
  have hmem : Summable (fun k => ‖lpOneMulAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)‖) := by
    simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp (mul_memℓp_mul f g)
  refine (Summable.tsum_le_tsum (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    hmem hsigma.sigma).trans (le_of_eq ?_)
  exact (hsigma.tsum_sigma' hsigma.sigma_factor) ▸
    (summable_norm f).tsum_mul_tsum (summable_norm g) (summable_norm_prod f g) ▸
    DiscreteConvolution.sigmaMulFiberEquiv.tsum_eq (fun p => ‖f p.1‖ * ‖g p.2‖)

omit [DecidableEq M] in
/-- Left-associated sum equals triple fiber sum (multiplicative). -/
@[to_additive (dont_translate := E) conv_assoc_left]
private theorem mulConv_assoc_left (f g h : lpOneAlg M E) (x : M) :
    ∑' cd : DiscreteConvolution.mulFiber x,
      (∑' ab : DiscreteConvolution.mulFiber cd.1.1,
        mulToRealSeq f ab.1.1 * mulToRealSeq g ab.1.2) * mulToRealSeq h cd.1.2 =
    ∑' p : DiscreteConvolution.tripleMulFiber x,
      mulToRealSeq f p.1.1 * mulToRealSeq g p.1.2.1 * mulToRealSeq h p.1.2.2 := by
  have h1 : ∀ cd : DiscreteConvolution.mulFiber x,
      (∑' ab : DiscreteConvolution.mulFiber cd.1.1,
        mulToRealSeq f ab.1.1 * mulToRealSeq g ab.1.2) * mulToRealSeq h cd.1.2 =
      ∑' ab : DiscreteConvolution.mulFiber cd.1.1,
        (mulToRealSeq f ab.1.1 * mulToRealSeq g ab.1.2) * mulToRealSeq h cd.1.2 := by
    intro cd; rw [tsum_mul_right]
  rw [tsum_congr h1]
  have hsigmaL : Summable fun p : Σ cd : DiscreteConvolution.mulFiber x,
      DiscreteConvolution.mulFiber cd.1.1 =>
      (mulToRealSeq f p.2.1.1 * mulToRealSeq g p.2.1.2) * mulToRealSeq h p.1.1.2 := by
    convert (DiscreteConvolution.leftMulAssocEquiv x).summable_iff.mpr
      (lpOneMulAlgConvCompat.tripleMulConvSummable f g h x) using 1
  have hfiberL (cd : DiscreteConvolution.mulFiber x) :
      Summable fun ab : DiscreteConvolution.mulFiber cd.1.1 =>
        (mulToRealSeq f ab.1.1 * mulToRealSeq g ab.1.2) * mulToRealSeq h cd.1.2 :=
    Summable.mul_right _ (lpOneMulAlgConvCompat.mulConvSummable f g cd.1.1)
  rw [← (DiscreteConvolution.leftMulAssocEquiv x).tsum_eq _, ←
    hsigmaL.tsum_sigma' hfiberL]; rfl

omit [DecidableEq M] in
/-- Right-associated sum equals triple fiber sum (multiplicative). -/
@[to_additive (dont_translate := E) conv_assoc_right]
private theorem mulConv_assoc_right (f g h : lpOneAlg M E) (x : M) :
    ∑' ae : DiscreteConvolution.mulFiber x,
      mulToRealSeq f ae.1.1 * (∑' bd : DiscreteConvolution.mulFiber ae.1.2,
        mulToRealSeq g bd.1.1 * mulToRealSeq h bd.1.2) =
    ∑' p : DiscreteConvolution.tripleMulFiber x,
      mulToRealSeq f p.1.1 * mulToRealSeq g p.1.2.1 * mulToRealSeq h p.1.2.2 := by
  have h1 : ∀ ae : DiscreteConvolution.mulFiber x,
      mulToRealSeq f ae.1.1 * (∑' bd : DiscreteConvolution.mulFiber ae.1.2,
        mulToRealSeq g bd.1.1 * mulToRealSeq h bd.1.2) =
      ∑' bd : DiscreteConvolution.mulFiber ae.1.2,
        mulToRealSeq f ae.1.1 * (mulToRealSeq g bd.1.1 * mulToRealSeq h bd.1.2) := by
    intro ae; rw [tsum_mul_left]
  rw [tsum_congr h1]
  have hsigmaR : Summable fun p : Σ ae : DiscreteConvolution.mulFiber x,
      DiscreteConvolution.mulFiber ae.1.2 =>
      mulToRealSeq f p.1.1.1 * (mulToRealSeq g p.2.1.1 * mulToRealSeq h p.2.1.2) := by
    simp_rw [← mul_assoc]
    convert (DiscreteConvolution.rightMulAssocEquiv x).summable_iff.mpr
      (lpOneMulAlgConvCompat.tripleMulConvSummable f g h x) using 1
  have hfiberR (ae : DiscreteConvolution.mulFiber x) :
      Summable fun bd : DiscreteConvolution.mulFiber ae.1.2 =>
        mulToRealSeq f ae.1.1 * (mulToRealSeq g bd.1.1 * mulToRealSeq h bd.1.2) :=
    Summable.mul_left _ (lpOneMulAlgConvCompat.mulConvSummable g h ae.1.2)
  rw [← (DiscreteConvolution.rightMulAssocEquiv x).tsum_eq _, ←
    hsigmaR.tsum_sigma' hfiberR]; simp_rw [← mul_assoc]; rfl

omit [DecidableEq M] in
@[to_additive (dont_translate := E) conv_assoc]
theorem mulConv_assoc (f g h : lpOneAlg M E) :
    DiscreteConvolution.ringConvolution
      (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g))
        (mulToRealSeq h) =
    DiscreteConvolution.ringConvolution
      (mulToRealSeq f) (DiscreteConvolution.ringConvolution (mulToRealSeq g)
        (mulToRealSeq h)) := by
  ext x
  simp only [DiscreteConvolution.ringConvolution_apply_eq]
  exact (mulConv_assoc_left f g h x).trans (mulConv_assoc_right f g h x).symm

end MulRingInfrastructure

/-! ### Mul / One / Ring / NormedRing instances (multiplicative index monoid) -/

section MulRingInstances

variable [Monoid M] [lpOneMulAlgRingData M E] [lpOneMulAlgConvCompat M E] [DecidableEq M]

instance instMulMul : Mul (lpOneAlg M E) where
  mul f g := ⟨⟨fun k => lpOneMulAlgRingData.ofReal (E := E) k
    (DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
    mul_memℓp_mul f g⟩⟩

instance instMulOne : One (lpOneAlg M E) where
  one := ⟨⟨fun m => lpOneMulAlgRingData.ofReal (E := E) m
    (DiscreteConvolution.delta (1 : ℝ) m), one_memℓp_mul⟩⟩

-- Key rewrites: mulToRealSeq of product/one = convolution/delta of mulToRealSeqs
omit [DecidableEq M] in
@[simp] theorem mulToRealSeq_mul_fun (f g : lpOneAlg M E) :
    mulToRealSeq (f * g) =
      DiscreteConvolution.ringConvolution (mulToRealSeq f) (mulToRealSeq g) := by
  ext k; unfold mulToRealSeq
  show lpOneMulAlgRingData.toReal k
    (lpOneMulAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.ringConvolution
        (fun m => lpOneMulAlgRingData.toReal m (f m))
        (fun m => lpOneMulAlgRingData.toReal m (g m)) k)) = _
  rw [lpOneMulAlgRingData.toReal_ofReal]

omit [lpOneMulAlgConvCompat M E] in
@[simp] theorem mulToRealSeq_one_fun :
    mulToRealSeq (1 : lpOneAlg M E) = DiscreteConvolution.delta 1 := by
  ext m; unfold mulToRealSeq
  show lpOneMulAlgRingData.toReal m
    (lpOneMulAlgRingData.ofReal (E := E) m (DiscreteConvolution.delta 1 m)) = _
  rw [lpOneMulAlgRingData.toReal_ofReal]

instance instMulRing : Ring (lpOneAlg M E) where
  mul_assoc f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun]
    exact congr_fun (mulConv_assoc f g h) k
  one_mul f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [DiscreteConvolution.delta_ringConvolution' 1 _ k, one_mul]
  mul_one f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [DiscreteConvolution.ringConvolution_delta' _ 1 k, mul_one]
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

instance instMulNormedRing : NormedRing (lpOneAlg M E) :=
  { lpOneAlg.instNormedAddCommGroup, lpOneAlg.instMulRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g => norm_mul_le_mul' f g }

end MulRingInstances

/-! ### Mul / One / Ring / NormedRing instances (additive index monoid) -/

section AddRingInstances

variable [AddMonoid M] [lpOneAlgRingData M E] [lpOneAlgConvCompat M E] [DecidableEq M]

instance instMul : Mul (lpOneAlg M E) where
  mul f g := ⟨⟨fun k => lpOneAlgRingData.ofReal (E := E) k
    (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k),
    mul_memℓp f g⟩⟩

instance instOne : One (lpOneAlg M E) where
  one := ⟨⟨fun m => lpOneAlgRingData.ofReal (E := E) m
    (DiscreteConvolution.addDelta (1 : ℝ) m), one_memℓp⟩⟩

-- Key rewrites: toRealSeq of product/one = convolution/delta of toRealSeqs
omit [DecidableEq M] in
@[simp] theorem toRealSeq_mul_fun (f g : lpOneAlg M E) :
    toRealSeq (f * g) =
      DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) := by
  ext k; unfold toRealSeq
  show lpOneAlgRingData.toReal k
    (lpOneAlgRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution
        (fun m => lpOneAlgRingData.toReal m (f m))
        (fun m => lpOneAlgRingData.toReal m (g m)) k)) = _
  rw [lpOneAlgRingData.toReal_ofReal]

omit [lpOneAlgConvCompat M E] in
@[simp] theorem toRealSeq_one_fun :
    toRealSeq (1 : lpOneAlg M E) = DiscreteConvolution.addDelta 1 := by
  ext m; unfold toRealSeq
  show lpOneAlgRingData.toReal m
    (lpOneAlgRingData.ofReal (E := E) m (DiscreteConvolution.addDelta 1 m)) = _
  rw [lpOneAlgRingData.toReal_ofReal]

instance instRing : Ring (lpOneAlg M E) where
  mul_assoc f g h := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun]
    exact congr_fun (conv_assoc f g h) k
  one_mul f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_one_fun]
    rw [DiscreteConvolution.addDelta_addRingConvolution' 1 _ k, one_mul]
  mul_one f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_one_fun]
    rw [DiscreteConvolution.addRingConvolution_addDelta' _ 1 k, mul_one]
  left_distrib f g h := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_add]
    exact congr_fun (DiscreteConvolution.addRingConvolution_add _ _ _
      (lpOneAlgConvCompat.convSummable f g) (lpOneAlgConvCompat.convSummable f h)) k
  right_distrib f g h := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_add]
    exact congr_fun (DiscreteConvolution.add_addRingConvolution _ _ _
      (lpOneAlgConvCompat.convSummable f h) (lpOneAlgConvCompat.convSummable g h)) k
  zero_mul f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_zero]
    exact congr_fun (DiscreteConvolution.zero_addRingConvolution _) k
  mul_zero f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_zero]
    exact congr_fun (DiscreteConvolution.addRingConvolution_zero _) k

instance instNormedRing : NormedRing (lpOneAlg M E) :=
  { lpOneAlg.instNormedAddCommGroup, lpOneAlg.instRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g => norm_mul_le' f g }

end AddRingInstances

end lpOneAlg

/-! ### Scalar Multiplication Compatibility -/

section lpOneAlgSmul

variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddMonoid M] [lpOneAlgRingData M E]
variable [∀ m, NormedSpace ℝ (E m)]
variable [lpOneAlgSmulCompat M E]

theorem lpOneAlg.toRealSeq_smul (r : ℝ) (f : lpOneAlg M E) :
    lpOneAlg.toRealSeq (r • f) = r • lpOneAlg.toRealSeq f := by
  ext m; simp only [lpOneAlg.toRealSeq, Pi.smul_apply, smul_eq_mul]
  exact lpOneAlgSmulCompat.toReal_smul m r (f m)

end lpOneAlgSmul

/-! ### CommRing, Algebra (separate section to avoid AddGroup/AddCommGroup diamond) -/

section lpOneAlgCommAlgebra

variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddCommMonoid M] [DecidableEq M]
variable [lpOneAlgRingData M E] [lpOneAlgConvCompat M E]

instance lpOneAlg.instCommRing : CommRing (lpOneAlg M E) where
  mul_comm f g := by
    apply lpOneAlg.ext_toRealSeq
    simp only [lpOneAlg.toRealSeq_mul_fun]
    exact DiscreteConvolution.addRingConvolution_comm _ _

instance lpOneAlg.instNormedCommRing : NormedCommRing (lpOneAlg M E) where
  mul_comm := lpOneAlg.instCommRing.mul_comm

variable [∀ m, NormedSpace ℝ (E m)]
variable [lpOneAlgSmulCompat M E]

instance lpOneAlg.instAlgebra : Algebra ℝ (lpOneAlg M E) :=
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

instance lpOneAlg.instNormedAlgebra : NormedAlgebra ℝ (lpOneAlg M E) where
  norm_smul_le := lpOneAlg.instNormedSpaceBase.norm_smul_le

end lpOneAlgCommAlgebra

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [AddMonoid M] [lpOneAlgRingData M E] [lpOneAlgConvCompat M E]
variable [lpOneAlgWeightMul M E] [DecidableEq M]

/-! ### Norm of Identity -/

omit [lpOneAlgWeightMul M E] in
theorem norm_one_eq :
    ‖(1 : lpOneAlg M E)‖ = ‖lpOneAlgRingData.ofReal (E := E) (0 : M) (1 : ℝ)‖ := by
  rw [norm_eq_tsum]
  have h : (fun m => ‖(1 : lpOneAlg M E) m‖) =
      fun m => if m = 0 then ‖lpOneAlgRingData.ofReal (E := E) (0 : M) (1 : ℝ)‖ else 0 := by
    ext m; by_cases hm : m = 0
    · subst hm
      change ‖lpOneAlgRingData.ofReal (E := E) 0 (DiscreteConvolution.addDelta 1 0)‖ = _
      rw [DiscreteConvolution.addDelta_zero_eq]; simp
    · rw [if_neg hm]
      show ‖lpOneAlgRingData.ofReal (E := E) m (DiscreteConvolution.addDelta 1 m)‖ = 0
      rw [DiscreteConvolution.addDelta_ne 1 hm, lpOneAlgRingData.ofReal_zero, norm_zero]
  rw [h, tsum_ite_eq]

instance instNormOneClass : NormOneClass (lpOneAlg M E) where
  norm_one := norm_one_eq.trans (lpOneAlgWeightMul.norm_ofReal_one_zero)

end lpOneAlg

end RadiiPolynomial

end
