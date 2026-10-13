import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.FiberTrivialization
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# The weighted ℓ¹ carrier `lpOneAlg M E`

`lpOneAlg M E` wraps `lp E 1`: the families `f m ∈ E m` with `∑' m, ‖f m‖ < ∞`, normed by that
sum. This file is the carrier half of the weighted ℓ¹ API; it uses no operation on the index type
and no convolution. The convolution ring structure is in `WeightedL1/Algebra.lean`.

## Contents

* The Beurling-weight classes `lpOneAlgWeightMul`, `lpOneAlgWeightSubMul` (and their
  multiplicative twins), stated on the weight `FiberTrivialization.weight` of the chosen frame.
* The structure `lpOneAlg`, its normed-group, complete-space and normed-space instances, and the
  norm faces `norm_eq_tsum`, `summable_norm`, `norm_apply_le_norm`.
* Frame-free fiber insertion `fiberSingle m x` (`x : E m`), bundled as the linear isometry
  `fiberSingleₗᵢ m : E m →ₗᵢ[𝕜] lpOneAlg M E`, its norm `norm_fiberSingle` and the expansion
  `hasSum_fiberSingle`, also pushed through any continuous linear map (`hasSum_fiberSingle_mapCLM`).
* Scalar coordinates through the chosen frame `θ`: the coefficient sequence
  `toRealSeq f m = θ_m⁻¹ (f m)` with extensionality `ext_toRealSeq`, its additive and scalar faces,
  the bundle `toRealSeqₗ : lpOneAlg M E →ₗ[𝕜] (M → 𝕜)` (`toRealSeq_injective`,
  `toRealSeq_finset_sum`), the weighted norm `norm_eq_abs_toReal_mul_weight`, and the bound
  `abs_toRealSeq_le` when every weight is at least `1`.
* Over the index `ℤ` with any fibers: the sign split `norm_eq_tsum_natCast_add_tsum_neg`, its
  vanishing-negative form `norm_eq_tsum_natCast_of_neg`, and the finite-support sums
  `norm_eq_bilatFinSum`, `norm_eq_natFinSum_of_finSupp`.
* The scalar singles `single m x = fiberSingle m (θ_m x)` (coefficient atom
  `toRealSeq_single_eq_piSingle`), the mode expansion `hasSum_single`, coordinate evaluation
  `evalCLM`, and the column-norm bounds `norm_le_of_cols`, `finsum_norm_le_of_cols`.

## Frames

The carrier, its normed-group/completeness/normed-space structure and `fiberSingle` are
frame-free. Scalar coordinates (`toRealSeq`, `single`), the weight classes and everything built
on them are indexed by the chosen `FiberTrivialization 𝕜 M E`. Equal weights do not determine the
frame: replacing every `θ_m` by `r ↦ θ_m (-r)` keeps every weight and changes the coordinates
and (in `WeightedL1/Algebra.lean`) the product. Every weight or convolution witness therefore
takes the frame it is about as an instance argument.

## Typeclass convention

The weight classes come in pairs: the additive classes (`lpOneAlgWeightMul`,
`lpOneAlgWeightSubMul`) are declared directly, and the multiplicative ones
(`lpOneMulAlgWeightMul`, `lpOneMulAlgWeightSubMul`) are linked to them by
`@[to_additive existing]`. Helper definitions and lemmas are stated in multiplicative spelling and
generate their additive versions via `@[to_additive]` (`mulToRealSeq` ↦ `toRealSeq`);
`mulToRealSeq` itself needs no monoid structure on `M`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### Beurling-weight classes (indexed by the chosen frame) -/

/-- Beurling weight of the chosen frame (additive index monoid): `ω_{j+l} ≤ ω_j ω_l` and
`ω_0 = 1`, with `ω_m = FiberTrivialization.weight m = ‖θ_m 1‖`. -/
class lpOneAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] where
  weight_add_le : ∀ j l : M,
    FiberTrivialization.weight (E := E) (j + l) ≤
      FiberTrivialization.weight (E := E) j * FiberTrivialization.weight (E := E) l
  weight_zero : FiberTrivialization.weight (E := E) (0 : M) = 1

/-- Beurling weight of the chosen frame (multiplicative index monoid): `ω_{j*l} ≤ ω_j ω_l` and
`ω_1 = 1`. Sufficient for the convolution ring on `lpOneAlg` when `[HasMulAntidiagonal M]`
(finite fibers, `lpOneAlg.instMulConvCompatOfAntidiag`) or when `𝕜` is complete
(`lpOneAlg.instMulConvCompatOfWeightMul`). -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgWeightMul]
class lpOneMulAlgWeightMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] where
  weight_mul_le : ∀ j l : M,
    FiberTrivialization.weight (E := E) (j * l) ≤
      FiberTrivialization.weight (E := E) j * FiberTrivialization.weight (E := E) l
  /-- Weight at identity = 1: ensures `‖1‖ = 1` (NormOneClass). -/
  weight_one : FiberTrivialization.weight (E := E) (1 : M) = 1

/-- Submultiplicative weight of the chosen frame with weight ≥ 1 (additive index monoid). -/
class lpOneAlgWeightSubMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] extends lpOneAlgWeightMul 𝕜 M E where
  /-- Weight ≥ 1: feeds the fiberwise bound `‖toRealSeq f m‖ ≤ ‖f m‖` (`abs_toRealSeq_le`),
  embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
  one_le_weight : ∀ m, 1 ≤ FiberTrivialization.weight (E := E) m

/-- Submultiplicative weight of the chosen frame with weight ≥ 1 (multiplicative index monoid).
The weight ≥ 1 axiom is not used for Cauchy sum convergence (submultiplicativity alone suffices,
see `instMulConvCompatOfWeightMul`); it feeds the fiberwise bound
`‖mulToRealSeq f m‖ ≤ ‖f m‖` (`abs_mulToRealSeq_le`, which needs only the weight ≥ 1 field),
embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgWeightSubMul]
class lpOneMulAlgWeightSubMul (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] extends lpOneMulAlgWeightMul 𝕜 M E where
  /-- Weight ≥ 1: feeds the fiberwise bound `‖mulToRealSeq f m‖ ≤ ‖f m‖`
  (`abs_mulToRealSeq_le`), embedding the extracted `𝕜`-sequence into unweighted `ℓ¹`. -/
  one_le_weight : ∀ m, 1 ≤ FiberTrivialization.weight (E := E) m

/-! ### lpOneAlg Structure -/

/-- The weighted ℓ¹ carrier: a wrapper of `lp E 1`, the families `f m ∈ E m` with
`∑' m, ‖f m‖ < ∞`. The convolution product of `WeightedL1/Algebra.lean` is defined on this
wrapper. -/
structure lpOneAlg (M : Type*) (E : M → Type*) [∀ m, NormedAddCommGroup (E m)] where
  /-- The underlying element of `lp E 1`. -/
  toLp : lp E 1

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-- The wrapper as an equivalence with `lp E 1` (the source of the normed-group structure). -/
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


/-! ### Scalar coordinates through the chosen frame (monoid-independent) -/

section Coordinates

variable {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

/-- The scalar coordinates in the chosen frame: `mulToRealSeq f m = θ_m⁻¹ (f m)`.
Monoid-independent. -/
@[to_additive (dont_translate := E 𝕜) toRealSeq
  /-- The scalar coordinates in the chosen frame: `toRealSeq f m = θ_m⁻¹ (f m)`. -/]
def mulToRealSeq (f : lpOneAlg M E) : M → 𝕜 :=
  fun m => (FiberTrivialization.equiv (E := E) m).symm (f m)

/-- The coordinate at `m` is the frame inverse of the fiber value: `θ_m⁻¹ (f m)`. -/
@[to_additive (dont_translate := E 𝕜) toRealSeq_apply
  /-- The coordinate at `m` is the frame inverse of the fiber value: `θ_m⁻¹ (f m)`. -/]
theorem mulToRealSeq_apply (f : lpOneAlg M E) (m : M) :
    mulToRealSeq f m = (FiberTrivialization.equiv (E := E) m).symm (f m) := rfl

/-- The frame recovers the fiber value from its coordinate: `θ_m (toRealSeq f m) = f m`. -/
@[to_additive (dont_translate := E 𝕜) equiv_toRealSeq]
theorem equiv_mulToRealSeq (f : lpOneAlg M E) (m : M) :
    FiberTrivialization.equiv (E := E) m (mulToRealSeq f m) = f m :=
  LinearEquiv.apply_symm_apply _ _

@[to_additive (dont_translate := E 𝕜) norm_eq_abs_toReal_mul_weight]
theorem norm_eq_abs_mulToReal_mul_weight (f : lpOneAlg M E) (m : M) :
    ‖f m‖ = ‖mulToRealSeq f m‖ * FiberTrivialization.weight (E := E) m := by
  rw [← FiberTrivialization.norm_equiv_apply, equiv_mulToRealSeq]

/-- Extensionality via toRealSeq. -/
@[to_additive (dont_translate := E 𝕜) ext_toRealSeq]
theorem ext_mulToRealSeq {f g : lpOneAlg M E}
    (h : mulToRealSeq f = mulToRealSeq g) : f = g :=
  ext fun m => by rw [← equiv_mulToRealSeq f m, ← equiv_mulToRealSeq g m, congr_fun h m]

@[to_additive (dont_translate := E 𝕜) toRealSeq_add]
theorem mulToRealSeq_add (f g : lpOneAlg M E) :
    mulToRealSeq (f + g) = mulToRealSeq f + mulToRealSeq g :=
  funext fun m => map_add (FiberTrivialization.equiv (E := E) m).symm (f m) (g m)

@[to_additive (dont_translate := E 𝕜) toRealSeq_zero]
theorem mulToRealSeq_zero : mulToRealSeq (0 : lpOneAlg M E) = 0 :=
  funext fun m => map_zero (FiberTrivialization.equiv (E := E) m).symm

@[to_additive (dont_translate := E 𝕜) toRealSeq_neg]
theorem mulToRealSeq_neg (f : lpOneAlg M E) :
    mulToRealSeq (-f) = -(mulToRealSeq f) :=
  funext fun m => map_neg (FiberTrivialization.equiv (E := E) m).symm (f m)

@[to_additive (dont_translate := E 𝕜) toRealSeq_sub]
theorem mulToRealSeq_sub (f g : lpOneAlg M E) :
    mulToRealSeq (f - g) = mulToRealSeq f - mulToRealSeq g := by
  rw [sub_eq_add_neg, mulToRealSeq_add, mulToRealSeq_neg, sub_eq_add_neg]

/-- The coordinates are `𝕜`-linear for the inherited module structure (`map_smul` of `θ_m⁻¹`). -/
@[to_additive (dont_translate := E 𝕜) toRealSeq_smul]
theorem mulToRealSeq_smul (r : 𝕜) (f : lpOneAlg M E) :
    mulToRealSeq (r • f) = r • mulToRealSeq f :=
  funext fun m => map_smul (FiberTrivialization.equiv (E := E) m).symm r (f m)

/-- The coefficient map `toRealSeq` as a `𝕜`-linear map (injective: `toRealSeq_injective`). -/
def toRealSeqₗ : lpOneAlg M E →ₗ[𝕜] (M → 𝕜) where
  toFun := toRealSeq
  map_add' := toRealSeq_add
  map_smul' := toRealSeq_smul

@[simp] theorem toRealSeqₗ_apply (f : lpOneAlg M E) :
    toRealSeqₗ (𝕜 := 𝕜) f = toRealSeq f := rfl

/-- The coefficient map `toRealSeq` is injective: two elements of `lpOneAlg M E` with the same
coefficients in every fiber are equal. -/
theorem toRealSeq_injective : Function.Injective (toRealSeq : lpOneAlg M E → M → 𝕜) :=
  fun _ _ h => ext_toRealSeq h

/-- Coefficient extraction commutes with finite sums (`map_sum` of `toRealSeqₗ`). -/
theorem toRealSeq_finset_sum {ι : Type*} (s : Finset ι) (a : ι → lpOneAlg M E) (k : M) :
    toRealSeq (∑ i ∈ s, a i) k = ∑ i ∈ s, toRealSeq (a i) k := by
  rw [← toRealSeqₗ_apply, map_sum, Finset.sum_apply]
  rfl

end Coordinates

/-! ### Weight ≥ 1: the coordinates embed into unweighted ℓ¹ (no monoid structure needed) -/

section WeightOneLe

variable {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

/-- `‖mulToRealSeq f m‖ ≤ ‖f m‖` when every weight of the frame is at least `1`. -/
@[to_additive (dont_translate := E 𝕜) abs_toRealSeq_le
  /-- `‖toRealSeq f m‖ ≤ ‖f m‖` when every weight of the frame is at least `1`. -/]
theorem abs_mulToRealSeq_le (hw : ∀ m, 1 ≤ FiberTrivialization.weight (E := E) m)
    (f : lpOneAlg M E) (m : M) : ‖mulToRealSeq f m‖ ≤ ‖f m‖ := by
  rw [norm_eq_abs_mulToReal_mul_weight f m]
  exact le_mul_of_one_le_right (norm_nonneg _) (hw m)

@[to_additive (dont_translate := E 𝕜) summable_abs_toRealSeq]
theorem summable_abs_mulToRealSeq (hw : ∀ m, 1 ≤ FiberTrivialization.weight (E := E) m)
    (f : lpOneAlg M E) : Summable (fun m => ‖mulToRealSeq f m‖) :=
  (summable_norm f).of_nonneg_of_le (fun _ => norm_nonneg _) (abs_mulToRealSeq_le hw f)

end WeightOneLe

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

/-! ### Scalar singles, mode expansion, and column-norm bounds

Monoid-independent API (the index `M` needs no algebraic structure except where
stated). The scalar single `single m x = fiberSingle m (θ_m x)` is the frame's atom scaled by
`x`; sequence-mentioning statements use the additive `toRealSeq` spelling.

The column-norm bounds realize the ℓ¹ principle: out of a weighted ℓ¹ space, an
operator's norm is controlled by the sup of its weighted column norms. Promoted
from the Example 14.2.1 toolkit (2026-08-25). -/

namespace lpOneAlg

section FrameFree

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

/-! ### Frame-free fiber insertion and expansion -/

section FiberSingle

variable [DecidableEq M]

/-- Frame-free insertion of a fiber vector: the element with value `x : E m` at index `m` and
`0` elsewhere. -/
def fiberSingle (m : M) (x : E m) : lpOneAlg M E :=
  ⟨lp.single 1 m x⟩

/-- The insertion is `Pi.single` at every index. -/
theorem fiberSingle_apply (m : M) (x : E m) (k : M) :
    fiberSingle m x k = (Pi.single m x : ∀ k, E k) k := rfl

/-- The inserted vector sits at its own index. -/
@[simp] theorem fiberSingle_apply_self (m : M) (x : E m) : fiberSingle m x m = x :=
  Pi.single_eq_same _ _

/-- The insertion vanishes away from its index. -/
theorem fiberSingle_apply_of_ne {m k : M} (x : E m) (h : k ≠ m) : fiberSingle m x k = 0 :=
  Pi.single_eq_of_ne h _

/-- The insertion of `0` is `0` (scalar-free; the `map_zero` of `fiberSingleₗᵢ`). -/
@[simp] theorem fiberSingle_zero (m : M) : fiberSingle m (0 : E m) = 0 := by
  show mk (lp.single 1 m 0) = mk 0
  rw [lp.single_zero]

/-- The insertion is additive (scalar-free; the `map_add` field of `fiberSingleₗᵢ`). -/
theorem fiberSingle_add (m : M) (x y : E m) :
    fiberSingle m (x + y) = fiberSingle m x + fiberSingle m y := by
  show mk (lp.single 1 m (x + y)) = mk (lp.single 1 m x + lp.single 1 m y)
  rw [lp.single_add]

/-- The insertion is isometric: `‖fiberSingle m x‖ = ‖x‖` (scalar-free; the `norm_map` field of
`fiberSingleₗᵢ`). -/
@[simp] theorem norm_fiberSingle (m : M) (x : E m) : ‖fiberSingle m x‖ = ‖x‖ :=
  lp.norm_single (by norm_num) m x

/-- The frame-free insertion bundled as a linear isometry `E m →ₗᵢ[𝕜] lpOneAlg M E` for the
inherited action; its zero, negation, subtraction and scalar laws are `map_*` of this bundle. -/
def fiberSingleₗᵢ [∀ m, NormedSpace 𝕜 (E m)] (m : M) : E m →ₗᵢ[𝕜] lpOneAlg M E where
  toFun := fiberSingle m
  map_add' := fiberSingle_add m
  map_smul' c x := by
    show mk (lp.single 1 m (c • x)) = mk (c • lp.single 1 m x)
    rw [lp.single_smul]
  norm_map' := norm_fiberSingle m

@[simp] theorem coe_fiberSingleₗᵢ [∀ m, NormedSpace 𝕜 (E m)] (m : M) :
    ⇑(fiberSingleₗᵢ (𝕜 := 𝕜) (E := E) m) = fiberSingle m := rfl

/-- Every element is the norm-convergent sum of its fiber insertions (transfer of
`lp.hasSum_single` through the wrapper). -/
theorem hasSum_fiberSingle (h : lpOneAlg M E) :
    HasSum (fun m : M => fiberSingle m (h m)) h :=
  (lp.hasSum_single (by norm_num) h.toLp).map (mkAddHom (E := E)) (isometry_mk (E := E)).continuous

/-- The fiber expansion pushed through a continuous linear map (for the inherited action). -/
theorem hasSum_fiberSingle_mapCLM [∀ m, NormedSpace 𝕜 (E m)] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (W : lpOneAlg M E →L[𝕜] F) (h : lpOneAlg M E) :
    HasSum (fun m : M => W (fiberSingle m (h m))) (W h) :=
  (hasSum_fiberSingle h).mapL W

end FiberSingle

end FrameFree

section Single

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]

/-- The element with scalar coordinate `x` at index `j` and `0` elsewhere:
`single j x = fiberSingle j (θ_j x)`. -/
def single (j : M) (x : 𝕜) : lpOneAlg M E :=
  fiberSingle j (FiberTrivialization.equiv (E := E) j x)

/-- The scalar single is the frame-free insertion of `θ_j x`. -/
theorem single_eq_fiberSingle (j : M) (x : 𝕜) :
    single (E := E) j x = fiberSingle j (FiberTrivialization.equiv (E := E) j x) := rfl

theorem toRealSeq_single (j : M) (x : 𝕜) (k : M) :
    toRealSeq (single (E := E) j x) k = if k = j then x else 0 := by
  rw [toRealSeq_apply, single_eq_fiberSingle]
  by_cases h : k = j
  · subst h
    rw [fiberSingle_apply_self, LinearEquiv.symm_apply_apply, ite_eq_left rfl]
  · rw [fiberSingle_apply_of_ne _ h, map_zero, ite_eq_right h]

/-- The coefficient sequence of an atom is the atom `Pi.single j x`. -/
theorem toRealSeq_single_eq_piSingle (j : M) (x : 𝕜) :
    toRealSeq (single (E := E) j x) = Pi.single j x :=
  funext fun k => (toRealSeq_single j x k).trans (Pi.single_apply j x k).symm

theorem norm_single (j : M) (x : 𝕜) :
    ‖(single (E := E) j x : lpOneAlg M E)‖ = ‖x‖ * FiberTrivialization.weight (E := E) j := by
  rw [single_eq_fiberSingle, norm_fiberSingle, FiberTrivialization.norm_equiv_apply]

/-- Every element is the norm-convergent sum of its scalar singles. -/
theorem hasSum_single (h : lpOneAlg M E) :
    HasSum (fun m : M => single (E := E) m (toRealSeq h m)) h := by
  simpa only [single_eq_fiberSingle, equiv_toRealSeq] using hasSum_fiberSingle h

/-- Mode expansion pushed through a continuous linear map. -/
theorem hasSum_single_mapCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (W : lpOneAlg M E →L[𝕜] F) (h : lpOneAlg M E) :
    HasSum (fun m : M => W (single m (toRealSeq h m))) (W h) :=
  (hasSum_single h).mapL W

theorem single_smul (j : M) (x : 𝕜) :
    single (E := E) j x = x • single j 1 := by
  show fiberSingleₗᵢ (𝕜 := 𝕜) j (FiberTrivialization.equiv j x) =
    x • fiberSingleₗᵢ (𝕜 := 𝕜) j (FiberTrivialization.equiv j 1)
  rw [← map_smul, ← map_smul, smul_eq_mul, mul_one]

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
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]

/-- **Column-norm bound.** Out of a weighted ℓ¹ space, an operator norm is
controlled by the weighted column norms: if `‖W (single m 1)‖ ≤ C · ω_m` for
every `m` (with `ω_m = FiberTrivialization.weight m` the weight of the frame), then
`‖W h‖ ≤ C · ‖h‖`. -/
theorem norm_le_of_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (W : lpOneAlg M E →L[𝕜] F) {C : ℝ}
    (hcol : ∀ m : M, ‖W (single m 1)‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) : ‖W h‖ ≤ C * ‖h‖ := by
  have hexp := hasSum_single_mapCLM W h
  have hterm : ∀ m : M, ‖W (single m (toRealSeq h m))‖
      ≤ ‖toRealSeq h m‖ * (C * FiberTrivialization.weight (E := E) m) := by
    intro m
    rw [single_smul, map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hcol m) (norm_nonneg _)
  have hmaj : Summable (fun m : M =>
      ‖toRealSeq h m‖ * (C * FiberTrivialization.weight (E := E) m)) := by
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
      ≤ ε * FiberTrivialization.weight (E := E) m)
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
      ‖toRealSeq h m‖ * (ε * FiberTrivialization.weight (E := E) m)) := by
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
      ≤ ‖toRealSeq h m‖ * (ε * FiberTrivialization.weight (E := E) m) := by
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
