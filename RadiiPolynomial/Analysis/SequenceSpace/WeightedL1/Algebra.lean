import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import RadiiPolynomial.Algebra.Convolution.Ring

/-!
# The convolution ring on the weighted ℓ¹ carrier

On the carrier `lpOneAlg M E` of `WeightedL1/Carrier.lean`, with a monoid structure on the index
type, convolution of the coefficient sequences is the multiplication. This file is the ring half of
the weighted ℓ¹ API.

* The convolution classes `lpOneAlgConvCompat` / `lpOneMulAlgConvCompat` supply the summability
  and fiber-norm primitives behind one ring instance; like the weight classes they are indexed by
  the chosen frame `θ` (`FiberTrivialization`). They have two instances: the tsum path
  `instConvCompatOfWeightMul` (submultiplicative weight, complete scalar field) and the finite-fiber
  path `instConvCompatOfAntidiag` (`Finset.HasAntidiagonal`, priority 1100).
* The instances `instMul`, `instOne`, `instRing`, `instNormedRing` (from the index monoid,
  `DecidableEq` and convolution compatibility; product `(f * g)_k = θ_k (θ⁻¹f ⋆ θ⁻¹g)_k`, unit
  `θ_k (δ_1)_k`), with the fiber faces `mul_apply`, `one_apply` and the coefficient faces
  `toRealSeq_mul_fun`, `toRealSeq_one_fun`; `instAlgebra` and `instNormedAlgebra` over any
  additive index monoid; `instCommRing` and `instNormedCommRing` over a commutative one;
  `instNormOneClass` (from the frame's `ω_0 = 1` alone; no convolution witness).
* Convolution evaluation: `toRealSeq_mul_tsum`, `toRealSeq_mul_eq_finsum`.

## Typeclass convention

The convolution classes come in pairs: the additive class `lpOneAlgConvCompat` is declared directly
and the multiplicative one `lpOneMulAlgConvCompat` is linked to it by `@[to_additive existing]` (the
class field `mulConvSummable` corresponds to `convSummable`). Helper lemmas are stated in
multiplicative spelling and generate their additive versions via `@[to_additive]`
(`mul_memℓp_mul` ↦ `mul_memℓp`, `norm_mul_le_mul'` ↦ `norm_mul_le'`, etc.). The ring *instances*
are generated the same way: `instMulMul`, `instMulOne`, `instMulRing`, `instMulNormedRing` (for
`[Monoid M]`) give `instMul`, `instOne`, `instRing`, `instNormedRing` (for `[AddMonoid M]`) by
`@[to_additive (dont_translate := E 𝕜)]`, with the fibers and the scalar field excluded from the
translation. The `Algebra`, `NormedAlgebra`, `CommRing` and `NormOneClass` instances are stated for
an additive index monoid only.

## Frames

The product and its unit are transported through the chosen frame, so two frames with equal
weights can give different products (replacing `θ_m r` by `θ_m (-r)` negates the product and
turns the unit into `-1`, the element whose scalar sequence in the original frame is `-δ₀`). Every convolution witness takes the frame as an instance argument.
-/

open scoped BigOperators Topology NNReal ENNReal DiscreteConvolution

noncomputable section

namespace RadiiPolynomial

open _root_.DiscreteConvolution RadiiPolynomial.DiscreteConvolution

/-! ### Convolution compatibility: abstraction over summability path -/

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (additive).
Two instances: from `[lpOneAlgWeightMul]` with `[CompleteSpace 𝕜]` (tsum path,
submultiplicativity alone) or from `[HasAntidiagonal M] + [lpOneAlgWeightMul 𝕜 M E]` (finite
sum path, priority 1100, no completeness). -/
class lpOneAlgConvCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [AddMonoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] where
  convSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : addFiber k =>
      lpOneAlg.toRealSeq f ab.1.1 * lpOneAlg.toRealSeq g ab.1.2
  tripleConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    AddTripleConvolutionSummable
      (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) (lpOneAlg.toRealSeq h) x
  norm_conv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖FiberTrivialization.equiv (E := E) k
      (addRingConvolution (lpOneAlg.toRealSeq f)
        (lpOneAlg.toRealSeq g) k)‖ ≤
    ∑' ab : addFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

/-- Provides the convolution primitives needed for Ring on `lpOneAlg M E` (multiplicative).
Two instances: from `[lpOneMulAlgWeightMul]` with `[CompleteSpace 𝕜]` (tsum path,
submultiplicativity alone) or from `[HasMulAntidiagonal M] + [lpOneMulAlgWeightMul 𝕜 M E]`
(finite sum path, priority 1100, no completeness). -/
@[to_additive existing (dont_translate := E 𝕜) lpOneAlgConvCompat]
class lpOneMulAlgConvCompat (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [Monoid M] [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] where
  mulConvSummable : ∀ (f g : lpOneAlg M E) (k : M),
    Summable fun ab : mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2
  tripleMulConvSummable : ∀ (f g h : lpOneAlg M E) (x : M),
    TripleConvolutionSummable
      (lpOneAlg.mulToRealSeq f) (lpOneAlg.mulToRealSeq g) (lpOneAlg.mulToRealSeq h) x
  norm_mulConv_le_fiber : ∀ (f g : lpOneAlg M E) (k : M),
    ‖FiberTrivialization.equiv (E := E) k
      (ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖

/-- Pointwise weighted bound for two extracted scalar coefficients. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.norm_toRealSeq_add_weight_le]
private theorem lpOneAlg.norm_mulToRealSeq_mul_weight_le
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) {j l k : M} (hjl : j * l = k) :
    ‖lpOneAlg.mulToRealSeq f j‖ * ‖lpOneAlg.mulToRealSeq g l‖ *
        FiberTrivialization.weight (E := E) k ≤
      ‖f j‖ * ‖g l‖ := by
  subst k
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f j,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g l]
  exact (mul_le_mul_of_nonneg_left (lpOneMulAlgWeightMul.weight_mul_le (E := E) j l)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

/-- Generic per-index bound: given fiber summability, proves the norm bound
via triangle inequality + submultiplicativity. Shared by both convolution paths. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.norm_conv_le_fiber_generic]
private theorem lpOneAlg.norm_mulConv_le_fiber_generic
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M)
    (habs : Summable fun ab : mulFiber k =>
      ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖) :
    ‖FiberTrivialization.equiv (E := E) k
      (ringConvolution (lpOneAlg.mulToRealSeq f)
        (lpOneAlg.mulToRealSeq g) k)‖ ≤
    ∑' ab : mulFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
  rw [FiberTrivialization.norm_equiv_apply, ringConvolution_apply]
  have hnorm_fiber : Summable (fun ab : mulFiber k =>
      ‖f ab.1.1‖ * ‖g ab.1.2‖) := (lpOneAlg.summable_norm_prod f g).subtype _
  have h_elem (ab : mulFiber k) :=
    lpOneAlg.norm_mulToRealSeq_mul_weight_le f g
      (mem_mulFiber.mp ab.2)
  have h_tri : ‖∑' ab : mulFiber k,
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2‖ ≤
      ∑' ab : mulFiber k,
        ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖ :=
    tsum_of_norm_bounded habs.hasSum
      fun ab => le_of_eq (norm_mul _ _)
  refine (mul_le_mul_of_nonneg_right h_tri (FiberTrivialization.weight_nonneg k)).trans ?_
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum h_elem
    (Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (FiberTrivialization.weight_nonneg k))
      h_elem hnorm_fiber) hnorm_fiber

/-- Absolute convolution fiber summability from `lpOneMulAlgWeightMul` alone (no weight ≥ 1).
Key bound: `|f_a|·|g_b|·w(k) ≤ ‖f a‖·‖g b‖` via submultiplicativity `w(k) ≤ w(a)·w(b)`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.abs_convSummable_of_weightMul]
private theorem lpOneAlg.abs_mulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : mulFiber k =>
      ‖lpOneAlg.mulToRealSeq f ab.1.1‖ * ‖lpOneAlg.mulToRealSeq g ab.1.2‖ := by
  have hnorm : Summable
      (fun ab : mulFiber k => ‖f ab.1.1‖ * ‖g ab.1.2‖) :=
    (lpOneAlg.summable_norm_prod f g).subtype _
  have hw := FiberTrivialization.weight_pos (E := E) k
  refine (hnorm.const_smul (FiberTrivialization.weight (E := E) k)⁻¹).of_norm_bounded
    fun ab => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [smul_eq_mul]
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact lpOneAlg.norm_mulToRealSeq_mul_weight_le f g
    (mem_mulFiber.mp ab.2)

@[to_additive (dont_translate := E 𝕜) lpOneAlg.convSummable_of_weightMul]
private theorem lpOneAlg.mulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g : lpOneAlg M E) (k : M) :
    Summable fun ab : mulFiber k =>
      lpOneAlg.mulToRealSeq f ab.1.1 * lpOneAlg.mulToRealSeq g ab.1.2 :=
  (lpOneAlg.abs_mulConvSummable_of_weightMul f g k).of_norm_bounded
    fun ⟨⟨_, _⟩, _⟩ => norm_mul_le _ _

/-- Triple convolution summability from `lpOneMulAlgWeightMul` alone.
Applies submultiplicativity twice: `w(a·b·c) ≤ w(a·b)·w(c) ≤ w(a)·w(b)·w(c)`. -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.tripleConvSummable_of_weightMul]
private theorem lpOneAlg.tripleMulConvSummable_of_weightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgWeightMul 𝕜 M E]
    (f g h : lpOneAlg M E) (x : M) :
    Summable fun p : tripleMulFiber x =>
      lpOneAlg.mulToRealSeq f p.1.1 * lpOneAlg.mulToRealSeq g p.1.2.1 *
        lpOneAlg.mulToRealSeq h p.1.2.2 := by
  have h3 : Summable (fun abc : M × M × M =>
      ‖f abc.1‖ * ‖g abc.2.1‖ * ‖h abc.2.2‖) :=
    ((lpOneAlg.summable_norm f).mul_of_nonneg (lpOneAlg.summable_norm_prod g h)
      (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).congr
      fun _ => (mul_assoc _ _ _).symm
  have hnorm3 : Summable (fun p : tripleMulFiber x =>
      ‖f p.1.1‖ * ‖g p.1.2.1‖ * ‖h p.1.2.2‖) := h3.subtype _
  have hw := FiberTrivialization.weight_pos (E := E) x
  refine (hnorm3.const_smul (FiberTrivialization.weight (E := E) x)⁻¹).of_norm_bounded
    fun p => ?_
  have hmem := p.2; rw [mem_tripleMulFiber] at hmem
  simp only [smul_eq_mul]
  rw [norm_mul, norm_mul]
  rw [lpOneAlg.norm_eq_abs_mulToReal_mul_weight f p.1.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight g p.1.2.1,
    lpOneAlg.norm_eq_abs_mulToReal_mul_weight h p.1.2.2]
  have hsub1 := lpOneMulAlgWeightMul.weight_mul_le (E := E) (p.1.1 * p.1.2.1) p.1.2.2
  have hsub2 := lpOneMulAlgWeightMul.weight_mul_le (E := E) p.1.1 p.1.2.1
  rw [hmem] at hsub1
  have hsub : FiberTrivialization.weight (E := E) x ≤
      FiberTrivialization.weight (E := E) p.1.1 *
      FiberTrivialization.weight (E := E) p.1.2.1 *
      FiberTrivialization.weight (E := E) p.1.2.2 :=
    hsub1.trans (mul_le_mul_of_nonneg_right hsub2 (FiberTrivialization.weight_nonneg _))
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  exact (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).trans_eq (by ring)

/-- Instance from `[lpOneMulAlgWeightMul]` and `[CompleteSpace 𝕜]`: tsum path using
submultiplicativity alone (no weight ≥ 1 needed). -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.instConvCompatOfWeightMul]
instance lpOneAlg.instMulConvCompatOfWeightMul
    {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M] [FiberTrivialization 𝕜 M E]
    [lpOneMulAlgWeightMul 𝕜 M E] : lpOneMulAlgConvCompat 𝕜 M E where
  mulConvSummable := lpOneAlg.mulConvSummable_of_weightMul
  tripleMulConvSummable := lpOneAlg.tripleMulConvSummable_of_weightMul
  norm_mulConv_le_fiber f g k :=
    lpOneAlg.norm_mulConv_le_fiber_generic f g k
      (lpOneAlg.abs_mulConvSummable_of_weightMul f g k)

/-- Instance from `[HasMulAntidiagonal M] + [lpOneMulAlgWeightMul M E]`:
finite sum path (antidiagonal gives finite fibers, no weight ≥ 1 needed). -/
@[to_additive (dont_translate := E 𝕜) lpOneAlg.instConvCompatOfAntidiag]
instance (priority := 1100) lpOneAlg.instMulConvCompatOfAntidiag
    {𝕜 : Type*} [NormedField 𝕜]
    {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [Monoid M]
    [Finset.HasMulAntidiagonal M] [FiberTrivialization 𝕜 M E]
    [lpOneMulAlgWeightMul 𝕜 M E] : lpOneMulAlgConvCompat 𝕜 M E where
  mulConvSummable f g k :=
    (mulFiber_finite k).summable (fun p : M × M =>
      lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2)
  tripleMulConvSummable f g h x := by
    have : ∀ k : M, Finite ↑(mulFiber k) :=
      fun k => (mulFiber_finite k).to_subtype
    have : Finite ↑(tripleMulFiber x) :=
      (leftMulAssocEquiv x).finite_iff.mp inferInstance
    exact (Set.toFinite _).summable
      (fun p : M × M × M =>
        lpOneAlg.mulToRealSeq f p.1 * lpOneAlg.mulToRealSeq g p.2.1 *
          lpOneAlg.mulToRealSeq h p.2.2)
  norm_mulConv_le_fiber f g k := by
    have : Finite ↑(mulFiber k) :=
      (mulFiber_finite k).to_subtype
    exact lpOneAlg.norm_mulConv_le_fiber_generic f g k
      ((mulFiber_finite k).summable (fun p : M × M =>
        ‖lpOneAlg.mulToRealSeq f p.1‖ * ‖lpOneAlg.mulToRealSeq g p.2‖))

namespace lpOneAlg

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-! ### Ring Infrastructure (multiplicative primary, additive via @[to_additive]) -/

section MulRingInfrastructure

variable {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)]
variable [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgConvCompat 𝕜 M E] [DecidableEq M]

/-! ### Mul Membership and Norm -/

omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) mul_memℓp]
theorem mul_memℓp_mul (f g : lpOneAlg M E) :
    Memℓp (fun k => FiberTrivialization.equiv (E := E) k
      (ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    (sigmaMulFiberEquiv.summable_iff.mpr
      (summable_norm_prod f g)).sigma

omit [lpOneMulAlgConvCompat 𝕜 M E] in
/-- `delta r` belongs to ℓ¹. Used by the identity and scalar casts. -/
@[to_additive (dont_translate := E 𝕜) delta_memℓp]
private theorem delta_memℓp_mul (r : 𝕜) :
    Memℓp (fun m => FiberTrivialization.equiv (E := E) m
      (delta r m)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact summable_of_ne_finset_zero (s := {1}) (fun b hb => by
    rw [Finset.mem_singleton] at hb
    rw [delta_ne r hb, map_zero, norm_zero])

omit [lpOneMulAlgConvCompat 𝕜 M E] in
@[to_additive (dont_translate := E 𝕜) one_memℓp]
theorem one_memℓp_mul :
    Memℓp (fun m => FiberTrivialization.equiv (E := E) m
      (delta (1 : 𝕜) m)) 1 :=
  delta_memℓp_mul (1 : 𝕜)

omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) norm_mul_le']
private theorem norm_mul_le_mul' (f g : lpOneAlg M E) :
    ‖(⟨⟨fun k => FiberTrivialization.equiv (E := E) k
        (ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
      mul_memℓp_mul f g⟩⟩ : lpOneAlg M E)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum]
  have hsigma :=
    sigmaMulFiberEquiv.summable_iff.mpr (summable_norm_prod f g)
  have hmem : Summable (fun k => ‖FiberTrivialization.equiv (E := E) k
      (ringConvolution (mulToRealSeq f) (mulToRealSeq g) k)‖) := by
    simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp (mul_memℓp_mul f g)
  refine (Summable.tsum_le_tsum (lpOneMulAlgConvCompat.norm_mulConv_le_fiber f g)
    hmem hsigma.sigma).trans (le_of_eq ?_)
  exact (hsigma.tsum_sigma' hsigma.sigma_factor) ▸
    (summable_norm f).tsum_mul_tsum (summable_norm g) (summable_norm_prod f g) ▸
    sigmaMulFiberEquiv.tsum_eq
      (fun p => ‖f p.1‖ * ‖g p.2‖)

end MulRingInfrastructure

/-! ### Mul / One / Ring / NormedRing instances (multiplicative index monoid) -/

section MulRingInstances

variable {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)]
variable [Monoid M] [FiberTrivialization 𝕜 M E] [lpOneMulAlgConvCompat 𝕜 M E] [DecidableEq M]

/-- The convolution product transported through the chosen frame:
`(f * g)_k = θ_k ((θ⁻¹ f ⋆ θ⁻¹ g)_k)`. -/
@[to_additive (dont_translate := E 𝕜) instMul]
instance instMulMul : Mul (lpOneAlg M E) where
  mul f g := ⟨⟨fun k => FiberTrivialization.equiv (E := E) k
    (ringConvolution (mulToRealSeq f) (mulToRealSeq g) k),
    mul_memℓp_mul f g⟩⟩

/-- The unit transported through the chosen frame: `1_k = θ_k (δ_k)`. -/
@[to_additive (dont_translate := E 𝕜) instOne]
instance instMulOne : One (lpOneAlg M E) where
  one := ⟨⟨fun m => FiberTrivialization.equiv (E := E) m
    (delta (1 : 𝕜) m), one_memℓp_mul⟩⟩

omit [DecidableEq M] in
/-- Fiber value of the product: `(f * g) k = θ_k ((θ⁻¹ f ⋆ θ⁻¹ g)_k)`. -/
@[to_additive (dont_translate := E 𝕜) mul_apply]
theorem mulMul_apply (f g : lpOneAlg M E) (k : M) :
    (f * g) k = FiberTrivialization.equiv (E := E) k
      (ringConvolution (mulToRealSeq f) (mulToRealSeq g) k) := rfl

omit [lpOneMulAlgConvCompat 𝕜 M E] in
/-- Fiber value of the unit: `1 m = θ_m (δ_m)`. -/
@[to_additive (dont_translate := E 𝕜) one_apply]
theorem mulOne_apply (m : M) :
    (1 : lpOneAlg M E) m = FiberTrivialization.equiv (E := E) m (delta (1 : 𝕜) m) := rfl

-- Key rewrites: mulToRealSeq of product/one = convolution/delta of mulToRealSeqs
omit [DecidableEq M] in
@[to_additive (dont_translate := E 𝕜) (attr := simp) toRealSeq_mul_fun]
theorem mulToRealSeq_mul_fun (f g : lpOneAlg M E) :
    mulToRealSeq (f * g) =
      ringConvolution (mulToRealSeq f) (mulToRealSeq g) :=
  funext fun k => LinearEquiv.symm_apply_apply (FiberTrivialization.equiv (E := E) k) _

omit [lpOneMulAlgConvCompat 𝕜 M E] in
@[to_additive (dont_translate := E 𝕜) (attr := simp) toRealSeq_one_fun]
theorem mulToRealSeq_one_fun :
    mulToRealSeq (1 : lpOneAlg M E) = delta (1 : 𝕜) :=
  funext fun m => LinearEquiv.symm_apply_apply (FiberTrivialization.equiv (E := E) m) _

@[to_additive (dont_translate := E 𝕜) instRing]
instance instMulRing : Ring (lpOneAlg M E) where
  mul_assoc f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun]
    exact congr_fun (ringConvolution_assoc _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f g)
      (lpOneMulAlgConvCompat.mulConvSummable g h)
      (lpOneMulAlgConvCompat.tripleMulConvSummable f g h)) k
  one_mul f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [delta_ringConvolution' (1 : 𝕜) _ k, one_mul]
  mul_one f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_one_fun]
    rw [ringConvolution_delta' _ (1 : 𝕜) k, mul_one]
  left_distrib f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_add]
    exact congr_fun (ringConvolution_add _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f g)
      (lpOneMulAlgConvCompat.mulConvSummable f h)) k
  right_distrib f g h := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_add]
    exact congr_fun (add_ringConvolution _ _ _
      (lpOneMulAlgConvCompat.mulConvSummable f h)
      (lpOneMulAlgConvCompat.mulConvSummable g h)) k
  zero_mul f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_zero]
    exact congr_fun (zero_ringConvolution _) k
  mul_zero f := by
    apply ext_mulToRealSeq; ext k
    simp only [mulToRealSeq_mul_fun, mulToRealSeq_zero]
    exact congr_fun (ringConvolution_zero _) k
  natCast n := ⟨⟨fun m => FiberTrivialization.equiv (E := E) m
    (delta ((n : 𝕜)) m), delta_memℓp_mul (n : 𝕜)⟩⟩
  natCast_zero := ext fun m => by
    show FiberTrivialization.equiv (E := E) m
      (delta ((0 : ℕ) : 𝕜) m) = 0
    simp [Nat.cast_zero, delta, Pi.single_apply]
  natCast_succ n := ext fun m => by
    show FiberTrivialization.equiv (E := E) m
        (delta ((↑(n + 1) : 𝕜)) m) =
      FiberTrivialization.equiv (E := E) m (delta ((n : 𝕜)) m) +
      FiberTrivialization.equiv (E := E) m (delta ((1 : 𝕜)) m)
    rw [← FiberTrivialization.equiv_add, Nat.cast_succ]
    congr 1; simp [delta, Pi.single_apply]; split_ifs <;> ring
  intCast n := ⟨⟨fun m => FiberTrivialization.equiv (E := E) m
    (delta ((n : 𝕜)) m), delta_memℓp_mul (n : 𝕜)⟩⟩
  intCast_ofNat n := ext fun m => by
    simp only [Int.cast_natCast]; rfl
  intCast_negSucc n := ext fun m => by
    show FiberTrivialization.equiv (E := E) m
        (delta ((Int.negSucc n : 𝕜)) m) =
      -(FiberTrivialization.equiv (E := E) m
        (delta ((↑(n + 1) : 𝕜)) m))
    simp only [Int.cast_negSucc]
    rw [show delta (-↑(n + 1) : 𝕜) m =
      -(delta ((↑(n + 1) : 𝕜)) m) from by
        simp [delta, Pi.single_apply]; split_ifs <;> ring]
    exact FiberTrivialization.equiv_neg m _

@[to_additive (dont_translate := E 𝕜) instNormedRing]
instance instMulNormedRing : NormedRing (lpOneAlg M E) :=
  fast_instance% { lpOneAlg.instNormedAddCommGroup, lpOneAlg.instMulRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g => norm_mul_le_mul' f g }

end MulRingInstances

end lpOneAlg

namespace lpOneAlg

section ConvolutionEval

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

/-- The convolution product evaluated as a tsum over the second factor's index. -/
@[to_additive (dont_translate := E 𝕜) toRealSeq_mul_tsum]
theorem mulToRealSeq_mul_tsum [Group M] [lpOneMulAlgConvCompat 𝕜 M E]
    (x y : lpOneAlg M E) (k : M) :
    mulToRealSeq (x * y) k
      = ∑' i : M, mulToRealSeq x (k / i) * mulToRealSeq y i := by
  refine (congr_fun (mulToRealSeq_mul_fun x y) k).trans ?_
  show (∑' p : mulFiber k,
      mulToRealSeq x p.1.1 * mulToRealSeq y p.1.2) = _
  exact ((mulFiberEquiv k).tsum_eq
    fun p : mulFiber k =>
      mulToRealSeq x p.1.1 * mulToRealSeq y p.1.2).symm

/-- Convolution against a finitely-supported factor is a finite sum. -/
@[to_additive (dont_translate := E 𝕜) toRealSeq_mul_eq_finsum]
theorem mulToRealSeq_mul_eq_finsum [Group M] [lpOneMulAlgConvCompat 𝕜 M E]
    (x y : lpOneAlg M E) (k : M) (s : Finset M)
    (hy : ∀ i ∉ s, mulToRealSeq y i = 0) :
    mulToRealSeq (x * y) k
      = ∑ i ∈ s, mulToRealSeq x (k / i) * mulToRealSeq y i := by
  rw [mulToRealSeq_mul_tsum]
  exact tsum_eq_sum fun i hi => by rw [hy i hi, mul_zero]

end ConvolutionEval

end lpOneAlg

/-! ### Algebra (any additive index monoid), then CommRing (commutative index)

The two `Algebra.ofModule` laws slide the scalar through the coefficient
field and never rearrange the convolution fibers, so `Algebra` and
`NormedAlgebra` hold over any `[AddMonoid M]`; the scalar slides through because `θ_m⁻¹` is
`𝕜`-linear (`toRealSeq_smul`). Only commutativity of the
product (`f * g = g * f`) flips fibers `(i, j) ↦ (j, i)` and needs
`[AddCommMonoid M]`. Sections kept separate from the Ring instances to avoid
the AddGroup/AddCommGroup diamond. -/

section lpOneAlgAlgebra

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddMonoid M] [DecidableEq M]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]

instance lpOneAlg.instAlgebra : Algebra 𝕜 (lpOneAlg M E) :=
  Algebra.ofModule
    (fun r f g => by
      apply lpOneAlg.ext_toRealSeq
      simp only [lpOneAlg.toRealSeq_mul_fun, lpOneAlg.toRealSeq_smul]
      exact smul_addRingConvolution r _ _
        (lpOneAlgConvCompat.convSummable f g))
    (fun r f g => by
      apply lpOneAlg.ext_toRealSeq
      simp only [lpOneAlg.toRealSeq_mul_fun, lpOneAlg.toRealSeq_smul]
      exact addRingConvolution_smul r _ _
        (lpOneAlgConvCompat.convSummable f g))

instance lpOneAlg.instNormedAlgebra : NormedAlgebra 𝕜 (lpOneAlg M E) where
  norm_smul_le := lpOneAlg.instNormedSpaceBase.norm_smul_le

end lpOneAlgAlgebra

section lpOneAlgCommAlgebra

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddCommMonoid M] [DecidableEq M]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]

instance lpOneAlg.instCommRing : CommRing (lpOneAlg M E) where
  mul_comm f g := by
    apply lpOneAlg.ext_toRealSeq
    simp only [lpOneAlg.toRealSeq_mul_fun]
    exact addRingConvolution_comm _ _

instance lpOneAlg.instNormedCommRing : NormedCommRing (lpOneAlg M E) where
  mul_comm := lpOneAlg.instCommRing.mul_comm

end lpOneAlgCommAlgebra

namespace lpOneAlg

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [AddMonoid M] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
variable [lpOneAlgWeightMul 𝕜 M E] [DecidableEq M]

/-! ### Norm of Identity

The unit `1_m = θ_m (δ_0)_m` needs no convolution witness, so neither does its norm. -/

omit [lpOneAlgWeightMul 𝕜 M E] in
/-- The norm of the unit is the weight at the identity: `‖1‖ = ω_0`. -/
theorem norm_one_eq :
    ‖(1 : lpOneAlg M E)‖ = FiberTrivialization.weight (E := E) (0 : M) := by
  rw [norm_eq_tsum]
  have h : (fun m => ‖(1 : lpOneAlg M E) m‖) =
      fun m => if m = 0 then FiberTrivialization.weight (E := E) (0 : M) else 0 := by
    ext m; by_cases hm : m = 0
    · subst hm
      rw [one_apply, addDelta_zero_eq, ite_eq_left rfl, FiberTrivialization.norm_equiv_apply,
        norm_one, one_mul]
    · rw [ite_eq_right hm, one_apply, addDelta_ne (1 : 𝕜) hm, map_zero, norm_zero]
  rw [h, tsum_ite_eq]

/-- `‖1‖ = 1` from `ω_0 = 1` (the `weight_zero` field of `lpOneAlgWeightMul`, the smallest
existing class carrying it). -/
instance instNormOneClass : NormOneClass (lpOneAlg M E) where
  norm_one := norm_one_eq.trans lpOneAlgWeightMul.weight_zero

end lpOneAlg

end RadiiPolynomial

end
