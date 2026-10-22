import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Algebra
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The universal property of the weighted ℓ¹ space

A continuous linear map out of `lpOneAlg M E` is determined by its values on the unit
singles (`continuousLinearMap_ext`). A weight-dominated family `v : M → F` induces
`liftCLM v C hv`, with its atom computation (`liftCLM_single`), application bound and
operator-norm bound. `eq_liftCLM_of_cols` and `exists_eq_liftCLM` recover a map from its
column family.

`liftCLM` builds a map out of the sequence space; `Operators/BlockDiagonal/Lift` instead
lifts defect data into a system sequence space.

For an additive index monoid, `single_mul_single`, `one_eq_single_zero` and `single_pow`
give the monoid computation rules. `mulLeftCLM` and `mulRightCLM` bundle one-sided
multiplication. A weight-dominated unital multiplicative family induces `liftAlgHom`,
with `liftAlgHom_single` and `norm_liftAlgHom_apply_le`. `continuousAlgHom_ext`,
`eq_liftAlgHom_of_atoms` and `exists_eq_liftAlgHom` give the corresponding determination
and reconstruction contracts. Their target-space and boundedness hypotheses are explicit
in the declarations.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

open _root_.DiscreteConvolution RadiiPolynomial.DiscreteConvolution

namespace lpOneAlg

section Ext

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- **Determination on the atoms.** Two continuous linear maps out of a
weighted ℓ¹ space agreeing on the unit singles are equal — the uniqueness
half of the universal property. -/
theorem continuousLinearMap_ext ⦃ψ₁ ψ₂ : lpOneAlg M E →L[𝕜] B⦄
    (h : ∀ m, ψ₁ (single m 1) = ψ₂ (single m 1)) : ψ₁ = ψ₂ := by
  ext f
  have h₁ := hasSum_single_mapCLM ψ₁ f
  have h₂ := hasSum_single_mapCLM ψ₂ f
  have hfun : (fun m => ψ₁ (single m (toRealSeq f m)))
      = fun m => ψ₂ (single m (toRealSeq f m)) := by
    funext m
    rw [single_smul, map_smul, map_smul, h m]
  rw [hfun] at h₁
  exact h₁.unique h₂


end Ext

section Lift

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [DecidableEq M] [CompleteSpace F] in
private theorem norm_smul_col_le (v : M → F) {C : ℝ}
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) (m : M) :
    ‖toRealSeq h m • v m‖ ≤ C * ‖h m‖ := by
  rw [norm_smul]
  refine (mul_le_mul_of_nonneg_left (hv m) (norm_nonneg _)).trans (le_of_eq ?_)
  rw [norm_eq_abs_toReal_mul_weight h m]
  ring

omit [DecidableEq M] in
/-- The lift-induced series converges absolutely. -/
theorem liftCLM_summable (v : M → F) {C : ℝ}
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) :
    Summable (fun m => toRealSeq h m • v m) :=
  Summable.of_norm (((summable_norm h).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_smul_col_le v hv h))

omit [DecidableEq M] [CompleteSpace F] in
private theorem norm_tsum_liftFun_le (v : M → F) {C : ℝ}
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) :
    ‖∑' m, toRealSeq h m • v m‖ ≤ C * ‖h‖ := by
  have hmaj : Summable (fun m => ‖toRealSeq h m • v m‖) :=
    ((summable_norm h).mul_left C).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_smul_col_le v hv h)
  refine (norm_tsum_le_tsum_norm hmaj).trans ?_
  refine (hmaj.tsum_le_tsum (norm_smul_col_le v hv h)
    ((summable_norm h).mul_left C)).trans (le_of_eq ?_)
  rw [norm_eq_tsum]
  exact tsum_mul_left

/-- **The lift.** A column family `v : M → F` dominated by the weights,
`‖v m‖ ≤ C · ω_m`, induces the continuous linear map
`h ↦ ∑' m, toRealSeq h m • v m` out of the weighted ℓ¹ space, of norm at
most `C` (`norm_liftCLM_le`), sending each single to its column
(`liftCLM_single`). This builds maps OUT of the sequence space from column
data — not to be confused with `Operators/BlockDiagonal/Lift`, which lifts
ℕ-indexed data INTO a system space. -/
def liftCLM (v : M → F) (C : ℝ)
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m) :
    lpOneAlg M E →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun h => ∑' m, toRealSeq h m • v m
      map_add' := fun f g => by
        have hf := liftCLM_summable v hv f
        have hg := liftCLM_summable v hv g
        have hfun : (fun m => toRealSeq (f + g) m • v m)
            = fun m => toRealSeq f m • v m + toRealSeq g m • v m := by
          funext m
          rw [congr_fun (toRealSeq_add f g) m, Pi.add_apply, add_smul]
        rw [hfun]
        exact hf.tsum_add hg
      map_smul' := fun r f => by
        have hfun : (fun m => toRealSeq (r • f) m • v m)
            = fun m => r • (toRealSeq f m • v m) := by
          funext m
          rw [congr_fun (toRealSeq_smul r f) m, Pi.smul_apply, smul_eq_mul,
            mul_smul]
        rw [RingHom.id_apply, hfun]
        exact ((liftCLM_summable v hv f).tsum_const_smul r).symm ▸ rfl }
    C (fun h => norm_tsum_liftFun_le v hv h)

omit [DecidableEq M] in
theorem liftCLM_apply (v : M → F) (C : ℝ)
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) :
    liftCLM v C hv h = ∑' m, toRealSeq h m • v m := rfl

@[simp] theorem liftCLM_single (v : M → F) (C : ℝ)
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (m : M) (x : 𝕜) :
    liftCLM v C hv (single m x) = x • v m := by
  show (∑' k, toRealSeq (single (E := E) m x) k • v k) = x • v m
  rw [tsum_eq_single m]
  · rw [toRealSeq_single, ite_eq_left rfl]
  · intro k hk
    rw [toRealSeq_single, ite_eq_right hk, zero_smul]

omit [DecidableEq M] in
/-- Pointwise norm bound for the lift, valid for every `C` (no sign
hypothesis). -/
theorem norm_liftCLM_apply_le (v : M → F) (C : ℝ)
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (h : lpOneAlg M E) :
    ‖liftCLM v C hv h‖ ≤ C * ‖h‖ :=
  norm_tsum_liftFun_le v hv h

/-- **Every continuous linear map out of the space is a lift** (completeness
of the API): a map whose columns satisfy the weighted bound is the lift of
its column family. Converse pairing of `norm_le_of_cols`. -/
theorem eq_liftCLM_of_cols (W : lpOneAlg M E →L[𝕜] F) {C : ℝ}
    (hv : ∀ m, ‖W (single m 1)‖
      ≤ C * FiberTrivialization.weight (E := E) m) :
    liftCLM (fun m => W (single m 1)) C hv = W :=
  continuousLinearMap_ext fun m => by rw [liftCLM_single, one_smul]

end Lift

section LiftOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [DecidableEq M] in
theorem norm_liftCLM_le (v : M → F) {C : ℝ}
    (hv : ∀ m, ‖v m‖ ≤ C * FiberTrivialization.weight (E := E) m)
    (hC : 0 ≤ C) :
    ‖liftCLM v C hv‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_liftCLM_apply_le v C hv)

/-- Every continuous linear map out of the space is the lift of its column
family at the operator norm. -/
theorem exists_eq_liftCLM (W : lpOneAlg M E →L[𝕜] F) :
    ∃ hv : ∀ m, ‖W (single m 1)‖
      ≤ ‖W‖ * FiberTrivialization.weight (E := E) m,
      liftCLM (fun m => W (single m 1)) ‖W‖ hv = W := by
  have hv : ∀ m, ‖W (single m 1)‖
      ≤ ‖W‖ * FiberTrivialization.weight (E := E) m := fun m => by
    have h := W.le_opNorm (single m 1)
    rwa [norm_single, norm_one, one_mul] at h
  exact ⟨hv, eq_liftCLM_of_cols W hv⟩

end LiftOpNorm

/-! ### Singles multiply

The multiplicative half of the universal property. Over an additive index
monoid the unit singles form a copy of the monoid inside the algebra:
`single i 1 * single j 1 = single (i + j) 1` and `1 = single 0 1`. -/

section SingleMul

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} [AddMonoid M] {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable [lpOneAlgConvCompat 𝕜 M E]

/-- Singles multiply by convolution of point masses:
`single i x * single j y = single (i+j) (x*y)`. -/
theorem single_mul_single (i j : M) (x y : 𝕜) :
    (single (E := E) i x) * single j y = single (i + j) (x * y) :=
  ext_toRealSeq <| by
    rw [toRealSeq_mul_fun, toRealSeq_single_eq_piSingle, toRealSeq_single_eq_piSingle,
      toRealSeq_single_eq_piSingle, single_addRingConvolution_single]

omit [lpOneAlgConvCompat 𝕜 M E] in
/-- The multiplicative unit is the single at index `0`. -/
theorem one_eq_single_zero : (1 : lpOneAlg M E) = single 0 (1 : 𝕜) := by
  apply ext_toRealSeq
  funext k
  rw [toRealSeq_single, congr_fun (toRealSeq_one_fun (E := E) (𝕜 := 𝕜)) k]
  simp [addDelta, Pi.single_apply]

/-- Powers of a unit single walk along the index monoid:
`(single a 1)ⁿ = single (n • a) 1`. -/
theorem single_pow (a : M) (n : ℕ) :
    (single (E := E) a (1 : 𝕜)) ^ n = single (n • a) 1 := by
  induction n with
  | zero => rw [pow_zero, zero_smul, one_eq_single_zero]
  | succ k ih => rw [pow_succ, ih, single_mul_single, one_mul, succ_nsmul]

end SingleMul

/-! ### One-sided multiplication operators -/

section MulCLM

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} [AddMonoid M] {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable [lpOneAlgConvCompat 𝕜 M E]

/-- Right multiplication `f ↦ f * g` as a continuous linear map (pointwise
bound `‖f * g‖ ≤ ‖g‖ * ‖f‖`). Built by `mkContinuous` rather than
`ContinuousLinearMap.mul`, which needs a nontrivially normed field. -/
def mulRightCLM (g : lpOneAlg M E) : lpOneAlg M E →L[𝕜] lpOneAlg M E :=
  LinearMap.mkContinuous
    { toFun := fun f => f * g
      map_add' := fun f₁ f₂ => add_mul f₁ f₂ g
      map_smul' := fun r f => smul_mul_assoc r f g }
    ‖g‖ (fun f => by rw [mul_comm ‖g‖ ‖f‖]; exact norm_mul_le f g)

@[simp] theorem mulRightCLM_apply (g f : lpOneAlg M E) :
    mulRightCLM (𝕜 := 𝕜) g f = f * g := rfl

/-- Left multiplication `g ↦ f * g` as a continuous linear map (pointwise
bound `‖f * g‖ ≤ ‖f‖ * ‖g‖`). -/
def mulLeftCLM (f : lpOneAlg M E) : lpOneAlg M E →L[𝕜] lpOneAlg M E :=
  LinearMap.mkContinuous
    { toFun := fun g => f * g
      map_add' := fun g₁ g₂ => mul_add f g₁ g₂
      map_smul' := fun r g => mul_smul_comm r f g }
    ‖f‖ (fun g => norm_mul_le f g)

@[simp] theorem mulLeftCLM_apply (f g : lpOneAlg M E) :
    mulLeftCLM (𝕜 := 𝕜) f g = f * g := rfl

end MulCLM

/-! ### The lift is multiplicative

When the column family `b : M → B` into a Banach algebra is a monoid map
(`b 0 = 1`, `b (m + n) = b m * b n`), the linear lift `liftCLM b C hb` is
unital and multiplicative. Multiplicativity is proved by consuming the
determination principle `continuousLinearMap_ext` twice, on the two readings
of `f * g` through one-sided multiplication operators — no rearrangement of
double series. -/

section LiftMul

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} [AddMonoid M] {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable [lpOneAlgConvCompat 𝕜 M E]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- Right multiplication by a fixed element of the target algebra as a
continuous linear map (avoids `ContinuousLinearMap.mul`, which needs a
nontrivially normed field). -/
private def mulRightTarget (c : B) : B →L[𝕜] B :=
  LinearMap.mkContinuous
    { toFun := fun y => y * c
      map_add' := fun y z => add_mul y z c
      map_smul' := fun r y => smul_mul_assoc r y c }
    ‖c‖ (fun y => by rw [mul_comm ‖c‖ ‖y‖]; exact norm_mul_le y c)

omit [CompleteSpace B] in
private theorem mulRightTarget_apply (c y : B) :
    mulRightTarget (𝕜 := 𝕜) c y = y * c := rfl

/-- Left multiplication by a fixed element of the target algebra as a
continuous linear map. -/
private def mulLeftTarget (c : B) : B →L[𝕜] B :=
  LinearMap.mkContinuous
    { toFun := fun y => c * y
      map_add' := fun y z => mul_add c y z
      map_smul' := fun r y => mul_smul_comm r c y }
    ‖c‖ (fun y => norm_mul_le c y)

omit [CompleteSpace B] in
private theorem mulLeftTarget_apply (c y : B) :
    mulLeftTarget (𝕜 := 𝕜) c y = c * y := rfl

variable (b : M → B) (C : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ C * FiberTrivialization.weight (E := E) m)

omit [lpOneAlgConvCompat 𝕜 M E] in
/-- The lift of a family with `b 0 = 1` is unital. -/
theorem liftCLM_one (hb0 : b 0 = 1) : liftCLM b C hb 1 = 1 := by
  rw [one_eq_single_zero, liftCLM_single, hb0, one_smul]

/-- **The lift of a monoid map is multiplicative.** Proved by consuming the
determination principle (`continuousLinearMap_ext`) twice. -/
theorem liftCLM_mul (hbmul : ∀ m n, b (m + n) = b m * b n) (f g : lpOneAlg M E) :
    liftCLM b C hb (f * g) = liftCLM b C hb f * liftCLM b C hb g := by
  have step1 : ∀ n : M, (liftCLM b C hb).comp (mulRightCLM (single n 1))
      = (mulRightTarget (b n)).comp (liftCLM b C hb) := by
    intro n
    apply continuousLinearMap_ext
    intro m
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      mulRightCLM_apply, single_mul_single, one_mul, liftCLM_single, liftCLM_single,
      one_smul, one_smul, mulRightTarget_apply, hbmul]
  have step2 : (liftCLM b C hb).comp (mulLeftCLM f)
      = (mulLeftTarget (liftCLM b C hb f)).comp (liftCLM b C hb) := by
    apply continuousLinearMap_ext
    intro n
    have h1 := DFunLike.congr_fun (step1 n) f
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      mulRightCLM_apply, mulRightTarget_apply] at h1
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      mulLeftCLM_apply, mulLeftTarget_apply, h1, liftCLM_single, one_smul]
  have h2 := DFunLike.congr_fun step2 g
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    mulLeftCLM_apply, mulLeftTarget_apply] at h2
  exact h2

/-- **The algebra lift** (introduction face). A weight-dominated monoid map
`b : M → B` into a Banach algebra induces the continuous algebra
homomorphism `h ↦ ∑' m, toRealSeq h m • b m` out of the weighted ℓ¹ algebra;
it agrees pointwise with `liftCLM b C hb` (`liftAlgHom_apply`, by `rfl`), so every bound
on `liftCLM` transfers. -/
def liftAlgHom (hb0 : b 0 = 1) (hbmul : ∀ m n, b (m + n) = b m * b n) :
    lpOneAlg M E →A[𝕜] B where
  toAlgHom := AlgHom.ofLinearMap (liftCLM b C hb).toLinearMap
    (liftCLM_one b C hb hb0) (liftCLM_mul b C hb hbmul)
  cont := (liftCLM b C hb).continuous

variable (hb0 : b 0 = 1) (hbmul : ∀ m n, b (m + n) = b m * b n)

theorem liftAlgHom_apply (h : lpOneAlg M E) :
    liftAlgHom b C hb hb0 hbmul h = liftCLM b C hb h := rfl


/-- Computation face: the algebra lift sends the unit single at `m` to `b m`. -/
@[simp] theorem liftAlgHom_single (m : M) :
    liftAlgHom b C hb hb0 hbmul (single m 1) = b m := by
  rw [liftAlgHom_apply, liftCLM_single, one_smul]

/-- Pointwise norm bound for the algebra lift, valid for every `C`. -/
theorem norm_liftAlgHom_apply_le (h : lpOneAlg M E) :
    ‖liftAlgHom b C hb hb0 hbmul h‖ ≤ C * ‖h‖ :=
  norm_liftCLM_apply_le b C hb h

end LiftMul

/-! ### Uniqueness and completeness for continuous algebra homomorphisms -/

section AlgHomExt

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} [AddMonoid M] {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable [lpOneAlgConvCompat 𝕜 M E]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- **Determination on the atoms** (uniqueness face): two continuous algebra
homomorphisms out of the weighted ℓ¹ algebra agreeing on the unit singles are
equal. Not an `@[ext]` lemma (agreement on singles is a proof obligation to
choose, not a default). -/
theorem continuousAlgHom_ext ⦃φ ψ : lpOneAlg M E →A[𝕜] B⦄
    (h : ∀ m, φ (single m 1) = ψ (single m 1)) : φ = ψ := by
  have hL : φ.toContinuousLinearMap = ψ.toContinuousLinearMap :=
    continuousLinearMap_ext fun m => h m
  exact ContinuousAlgHom.ext fun a => DFunLike.congr_fun hL a

/-- The atom family of a continuous algebra homomorphism is unital. -/
theorem continuousAlgHom_single_zero (φ : lpOneAlg M E →A[𝕜] B) :
    φ (single 0 (1 : 𝕜)) = 1 := by
  rw [← one_eq_single_zero, map_one]

/-- The atom family of a continuous algebra homomorphism is multiplicative. -/
theorem continuousAlgHom_single_add (φ : lpOneAlg M E →A[𝕜] B) (m n : M) :
    φ (single (m + n) (1 : 𝕜)) = φ (single m 1) * φ (single n 1) := by
  rw [← map_mul, single_mul_single, one_mul]

variable [CompleteSpace B]

/-- **Every continuous algebra homomorphism out of the algebra is an algebra
lift** (completeness face): a homomorphism whose atoms satisfy the weighted
bound is the lift of its atom family. -/
theorem eq_liftAlgHom_of_atoms (φ : lpOneAlg M E →A[𝕜] B) {C : ℝ}
    (hb : ∀ m, ‖φ (single m 1)‖
      ≤ C * FiberTrivialization.weight (E := E) m) :
    liftAlgHom (fun m => φ (single m 1)) C hb
      (continuousAlgHom_single_zero φ) (continuousAlgHom_single_add φ) = φ :=
  continuousAlgHom_ext fun m => by rw [liftAlgHom_single]

end AlgHomExt

section AlgHomOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {M : Type*} [AddMonoid M] {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [DecidableEq M]
variable [lpOneAlgConvCompat 𝕜 M E]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- Every continuous algebra homomorphism out of the algebra is the algebra
lift of its atom family at the operator norm of its underlying continuous
linear map (`ContinuousAlgHom` carries no norm of its own). -/
theorem exists_eq_liftAlgHom (φ : lpOneAlg M E →A[𝕜] B) :
    ∃ hb : ∀ m, ‖φ (single m 1)‖
      ≤ ‖φ.toContinuousLinearMap‖ * FiberTrivialization.weight (E := E) m,
      liftAlgHom (fun m => φ (single m 1)) ‖φ.toContinuousLinearMap‖ hb
        (continuousAlgHom_single_zero φ) (continuousAlgHom_single_add φ) = φ := by
  obtain ⟨hb, -⟩ := exists_eq_liftCLM φ.toContinuousLinearMap
  exact ⟨hb, eq_liftAlgHom_of_atoms φ hb⟩

end AlgHomOpNorm

end lpOneAlg

end RadiiPolynomial

end
