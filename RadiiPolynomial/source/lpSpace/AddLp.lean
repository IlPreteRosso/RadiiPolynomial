import RadiiPolynomial.source.lpSpace.DiscreteConvolutionRing
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Generalized ℓ¹ Banach Algebra with Non-Uniform Fibers

`AddLp M E` wraps `lp E 1` with additive convolution as multiplication.
Supports non-uniform fibers via `AddLpRingData`/`AddLpWeightSubMul`.
-/

open scoped BigOperators Topology NNReal ENNReal DiscreteConvolution

noncomputable section

namespace RadiiPolynomial

/-! ### Typeclasses -/

class AddLpRingData (M : Type*) (E : M → Type*)
    [AddGroup M] [∀ m, NormedAddCommGroup (E m)] where
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

class AddLpWeightSubMul (M : Type*) (E : M → Type*)
    [AddGroup M] [∀ m, NormedAddCommGroup (E m)] [AddLpRingData M E] where
  norm_ofReal_mul_le : ∀ (j l : M) (a b : ℝ),
    ‖AddLpRingData.ofReal (E := E) (j + l) (a * b)‖ ≤
    ‖AddLpRingData.ofReal (E := E) j a‖ * ‖AddLpRingData.ofReal (E := E) l b‖
  /-- Weight ≥ 1: ensures `|toRealSeq f m| ≤ ‖f m‖`, needed for summability.
  For ScaledRealZ with ν ≥ 1: `ν^{|k|} ≥ 1`. -/
  norm_ofReal_one_ge : ∀ m, 1 ≤ ‖AddLpRingData.ofReal (E := E) m 1‖

/-! ### AddLp Structure -/

structure AddLp (M : Type*) (E : M → Type*) [∀ m, NormedAddCommGroup (E m)] where
  toLp : lp E 1

namespace AddLp

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

protected def equiv : AddLp M E ≃ lp E 1 where
  toFun := toLp
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instNormedAddCommGroup : NormedAddCommGroup (AddLp M E) :=
  AddLp.equiv.normedAddCommGroup

instance : CoeFun (AddLp M E) (fun _ => ∀ m, E m) where
  coe f := f.toLp

@[simp] theorem toLp_zero : (0 : AddLp M E).toLp = 0 := rfl
@[simp] theorem toLp_add (f g : AddLp M E) : (f + g).toLp = f.toLp + g.toLp := rfl
@[simp] theorem toLp_neg (f : AddLp M E) : (-f).toLp = -f.toLp := rfl
@[simp] theorem toLp_sub (f g : AddLp M E) : (f - g).toLp = f.toLp - g.toLp := rfl

theorem ext {f g : AddLp M E} (h : ∀ m, f m = g m) : f = g := by
  have : f.toLp = g.toLp := lp.ext (funext h)
  cases f; cases g; simpa using this

theorem norm_def (f : AddLp M E) : ‖f‖ = ‖f.toLp‖ := rfl

theorem norm_eq_tsum (f : AddLp M E) : ‖f‖ = ∑' m, ‖f m‖ := by
  rw [norm_def, lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]

theorem summable_norm (f : AddLp M E) : Summable (fun m => ‖f m‖) := by
  have hf := lp.memℓp f.toLp
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)] at hf
  simpa using hf

/-! ### Underlying ℝ Sequence -/

variable [AddGroup M] [AddLpRingData M E]

def toRealSeq (f : AddLp M E) : M → ℝ :=
  fun m => AddLpRingData.toReal m (f m)

theorem norm_eq_abs_toReal_mul_weight (f : AddLp M E) (m : M) :
    ‖f m‖ = |toRealSeq f m| * ‖AddLpRingData.ofReal (E := E) m 1‖ := by
  conv_lhs => rw [show f m = AddLpRingData.ofReal (E := E) m (toRealSeq f m)
    from (AddLpRingData.ofReal_toReal m (f m)).symm]
  exact AddLpRingData.norm_ofReal_eq m _

/-! ### Summability Helpers -/

variable [AddLpWeightSubMul M E]

/-- `|toRealSeq f m| ≤ ‖f m‖` (from weight ≥ 1). -/
theorem abs_toRealSeq_le (f : AddLp M E) (m : M) : |toRealSeq f m| ≤ ‖f m‖ := by
  rw [norm_eq_abs_toReal_mul_weight f m]
  exact le_mul_of_one_le_right (abs_nonneg _) (AddLpWeightSubMul.norm_ofReal_one_ge m)

theorem summable_abs_toRealSeq (f : AddLp M E) :
    Summable (fun m => |toRealSeq f m|) :=
  (summable_norm f).of_nonneg_of_le (fun _ => abs_nonneg _) (abs_toRealSeq_le f)

/-! ### Product Summability -/

variable [DecidableEq M]

theorem summable_abs_toRealSeq_mul (f g : AddLp M E) :
    Summable (fun ab : M × M => |toRealSeq f ab.1| * |toRealSeq g ab.2|) :=
  (summable_abs_toRealSeq f).mul_of_nonneg (summable_abs_toRealSeq g)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)

theorem convSummable (f g : AddLp M E) (x : M) :
    Summable fun ab : DiscreteConvolution.addFiber x =>
      toRealSeq f ab.1.1 * toRealSeq g ab.1.2 :=
  ((summable_abs_toRealSeq_mul f g).subtype _).of_norm_bounded
    fun ⟨⟨j, l⟩, _⟩ => by simp [Real.norm_eq_abs, abs_mul]

/-! ### Mul Membership and Norm -/

/-- Per-index bound: `‖ofReal k (conv k)‖ ≤ ∑' ab : fiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖`.
Uses norm_ofReal_eq + norm_tsum_le_tsum_norm + weight submultiplicativity. -/
private theorem norm_conv_le_fiber (f g : AddLp M E) (k : M) :
    ‖AddLpRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k)‖ ≤
    ∑' ab : DiscreteConvolution.addFiber k, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
  sorry

theorem mul_memℓp (f g : AddLp M E) :
    Memℓp (fun k => AddLpRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hprod : Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
    (summable_norm f).mul_of_nonneg (summable_norm g)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_conv_le_fiber f g)
    (DiscreteConvolution.sigmaAddFiberEquiv.summable_iff.mpr hprod).sigma

theorem one_memℓp :
    Memℓp (fun m => AddLpRingData.ofReal (E := E) m
      (DiscreteConvolution.addDelta (1 : ℝ) m)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact summable_of_ne_finset_zero (s := {0}) (fun b hb => by
    rw [Finset.mem_singleton] at hb
    rw [DiscreteConvolution.addDelta_ne 1 hb, AddLpRingData.ofReal_zero, norm_zero])

theorem norm_mul_le' (f g : AddLp M E) :
    ‖(⟨⟨fun k => AddLpRingData.ofReal (E := E) k
        (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k),
      mul_memℓp f g⟩⟩ : AddLp M E)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum]
  have hprod : Summable (fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖) :=
    (summable_norm f).mul_of_nonneg (summable_norm g)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsigma := DiscreteConvolution.sigmaAddFiberEquiv.summable_iff.mpr hprod
  have hmem : Summable (fun k => ‖AddLpRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k)‖) := by
    simpa using (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mp (mul_memℓp f g)
  refine (Summable.tsum_le_tsum (norm_conv_le_fiber f g) hmem hsigma.sigma).trans (le_of_eq ?_)
  exact (hsigma.tsum_sigma' hsigma.sigma_factor) ▸
    (summable_norm f).tsum_mul_tsum (summable_norm g) hprod ▸
    DiscreteConvolution.sigmaAddFiberEquiv.tsum_eq (fun p => ‖f p.1‖ * ‖g p.2‖)

theorem conv_assoc (f g h : AddLp M E) :
    DiscreteConvolution.addRingConvolution
      (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g)) (toRealSeq h) =
    DiscreteConvolution.addRingConvolution
      (toRealSeq f) (DiscreteConvolution.addRingConvolution (toRealSeq g) (toRealSeq h)) := by
  sorry

-- Mul and One instances
instance instMul : Mul (AddLp M E) where
  mul f g := ⟨⟨fun k => AddLpRingData.ofReal (E := E) k
    (DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) k),
    mul_memℓp f g⟩⟩

instance instOne : One (AddLp M E) where
  one := ⟨⟨fun m => AddLpRingData.ofReal (E := E) m
    (DiscreteConvolution.addDelta (1 : ℝ) m), one_memℓp⟩⟩

-- Extensionality via toRealSeq (avoids fighting with ofReal/toReal at each index)
theorem ext_toRealSeq {f g : AddLp M E} (h : toRealSeq f = toRealSeq g) : f = g := by
  apply ext; intro m
  have := congr_fun h m
  calc f m = AddLpRingData.ofReal (E := E) m (toRealSeq f m) :=
        (AddLpRingData.ofReal_toReal m (f m)).symm
    _ = AddLpRingData.ofReal (E := E) m (toRealSeq g m) := by rw [this]
    _ = g m := AddLpRingData.ofReal_toReal m (g m)

-- Function-level toRealSeq lemmas
theorem toRealSeq_add (f g : AddLp M E) :
    toRealSeq (f + g) = toRealSeq f + toRealSeq g :=
  funext fun m => AddLpRingData.toReal_add m _ _

theorem toRealSeq_zero : toRealSeq (0 : AddLp M E) = 0 :=
  funext fun m => AddLpRingData.toReal_zero m

-- toRealSeq_smul moved to Algebra section (needs NormedSpace ℝ)

-- Key rewrites: toRealSeq of product/one = convolution/delta of toRealSeqs
-- Function-level (for rewriting under addRingConvolution arguments)
@[simp] theorem toRealSeq_mul_fun (f g : AddLp M E) :
    toRealSeq (f * g) =
      DiscreteConvolution.addRingConvolution (toRealSeq f) (toRealSeq g) := by
  ext k; unfold toRealSeq
  show AddLpRingData.toReal k
    (AddLpRingData.ofReal (E := E) k
      (DiscreteConvolution.addRingConvolution
        (fun m => AddLpRingData.toReal m (f m))
        (fun m => AddLpRingData.toReal m (g m)) k)) = _
  rw [AddLpRingData.toReal_ofReal]

@[simp] theorem toRealSeq_one_fun :
    toRealSeq (1 : AddLp M E) = DiscreteConvolution.addDelta 1 := by
  ext m; unfold toRealSeq
  show AddLpRingData.toReal m
    (AddLpRingData.ofReal (E := E) m (DiscreteConvolution.addDelta 1 m)) = _
  rw [AddLpRingData.toReal_ofReal]

-- Helper: toRealSeq of zero is zero
private theorem toRealSeq_zero_fun :
    (fun m => AddLpRingData.toReal m ((0 : AddLp M E) m)) = (0 : M → ℝ) := by
  ext m; exact AddLpRingData.toReal_zero m

-- Helper: toRealSeq of sum
private theorem toRealSeq_add_fun (f g : AddLp M E) :
    (fun m => AddLpRingData.toReal m ((f + g) m)) =
    (fun m => AddLpRingData.toReal m (f m)) +
    (fun m => AddLpRingData.toReal m (g m)) := by
  ext m; simp [Pi.add_apply, AddLpRingData.toReal_add]

-- Ring instance (proofs delegated to addRingConvolution axioms from Phase 1)
instance instRing : Ring (AddLp M E) where
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
      (convSummable f g) (convSummable f h)) k
  right_distrib f g h := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_add]
    exact congr_fun (DiscreteConvolution.add_addRingConvolution _ _ _
      (convSummable f h) (convSummable g h)) k
  zero_mul f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_zero]
    exact congr_fun (DiscreteConvolution.zero_addRingConvolution _) k
  mul_zero f := by
    apply ext_toRealSeq; ext k
    simp only [toRealSeq_mul_fun, toRealSeq_zero]
    exact congr_fun (DiscreteConvolution.addRingConvolution_zero _) k

instance instNormedRing : NormedRing (AddLp M E) :=
  { AddLp.instNormedAddCommGroup, AddLp.instRing with
    dist_eq := fun _ _ => rfl
    norm_mul_le := fun f g => norm_mul_le' f g }

end AddLp

/-! ### CommRing, Algebra (separate section to avoid AddGroup/AddCommGroup diamond) -/

section AddLpCommAlgebra

variable {M : Type*} {E : M → Type*}
variable [∀ m, NormedAddCommGroup (E m)]
variable [AddCommGroup M] [DecidableEq M]
variable [AddLpRingData M E] [AddLpWeightSubMul M E]

instance AddLp.instCommRing : CommRing (AddLp M E) where
  mul_comm f g := by
    apply AddLp.ext_toRealSeq
    simp only [AddLp.toRealSeq_mul_fun]
    exact DiscreteConvolution.addRingConvolution_comm _ _

instance AddLp.instNormedCommRing : NormedCommRing (AddLp M E) where
  mul_comm := AddLp.instCommRing.mul_comm

variable [∀ m, NormedSpace ℝ (E m)]

instance AddLp.instNormedSpace : NormedSpace ℝ (AddLp M E) :=
  { AddLp.equiv.module ℝ with
    norm_smul_le := fun r f => by
      show ‖r • f.toLp‖ ≤ _; exact norm_smul_le r f.toLp }

instance AddLp.instAlgebra : Algebra ℝ (AddLp M E) :=
  Algebra.ofModule
    (fun _ _ _ => by sorry)  -- smul_mul_assoc: needs toRealSeq_smul + smul_addRingConvolution
    (fun _ _ _ => by sorry)  -- mul_smul_comm: needs toRealSeq_smul + addRingConvolution_smul

instance AddLp.instNormedAlgebra : NormedAlgebra ℝ (AddLp M E) where
  norm_smul_le := AddLp.instNormedSpace.norm_smul_le

end AddLpCommAlgebra

namespace AddLp

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]
variable [AddGroup M] [AddLpRingData M E] [AddLpWeightSubMul M E] [DecidableEq M]

/-! ### Norm of Identity -/

theorem norm_one_eq :
    ‖(1 : AddLp M E)‖ = ‖AddLpRingData.ofReal (E := E) (0 : M) (1 : ℝ)‖ := by
  rw [norm_eq_tsum]
  have h : (fun m => ‖(1 : AddLp M E) m‖) =
      fun m => if m = 0 then ‖AddLpRingData.ofReal (E := E) (0 : M) (1 : ℝ)‖ else 0 := by
    ext m; by_cases hm : m = 0
    · subst hm
      change ‖AddLpRingData.ofReal (E := E) 0 (DiscreteConvolution.addDelta 1 0)‖ = _
      rw [DiscreteConvolution.addDelta_zero_eq]; simp
    · rw [if_neg hm]
      show ‖AddLpRingData.ofReal (E := E) m (DiscreteConvolution.addDelta 1 m)‖ = 0
      rw [DiscreteConvolution.addDelta_ne 1 hm, AddLpRingData.ofReal_zero, norm_zero]
  rw [h, tsum_ite_eq]

end AddLp

end RadiiPolynomial

end
