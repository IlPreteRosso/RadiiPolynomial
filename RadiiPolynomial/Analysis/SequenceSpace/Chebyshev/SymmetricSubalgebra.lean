import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered

/-!
# The flip-fixed Chebyshev algebra

The physical Chebyshev algebra is the closed subalgebra of the bilateral
coefficient algebra formed by the symmetric sequences `a₋ₖ = aₖ`.  This file
bundles that subalgebra and the isometric restriction of a symmetric sequence
to the bordered, nonnegative-mode carrier: `symmetricRetract` is the continuous
linear retraction of the bilateral algebra onto the subalgebra (not an algebra
homomorphism), and `physicalBorderedEquiv` is the linear isometry equivalence
between the symmetric elements and the bordered carrier.
-/

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

variable {ν : PosReal}

section Algebra

variable [Fact (1 ≤ (ν : ℝ))]

/-- The physical Chebyshev algebra: the flip-fixed elements of the bilateral
weighted convolution algebra. -/
def symmetricSubalgebra (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    Subalgebra ℝ (l1Chebyshev ν) where
  carrier := {a | a.IsSymmetric}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact isSymmetric_one.smul r

@[simp] theorem mem_symmetricSubalgebra {a : l1Chebyshev ν} :
    a ∈ symmetricSubalgebra ν ↔ a.IsSymmetric :=
  Iff.rfl

/-- The flip-fixed algebra is closed in the bilateral Banach algebra. -/
theorem isClosed_symmetricSubalgebra (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    IsClosed ((symmetricSubalgebra ν : Set (l1Chebyshev ν))) := by
  have hset : (symmetricSubalgebra ν : Set (l1Chebyshev ν)) =
      {a : l1Chebyshev ν | symmetrize_CLM a = a} := by
    ext a
    change a.IsSymmetric ↔ symmetrize_CLM a = a
    constructor
    · exact symmetrize_eq_self_of_isSymmetric a
    · intro ha
      rw [← ha]
      exact symmetrize_isSymmetric a
  rw [hset]
  exact isClosed_eq symmetrize_CLM.continuous continuous_id

/-- The flip-fixed algebra inherits completeness from the bilateral Banach
algebra. -/
instance symmetricSubalgebra.instCompleteSpace :
    CompleteSpace (symmetricSubalgebra ν) :=
  (isClosed_symmetricSubalgebra ν).completeSpace_coe

/-- The flip-fixed algebra has a unit of norm one: its unit is the unit of the bilateral algebra.
(Mathlib's `SubringClass.toNormOneClass` is stated for the `SubringClass` norm structure, which
agrees with `Subalgebra.normedRing` here only after unfolding, so instance search does not use it.) -/
instance symmetricSubalgebra.instNormOneClass :
    NormOneClass (symmetricSubalgebra ν) :=
  ⟨by
    change ‖((1 : symmetricSubalgebra ν) : l1Chebyshev ν)‖ = 1
    rw [OneMemClass.coe_one, norm_one]⟩

/-- **Symmetrization onto the physical algebra**: `symmetrize_CLM` with codomain
`symmetricSubalgebra ν`. A continuous linear retraction of the inclusion (`symmetricRetract_coe`),
not an algebra homomorphism: it sends every strictly negative single to `0`
(`symmetrize_single_negSucc`). -/
def symmetricRetract (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev ν →L[ℝ] symmetricSubalgebra ν :=
  (symmetrize_CLM (ν := ν)).codRestrict (symmetricSubalgebra ν).toSubmodule
    fun a => symmetrize_isSymmetric a

@[simp] theorem coe_symmetricRetract (a : l1Chebyshev ν) :
    (symmetricRetract ν a : l1Chebyshev ν) = symmetrize a :=
  rfl

/-- The retraction law: `symmetricRetract` restricts to the identity on the physical algebra. -/
@[simp] theorem symmetricRetract_coe (a : symmetricSubalgebra ν) :
    symmetricRetract ν (a : l1Chebyshev ν) = a :=
  Subtype.ext (symmetrize_eq_self_of_isSymmetric _ a.property)

theorem norm_symmetricRetract_le : ‖symmetricRetract ν‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two fun a => by
    change ‖symmetrize a‖ ≤ 2 * ‖a‖
    exact symmetrize_norm_le a

private def symmetricEvalAlgHom (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (t : ℝ) (ht : |t| ≤ 1) : symmetricSubalgebra ν →ₐ[ℝ] ℝ where
  toFun a := eval (a : l1Chebyshev ν) t
  map_one' := eval_one t
  map_mul' a b := eval_mul_of_isSymmetric
    (a : l1Chebyshev ν) (b : l1Chebyshev ν) a.2 b.2 ht
  map_zero' := by
    simpa using eval_smul 0 (1 : l1Chebyshev ν) t
  map_add' a b := by
    simpa using eval_add (a : l1Chebyshev ν) (b : l1Chebyshev ν) ht
  commutes' r := by
    change eval (r • (1 : l1Chebyshev ν)) t = r
    rw [eval_smul, eval_one]
    ring

/-- Evaluation at a physical point `t ∈ [-1, 1]` as a character of the
flip-fixed Chebyshev algebra. -/
def symmetricEvalCharacter (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (t : ℝ) (ht : |t| ≤ 1) : symmetricSubalgebra ν →A[ℝ] ℝ where
  toAlgHom := symmetricEvalAlgHom ν t ht
  cont := AddMonoidHomClass.continuous_of_bound
    (symmetricEvalAlgHom ν t ht) 1 (fun a => by
      rw [one_mul, Real.norm_eq_abs]
      exact abs_eval_le_norm_of_isSymmetric (a : l1Chebyshev ν) a.2 ht)

@[simp] theorem symmetricEvalCharacter_apply (t : ℝ) (ht : |t| ≤ 1)
    (a : symmetricSubalgebra ν) :
    symmetricEvalCharacter ν t ht a = eval (a : l1Chebyshev ν) t :=
  rfl

end Algebra

/-! ### Restriction to nonnegative modes -/

lemma nonnegRestrict_add (a b : l1Chebyshev ν) :
    nonnegRestrict (a + b) = nonnegRestrict a + nonnegRestrict b := by
  apply lpOneAlg.ext_toRealSeq
  funext n
  simp only [nonnegRestrict_toSeq, lpOneAlg.toRealSeq_add, Pi.add_apply]

lemma nonnegRestrict_smul (r : ℝ) (a : l1Chebyshev ν) :
    nonnegRestrict (r • a) = r • nonnegRestrict a := by
  apply lpOneAlg.ext_toRealSeq
  funext n
  simp only [nonnegRestrict_toSeq, lpOneAlg.toRealSeq_smul, Pi.smul_apply]

/-- Restriction to the nonnegative modes is `2`-bounded on the full bilateral
carrier (`nonnegRestrict_norm_le`).  On symmetric elements it is an isometry
(`nonnegRestrictCLM_norm_of_isSymmetric`). -/
def nonnegRestrictCLM (ν : PosReal) : l1Chebyshev ν →L[ℝ] l1Bordered ν :=
  LinearMap.mkContinuous
    { toFun := nonnegRestrict
      map_add' := nonnegRestrict_add
      map_smul' := nonnegRestrict_smul }
    2 (fun a => by
      change ‖nonnegRestrict a‖ ≤ 2 * ‖a‖
      exact nonnegRestrict_norm_le a)

@[simp] theorem nonnegRestrictCLM_apply (a : l1Chebyshev ν) :
    nonnegRestrictCLM ν a = nonnegRestrict a :=
  rfl

theorem nonnegRestrictCLM_norm_le :
    ‖nonnegRestrictCLM ν‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- On a symmetric sequence, restriction to the nonnegative modes preserves
the norm exactly, for every `ν` (for `1 ≤ ν` this is `norm_map` of `physicalBorderedEquiv`). -/
theorem nonnegRestrictCLM_norm_of_isSymmetric (a : l1Chebyshev ν)
    (ha : a.IsSymmetric) : ‖nonnegRestrictCLM ν a‖ = ‖a‖ := by
  rw [nonnegRestrictCLM_apply]
  exact nonnegRestrict_norm_of_isSymmetric a ha

/-! ### The physical algebra is isometrically the bordered carrier -/

private theorem borderedEmbed_memℓp (b : l1Bordered ν) :
    Memℓp (fun k : ℤ => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (if 0 ≤ k then lpOneAlg.toRealSeq b k.toNat else 0)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (lpOneAlg.summable_norm b)
    rw [ScaledRealZ.norm_equiv_apply, ite_eq_left (by omega), Int.toNat_natCast,
      Int.natAbs_natCast, lpOneAlg.norm_eq_abs_toReal_mul_weight b n,
      WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν n) (abs_nonneg _)
  · refine summable_zero.congr fun n => ?_
    rw [ScaledRealZ.norm_equiv_apply, ite_eq_right (by omega), abs_zero, zero_mul]

/-- The bordered coefficients placed on the nonnegative bilateral modes. -/
private def borderedEmbed (b : l1Bordered ν) : l1Chebyshev ν :=
  ⟨⟨fun k => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (if 0 ≤ k then lpOneAlg.toRealSeq b k.toNat else 0), borderedEmbed_memℓp b⟩⟩

private theorem borderedEmbed_toSeq (b : l1Bordered ν) (k : ℤ) :
    toSeq (borderedEmbed b) k = if 0 ≤ k then lpOneAlg.toRealSeq b k.toNat else 0 :=
  FiberTrivialization.equiv_symm_apply_equiv k _

private theorem nonnegRestrict_borderedEmbed (b : l1Bordered ν) :
    nonnegRestrict (borderedEmbed b) = b := by
  apply lpOneAlg.ext_toRealSeq; funext n
  rw [nonnegRestrict_toSeq]
  change toSeq (borderedEmbed b) (n : ℤ) = _
  rw [borderedEmbed_toSeq, ite_eq_left (by omega), Int.toNat_natCast]

section PhysicalBordered

variable [Fact (1 ≤ (ν : ℝ))]

/-- **The physical algebra is isometrically the bordered carrier**: a linear isometry
equivalence `symmetricSubalgebra ν ≃ₗᵢ[ℝ] l1Bordered ν` with forward map `nonnegRestrict` and
inverse `b ↦ symmetrize b̃`, where `b̃` places `b` on the nonnegative bilateral modes. It is not
multiplicative: the ring carried by `l1Bordered ν` is the plain ℕ-Cauchy product, not the
physical Chebyshev product. -/
def physicalBorderedEquiv : symmetricSubalgebra ν ≃ₗᵢ[ℝ] l1Bordered ν where
  toFun a := nonnegRestrict (a : l1Chebyshev ν)
  invFun b := ⟨symmetrize (borderedEmbed b), symmetrize_isSymmetric _⟩
  map_add' a b := nonnegRestrict_add _ _
  map_smul' r a := nonnegRestrict_smul r _
  left_inv a := by
    apply Subtype.ext
    change symmetrize (borderedEmbed (nonnegRestrict (a : l1Chebyshev ν))) = a
    conv_rhs => rw [← symmetrize_eq_self_of_isSymmetric _ a.2]
    apply lpOneAlg.ext_toRealSeq; funext k
    change toSeq _ k = toSeq _ k
    rw [symmetrize_toSeq, symmetrize_toSeq, borderedEmbed_toSeq, ite_eq_left (by omega),
      Int.toNat_natCast, nonnegRestrict_toSeq]
    rfl
  right_inv b := by
    change nonnegRestrict (symmetrize (borderedEmbed b)) = b
    rw [nonnegRestrict_symmetrize, nonnegRestrict_borderedEmbed]
  norm_map' a := nonnegRestrict_norm_of_isSymmetric _ a.2

@[simp] theorem physicalBorderedEquiv_apply (a : symmetricSubalgebra ν) :
    physicalBorderedEquiv a = nonnegRestrict (a : l1Chebyshev ν) :=
  rfl

end PhysicalBordered

end l1Chebyshev

end RadiiPolynomial

end
