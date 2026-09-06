import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation

/-!
# The flip-fixed Chebyshev algebra

The physical Chebyshev algebra is the closed subalgebra of the bilateral
coefficient algebra formed by the symmetric sequences `a₋ₖ = aₖ`.  This file
bundles that subalgebra and the isometric restriction of a symmetric sequence
to the bordered, nonnegative-mode carrier.
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
carrier.  On symmetric elements it is an isometry
(`nonnegRestrictCLM_norm_of_isSymmetric`). -/
def nonnegRestrictCLM (ν : PosReal) : l1Chebyshev ν →L[ℝ] l1Bordered ν :=
  LinearMap.mkContinuous
    { toFun := nonnegRestrict
      map_add' := nonnegRestrict_add
      map_smul' := nonnegRestrict_smul }
    2 (fun a => by
      change ‖nonnegRestrict a‖ ≤ 2 * ‖a‖
      rw [← nonnegRestrict_symmetrize a,
        nonnegRestrict_norm_of_isSymmetric _ (symmetrize_isSymmetric a)]
      exact symmetrize_norm_le a)

@[simp] theorem nonnegRestrictCLM_apply (a : l1Chebyshev ν) :
    nonnegRestrictCLM ν a = nonnegRestrict a :=
  rfl

theorem nonnegRestrictCLM_norm_le :
    ‖nonnegRestrictCLM ν‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- On a symmetric sequence, restriction to the nonnegative modes preserves
the norm exactly. -/
theorem nonnegRestrictCLM_norm_of_isSymmetric (a : l1Chebyshev ν)
    (ha : a.IsSymmetric) : ‖nonnegRestrictCLM ν a‖ = ‖a‖ := by
  rw [nonnegRestrictCLM_apply]
  exact nonnegRestrict_norm_of_isSymmetric a ha

end l1Chebyshev

end RadiiPolynomial

end
