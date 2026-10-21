import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered

/-!
# The flip-fixed Chebyshev algebra

`symmetricSubalgebra ν` is the subalgebra of symmetric bilateral sequences.
This shipped module retains the continuous linear symmetrization `symmetricRetract`
and the bundled nonnegative-mode restriction `nonnegRestrictCLM`.
The retraction laws, symmetric-storage norm comparisons and physical/bordered linear
isometry equivalence belong to `B5RecordSymmetricStorageBordered` and are not exports
of this shipped owner.
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




/-- The flip-fixed algebra has a unit of norm one: its unit is the unit of the bilateral algebra.
(Mathlib's `SubringClass.toNormOneClass` is stated for the `SubringClass` norm structure, which
agrees with `Subalgebra.normedRing` here only after unfolding, so instance search does not use it.) -/
instance symmetricSubalgebra.instNormOneClass :
    NormOneClass (symmetricSubalgebra ν) :=
  ⟨by
    change ‖((1 : symmetricSubalgebra ν) : l1Chebyshev ν)‖ = 1
    rw [OneMemClass.coe_one, norm_one]⟩

/-- **Symmetrization onto the physical algebra**: `symmetrize_CLM` with codomain
`symmetricSubalgebra ν`. This is a continuous linear map, not an algebra homomorphism.
Its additional retraction and atom laws belong to `B5RecordSymmetricStorageBordered`. -/
def symmetricRetract (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev ν →L[ℝ] symmetricSubalgebra ν :=
  (symmetrize_CLM (ν := ν)).codRestrict (symmetricSubalgebra ν).toSubmodule
    fun a => symmetrize_isSymmetric a




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
carrier (`nonnegRestrict_norm_le`). The additional symmetric-storage isometry
comparison is recovered in `B5RecordSymmetricStorageBordered`. -/
def nonnegRestrictCLM (ν : PosReal) : l1Chebyshev ν →L[ℝ] l1Bordered ν :=
  LinearMap.mkContinuous
    { toFun := nonnegRestrict
      map_add' := nonnegRestrict_add
      map_smul' := nonnegRestrict_smul }
    2 (fun a => by
      change ‖nonnegRestrict a‖ ≤ 2 * ‖a‖
      exact nonnegRestrict_norm_le a)




/-! ### The physical algebra is isometrically the bordered carrier -/





section PhysicalBordered

variable [Fact (1 ≤ (ν : ℝ))]



end PhysicalBordered

end l1Chebyshev

end RadiiPolynomial

end
