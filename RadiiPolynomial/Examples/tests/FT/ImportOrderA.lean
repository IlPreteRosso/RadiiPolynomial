import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.FiberTrivialization
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.ScalarInstances
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Carrier
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal

/-! # Frame re-index probe: station modules imported bottom-up

Unit E1, gate "both import orders". -/

noncomputable section

namespace RadiiPolynomial.Tests.FTImportOrderA

open RadiiPolynomial

/-- The Beurling weight `2ⁿ`. -/
def pow2 : ℕ → ℝ := fun n => 2 ^ n

instance : SubMulWeightBase pow2 where
  weight_pos _ := by unfold pow2; positivity
  submul m n := by unfold pow2; rw [pow_add]

instance : NormalizedWeight pow2 where
  weight_zero := by simp [pow2]

/-- The Beurling weight `2^|k|` on `ℤ`. -/
def pow2Z : ℤ → ℝ := fun k => 2 ^ k.natAbs

instance : SubMulWeightBase pow2Z where
  weight_pos _ := by unfold pow2Z; positivity
  submul m n := by
    unfold pow2Z
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (Int.natAbs_add_le m n)

-- One frame instance path.
example : (inferInstance : FiberTrivialization ℝ ℕ (WeightedScalar ℝ pow2)) =
    WeightedScalar.instFiberTrivialization := rfl
-- These proof equalities check compatibility only: proof irrelevance does not identify a producer.
-- The selected definitions and prints below provide the inspectable producer expressions.
example : (inferInstance : lpOneAlgConvCompat ℝ ℕ (WeightedScalar ℝ pow2)) =
    lpOneAlg.instConvCompatOfAntidiag := rfl
example : (inferInstance : lpOneAlgConvCompat ℝ ℤ (WeightedScalar ℝ pow2Z)) =
    lpOneAlg.instConvCompatOfWeightMul := rfl
/-- Inspect the body: expected outer constant `lpOneAlg.instConvCompatOfAntidiag`. -/
theorem selectedNatRationalCompat : lpOneAlgConvCompat ℚ ℕ (WeightedScalar ℚ pow2) :=
  inferInstance

/-- Inspect the body: expected outer constant `lpOneAlg.instConvCompatOfAntidiag`. -/
theorem selectedNatRealCompat : lpOneAlgConvCompat ℝ ℕ (WeightedScalar ℝ pow2) :=
  inferInstance

/-- Inspect the body: expected outer constant `lpOneAlg.instConvCompatOfWeightMul`. -/
theorem selectedIntRealCompat : lpOneAlgConvCompat ℝ ℤ (WeightedScalar ℝ pow2Z) :=
  inferInstance

section SelectedProducerInspection

set_option pp.all true
set_option pp.proofs true
set_option pp.explicit true

#print selectedNatRationalCompat
#print selectedNatRealCompat
#print selectedIntRealCompat
-- Registered priorities are inspected separately by the audit environment query.

end SelectedProducerInspection

-- Ring/algebra instances are the station ones.
example : (inferInstance : NormedRing (lpOneAlg ℕ (WeightedScalar ℝ pow2))) =
    lpOneAlg.instNormedRing := rfl
example : (inferInstance : NormedAlgebra ℝ (lpOneAlg ℕ (WeightedScalar ℝ pow2))) =
    lpOneAlg.instNormedAlgebra := rfl
example : (inferInstance : NormOneClass (lpOneAlg ℕ (WeightedScalar ℝ pow2))) =
    lpOneAlg.instNormOneClass := rfl
-- The same product formula.
example (f g : lpOneAlg ℕ (WeightedScalar ℝ pow2)) :
    lpOneAlg.toRealSeq (f * g) = _root_.DiscreteConvolution.addRingConvolution
      (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) := lpOneAlg.toRealSeq_mul_fun f g
example : ‖(lpOneAlg.single (E := WeightedScalar ℝ pow2) 3 (1 : ℝ))‖ = 8 := by
  rw [lpOneAlg.norm_single]; norm_num [pow2]

end RadiiPolynomial.Tests.FTImportOrderA

end
