import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.ScalarInstances

/-!
# ScaledReal: Geometric Weight Specialization

`ScaledReal ν n` is `WeightedScalar (fun n => ν^n) n` — the Taylor/power series fiber.
All instances (NormedAddCommGroup, NormedSpace, etc.) flow from `WeightedScalar`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-- Positive real numbers. -/
abbrev PosReal := {x : ℝ // 0 < x}

namespace PosReal

/-- Coercion to real numbers. -/
@[coe] def toReal (ν : PosReal) : ℝ := ν.1

instance : Coe PosReal ℝ := ⟨PosReal.toReal⟩

@[simp] lemma coe_pos (ν : PosReal) : (0 : ℝ) < ν := ν.2
@[simp] lemma coe_nonneg (ν : PosReal) : (0 : ℝ) ≤ ν := le_of_lt ν.2
@[simp] lemma coe_ne_zero (ν : PosReal) : (ν : ℝ) ≠ 0 := ne_of_gt ν.2

/-- Coercion to nonnegative reals. -/
@[coe] def toNNReal (ν : PosReal) : ℝ≥0 := ⟨ν.1, le_of_lt ν.2⟩

instance : Coe PosReal ℝ≥0 := ⟨PosReal.toNNReal⟩

@[simp, norm_cast] lemma coe_toNNReal (ν : PosReal) : ((ν : ℝ≥0) : ℝ) = (ν : ℝ) := rfl

end PosReal

/-! ### ScaledReal as WeightedScalar specialization -/

/-- `ScaledReal ν n` is `ℝ` with norm `|x| * ν^n` — geometric weight for Taylor series. -/
abbrev ScaledReal (ν : PosReal) := WeightedScalar ℝ (fun n : ℕ => (ν : ℝ) ^ n)

/-! ### Weight instances -/

instance ScaledReal.instPosWeight (ν : PosReal) :
    PosWeight (fun n : ℕ => (ν : ℝ) ^ n) where
  weight_pos n := pow_pos ν.coe_pos n

/-- Submultiplicative weight base for ALL ν > 0. No ν ≥ 1 required. -/
instance ScaledReal.instSubMulWeightBase (ν : PosReal) :
    SubMulWeightBase (fun n : ℕ => (ν : ℝ) ^ n) where
  weight_pos n := pow_pos ν.coe_pos n
  submul m n := le_of_eq (pow_add (ν : ℝ) m n)
  weight_zero := pow_zero _

/-- Full SubMulWeight (adds weight ≥ 1). Requires ν ≥ 1. -/
instance ScaledReal.instSubMulWeight (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    SubMulWeight (fun n : ℕ => (ν : ℝ) ^ n) where
  one_le n := by
    have hν : (1 : ℝ) ≤ (ν : ℝ) := Fact.out
    exact ((one_pow n).symm.le).trans (pow_le_pow_left₀ zero_le_one hν n)

/-! ### Compatibility aliases -/

namespace ScaledReal

variable {ν : PosReal} {n : ℕ}

/-- Identity map to `ℝ`. Alias for `WeightedScalar.toReal`. -/
abbrev toReal (x : ScaledReal ν n) : ℝ := WeightedScalar.toReal x

/-- Additive equivalence from `ℝ`. Alias for `WeightedScalar.ofReal`. -/
abbrev ofReal : ℝ ≃+ ScaledReal ν n := WeightedScalar.ofReal

lemma norm_def (x : ScaledReal ν n) : ‖x‖ = |toReal x| * (ν : ℝ) ^ n := rfl

@[simp] lemma toReal_apply (x : ScaledReal ν n) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : ScaledReal ν n) = x := rfl

end ScaledReal

end RadiiPolynomial

end
