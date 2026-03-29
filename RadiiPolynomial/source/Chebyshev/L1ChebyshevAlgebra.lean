import RadiiPolynomial.source.lpSpace.AddLp
import RadiiPolynomial.source.Chebyshev.ScaledRealZ
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Chebyshev ℓ¹ Banach Algebra

`l1Chebyshev ν = AddLp ℤ (ScaledRealZ ν)` — ℤ-indexed sequences with
bilateral weighted norm `∑|a_k|·ν^{|k|}` and convolution product.

All ring and algebra instances come from the generalized `AddLp` framework.
Only the `AddLpRingData` and `AddLpWeightSubMul` instances are Chebyshev-specific.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

/-! ### AddLpRingData: ScaledRealZ is ℝ underneath (all coercions are identity) -/

instance ScaledRealZ.addLpRingData (ν : PosReal) : AddLpRingData ℤ (ScaledRealZ ν) where
  toReal _k x := ScaledRealZ.toReal x
  ofReal _k r := ScaledRealZ.ofReal r
  toReal_ofReal _ _ := rfl
  ofReal_toReal _ _ := rfl
  ofReal_add _ _ _ := rfl
  ofReal_zero _ := rfl
  toReal_add _ _ _ := rfl
  toReal_zero _ := rfl
  toReal_neg _ _ := rfl
  norm_ofReal_eq k r := by
    simp only [ScaledRealZ.norm_def, ScaledRealZ.toReal_apply, ScaledRealZ.ofReal_apply,
      abs_one, one_mul]

/-! ### Bridge: norm of AddLpRingData.ofReal for ScaledRealZ -/

/-- The fiber norm of `AddLpRingData.ofReal k r` for ScaledRealZ equals `|r| * ν^{|k|}`. -/
@[simp] theorem ScaledRealZ.norm_addLpRingData_ofReal (ν : PosReal) (k : ℤ) (r : ℝ) :
    ‖AddLpRingData.ofReal (E := ScaledRealZ ν) k r‖ = |r| * (ν : ℝ) ^ k.natAbs := by
  show ‖ScaledRealZ.ofReal r‖ = _
  simp [ScaledRealZ.norm_def, ScaledRealZ.toReal_apply]

/-! ### AddLpWeightSubMul: from pow_natAbs_add_le -/

instance ScaledRealZ.addLpWeightSubMul (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    AddLpWeightSubMul ℤ (ScaledRealZ ν) where
  norm_ofReal_mul_le j l a b := by
    simp only [norm_addLpRingData_ofReal, abs_mul]
    calc |a| * |b| * (ν : ℝ) ^ (j + l).natAbs
        ≤ |a| * |b| * ((ν : ℝ) ^ j.natAbs * (ν : ℝ) ^ l.natAbs) :=
          mul_le_mul_of_nonneg_left (ScaledRealZ.pow_natAbs_add_le ν Fact.out j l)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (|a| * (ν : ℝ) ^ j.natAbs) * (|b| * (ν : ℝ) ^ l.natAbs) := by ring
  norm_ofReal_one_ge k := by
    simp only [norm_addLpRingData_ofReal, abs_one, one_mul]
    calc (1 : ℝ) = 1 ^ k.natAbs := (one_pow _).symm
      _ ≤ (ν : ℝ) ^ k.natAbs := by
          apply pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) Fact.out

/-! ### l1Chebyshev: the Chebyshev Banach algebra -/

/-- Chebyshev ℓ¹ Banach algebra: ℤ-indexed sequences with norm `∑|a_k|·ν^{|k|}`
and bilateral Cauchy product. All instances from generalized `AddLp`. -/
abbrev l1Chebyshev (ν : PosReal) := AddLp ℤ (ScaledRealZ ν)

namespace l1Chebyshev

variable {ν : PosReal}

/-- Extract underlying ℝ-valued sequence. -/
def toSeq (f : l1Chebyshev ν) : ℤ → ℝ := AddLp.toRealSeq f

-- Instances automatically available from AddLp:
-- NormedAddCommGroup, Ring, NormedRing (always)
-- CommRing, NormedCommRing (ℤ is AddCommGroup ✓)
-- NormedSpace ℝ, Algebra ℝ, NormedAlgebra ℝ (ScaledRealZ has NormedSpace ℝ ✓)
-- All require [Fact (1 ≤ (ν : ℝ))] for the NormedRing instances (via AddLpWeightSubMul)

-- Verify the key instances synthesize:
example [Fact (1 ≤ (ν : ℝ))] : NormedRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedCommRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedAlgebra ℝ (l1Chebyshev ν) := inferInstance

/-- Left multiplication CLM. -/
noncomputable abbrev leftMul [Fact (1 ≤ (ν : ℝ))] (a : l1Chebyshev ν) :=
  ContinuousLinearMap.mul ℝ (l1Chebyshev ν) a

end l1Chebyshev

end RadiiPolynomial

end
