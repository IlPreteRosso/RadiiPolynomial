import RadiiPolynomial.source.Chebyshev.ScaledRealZ
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Chebyshev ℓ¹ Banach Algebra

`l1Chebyshev ν = lpOneAlg ℤ (ScaledRealZ ν)` — ℤ-indexed sequences with
bilateral weighted norm `∑|a_k|·ν^{|k|}` and convolution product.

Ring and algebra instances flow from `lpOneAlg` + `SubMulWeight` via
generic `WeightedScalar` instances in `WeightedScalar.lean`.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

/-! ### Bridge lemma for downstream use -/

/-- The fiber norm of `lpOneAlgRingData.ofReal k r` for ScaledRealZ equals `|r| * ν^{|k|}`. -/
@[simp] theorem ScaledRealZ.norm_lpOneAlgRingData_ofReal (ν : PosReal) (k : ℤ) (r : ℝ) :
    ‖lpOneAlgRingData.ofReal (E := ScaledRealZ ν) k r‖ = |r| * (ν : ℝ) ^ k.natAbs :=
  WeightedScalar.norm_ofReal r

/-! ### l1Chebyshev: the Chebyshev Banach algebra -/

/-- Chebyshev ℓ¹ Banach algebra: ℤ-indexed sequences with norm `∑|a_k|·ν^{|k|}`
and bilateral Cauchy product. All instances from generalized `lpOneAlg` + `SubMulWeight`. -/
abbrev l1Chebyshev (ν : PosReal) := lpOneAlg ℤ (ScaledRealZ ν)

namespace l1Chebyshev

variable {ν : PosReal}

/-- Extract underlying ℝ-valued sequence. -/
def toSeq (f : l1Chebyshev ν) : ℤ → ℝ := lpOneAlg.toRealSeq f

@[simp] lemma toSeq_add (f g : l1Chebyshev ν) (m : ℤ) :
    toSeq (f + g) m = toSeq f m + toSeq g m :=
  congr_fun (lpOneAlg.toRealSeq_add f g) m

-- Instances automatically available from lpOneAlg + SubMulWeight:
-- NormedAddCommGroup, Ring, NormedRing (always)
-- CommRing, NormedCommRing (ℤ is AddCommGroup ✓)
-- NormedSpace ℝ, Algebra ℝ, NormedAlgebra ℝ (ScaledRealZ has NormedSpace ℝ ✓)
-- All require [Fact (1 ≤ (ν : ℝ))] for Ring (via SubMulWeightBase: submul on ℤ needs ν ≥ 1)

-- Verify the key instances synthesize:
example [Fact (1 ≤ (ν : ℝ))] : NormedRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedCommRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedAlgebra ℝ (l1Chebyshev ν) := inferInstance

/-- Left multiplication CLM. -/
noncomputable abbrev leftMul [Fact (1 ≤ (ν : ℝ))] (a : l1Chebyshev ν) :
    l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  letI : Algebra ℝ (l1Chebyshev ν) := lpOneAlg.instAlgebra
  letI : IsScalarTower ℝ (l1Chebyshev ν) (l1Chebyshev ν) := IsScalarTower.right
  letI : SMulCommClass ℝ (l1Chebyshev ν) (l1Chebyshev ν) := Algebra.to_smulCommClass
  ContinuousLinearMap.mul ℝ (l1Chebyshev ν) a

end l1Chebyshev

end RadiiPolynomial

end
