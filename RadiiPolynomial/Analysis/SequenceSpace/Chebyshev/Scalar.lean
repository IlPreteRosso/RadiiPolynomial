import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Scalar

/-!
# ScaledRealZ: Bilateral Geometric Weight Specialization

`ScaledRealZ ν k` is `WeightedScalar (fun k : ℤ => ν^|k|) k` — bilateral Chebyshev fiber.
All instances (NormedAddCommGroup, NormedSpace, etc.) flow from `WeightedScalar`.

This file owns the bilateral weight `k ↦ ν^|k|` and its instances, so it also holds the
weight-level faces: the fiber over any normed field `geomFiberZ 𝕜 ν` (with
`ScaledRealZ ν = geomFiberZ ℝ ν` definitionally) and its fiber weight `geomFiberZ_weight`,
used by the Fourier carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)`, and the real fiber-norm bridge
`ScaledRealZ.norm_lpAlgRingData_ofReal`, twin of `ScaledReal.norm_lpAlgRingData_ofReal`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### ScaledRealZ as WeightedScalar specialization -/

/-- `ScaledRealZ ν k` is `ℝ` with norm `|x| * ν^|k|` — bilateral weight for Chebyshev. -/
abbrev ScaledRealZ (ν : PosReal) := WeightedScalar ℝ (fun k : ℤ => (ν : ℝ) ^ k.natAbs)

/-! ### Weight instances -/

instance ScaledRealZ.instPosWeight (ν : PosReal) :
    PosWeight (fun k : ℤ => (ν : ℝ) ^ k.natAbs) where
  weight_pos k := pow_pos ν.coe_pos k.natAbs

/-- Key inequality for Chebyshev submultiplicativity: `ν^{|j+l|} ≤ ν^{|j|} * ν^{|l|}`
when `ν ≥ 1`. Uses `|j+l| ≤ |j| + |l|` (triangle inequality on ℤ). -/
lemma ScaledRealZ.pow_natAbs_add_le (ν : PosReal) (hν : 1 ≤ (ν : ℝ)) (j l : ℤ) :
    (ν : ℝ) ^ (j + l).natAbs ≤ (ν : ℝ) ^ j.natAbs * (ν : ℝ) ^ l.natAbs := by
  rw [← pow_add]
  exact pow_le_pow_right₀ hν (Int.natAbs_add_le j l)

/-- Submultiplicative weight base. Requires ν ≥ 1 (unlike ScaledReal where ν^(m+n) = ν^m·ν^n
is exact). For ℤ, `ν^|j+l| ≤ ν^|j|·ν^|l|` needs `|j+l| ≤ |j|+|l|` plus `ν ≥ 1`. -/
instance ScaledRealZ.instSubMulWeightBase (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    SubMulWeightBase (fun k : ℤ => (ν : ℝ) ^ k.natAbs) where
  weight_pos k := pow_pos ν.coe_pos k.natAbs
  submul j l := pow_natAbs_add_le ν Fact.out j l
  weight_zero := pow_zero _

/-- Full SubMulWeight (adds weight ≥ 1). Requires ν ≥ 1. -/
instance ScaledRealZ.instSubMulWeight (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    SubMulWeight (fun k : ℤ => (ν : ℝ) ^ k.natAbs) where
  one_le k := by
    have hν : (1 : ℝ) ≤ (ν : ℝ) := Fact.out
    exact ((one_pow k.natAbs).symm.le).trans (pow_le_pow_left₀ zero_le_one hν k.natAbs)

/-! ### The bilateral geometric fiber over any normed field -/

/-- The bilateral geometric fiber over a normed field `𝕜`: `𝕜` with norm
`‖x‖ ν^|k|` at mode `k : ℤ`. Its real instance is `ScaledRealZ ν`
(definitionally), so `l1Chebyshev ν = lpOneAlg ℤ (geomFiberZ ℝ ν)`. -/
abbrev geomFiberZ (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal) :=
  WeightedScalar 𝕜 (fun k : ℤ => (ν : ℝ) ^ k.natAbs)

example (ν : PosReal) : ScaledRealZ ν = geomFiberZ ℝ ν := rfl

/-- The fiber weight of `geomFiberZ 𝕜 ν` at `k` is `ν^|k|`. -/
theorem geomFiberZ_weight {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal) (k : ℤ) :
    ‖lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)‖ = (ν : ℝ) ^ k.natAbs := by
  rw [show lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)
      = WeightedScalar.ofReal 1 from rfl, WeightedScalar.norm_ofReal,
    norm_one, one_mul]

/-- The norm of an atom of the bilateral geometric carrier: `‖single j x‖ = ‖x‖ ν^|j|`. -/
theorem lpOneAlg.norm_single_geomFiberZ {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal) (j : ℤ)
    (x : 𝕜) :
    ‖(lpOneAlg.single (E := geomFiberZ 𝕜 ν) j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖
      = ‖x‖ * (ν : ℝ) ^ j.natAbs := by
  rw [lpOneAlg.norm_single, geomFiberZ_weight]

/-! ### Fiber-norm bridge -/

/-- The fiber norm of `lpAlgRingData.ofReal k r` for `ScaledRealZ` equals `|r| * ν^|k|`. -/
@[simp] theorem ScaledRealZ.norm_lpAlgRingData_ofReal (ν : PosReal) (k : ℤ) (r : ℝ) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) k r‖ = |r| * (ν : ℝ) ^ k.natAbs :=
  WeightedScalar.norm_ofReal r

end RadiiPolynomial

end
