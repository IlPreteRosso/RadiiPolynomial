import RadiiPolynomial.source.lpSpace.ScaledReal

/-!
# ScaledRealZ: Bilateral Geometric Weight Specialization

`ScaledRealZ ν k` is `WeightedScalar (fun k : ℤ => ν^|k|) k` — bilateral Chebyshev fiber.
All instances (NormedAddCommGroup, NormedSpace, etc.) flow from `WeightedScalar`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### ScaledRealZ as WeightedScalar specialization -/

/-- `ScaledRealZ ν k` is `ℝ` with norm `|x| * ν^|k|` — bilateral weight for Chebyshev. -/
abbrev ScaledRealZ (ν : PosReal) := WeightedScalar (fun k : ℤ => (ν : ℝ) ^ k.natAbs)

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

instance ScaledRealZ.instSubMulWeight (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    SubMulWeight (fun k : ℤ => (ν : ℝ) ^ k.natAbs) where
  weight_pos k := pow_pos ν.coe_pos k.natAbs
  one_le k := by
    have hν : (1 : ℝ) ≤ (ν : ℝ) := Fact.out
    exact ((one_pow k.natAbs).symm.le).trans (pow_le_pow_left₀ zero_le_one hν k.natAbs)
  submul j l := pow_natAbs_add_le ν Fact.out j l
  weight_zero := pow_zero _

/-! ### Compatibility aliases -/

namespace ScaledRealZ

variable {ν : PosReal} {k : ℤ}

/-- Identity map to `ℝ`. Alias for `WeightedScalar.toReal`. -/
abbrev toReal (x : ScaledRealZ ν k) : ℝ := WeightedScalar.toReal x

end ScaledRealZ

end RadiiPolynomial

end
