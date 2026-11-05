import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Carrier

/-! The geometric moderation constant 1 at ν ≥ 1. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Fourier

section Symbol

variable {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))]

/-- The carrier weight `ν^|k|` is moderate with respect to the symbol weight `ν^|k|`, with
constant `1` (`ν ≥ 1`; the frame form of `Bilateral.geomSubmul`). -/
theorem moderate_geomFiberZ :
    Moderate (FiberTrivialization.weight (E := geomFiberZ ℂ ν))
      (fun k : ℤ => (ν : ℝ) ^ k.natAbs) 1 :=
  Moderate.weightedScalar_iff.mpr (Bilateral.geomSubmul ν)




end Symbol

end RadiiPolynomial.WeightedLp.Fourier

end
