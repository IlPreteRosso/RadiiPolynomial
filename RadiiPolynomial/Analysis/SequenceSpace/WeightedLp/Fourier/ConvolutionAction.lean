import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar

/-! The geometric moderation constant 1 at ν ≥ 1. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Fourier

section Symbol

variable {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))]

/-- The carrier weight `ν^|k|` is moderate with respect to the symbol weight `ν^|k|`, with
constant `1` (`ν ≥ 1`; `Moderate.of_submul`). -/
theorem moderate_geomFiberZ :
    Moderate (FiberTrivialization.weight (E := geomFiberZ ℂ ν))
      (fun k : ℤ => (ν : ℝ) ^ k.natAbs) 1 := by
  rw [show FiberTrivialization.weight (E := geomFiberZ ℂ ν) = fun k : ℤ => (ν : ℝ) ^ k.natAbs from
    funext (geomFiberZ_weight ν)]
  exact Moderate.of_submul (ScaledRealZ.pow_natAbs_add_le ν Fact.out)




end Symbol

end RadiiPolynomial.WeightedLp.Fourier

end
