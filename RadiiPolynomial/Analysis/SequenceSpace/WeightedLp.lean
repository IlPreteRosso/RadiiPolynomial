import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Convolution
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reweight

/-! Framed weighted ℓᵖ carriers and bounded operators.

With a positive symbol weight v and a v-moderate state weight, ℓ¹ symbols act on ℓᵖ by an
operator series. For submultiplicative v, the universal algebra lift specifies that action.
Schur tests provide sufficient kernel bounds. For the bilateral ℓ² consumer, convolution takes values in weighted ℓ∞,
and a bounded smoothing map returns those values to ℓ². The carrier selects no convolution product: a weight whose
ratio rows are bounded at the Hölder conjugate exponent carries the explicit bounded bilinear product `convCLM`
(the admissible polynomial ℓ² states do, the bilateral geometric ℓ² state does not), with no `Mul` or `NormedRing`
instance. `reweightCLM` compares two weights on one coefficient family.
-/
