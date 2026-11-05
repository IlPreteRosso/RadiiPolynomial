import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Convolution

/-!
# The bounded product to `ℓ^∞_w` and the row-bounded convolution agree

On the bilateral ℓ² carrier `X_w = WeightedLp ℤ (WeightedScalar 𝕜 w) 2` of a positive weight `w`,
two bounded products may exist: the product to the bounded-coefficient carrier
`Bilateral.prodCLM hsub : X_w →L X_w →L Y_w` (`Bilateral/Product`, from the positive
submultiplicativity `hsub : Moderate w w 1`) and the self-convolution
`convCLM h : X_w →L X_w →L X_w` (`WeightedLp/Convolution`, from a row bound `h` of the frame weight
at the Hölder conjugate exponent `2`). Both are the convolution `∑' j, x_j y_(k−j)` of the raw
coefficients, so `incl_convCLM_eq_prodCLM : ι (convCLM h x y) = prodCLM hsub x y`, with the
inclusion `ι = Bilateral.incl : X_w →L Y_w` (`Bilateral/Quadratic`). The comparison lives here so
that the elementary product module does not import the self-convolution machinery.
-/

open scoped ENNReal NNReal DiscreteConvolution

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

open _root_.DiscreteConvolution (addRingConvolution_apply)
open RadiiPolynomial.DiscreteConvolution (addFiberEquiv)

section ProductConvolution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {w : ℤ → ℝ} [PosWeight w]
  {K : ℝ}

/-- **The two bounded products agree**: when both exist (a row bound `h` of the frame weight at
`q = 2` and the positive submultiplicativity `hsub`), the self-convolution followed by the
inclusion `ι : X_w → Y_w` is the product to `Y_w`, coefficientwise
`(x ⋆ y)_k = ∑' j, x_j y_(k−j)`. -/
theorem incl_convCLM_eq_prodCLM
    (h : RowBound (FiberTrivialization.weight (E := WeightedScalar 𝕜 w)) 2 K)
    (hsub : Moderate w w 1) (x y : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) :
    incl (convCLM h x y) = prodCLM hsub x y :=
  ext_coeff <| funext fun k => by
    rw [coeff_incl, coeff_prodCLM, coeff_convCLM, convCoeff, addRingConvolution_apply,
      ← ((Equiv.subLeft k).trans (addFiberEquiv k)).tsum_eq]
    exact tsum_congr fun j => by
      show coeff x (k - (k - j)) * coeff y (k - j) = coeff x j * coeff y (k - j)
      rw [sub_sub_cancel]

end ProductConvolution

end RadiiPolynomial.WeightedLp.Bilateral

end
