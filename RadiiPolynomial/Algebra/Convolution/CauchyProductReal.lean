import Mathlib.Basic.Real.Basic
import RadiiPolynomial.Algebra.Convolution.CauchyProduct

/-!
# The Cauchy product and the cast `ℚ → ℝ`

The Cauchy product commutes with every ring homomorphism of the coefficients
(`RadiiPolynomial.cauchyProduct.map_cauchyProduct`). This module records the specialization of
that law to the cast `ℚ → ℝ`, the only fact of the Cauchy-product API that mentions the real
numbers. It lives apart from `RadiiPolynomial.Algebra.Convolution.CauchyProduct`, so the generic
module does not import `Mathlib.Basic.Real.Basic`; a consumer that needs the real specialization
imports this module.

## Main results

* `RadiiPolynomial.cauchyProduct.ratCast`: the Cauchy product of the real casts of two rational
  sequences is the real cast of their rational Cauchy product.
-/

namespace RadiiPolynomial

/-- Cauchy product with `ℚ → ℝ` cast. -/
theorem cauchyProduct.ratCast (a b : ℕ → ℚ) (n : ℕ) :
    cauchyProduct (fun k => (a k : ℝ)) (fun k => (b k : ℝ)) n =
      ↑(cauchyProduct a b n) :=
  cauchyProduct.map_cauchyProduct (Rat.castHom ℝ) a b n

end RadiiPolynomial
