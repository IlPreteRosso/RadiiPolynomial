import RadiiPolynomial.Algebra.Convolution.Basic
import RadiiPolynomial.Algebra.Convolution.Finite
import RadiiPolynomial.Algebra.Convolution.Ring
import RadiiPolynomial.Algebra.Convolution.CauchyProduct

/-!
# Discrete convolution

`Basic` re-exports Mathlib's discrete convolution. The library-owned finite-fiber core
`Finite` gives `finiteMulConvolution` and `finiteAddConvolution` on raw coefficient functions,
with their explicit finite-factorization hypotheses. `Ring` adds point masses and
associativity for Mathlib's ring convolution under explicit summability hypotheses.

`CauchyProduct` is the natural-index specialization, with the coefficient view
`toPowerSeries`. The generic `map_cauchyProduct` is instantiated with `Rat.castHom ℝ` at the
real consumer, so the generic Cauchy module is real-free.
-/
