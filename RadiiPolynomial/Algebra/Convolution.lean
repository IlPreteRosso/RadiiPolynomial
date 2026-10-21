import RadiiPolynomial.Algebra.Convolution.Basic
import RadiiPolynomial.Algebra.Convolution.Finite
import RadiiPolynomial.Algebra.Convolution.Ring
import RadiiPolynomial.Algebra.Convolution.CauchyProduct

/-!
# Discrete convolution

`Basic` re-exports Mathlib's discrete convolution. The library-owned finite-fiber core
`Finite` gives `finiteMulConvolution` and `finiteAddConvolution` on raw coefficient functions,
with their explicit finite-factorization hypotheses. `Ring` identifies the finite operation
with Mathlib's ring convolution under its stated summability assumptions.

`CauchyProduct` is the natural-index specialization, retaining the coefficient view
`toPowerSeries`. The bundled power-series bridge is recovered in `B5RecordPowerSeriesBridge`,
not exported by this facade. The generic
`map_cauchyProduct` is instantiated with `Rat.castHom ℝ` at the real consumer,
while the generic Cauchy module remains real-free. The optional wrapper carrier, monoid
algebra embedding and ring equivalences have a separate recoverable B2 record.
-/
