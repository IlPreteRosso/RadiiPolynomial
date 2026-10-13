import RadiiPolynomial.Algebra.Convolution.Basic
import RadiiPolynomial.Algebra.Convolution.Finite
import RadiiPolynomial.Algebra.Convolution.FiniteFiber
import RadiiPolynomial.Algebra.Convolution.FiniteFiber.PowerSeries
import RadiiPolynomial.Algebra.Convolution.FiniteFiber.MonoidAlgebra
import RadiiPolynomial.Algebra.Convolution.Ring
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Algebra.Convolution.CauchyProductReal

/-!
# Discrete convolution

Public entry point for discrete convolution. `Basic` imports Mathlib's discrete convolution over
monoids (`Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution`) and adds the parametrization of
the fibers over a group index. `Ring` adds the point masses `delta e`, the decomposition of `M × M`
into multiplication fibers and associativity of the ring convolution under explicit summability
hypotheses. `Finite` is the topology-free finite-fiber convolution over an index with
`Finset.HasMulAntidiagonal`, and `CauchyProduct` is its specialization to the index `ℕ`.
`FiniteFiber` packages the finite-fiber convolution as the multiplication of the type synonyms
`FiniteFiberConvolution M R` and `FiniteFiberAddConvolution M R` of all functions `M → R`.
`FiniteFiber.PowerSeries` identifies the additive-index wrapper over `ℕ` with `PowerSeries R` and
over `σ →₀ ℕ` with `MvPowerSeries σ R`, as ring equivalences. `FiniteFiber.MonoidAlgebra` embeds
`MonoidAlgebra R M` into `FiniteFiberConvolution M R` as an injective ring homomorphism whose range
is the finitely supported elements. `CauchyProduct` also carries the coefficient bridge to
`PowerSeries R` (`toPowerSeries`, bundled as the `S`-linear equivalence `toPowerSeriesLinearEquiv`),
and `Ring` records `cauchyProduct.eq_addRingConvolution`. `CauchyProductReal` records the cast
`ℚ → ℝ` through the Cauchy product (`cauchyProduct.ratCast`), the only real-number fact of this
layer, so `CauchyProduct` itself does not import the reals. The library-owned declarations live in
the namespace `RadiiPolynomial`.
-/
