import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Laurent
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev.Bounds

/-!
# CompPoly API

Public facade for the generic computable AST, Taylor coefficients, finite Laurent
coefficients, and stored Chebyshev semantics.
Import `CompPoly.Core` when only syntax, computation, or generic algebra evaluation is needed.
Import `CompPoly.Laurent` for computable finite Laurent and symmetric-array evaluation;
`CompPoly.Chebyshev` adds correctness in the completed algebra and differentiation.
`CompPoly.Bounds` and `CompPoly.Chebyshev.Bounds` read certificate constants (norm,
Lipschitz, derivative operator norm, derivative Lipschitz) off the syntax tree.
-/
