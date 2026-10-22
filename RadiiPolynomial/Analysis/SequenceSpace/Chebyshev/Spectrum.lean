import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Basic
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Classification
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Ellipse
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Series
import Mathlib.Topology.Algebra.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Holomorphic

/-! Public API for the complex character space of the physical Chebyshev algebra:
characters of `l1Chebyshev.symmetricSubalgebra ν` and their mode extensionality
(`Basic`), their classification as annular Laurent evaluations (`Classification`),
the filled Bernstein ellipse parameterization (`Ellipse`), the Chebyshev recurrence of the
character values with Bernstein's bound (`Series`), and holomorphy on the open ellipse with
real analyticity of `l1Chebyshev.eval` near `[-1, 1]` (`Holomorphic`). -/
