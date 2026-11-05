-- Root import for the RadiiPolynomial library.
--
-- The order mirrors the intended layering: sequence/Banach infrastructure, abstract
-- radii-polynomial theorem, algebraic polynomial bridge, numerical/tactic support,
-- domain-specific IVP/Chebyshev infrastructure, then production examples.

-- Algebra and analysis
import RadiiPolynomial.Algebra.Convolution
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.FiniteBlockTransport
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reality
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Pairing
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Bootstrap
import RadiiPolynomial.Analysis.SequenceSpace.Geometric
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev
import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry
import RadiiPolynomial.Analysis.Norm.FiniteSum
import RadiiPolynomial.Analysis.Norm.Exponential
import RadiiPolynomial.Core
import RadiiPolynomial.Algebra.Polynomial
import RadiiPolynomial.Operators.Matrix
import RadiiPolynomial.Operators.BlockDiagonal
import RadiiPolynomial.Operators.BlockDiagonal.ProdBlock
import RadiiPolynomial.Certification
import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Applications.IVP.Taylor.Analytic
import RadiiPolynomial.Applications.IVP.Taylor.Analyticity
import RadiiPolynomial.Applications.IVP.Taylor.ComplexTime
import RadiiPolynomial.Certification.IVP.Taylor
import RadiiPolynomial.Applications.IVP.Chebyshev
import RadiiPolynomial.Certification.IVP.Chebyshev
import RadiiPolynomial.Applications.Galerkin.Face
import RadiiPolynomial.Applications.FiniteDimensional.Face
import RadiiPolynomial.Applications.FiniteDimensional.Polynomial
import RadiiPolynomial.Applications.FiniteDimensional.Scalar
import RadiiPolynomial.Core.Theorem
import RadiiPolynomial.Applications.PowerSeries.AffineZ2
import RadiiPolynomial.Applications.PowerSeries.PolynomialZero
import RadiiPolynomial.Certification.PowerSeries.PolynomialZero
import RadiiPolynomial.Applications.Fourier.IkData
import RadiiPolynomial.Applications.Fourier.Quadratic
import RadiiPolynomial.Applications.Fourier.Duffing
import RadiiPolynomial.Applications.Fourier.Realization
import RadiiPolynomial.Applications.Fourier.Eigenpair
import RadiiPolynomial.Certification.Fourier.Quadratic
import RadiiPolynomial.Examples

-- Core theory

-- Algebraic polynomial bridge

-- Finite and block-diagonal operators

-- Certification adapters

-- Tactics

-- Taylor IVP application

-- Chebyshev IVP application

-- Galerkin application

-- Finite-dimensional application

-- Power-series application

-- Examples
