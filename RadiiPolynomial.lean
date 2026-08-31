-- Root import for the RadiiPolynomial library.
--
-- The order mirrors the intended layering: sequence/Banach infrastructure, abstract
-- radii-polynomial theorem, algebraic polynomial bridge, numerical/tactic support,
-- domain-specific IVP/Chebyshev infrastructure, then production examples.

-- Algebra and analysis
import RadiiPolynomial.Algebra.Convolution
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.Geometric
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev
import RadiiPolynomial.Analysis.Norm.FiniteSum

-- Core theory
import RadiiPolynomial.Core

-- Algebraic polynomial bridge
import RadiiPolynomial.Algebra.Polynomial

-- Finite and block-diagonal operators
import RadiiPolynomial.Operators.Matrix
import RadiiPolynomial.Operators.BlockDiagonal

-- Certification adapters
import RadiiPolynomial.Certification

-- Tactics
import RadiiPolynomial.Tactic.AutoPolyFDeriv
import RadiiPolynomial.Tactic.PDerivSimp
import RadiiPolynomial.Tactic.MakeCompPoly
import RadiiPolynomial.Tactic.FinMatrixBound

-- Taylor IVP application
import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Applications.IVP.Taylor.Analytic

-- Chebyshev IVP application
import RadiiPolynomial.Applications.IVP.Chebyshev

-- Examples
import RadiiPolynomial.Examples

