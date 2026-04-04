-- Root import for the RadiiPolynomial library
-- lpSpace
import RadiiPolynomial.source.lpSpace.LpOneAlg
import RadiiPolynomial.source.lpSpace.WeightedScalar
import RadiiPolynomial.source.lpSpace.ScaledReal
import RadiiPolynomial.source.lpSpace.NormHelpers
import RadiiPolynomial.source.lpSpace.FiniteWeightedNorm
import RadiiPolynomial.source.lpSpace.DiscreteConvolution
import RadiiPolynomial.source.lpSpace.DiscreteConvolutionRing
import RadiiPolynomial.source.lpSpace.CauchyProduct
import RadiiPolynomial.source.lpSpace.lpWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.lpSpace.MatrixCLM
import RadiiPolynomial.source.lpSpace.OperatorNorm
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.Eval
-- Core theory
import RadiiPolynomial.source.RadiiPolyGeneral
import RadiiPolynomial.source.Core
-- BlockDiag
import RadiiPolynomial.source.BlockDiag.Base
import RadiiPolynomial.source.BlockDiag.Lift
import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.BlockDiag.Scalar
-- Witness and evaluation
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
-- IVP infrastructure
import RadiiPolynomial.source.IVP.Setup
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.StandardIVP
-- Tactics
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.Tactic.PDerivSimp
-- import RadiiPolynomial.source.Tactic.FinMatrixBound  -- requires LeanCert rebuild
-- Z₂ affine bounds
import RadiiPolynomial.source.Z2Affine
-- MvPolyBridge
import RadiiPolynomial.source.MvPolyBridge.Basic
-- Chebyshev infrastructure
import RadiiPolynomial.source.Chebyshev.ScaledRealZ
import RadiiPolynomial.source.Chebyshev.L1ChebyshevAlgebra
import RadiiPolynomial.source.Chebyshev.ChebyshevIVP
import RadiiPolynomial.source.Chebyshev.StandardChebyshevIVP
import RadiiPolynomial.source.Chebyshev.ChebyshevBlockDiag
-- Examples
import RadiiPolynomial.examples.Example81.Numbers
import RadiiPolynomial.examples.Example81.Algebra
import RadiiPolynomial.examples.Example81.Certificate
import RadiiPolynomial.examples.Example77.Algebra
import RadiiPolynomial.examples.Example77.Certificate
import RadiiPolynomial.examples.Example83.Numbers
import RadiiPolynomial.examples.Example83.Algebra
import RadiiPolynomial.examples.Example83.Certificate
import RadiiPolynomial.examples.Example245.Algebra
import RadiiPolynomial.examples.Example245.Certificate
import RadiiPolynomial.examples.Example1421.Algebra
import RadiiPolynomial.examples.Example1421.Numbers
import RadiiPolynomial.examples.TestCrossProduct.Algebra
import RadiiPolynomial.examples.TestCubic.Algebra
