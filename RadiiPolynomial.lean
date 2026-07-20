-- Root import for the RadiiPolynomial library.
--
-- The order mirrors the intended layering: sequence/Banach infrastructure, abstract
-- radii-polynomial theorem, algebraic polynomial bridge, numerical/tactic support,
-- domain-specific IVP/Chebyshev infrastructure, then production examples.

-- lpSpace infrastructure
import RadiiPolynomial.source.lpSpace.LpOneAlg
import RadiiPolynomial.source.lpSpace.WeightedScalar
import RadiiPolynomial.source.lpSpace.WeightedScalarInstances
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
import RadiiPolynomial.source.lpSpace.EvalDeriv

-- Core theory
import RadiiPolynomial.source.RadiiPolyGeneral
import RadiiPolynomial.source.Core

-- Algebraic polynomial bridge
import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.source.MvPolyBridge.CompPoly

-- Witness and evaluation
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.Z2Affine

-- Tactics
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.Tactic.PDerivSimp
import RadiiPolynomial.source.Tactic.MakeCompPoly
-- import RadiiPolynomial.source.Tactic.FinMatrixBound  -- requires LeanCert rebuild

-- BlockDiag
import RadiiPolynomial.source.BlockDiag.Base
import RadiiPolynomial.source.BlockDiag.Lift
import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.BlockDiag.Scalar

-- IVP infrastructure
import RadiiPolynomial.source.IVP.Setup
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.IVP.CompPoly
import RadiiPolynomial.source.IVP.Bridge
import RadiiPolynomial.source.IVP.AnalyticGlue

-- Chebyshev infrastructure
import RadiiPolynomial.source.Chebyshev.ScaledRealZ
import RadiiPolynomial.source.Chebyshev.L1ChebyshevAlgebra
import RadiiPolynomial.source.Chebyshev.ChebyshevIVP
import RadiiPolynomial.source.Chebyshev.StandardChebyshevIVP
import RadiiPolynomial.source.Chebyshev.ChebyshevBlockDiag

-- Examples
import RadiiPolynomial.examples.Example77.Algebra
import RadiiPolynomial.examples.Example77.Certificate
import RadiiPolynomial.examples.Example77.Analytic
import RadiiPolynomial.examples.Example81.Numbers
import RadiiPolynomial.examples.Example81.Algebra
import RadiiPolynomial.examples.Example81.Certificate
import RadiiPolynomial.examples.Example81.Analytic
import RadiiPolynomial.examples.Example83.Numbers
import RadiiPolynomial.examples.Example83.Algebra
import RadiiPolynomial.examples.Example83.Certificate
import RadiiPolynomial.examples.Example83.Analytic
import RadiiPolynomial.examples.Example245.Algebra
import RadiiPolynomial.examples.Example245.Certificate

-- Pending Chebyshev example scaffold. Keep out of the default build until the
-- Julia-exported numerical data and certificate are present.
-- import RadiiPolynomial.examples.Example1421.Numbers
-- import RadiiPolynomial.examples.Example1421.Algebra

-- Test files (skeleton with sorries) are excluded from the default project
-- build to keep `lake build` warning-free. Build them individually on demand:
--   lake build RadiiPolynomial.examples.tests.easy.Quadratic
-- Easy tests: full pipeline skeleton with expected results stated, all sorried.
-- Hard tests: only f given; autoformalizer must synthesize F, A, A†, pipeline.
-- import RadiiPolynomial.examples.tests.easy.CrossProduct
-- import RadiiPolynomial.examples.tests.easy.Cubic
-- import RadiiPolynomial.examples.tests.easy.Quadratic
-- import RadiiPolynomial.examples.tests.hard.Quartic
-- import RadiiPolynomial.examples.tests.hard.SimpleIVP
-- import RadiiPolynomial.examples.tests.hard.CrossProductIVP
