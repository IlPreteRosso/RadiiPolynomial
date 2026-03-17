-- Root import for the RadiiPolynomial library
-- lpSpace
import RadiiPolynomial.source.lpSpace.ScaledReal
import RadiiPolynomial.source.lpSpace.NormHelpers
import RadiiPolynomial.source.lpSpace.FiniteWeightedNorm
import RadiiPolynomial.source.lpSpace.DiscreteConvolution
import RadiiPolynomial.source.lpSpace.CauchyProduct
import RadiiPolynomial.source.lpSpace.lpWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.lpSpace.LpOneBanachAlgebra
import RadiiPolynomial.source.lpSpace.MatrixCLM
import RadiiPolynomial.source.lpSpace.OperatorNorm
import RadiiPolynomial.source.lpSpace.OmegaWeighted
-- Core theory
import RadiiPolynomial.source.RadiiPolyGeneral
import RadiiPolynomial.source.Core
-- BlockDiag
import RadiiPolynomial.source.BlockDiag.Base
import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.BlockDiag.Scalar
-- Witness and evaluation
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
-- IVP infrastructure
import RadiiPolynomial.source.IVP.Setup
-- Tactics
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
-- import RadiiPolynomial.source.Tactic.FinMatrixBound  -- requires LeanCert rebuild
-- MvPolyBridge
import RadiiPolynomial.source.MvPolyBridge.Basic
