import RadiiPolynomial.Certification.Witness
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.NhdsWithin
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Algebra
import RadiiPolynomial.Certification.RadiiPolynomialQ
import RadiiPolynomial.Certification.Rational.Frac
import RadiiPolynomial.Certification.Rational.Grid

/-!
# Certification facade

The shipped facade exposes witness reductions (`Witness`), exact rational matrix/action
bridges (`Rational.Matrix`), grid checkers (`Rational.Frac`, `Rational.Grid`), rational radii
polynomial checks (`RadiiPolynomialQ`) and the retained LeanCert adapter.
Residual/Neumann correction and finite-support completeness belong to the recovery modules
`B5RecordResidualP1` and `B5RecordResidualP2`; dyadic evaluator families also have recovery ownership.

The family faces `Certification.IVP.Taylor`, `Certification.IVP.Chebyshev` and
`Certification.PowerSeries.PolynomialZero` import their application discretizations and are
not part of this facade. Certificates import their family face directly, so a Taylor
certificate does not load the Chebyshev discretization.
-/
