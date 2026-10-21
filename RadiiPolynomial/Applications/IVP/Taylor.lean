import RadiiPolynomial.Applications.IVP.VectorField
import RadiiPolynomial.Applications.IVP.Taylor.Operator
import RadiiPolynomial.Applications.IVP.Taylor.Theorem
import RadiiPolynomial.Applications.IVP.Taylor.Jacobian
import RadiiPolynomial.Applications.IVP.Taylor.Standard
import RadiiPolynomial.Applications.IVP.Taylor.Polynomial
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Module.Basic
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation

/-! Public algebraic and certificate-facing API for Taylor-coefficient IVPs.

Import `RadiiPolynomial.Applications.IVP.Taylor.Analytic` separately for the
function-space existence and uniqueness endpoint,
`RadiiPolynomial.Applications.IVP.Taylor.Analyticity` for real analyticity of the
canonical trajectory, and `RadiiPolynomial.Applications.IVP.Taylor.ComplexTime`
for its complex-time trajectory.
-/
