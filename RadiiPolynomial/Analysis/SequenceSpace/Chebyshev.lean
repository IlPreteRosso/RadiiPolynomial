import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Symmetrize
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Galerkin
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.EvaluationBounds
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided

/-! Public API for the bilateral Chebyshev weighted sequence algebra, its Laurent evaluation on
the closed annulus (`Chebyshev.UnitLift`), the physical spectrum branch (`Chebyshev.Spectrum`:
classification, Bernstein ellipse, Bernstein's bound, holomorphy on the open ellipse), and the
finite Galerkin carrier `FνN` with its even padding and truncation (`Chebyshev.Galerkin`).
`Chebyshev/Spectrum/*` sits above `CrossGeometry/Joukowski`. -/
