import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.EvaluationBounds
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.LaurentSpectrum
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum

/-! Public API for the bilateral Chebyshev weighted sequence algebra, the Laurent character
space as the closed annulus (`Chebyshev.LaurentSpectrum`), and the physical spectrum branch
(`Chebyshev.Spectrum`: classification, Bernstein ellipse, series, pointwise topology,
holomorphy on the open ellipse). `Chebyshev/Spectrum/*` sits above `CrossGeometry/Joukowski`. -/
