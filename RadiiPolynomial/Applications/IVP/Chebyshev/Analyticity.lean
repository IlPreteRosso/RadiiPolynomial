import RadiiPolynomial.Applications.IVP.Chebyshev.Analytic
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Holomorphic

/-!
# Analyticity of the canonical Chebyshev solution

Application layer. `Chebyshev/Analytic.lean` builds the canonical solution
`ChebyshevIVP.x_sol` from a sequence-space zero and proves continuity on `[-1, 1]` and a
one-sided derivative on `[-1, 1)`. This module adds real analyticity: for a coefficient weight
`1 < ν`, each component `l1Chebyshev.eval (a l)` is analytic on a neighbourhood of every point
of `[-1, 1]`, endpoints included (`PhysicalSpectrum.analyticOnNhd_eval_Icc`, from holomorphy on
the Bernstein ellipse), hence so is `x_sol a`. The statement holds for every coefficient vector
`a`, certified or not. The certified instance is
`Examples/IVP/Chebyshev/Example1421/Analyticity.lean`.
-/

open RadiiPolynomial Set

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- Every canonical Chebyshev realization is real analytic across the endpoints
as soon as the coefficient weight is strictly above one. -/
theorem analyticOnNhd_x_sol (hν : 1 < (ν : ℝ)) (a : XCheb ν L) :
    AnalyticOnNhd ℝ (ChebyshevIVP.x_sol a) (Set.Icc (-1 : ℝ) 1) :=
  AnalyticOnNhd.pi (fun l => PhysicalSpectrum.analyticOnNhd_eval_Icc ν hν (a l))

end ChebyshevIVP
