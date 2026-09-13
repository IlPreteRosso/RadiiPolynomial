import RadiiPolynomial.Applications.IVP.Chebyshev.Analytic
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Holomorphic

/-!
# Analyticity of the canonical Chebyshev solution

Application layer. `Chebyshev/Analytic.lean` builds the canonical solution
`ChebyshevIVP.x_sol` out of a sequence-space zero and claims continuity plus a
one-sided derivative on `[-1, 1]` — deliberately no analyticity, for want of a
Bernstein-ellipse statement. `Analysis/SequenceSpace/Chebyshev/Spectrum/Holomorphic.lean`
now supplies exactly that statement, so the canonical realization is here shown to be
real analytic on a neighbourhood of every point of the closed reference interval,
endpoints included, as soon as the coefficient weight satisfies `1 < ν`.

Closes the Chebyshev analyticity gap at the application level; the certified instance
is `Examples/IVP/Chebyshev/Example1421/Analyticity.lean`.
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
