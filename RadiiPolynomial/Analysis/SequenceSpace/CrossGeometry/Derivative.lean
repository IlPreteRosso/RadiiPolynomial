import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import Mathlib.RingTheory.Polynomial.Chebyshev
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega

/-!
# Differentiation across the Chebyshev--Taylor realization

The Taylor realization of `Tₖ` differentiates to `k Uₖ₋₁`, coefficient for
coefficient.  The zero mode is included by retaining Mathlib's integer-indexed
`U₋₁ = 0`.  The intrinsic Chebyshev derivative lands in omega-weighted
`U`-coefficients; a separate synthesis map realizes those polynomials on a
Taylor disc.  Their composite is Taylor differentiation after restriction,
giving the four-corner derivative naturality square.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace CrossGeometry

open lpOneAlg Polynomial

/-! ### Polynomial coefficient realizations -/

private lemma polynomialOmega_mem (σ : PosReal) (p : ℝ[X]) :
    l1Omega.Mem σ p.coeff := by
  rw [l1Omega.mem_iff]
  refine summable_of_ne_finset_zero (s := p.support) fun n hn => ?_
  rw [Polynomial.notMem_support_iff.mp hn, abs_zero, zero_mul]





/-! ### The intrinsic Chebyshev derivative -/

















/-! ### Synthesis of `U`-polynomials on a smaller Taylor radius -/









/-! ### The physical derivative and its naturality square -/











end CrossGeometry

end RadiiPolynomial

end
