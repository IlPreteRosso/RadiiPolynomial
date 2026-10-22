import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import Mathlib.RingTheory.Polynomial.Chebyshev
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega

/-!
# Polynomial coefficients in the omega-weighted space

The coefficient sequence `p.coeff` of a real polynomial `p` is finitely supported, so it lies
in the omega-weighted space `l1Omega σ` at every weight `σ` (a private membership lemma).
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















end CrossGeometry

end RadiiPolynomial

end
