import Mathlib.Topology.Algebra.Algebra

/-!
# The pointwise topology on a space of continuous characters

Carrier-independent layer shared by the three spectrum modules
(`Geometric/Spectrum.lean`, `Chebyshev/LaurentSpectrum.lean`,
`Chebyshev/Spectrum/Topology.lean`). Each of them bundles its characters
`A →A[ℝ] ℂ` as a topological space with the topology of pointwise convergence and
needs exactly one continuity fact about it; neither the definition nor that fact
mentions the carrier, so both live here once.

The topology is a plain `def`, never a global instance: a global instance would
compete with the operator-norm topology carried by the underlying continuous
linear map. Every consumer installs it with its own `local instance`.
-/

noncomputable section

namespace RadiiPolynomial.Gelfand

variable {R : Type*} [CommSemiring R]
  (A : Type*) [Semiring A] [TopologicalSpace A] [Algebra R A]
  (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R B]

/-- Topology of pointwise convergence on the continuous characters `A →A[R] B`,
induced from the product topology on `A → B`. The scalar ring `R` is explicit: nothing
in the type of `A` or `B` determines it. -/
@[instance_reducible]
def pointwiseTopology (R : Type*) [CommSemiring R]
    (A : Type*) [Semiring A] [TopologicalSpace A] [Algebra R A]
    (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R B] :
    TopologicalSpace (A →A[R] B) :=
  TopologicalSpace.induced (fun χ : A →A[R] B => (χ : A → B)) inferInstance

local instance : TopologicalSpace (A →A[R] B) := pointwiseTopology R A B

/-- Evaluation at a fixed algebra element is continuous for the pointwise topology. -/
theorem continuous_character_apply (a : A) :
    Continuous (fun χ : A →A[R] B => χ a) :=
  (continuous_apply a).comp continuous_induced_dom

end RadiiPolynomial.Gelfand

end
