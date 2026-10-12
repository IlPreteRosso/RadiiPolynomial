import Mathlib.Topology.Algebra.Algebra

/-!
# The pointwise topology on a space of continuous characters

Carrier-independent layer shared by the three spectrum modules
(`Geometric/Spectrum.lean`, `Chebyshev/LaurentSpectrum.lean`,
`Chebyshev/Spectrum/Topology.lean`). Each of them bundles its characters
`A →A[ℝ] ℂ` as a topological space with the topology of pointwise convergence. The
definition and its continuity API do not mention the carrier, so they live here once:

* elimination — `continuous_character_apply`: evaluation at a fixed algebra element is
  continuous;
* introduction — `continuous_of_continuous_apply`: a family of characters is continuous as
  soon as each of its evaluations is (the universal property of the induced topology).

The topology is a plain `def`, never a global instance: a global instance would
compete with the operator-norm topology carried by the underlying continuous
linear map. Every consumer installs it with its own `local instance`.
-/

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

/-- **Elimination rule.** Evaluation at a fixed algebra element is continuous for the
pointwise topology. -/
theorem continuous_character_apply (a : A) :
    Continuous (fun χ : A →A[R] B => χ a) :=
  (continuous_apply a).comp continuous_induced_dom

variable {A B} in
/-- **Introduction rule.** A family of characters `φ : X → (A →A[R] B)` is continuous for the
pointwise topology as soon as each evaluation `x ↦ φ x a` is continuous: the universal
property of the topology induced from the product topology on `A → B`. -/
theorem continuous_of_continuous_apply {X : Type*} [TopologicalSpace X] {φ : X → (A →A[R] B)}
    (h : ∀ a, Continuous fun x => φ x a) : Continuous φ :=
  continuous_induced_rng.mpr (continuous_pi h)

end RadiiPolynomial.Gelfand
