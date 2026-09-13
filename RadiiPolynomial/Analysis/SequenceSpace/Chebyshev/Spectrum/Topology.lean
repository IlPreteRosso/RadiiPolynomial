import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Series
import RadiiPolynomial.Analysis.SequenceSpace.CharacterTopology

/-!
# The Gelfand topology on the physical character space

Topological layer. `pointwiseTopology ν` is the carrier-independent topology of pointwise
convergence from `Analysis/SequenceSpace/CharacterTopology.lean`, specialized to
`Character ν`, declared as a plain `def` and installed only as a `local instance`: a
global instance would compete with the operator-norm topology carried by the underlying
continuous linear map, so it is deliberately not introduced. With that topology the
set-level bijection of `Spectrum/Ellipse.lean` upgrades to a homeomorphism
`characterHomeomorphEllipse : Character ν ≃ₜ Ellipse ν` in the coordinate `χ ↦ χ(g)`.

Closes the "spectrum as a topological space" gap for the Chebyshev geometry: production
bundles no topological spectrum object at all.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open CrossGeometry

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- Topology of pointwise convergence on the actual physical coefficient
vectors. Kept explicit to avoid changing any global topology instance. -/
@[instance_reducible]
def pointwiseTopology : TopologicalSpace (Character ν) :=
  Gelfand.pointwiseTopology ℝ (Physical ν) ℂ

local instance : TopologicalSpace (Character ν) := pointwiseTopology ν

theorem continuous_character_apply (a : Physical ν) :
    Continuous (fun χ : Character ν => χ a) :=
  Gelfand.continuous_character_apply (R := ℝ) (Physical ν) ℂ a

theorem continuous_ellipseCharacter : Continuous (ellipseCharacter ν) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun a => continuous_ellipseCharacter_apply ν a)

/-- The complex character space of the production real physical algebra,
with pointwise topology, is homeomorphic to the closed filled Bernstein
ellipse in the normalized physical coordinate `χ ↦ χ(g)`. -/
def characterHomeomorphEllipse : Character ν ≃ₜ Ellipse ν where
  toEquiv := characterEquivEllipse ν
  continuous_toFun := (continuous_character_apply ν (joukowskiGenSymm ν)).subtype_mk _
  continuous_invFun := continuous_ellipseCharacter ν

@[simp] theorem characterHomeomorphEllipse_apply (χ : Character ν) :
    (characterHomeomorphEllipse ν χ).val = χ (joukowskiGenSymm ν) := rfl

end RadiiPolynomial.PhysicalSpectrum
