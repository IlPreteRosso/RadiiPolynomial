import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra

/-!
# The Joukowski map and the symmetric Laurent generator

The symmetric Laurent generator

`g = (e₁ + e₋₁) / 2`

(`joukowskiGen`) is fixed by reflection of the bilateral modes (`joukowskiGen_isSymmetric`),
so it is an element of the physical, flip-fixed Chebyshev algebra (`joukowskiGenSymm`).
`joukowski z = (z + z⁻¹) / 2` is the classical Joukowski map; Laurent evaluation at an
annulus point `z` sends `g` to `joukowski z` (`PhysicalSpectrum.restriction_gen` in
`Chebyshev/Spectrum/Basic.lean`).

This module is independent of the concrete Taylor/Chebyshev IVP applications
and is exposed by the `CrossGeometry` sequence-space facade.
-/

noncomputable section

namespace RadiiPolynomial

namespace CrossGeometry

open lpOneAlg












/-- The Joukowski map `z ↦ (z + z⁻¹) / 2`. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The symmetric Laurent generator `(e₁ + e₋₁) / 2`. -/
def joukowskiGen (ν : PosReal) : l1Chebyshev ν :=
  (2 : ℝ)⁻¹ • (single 1 1 + single (-1) 1)

/-- The Joukowski generator is fixed by reflection of the bilateral modes. -/
theorem joukowskiGen_isSymmetric (ν : PosReal) : (joukowskiGen ν).IsSymmetric := by
  apply l1Chebyshev.IsSymmetric.smul
  intro k
  show l1Chebyshev.toSeq (single 1 1 + single (-1) 1 : l1Chebyshev ν) (-k) =
    l1Chebyshev.toSeq (single 1 1 + single (-1) 1 : l1Chebyshev ν) k
  simp only [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_single, neg_eq_iff_eq_neg]
  ring_nf

/-- The Joukowski generator as an element of the physical Chebyshev algebra. -/
def joukowskiGenSymm (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev.symmetricSubalgebra ν :=
  ⟨joukowskiGen ν, joukowskiGen_isSymmetric ν⟩
































end CrossGeometry

end RadiiPolynomial

end
