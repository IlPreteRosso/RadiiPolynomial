import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra

/-!
# The forward Joukowski map between coefficient algebras

The symmetric Laurent generator

`g = (e₁ + e₋₁) / 2`

has power growth `‖gⁿ‖ ≤ 2 a(ν)ⁿ`, where
`a(ν) = (ν + ν⁻¹) / 2` is the semi-major axis of the Bernstein ellipse.
Consequently, whenever `a(ν) ≤ r`, the universal property of the Taylor
algebra produces a continuous algebra homomorphism into the physical,
flip-fixed Chebyshev algebra.  Its composite with the inclusion into the
bilateral carrier is

`joukowskiAeval : l1Weighted r →A[ℝ] l1Chebyshev ν`.

On characters this map is contravariantly the classical Joukowski map
`z ↦ (z + z⁻¹) / 2`: Laurent evaluation at an annulus point after
`joukowskiAeval` is Taylor evaluation at its Joukowski image.  A further
theorem (`comp_joukowskiAeval_eq_evalC`) states the same naturality for an
arbitrary complex-valued character.  The last section replaces `g` by `1 + g`
under the stronger gate `1 + a(ν) ≤ r`, so that the Chebyshev left endpoint
pulls back to the Taylor centre.

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






















/-! ### Boundary-aligned substitution -/











end CrossGeometry

end RadiiPolynomial

end
