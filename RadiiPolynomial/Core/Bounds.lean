import RadiiPolynomial.Core.Theorem

/-!
# RadiiPolynomial Core API (Section 8.2 direction)

Canonical norm quantities for radii-polynomial validation over general domain and range spaces.
Finite systems use the ordinary Pi type `Fin L → E` at their concrete realization.

Canonical norm quantities (`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`) are
defined over general real normed spaces (`E F : Type*` with `NormedAddCommGroup` and
`NormedSpace ℝ`; no completeness is assumed),
so both `l1Weighted ν` (scalar) and `XL1 ν L` (system) can use them directly.

Certificates call `general_radii_polynomial_theorem` directly with these
canonical norm definitions.
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

section CanonicalBounds

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical `Y₀`: `‖A(f(x̄))‖`.
Ref: (7.30), Thm 7.6.2; cf. Thm 8.2.2 (p.200). -/
def Y₀_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) : ℝ := ‖A (f xBar)‖

/-- Canonical `Z₀`: `‖I - A∘A†‖`.
Ref: (7.31), Thm 7.6.2; aggregated as (8.22), p.200. -/
def Z₀_norm (A : F →L[ℝ] E) (A_dagger : E →L[ℝ] F) : ℝ :=
  ‖ContinuousLinearMap.id ℝ E - A.comp A_dagger‖

/-- Canonical `Z₁`: `‖A∘(A† - Df(x̄))‖`.
Ref: (7.32), Thm 7.6.2; aggregated as (8.23), p.200. -/
def Z₁_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) (A_dagger : E →L[ℝ] F) : ℝ :=
  ‖A.comp (A_dagger - fderiv ℝ f xBar)‖

/-- Canonical `Z₂` at `c`: `‖A∘(Df(c) - Df(x̄))‖`.
Ref: (7.33), Thm 7.6.2; aggregated as (8.24), p.200. -/
def Z₂_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) (c : E) : ℝ :=
  ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖

end CanonicalBounds


end RadiiPolynomial
