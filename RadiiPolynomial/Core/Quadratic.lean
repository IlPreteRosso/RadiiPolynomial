import RadiiPolynomial.Core.Theorem
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Quadratic maps and their radii theorem

For `f x = c + L x + B x x`, the bilinear map `B` need not be symmetric.
Calculus uses normed spaces only. The radii theorem adds completeness of the domain and
explicit real scalar structures, and consumes the bound on `C + C.flip`, where `C z h = A (B z h)`.
-/

noncomputable section

namespace RadiiPolynomial

open ContinuousLinearMap Metric

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An affine map plus a bounded bilinear map evaluated on the diagonal. -/
def quadMap (c : F) (L : E →L[𝕜] F) (B : E →L[𝕜] E →L[𝕜] F) (x : E) : F :=
  c + L x + B x x

/-- The derivative expression retains both orders of the bilinear arguments. -/
abbrev quadDeriv (L : E →L[𝕜] F) (B : E →L[𝕜] E →L[𝕜] F) (x : E) : E →L[𝕜] F :=
  L + B x + B.flip x

/-- The derivative of a quadratic map, without completeness or symmetry assumptions. -/
theorem hasFDerivAt_quadMap (c : F) (L : E →L[𝕜] F)
    (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    HasFDerivAt (quadMap c L B) (quadDeriv L B x) x := by
  have hB := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have hD : B.precompR E x (ContinuousLinearMap.id 𝕜 E) +
      B.precompL E (ContinuousLinearMap.id 𝕜 E) x = B x + B.flip x := by
    ext h
    simp
  have h := ((hasFDerivAt_const c x).add L.hasFDerivAt).add (hB.congr_fderiv hD)
  change HasFDerivAt (quadMap c L B) ((0 + L) + (B x + B.flip x)) x at h
  simpa only [quadDeriv, zero_add, add_assoc] using h

/-- Apply the preconditioner to the output of the bilinear map. -/
def quadComp (A : F →L[𝕜] E) (B : E →L[𝕜] E →L[𝕜] F) : E →L[𝕜] E →L[𝕜] E :=
  (ContinuousLinearMap.compL 𝕜 E F E A).comp B

@[simp] theorem quadComp_apply (A : F →L[𝕜] E) (B : E →L[𝕜] E →L[𝕜] F) (z h : E) :
    quadComp A B z h = A (B z h) := rfl

/-- The exact derivative difference uses the symmetrized preconditioned bilinear map. -/
theorem comp_quadDeriv_sub (A : F →L[𝕜] E) (L : E →L[𝕜] F)
    (B : E →L[𝕜] E →L[𝕜] F) (y x : E) :
    A.comp (quadDeriv L B y - quadDeriv L B x) =
      (quadComp A B + (quadComp A B).flip) (y - x) := by
  ext h
  simp only [quadDeriv, comp_apply, sub_apply, add_apply, flip_apply, quadComp_apply,
    map_sub, map_add]
  abel

/-- A curvature bound for a quadratic map, before restricting to a ball. -/
theorem norm_comp_quadDeriv_sub_le (A : F →L[𝕜] E) (L : E →L[𝕜] F)
    (B : E →L[𝕜] E →L[𝕜] F) (y x : E) :
    ‖A.comp (quadDeriv L B y - quadDeriv L B x)‖ ≤
      ‖quadComp A B + (quadComp A B).flip‖ * ‖y - x‖ := by
  rw [comp_quadDeriv_sub]
  exact ContinuousLinearMap.le_opNorm _ _

/-- The usual twice-the-norm estimate is a sufficient bound for the primary curvature socket. -/
theorem norm_quadComp_add_flip_le (A : F →L[𝕜] E) (B : E →L[𝕜] E →L[𝕜] F) :
    ‖quadComp A B + (quadComp A B).flip‖ ≤ 2 * ‖quadComp A B‖ := by
  simpa only [opNorm_flip, two_mul] using norm_add_le (quadComp A B) (quadComp A B).flip

section Radii

variable [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [CompleteSpace E]

/-- Quadratic radii theorem with an open-ball zero and invertible real derivative.
The four bounds are stated over the original scalar field. -/
theorem quadratic_radii_theorem_nondegenerate_local
    {c : F} {L : E →L[𝕜] F} {B : E →L[𝕜] E →L[𝕜] F}
    {xBar : E} {A : F →L[𝕜] E} {A_dagger : E →L[𝕜] F}
    {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖A (quadMap c L B xBar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 E - A.comp A_dagger‖ ≤ Z₀)
    (hZ₁ : ‖A.comp (A_dagger - quadDeriv L B xBar)‖ ≤ Z₁)
    (hZ₂ : ‖quadComp A B + (quadComp A B).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hA : Function.Injective A) :
    ∃ xTilde ∈ ball xBar r₀, quadMap c L B xTilde = 0 ∧
      ((quadDeriv L B xTilde).restrictScalars ℝ).IsInvertible ∧
      ∀ z ∈ closedBall xBar r₀, quadMap c L B z = 0 → z = xTilde := by
  refine general_radii_polynomial_theorem_nondegenerate_local
    (f := quadMap c L B) (Df := fun x => (quadDeriv L B x).restrictScalars ℝ)
    (A := A.restrictScalars ℝ) (A_dagger := A_dagger.restrictScalars ℝ)
    hr₀ hY₀ ?_ ?_ ?_ (fun x _ =>
      ((hasFDerivAt_quadMap c L B x).restrictScalars ℝ).hasFDerivWithinAt) hrad hA
  · change ‖(ContinuousLinearMap.id 𝕜 E - A.comp A_dagger).restrictScalars ℝ‖ ≤ Z₀
    rwa [ContinuousLinearMap.norm_restrictScalars]
  · change ‖(A.comp (A_dagger - quadDeriv L B xBar)).restrictScalars ℝ‖ ≤ Z₁
    rwa [ContinuousLinearMap.norm_restrictScalars]
  · intro y hy
    change ‖(A.comp (quadDeriv L B y - quadDeriv L B xBar)).restrictScalars ℝ‖ ≤ Z₂ * r₀
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact (norm_comp_quadDeriv_sub_le A L B y xBar).trans
      ((mul_le_mul_of_nonneg_right hZ₂ (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
          ((norm_nonneg _).trans hZ₂)))

/-- A unique closed-ball zero from the four quadratic radii bounds. -/
theorem quadratic_radii_theorem_local
    {c : F} {L : E →L[𝕜] F} {B : E →L[𝕜] E →L[𝕜] F}
    {xBar : E} {A : F →L[𝕜] E} {A_dagger : E →L[𝕜] F}
    {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖A (quadMap c L B xBar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 E - A.comp A_dagger‖ ≤ Z₀)
    (hZ₁ : ‖A.comp (A_dagger - quadDeriv L B xBar)‖ ≤ Z₁)
    (hZ₂ : ‖quadComp A B + (quadComp A B).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hA : Function.Injective A) :
    ∃! xTilde ∈ closedBall xBar r₀, quadMap c L B xTilde = 0 := by
  obtain ⟨x, hx, hfx, -, hu⟩ :=
    quadratic_radii_theorem_nondegenerate_local hr₀ hY₀ hZ₀ hZ₁ hZ₂ hrad hA
  exact ⟨x, ⟨ball_subset_closedBall hx, hfx⟩, fun z ⟨hz, hz0⟩ => hu z hz hz0⟩

end Radii

end RadiiPolynomial
