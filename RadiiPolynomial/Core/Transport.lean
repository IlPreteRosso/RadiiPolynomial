import RadiiPolynomial.Core.Theorem

/-!
# Pulled-back norms and isometric zero transport

Two transport services used by the application layer:

* `rp_transport_local` runs the local finite-dimensional radii-polynomial theorem
  through a continuous linear equivalence, with pointwise bounds in the pulled-back
  norm `W y = ‖e.symm y‖`. Derivative hypotheses are local to that ball.
* `existsUnique_zero_transport` moves an already-proved unique zero in a closed ball
  along a metric isometry and a supplied equivalence of the zero predicates.

These are distinct services. Isometric transport of an existing zero does not
reprice a four-bound certificate along a non-isometric equivalence.
-/

open Metric ContinuousLinearMap

namespace RadiiPolynomial

section FinDimTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local general radii polynomial theorem in pointwise form, through a pulled-back norm.**
Any continuous linear equivalence `e : E ≃L[ℝ] E'` onto `E'` from a finite-dimensional `E`, any
pulled-back norm `W y = ‖e.symm y‖` carried as a plain function, `A`, `A†` only linear, every bound
a pointwise inequality in `W`, derivative data `HasFDerivWithinAt` on the `W`-ball only, a general
`Z₁` slot and `Z₂ : ℝ → ℝ`. No sign hypothesis: `0 ≤ Z₀`, `0 ≤ Z₁`, `0 ≤ Z₂ r · r` are derived
(the degenerate space is handled separately). -/
theorem rp_transport_local {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (e : E ≃L[ℝ] E') {W : E' → ℝ} (hW : ∀ y, W y = ‖e.symm y‖) {F₀ : E' → E'}
    {DF : E' → E' →L[ℝ] E'} (A A_dagger : E' →ₗ[ℝ] E') {xBar : E'} {Y₀ Z₀ Z₁ : ℝ}
    {Z₂ : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ x, W (x - xBar) ≤ r → HasFDerivWithinAt F₀ (DF x) {y | W (y - xBar) ≤ r} x)
    (hY₀ : W (A (F₀ xBar)) ≤ Y₀) (hZ₀ : ∀ h, W (h - A (A_dagger h)) ≤ Z₀ * W h)
    (hZ₁ : ∀ h, W (A (A_dagger h - DF xBar h)) ≤ Z₁ * W h)
    (hZ₂ : ∀ c, W (c - xBar) ≤ r → ∀ h, W (A (DF c h - DF xBar h)) ≤ Z₂ r * r * W h)
    (hp : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r < 0) :
    ∃! xTilde, W (xTilde - xBar) ≤ r ∧ F₀ xTilde = 0 := by
  have hWe : ∀ x, W (e x) = ‖x‖ := fun x => by rw [hW, e.symm_apply_apply]
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton E' := e.symm.injective.subsingleton
    refine ⟨xBar, ⟨?_, Subsingleton.elim _ _⟩, fun y _ => Subsingleton.elim _ _⟩
    rw [sub_self, hW, map_zero, norm_zero]
    exact hr.le
  obtain ⟨y0, hy0⟩ := exists_ne (0 : E)
  have hy0' : 0 < ‖y0‖ := norm_pos_iff.2 hy0
  -- a pointwise bound `W (u h) ≤ K W h` for every `h` forces `0 ≤ K`
  have hnn : ∀ (K : ℝ) (u : E' → E'), (∀ h, W (u h) ≤ K * W h) → 0 ≤ K := fun K u hu => by
    have h1 := hu (e y0)
    have h2 : 0 ≤ W (u (e y0)) := by rw [hW]; exact norm_nonneg _
    rw [hWe] at h1
    nlinarith
  have hx0 : W (xBar - xBar) ≤ r := by rw [sub_self, hW, map_zero, norm_zero]; exact hr.le
  have hZ₀nn := hnn Z₀ (fun h => h - A (A_dagger h)) hZ₀
  have hZ₁nn := hnn Z₁ (fun h => A (A_dagger h - DF xBar h)) hZ₁
  have hZ₂nn := hnn (Z₂ r * r) (fun h => A (DF xBar h - DF xBar h)) (hZ₂ xBar hx0)
  let f : E → E := e.symm ∘ F₀ ∘ e
  let Df : E → E →L[ℝ] E := fun z =>
    (e.symm : E' →L[ℝ] E).comp ((DF (e z)).comp (e : E →L[ℝ] E'))
  have hDf : ∀ z y, Df z y = e.symm (DF (e z) (e y)) := fun _ _ => rfl
  let A' : E →L[ℝ] E := LinearMap.toContinuousLinearMap
    ((e.symm : E' →ₗ[ℝ] E) ∘ₗ A ∘ₗ (e : E →ₗ[ℝ] E'))
  have hA' : ∀ y, A' y = e.symm (A (e y)) := fun y => rfl
  let Ad' : E →L[ℝ] E := LinearMap.toContinuousLinearMap
    ((e.symm : E' →ₗ[ℝ] E) ∘ₗ A_dagger ∘ₗ (e : E →ₗ[ℝ] E'))
  have hAd' : ∀ y, Ad' y = e.symm (A_dagger (e y)) := fun y => rfl
  have hmaps : Set.MapsTo e (closedBall (e.symm xBar) r) {y | W (y - xBar) ≤ r} :=
    fun w hw => by
      show W (e w - xBar) ≤ r
      rw [hW, map_sub, e.symm_apply_apply, ← dist_eq_norm]
      exact hw
  have hf : ∀ z ∈ closedBall (e.symm xBar) r,
      HasFDerivWithinAt f (Df z) (closedBall (e.symm xBar) r) z := fun z hz =>
    e.symm.hasFDerivAt.comp_hasFDerivWithinAt z
      ((hF (e z) (hmaps hz)).comp z e.hasFDerivAt.hasFDerivWithinAt hmaps)
  have main := general_rp_findim_local (f := f) (Df := Df) (xBar := e.symm xBar) (A := A')
    (A_dagger := Ad') (Z₂ := Z₂) hr
    (by
      rw [hA']
      simpa only [f, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, ← hW] using hY₀)
    (ContinuousLinearMap.opNorm_le_bound _ hZ₀nn fun y => by
      have h1 := hZ₀ (e y)
      rw [hWe, hW, map_sub, e.symm_apply_apply] at h1
      simpa only [sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, hA', hAd', ContinuousLinearEquiv.apply_symm_apply]
        using h1)
    (ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun y => by
      have h1 := hZ₁ (e y)
      rw [hWe, hW] at h1
      simpa only [ContinuousLinearMap.comp_apply, sub_apply, hA', hAd',
        hDf, ContinuousLinearEquiv.apply_symm_apply, map_sub] using h1)
    (fun c hc => ContinuousLinearMap.opNorm_le_bound _ hZ₂nn fun y => by
      have hc' : W (e c - xBar) ≤ r := hmaps hc
      have h1 := hZ₂ (e c) hc' (e y)
      rw [hWe, hW] at h1
      simpa only [ContinuousLinearMap.comp_apply, sub_apply, hA', hDf,
        ContinuousLinearEquiv.apply_symm_apply, map_sub] using h1)
    hf hp
  obtain ⟨z, hz1, hz2, -, hzu⟩ := main
  refine ⟨e z, ⟨?_, ?_⟩, fun y hy => ?_⟩
  · rw [hW, map_sub, e.symm_apply_apply, ← dist_eq_norm]
    exact (mem_ball.1 hz1).le
  · simpa [f] using congrArg e hz2
  · have hyz := hzu (e.symm y)
      (by rw [mem_closedBall, dist_eq_norm, ← map_sub, ← hW]; exact hy.1)
      (by simp [f, hy.2])
    rw [← hyz, e.apply_symm_apply]

end FinDimTransport

section IsometricTransport

/-- A unique zero in a closed ball transports along any isometric equivalence. -/
theorem existsUnique_zero_transport {X Y M N : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [Zero M] [Zero N] (e : X ≃ᵢ Y) {F : X → M} {g : Y → N}
    (hFg : ∀ x, g (e x) = 0 ↔ F x = 0) {c : X} {r : ℝ}
    (h : ∃! x ∈ closedBall c r, F x = 0) : ∃! y ∈ closedBall (e c) r, g y = 0 := by
  obtain ⟨x, ⟨hx, hFx⟩, hu⟩ := h
  refine ⟨e x, ⟨?_, (hFg x).2 hFx⟩, fun y ⟨hy, hgy⟩ => ?_⟩
  · rwa [mem_closedBall, e.dist_eq]
  · have hy' : e.symm y ∈ closedBall c r := by
      rwa [mem_closedBall, ← e.dist_eq, e.apply_symm_apply]
    have := hu (e.symm y) ⟨hy', (hFg _).1 (by rwa [e.apply_symm_apply])⟩
    rw [← this, e.apply_symm_apply]

end IsometricTransport

end RadiiPolynomial
