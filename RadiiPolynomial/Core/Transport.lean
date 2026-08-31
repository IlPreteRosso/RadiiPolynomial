import RadiiPolynomial.Core.Theorem

/-!
# Certificate transport (the κ meta-theorems)

A radii-polynomial certificate transports along continuous linear equivalences
of the ambient spaces, at a price κ = αβ set by the operator norms of the
domain equivalence and its inverse. Developed 2026-08-24 as the
`tmp/kappa_transport` experiment; promoted to `Core` 2026-08-25.

Contents:
* `transported_radii_identity` — the exact price algebra
  β·p_C(r₁) = κ·p_B(β r₁) + (κ−1)·(β r₁), κ = αβ, pure ring identity.
* `transport_radii_polynomial` — the meta-theorem: a radii-polynomial
  certificate for f : E → F transports along u : E ≃L E', w : F ≃L F'
  (square f' ∘ u = w ∘ f as a HYPOTHESIS) to a certificate for f' with
  bounds (α·Y₀, αβ·Z₀, αβ·Z₁, αβ²·Z₂(β·)) at radius r₁ where r₀ = β·r₁.
  Only ‖u‖ ≤ α and ‖u.symm‖ ≤ β are priced; w cancels in every bound.
* `transport_radii_polynomial_of_margin` — acceptance via the native margin:
  κ·p_B(r₀) + (κ−1)·r₀ < 0 suffices.
* `gateQ` / `gateQ_sound` — the reuse-or-reprove decision procedure: one
  rational-arithmetic check (run by `native_decide` on certificate data)
  discharging the margin hypothesis.

Design notes:
* The B side needs no `CompleteSpace` — only the C side runs the fixed-point
  argument. The transported data is (A' = u∘A∘w⁻¹, A†' = w∘A†∘u⁻¹).
* r₀ = β·r₁ is a hypothesis (no division anywhere).
* All four C-side bounds are proved by conjugation telescoping + two
  applications of `opNorm_comp_le`; no tsums, no basis.

Instances: `Examples/Transport/KappaToy.lean` (toy, κ = 8/3 through
`borderedTU_equiv`) and `Examples/Transport/TwinTransport.lean`
(Example 14.2.1, generic in the equivalence).
-/

open Metric ContinuousLinearMap

section PriceAlgebra

/-- §1 The exact transport identity for the radii polynomial: with κ = αβ and
    B-side radius r₀ = β·r₁,
    `β · p_C(r₁) = κ · p_B(r₀) + (κ − 1) · r₀`.
    Acceptance on the C side is therefore equivalent to the native margin of
    the B-side certificate exceeding (κ−1)/κ. Pure ring identity. -/
lemma transported_radii_identity (Y₀ Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (α β r₁ : ℝ) :
    β * generalRadiiPolynomial (α * Y₀) (α * β * Z₀) (α * β * Z₁)
        (fun s => α * β * β * Z₂ (β * s)) r₁
      = α * β * generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ (β * r₁)
        + (α * β - 1) * (β * r₁) := by
  simp only [generalRadiiPolynomial]
  ring

end PriceAlgebra

section TransportTheorem

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- §2 **Certificate transport.** A radii-polynomial certificate for
    `f : E → F` at `x̄` transports along equivalences `u : E ≃L E'`,
    `w : F ≃L F'` intertwining `f` with `f'` (the square is a hypothesis, not
    a definition) to a certificate for `f'` at `u x̄`:

    * transported data: `A' = u ∘ A ∘ w⁻¹`, `A†' = w ∘ A† ∘ u⁻¹`;
    * transported bounds: `(α·Y₀, αβ·Z₀, αβ·Z₁, αβ²·Z₂(β·))` where
      `‖u‖ ≤ α`, `‖u⁻¹‖ ≤ β` — the codomain equivalence `w` cancels in every
      bound and contributes no constant;
    * transported radius: `r₁` with `r₀ = β·r₁`.

    The conclusion is existence and uniqueness of a zero of `f'` in
    `B̄_{r₁}(u x̄)`, provided the transported radii polynomial is negative at
    `r₁`. The B side is never run: no `CompleteSpace E` is assumed. -/
theorem transport_radii_polynomial
    {f : E → F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (u : E ≃L[ℝ] E') (w : F ≃L[ℝ] F') {f' : E' → F'}
    (hsquare : ∀ x, f' (u x) = w (f x))
    {α β : ℝ}
    (hα : ‖(u : E →L[ℝ] E')‖ ≤ α) (hβ : ‖(u.symm : E' →L[ℝ] E)‖ ≤ β)
    {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₀ : r₀ = β * r₁)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - fderiv ℝ f xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,
      ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf_diff : Differentiable ℝ f)
    (h_radii' : generalRadiiPolynomial (α * Y₀) (α * β * Z₀) (α * β * Z₁)
        (fun s => α * β * β * Z₂ (β * s)) r₁ < 0)
    (hA_inj : Function.Injective A) :
    ∃! xTilde ∈ Metric.closedBall (u xBar) r₁, f' xTilde = 0 := by
  -- Identify f' with the conjugated map once and for all.
  have hf'g : f' = fun x' => w (f (u.symm x')) := by
    funext x'
    rw [← u.apply_symm_apply x', hsquare, u.symm_apply_apply]
  subst hf'g
  -- Nonnegativity of the prices.
  have hα0 : 0 ≤ α := le_trans (norm_nonneg _) hα
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  -- Transported operator data.
  set uL : E →L[ℝ] E' := (u : E →L[ℝ] E') with huL
  set uLinv : E' →L[ℝ] E := (u.symm : E' →L[ℝ] E) with huLinv
  set wL : F →L[ℝ] F' := (w : F →L[ℝ] F') with hwL
  set wLinv : F' →L[ℝ] F := (w.symm : F' →L[ℝ] F) with hwLinv
  set A' : F' →L[ℝ] E' := uL.comp (A.comp wLinv) with hA'
  set Ad' : E' →L[ℝ] F' := wL.comp (A_dagger.comp uLinv) with hAd'
  -- Differentiability and the fderiv formula for the conjugated map.
  have hf'_diff : Differentiable ℝ (fun x' => w (f (u.symm x'))) :=
    wL.differentiable.comp (hf_diff.comp u.symm.differentiable)
  have hDf' : ∀ x' : E',
      fderiv ℝ (fun y' => w (f (u.symm y'))) x'
        = wL.comp ((fderiv ℝ f (u.symm x')).comp uLinv) := by
    intro x'
    have h1 : HasFDerivAt f (fderiv ℝ f (u.symm x')) (u.symm x') :=
      (hf_diff (u.symm x')).hasFDerivAt
    have h2 : HasFDerivAt (fun y' : E' => u.symm y') uLinv x' :=
      u.symm.hasFDerivAt
    have h3 : HasFDerivAt (fun y' : E' => f (u.symm y'))
        ((fderiv ℝ f (u.symm x')).comp uLinv) x' := h1.comp x' h2
    have h4 : HasFDerivAt (fun y' : E' => w (f (u.symm y')))
        (wL.comp ((fderiv ℝ f (u.symm x')).comp uLinv)) x' :=
      (wL.hasFDerivAt.comp x' h3 :)
    exact h4.fderiv
  -- Y₀ bound: A'(f'(u x̄)) = u (A (f x̄)).
  have hY' : ‖A' ((fun x' => w (f (u.symm x'))) (u xBar))‖ ≤ α * Y₀ := by
    have hpt : A' ((fun x' => w (f (u.symm x'))) (u xBar)) = uL (A (f xBar)) := by
      simp [hA', huL, hwLinv, ContinuousLinearMap.comp_apply,
        u.symm_apply_apply, w.symm_apply_apply]
    rw [hpt]
    exact le_trans (uL.le_opNorm _) (mul_le_mul hα h_Y₀ (norm_nonneg _) hα0)
  -- A norm bound for u ∘ B ∘ u⁻¹ conjugations, used three times.
  have hconj : ∀ B : E →L[ℝ] E, ‖(uL.comp B).comp uLinv‖ ≤ α * β * ‖B‖ := by
    intro B
    refine le_trans (opNorm_comp_le _ _) ?_
    have h1 : ‖uL.comp B‖ ≤ α * ‖B‖ :=
      le_trans (opNorm_comp_le _ _) (mul_le_mul_of_nonneg_right hα (norm_nonneg _))
    have h2 : ‖uL.comp B‖ * ‖uLinv‖ ≤ (α * ‖B‖) * β :=
      mul_le_mul h1 hβ (norm_nonneg _) (by positivity)
    linarith [h2, show (α * ‖B‖) * β = α * β * ‖B‖ from by ring]
  -- Z₀ bound: I − A'A†' = u ∘ (I − AA†) ∘ u⁻¹.
  have hZ₀' : ‖ContinuousLinearMap.id ℝ E' - A'.comp Ad'‖ ≤ α * β * Z₀ := by
    have hkey : ContinuousLinearMap.id ℝ E' - A'.comp Ad'
        = (uL.comp (ContinuousLinearMap.id ℝ E - A.comp A_dagger)).comp uLinv := by
      ext x'
      simp [hA', hAd', huL, huLinv, hwL, hwLinv, ContinuousLinearMap.comp_apply,
        w.symm_apply_apply]
    rw [hkey]
    exact le_trans (hconj _)
      (mul_le_mul_of_nonneg_left h_Z₀ (by positivity))
  -- Z₁ bound: A' ∘ (A†' − Df'(x̄')) = u ∘ (A ∘ (A† − Df(x̄))) ∘ u⁻¹.
  have hZ₁' : ‖A'.comp (Ad' - fderiv ℝ (fun x' => w (f (u.symm x'))) (u xBar))‖
      ≤ α * β * Z₁ := by
    have hkey : A'.comp (Ad' - fderiv ℝ (fun x' => w (f (u.symm x'))) (u xBar))
        = (uL.comp (A.comp (A_dagger - fderiv ℝ f xBar))).comp uLinv := by
      rw [hDf' (u xBar), u.symm_apply_apply]
      ext x'
      simp [hA', hAd', huL, huLinv, hwL, hwLinv, ContinuousLinearMap.comp_apply,
        w.symm_apply_apply]
    rw [hkey]
    exact le_trans (hconj _)
      (mul_le_mul_of_nonneg_left h_Z₁ (by positivity))
  -- Z₂ bound: pull c' back through u⁻¹, conjugate, and reprice.
  have hZ₂' : ∀ c' ∈ Metric.closedBall (u xBar) r₁,
      ‖A'.comp (fderiv ℝ (fun x' => w (f (u.symm x'))) c'
          - fderiv ℝ (fun x' => w (f (u.symm x'))) (u xBar))‖
        ≤ (fun s => α * β * β * Z₂ (β * s)) r₁ * r₁ := by
    intro c' hc'
    have hcball : u.symm c' ∈ Metric.closedBall xBar r₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hc' ⊢
      have hpull : u.symm c' - xBar = uLinv (c' - u xBar) := by
        simp [huLinv, map_sub, u.symm_apply_apply]
      rw [hpull, hr₀]
      exact le_trans (uLinv.le_opNorm _)
        (mul_le_mul hβ hc' (norm_nonneg _) hβ0)
    have hkey : A'.comp (fderiv ℝ (fun x' => w (f (u.symm x'))) c'
          - fderiv ℝ (fun x' => w (f (u.symm x'))) (u xBar))
        = (uL.comp (A.comp (fderiv ℝ f (u.symm c') - fderiv ℝ f xBar))).comp uLinv := by
      rw [hDf' c', hDf' (u xBar), u.symm_apply_apply]
      ext x'
      simp [hA', huL, huLinv, hwL, hwLinv, ContinuousLinearMap.comp_apply,
        w.symm_apply_apply]
    rw [hkey]
    refine le_trans (hconj _) ?_
    have hbase : ‖A.comp (fderiv ℝ f (u.symm c') - fderiv ℝ f xBar)‖
        ≤ Z₂ r₀ * r₀ := h_Z₂ _ hcball
    have harr : α * β * (Z₂ r₀ * r₀) = α * β * β * Z₂ (β * r₁) * r₁ := by
      rw [hr₀]; ring
    have hstep : α * β * ‖A.comp (fderiv ℝ f (u.symm c') - fderiv ℝ f xBar)‖
        ≤ α * β * (Z₂ r₀ * r₀) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    show α * β * ‖A.comp (fderiv ℝ f (u.symm c') - fderiv ℝ f xBar)‖
        ≤ α * β * β * Z₂ (β * r₁) * r₁
    linarith [hstep, harr]
  -- Injectivity of A' = u ∘ A ∘ w⁻¹.
  have hA'_inj : Function.Injective A' := by
    have : (A' : F' → E') = (fun y => u (A (w.symm y))) := by
      funext y; simp [hA', huL, hwLinv, ContinuousLinearMap.comp_apply]
    rw [this]
    exact u.injective.comp (hA_inj.comp w.symm.injective)
  -- Run the abstract theorem on the C side.
  exact general_radii_polynomial_theorem hr₁ hY' hZ₀' hZ₁' hZ₂' hf'_diff h_radii' hA'_inj

/-- §3 **Margin form.** Acceptance of the transported certificate follows from
    the native-margin inequality `κ·p_B(r₀) + (κ−1)·r₀ < 0` with `κ = αβ` —
    equivalently `m_B(r₀) = 1 − q_B(r₀)/r₀ > (κ−1)/κ`. This is the form a
    `native_decide` gate checks on ℚ data. -/
theorem transport_radii_polynomial_of_margin
    {f : E → F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (u : E ≃L[ℝ] E') (w : F ≃L[ℝ] F') {f' : E' → F'}
    (hsquare : ∀ x, f' (u x) = w (f x))
    {α β : ℝ}
    (hα : ‖(u : E →L[ℝ] E')‖ ≤ α) (hβ : ‖(u.symm : E' →L[ℝ] E)‖ ≤ β)
    (hβpos : 0 < β)
    {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₀ : r₀ = β * r₁)
    (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
    (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)
    (h_Z₁ : ‖A.comp (A_dagger - fderiv ℝ f xBar)‖ ≤ Z₁)
    (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,
      ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
    (hf_diff : Differentiable ℝ f)
    (h_margin : α * β * generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀
        + (α * β - 1) * r₀ < 0)
    (hA_inj : Function.Injective A) :
    ∃! xTilde ∈ Metric.closedBall (u xBar) r₁, f' xTilde = 0 := by
  refine transport_radii_polynomial u w hsquare hα hβ hr₁ hr₀
    h_Y₀ h_Z₀ h_Z₁ h_Z₂ hf_diff ?_ hA_inj
  have hid := transported_radii_identity Y₀ Z₀ Z₁ Z₂ α β r₁
  rw [hr₀] at h_margin
  nlinarith [h_margin, hid, hβpos]

end TransportTheorem

/-! ## The ℚ gate: the reuse-or-reprove decision procedure

`gateQ` is the entire decision procedure: given the B-side certificate numbers
and the transport price κ = αβ, one rational-arithmetic check decides whether
the transported certificate closes. `gateQ_sound` connects a `true` verdict to
the hypothesis of `transport_radii_polynomial_of_margin`. -/

def gateQ (Y₀ Z₀ Z₁ Z₂ r₀ κ : ℚ) : Bool :=
  decide (κ * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + (κ - 1) * r₀ < 0)

theorem gateQ_sound {Y₀ Z₀ Z₁ Z₂ r₀ α β : ℚ}
    (h : gateQ Y₀ Z₀ Z₁ Z₂ r₀ (α * β) = true) :
    (α : ℝ) * (β : ℝ) *
        generalRadiiPolynomial (Y₀ : ℝ) (Z₀ : ℝ) (Z₁ : ℝ) (fun _ => (Z₂ : ℝ)) (r₀ : ℝ)
      + ((α : ℝ) * (β : ℝ) - 1) * (r₀ : ℝ) < 0 := by
  have hq : ((α * β) * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + ((α * β) - 1) * r₀ : ℚ) < 0 :=
    of_decide_eq_true h
  have hR : (((α * β) * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + ((α * β) - 1) * r₀ : ℚ) : ℝ)
      < 0 := by exact_mod_cast hq
  push_cast at hR
  simp only [generalRadiiPolynomial]
  linarith [hR]
