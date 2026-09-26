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

/-! ## Pulled-back norms and isometric transport

Engine-level transport along continuous linear equivalences and isometries (namespace
`RadiiPolynomial`; any normed spaces, local hypotheses only):
* `hasFDerivAt_conj` / `fderiv_conj_apply` — a map read through continuous linear equivalences
  on both sides has the conjugated derivative;
* `Z₂_transport` / `Z₂_transport_lip` — a carrier bound `‖DF z − DF x̄‖ ≤ Z` on a ball, read on
  the other side through `e` against a pulled-back norm `W y = ‖e.symm y‖` (a weighted norm carried
  as a plain function) and an operator bound `W (A y) ≤ Anorm · W y`;
* `rp_transport_local` — the local general radii polynomial theorem in pointwise form through a
  pulled-back norm onto a finite-dimensional space;
* `existsUnique_zero_transport(_linear)` — a unique zero in a closed ball transports along an
  isometric equivalence.
-/

namespace RadiiPolynomial

section PulledBackNorms

variable {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **Derivative transport.** A map read through continuous linear equivalences on both sides
has the conjugated derivative. -/
theorem hasFDerivAt_conj (e : E ≃L[ℝ] E') (e' : F ≃L[ℝ] F') {g : E → F} {D : E →L[ℝ] F}
    {x : E'} (hg : HasFDerivAt g D (e.symm x)) :
    HasFDerivAt (e' ∘ g ∘ e.symm) ((e' : F →L[ℝ] F').comp (D.comp (e.symm : E' →L[ℝ] E))) x :=
  e'.hasFDerivAt.comp x (hg.comp x e.symm.hasFDerivAt)

/-- Pointwise form of `hasFDerivAt_conj`. -/
theorem fderiv_conj_apply (e : E ≃L[ℝ] E') (e' : F ≃L[ℝ] F') {g : E → F} {D : E →L[ℝ] F}
    {x : E'} (hg : HasFDerivAt g D (e.symm x)) (h : E') :
    fderiv ℝ (e' ∘ g ∘ e.symm) x h = e' (D (e.symm h)) := by
  rw [(hasFDerivAt_conj e e' hg).fderiv]
  rfl

/-- **`Z₂` transport, local centred form.** A carrier bound `‖DF z − DF x̄‖ ≤ Z` for `z` in the
ball `‖z − x̄‖ ≤ r` only (with `HasFDerivAt` only there), read on `E'` through `e`, against a
pulled-back norm `W y = ‖e.symm y‖` and an operator bound `W (A y) ≤ Anorm · W y`. No global
quantifier: `0 ≤ Z` is read off the hypothesis at `c` itself, and a negative `Anorm` forces
`W h = 0` through `hA`. -/
theorem Z₂_transport (e : E ≃L[ℝ] E') {W : E' → ℝ} (hW : ∀ y, W y = ‖e.symm y‖)
    {F₀ : E → E} {DF : E → E →L[ℝ] E} {r : ℝ} {xBar : E'}
    (hF : ∀ z, ‖z - e.symm xBar‖ ≤ r → HasFDerivAt F₀ (DF z) z) {Z : ℝ}
    (hZ : ∀ z, ‖z - e.symm xBar‖ ≤ r → ‖DF z - DF (e.symm xBar)‖ ≤ Z) (A : E' →L[ℝ] E')
    {Anorm : ℝ} (hA : ∀ y, W (A y) ≤ Anorm * W y) {c : E'} (hc : W (c - xBar) ≤ r) (h : E') :
    W (A ((fderiv ℝ (e ∘ F₀ ∘ e.symm) c - fderiv ℝ (e ∘ F₀ ∘ e.symm) xBar) h)) ≤
      Anorm * Z * W h := by
  have hd : ‖e.symm c - e.symm xBar‖ ≤ r := by rw [← map_sub, ← hW]; exact hc
  have h0 : ‖e.symm xBar - e.symm xBar‖ ≤ r := by
    rw [sub_self, norm_zero]; exact (norm_nonneg _).trans hd
  set v := (fderiv ℝ (e ∘ F₀ ∘ e.symm) c - fderiv ℝ (e ∘ F₀ ∘ e.symm) xBar) h with hv_def
  have hv : W v = ‖(DF (e.symm c) - DF (e.symm xBar)) (e.symm h)‖ := by
    rw [hW, hv_def, sub_apply, fderiv_conj_apply e e (hF _ hd),
      fderiv_conj_apply e e (hF _ h0), ← map_sub, ContinuousLinearEquiv.symm_apply_apply,
      sub_apply]
  have hZc := hZ _ hd
  have hWv : W v ≤ Z * W h := by
    rw [hv, hW h]
    exact ((DF _ - DF _).le_opNorm _).trans (mul_le_mul_of_nonneg_right hZc (norm_nonneg _))
  have hW0 : ∀ y, 0 ≤ W y := fun y => (hW y).symm ▸ norm_nonneg _
  rcases le_or_gt 0 Anorm with hA0 | hA0
  · rw [mul_assoc]
    exact (hA v).trans (mul_le_mul_of_nonneg_left hWv hA0)
  · have hh : W h = 0 := le_antisymm (by nlinarith [hA h, hW0 (A h), hW0 h]) (hW0 h)
    rw [hh, mul_zero]
    nlinarith [hA v, hW0 v, hW0 (A v)]

/-- **`Z₂` transport, local Lipschitz shape.** `‖DF z − DF x̄‖ ≤ K ‖z − x̄‖` on the ball only,
with an explicit `0 ≤ K`. -/
theorem Z₂_transport_lip (e : E ≃L[ℝ] E') {W : E' → ℝ} (hW : ∀ y, W y = ‖e.symm y‖)
    {F₀ : E → E} {DF : E → E →L[ℝ] E} {r : ℝ} {xBar : E'}
    (hF : ∀ z, ‖z - e.symm xBar‖ ≤ r → HasFDerivAt F₀ (DF z) z) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z, ‖z - e.symm xBar‖ ≤ r → ‖DF z - DF (e.symm xBar)‖ ≤ K * ‖z - e.symm xBar‖)
    (A : E' →L[ℝ] E') {Anorm : ℝ} (hA : ∀ y, W (A y) ≤ Anorm * W y) {c : E'}
    (hc : W (c - xBar) ≤ r) (h : E') :
    W (A ((fderiv ℝ (e ∘ F₀ ∘ e.symm) c - fderiv ℝ (e ∘ F₀ ∘ e.symm) xBar) h)) ≤
      K * Anorm * r * W h :=
  (Z₂_transport e hW hF (Z := K * r) (fun z hz => (hK z hz).trans
    (mul_le_mul_of_nonneg_left hz hK0)) A hA hc h).trans_eq (by ring)

end PulledBackNorms

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

/-- The linear-isometry form of `existsUnique_zero_transport` (any `E ≃ₗᵢ[ℝ] E'`). -/
theorem existsUnique_zero_transport_linear {E E' M N : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E'] [NormedSpace ℝ E] [NormedSpace ℝ E'] [Zero M] [Zero N]
    (e : E ≃ₗᵢ[ℝ] E') {F : E → M} {g : E' → N} (hFg : ∀ x, g (e x) = 0 ↔ F x = 0) {c : E}
    {r : ℝ} (h : ∃! x ∈ closedBall c r, F x = 0) : ∃! y ∈ closedBall (e c) r, g y = 0 :=
  existsUnique_zero_transport e.toIsometryEquiv hFg h

end IsometricTransport

end RadiiPolynomial
