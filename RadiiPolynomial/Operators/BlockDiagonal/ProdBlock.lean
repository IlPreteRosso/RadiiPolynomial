import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Block norms of operators between binary products

Under the max norm on `E₁ × E₂` and `F₁ × F₂`, an operator `T : E₁ × E₂ →L[𝕜] F₁ × F₂` has norm at
most the larger of its two row sums of block norms (`opNorm_le_max_block`); `opNorm_le_max_of_rows`
is the same bound from four pointwise block bounds. The statements are carrier-free; the eigenpair
faces of `Applications/Fourier/Eigenpair` read them on `Y = XR × ℝ`.
-/

noncomputable section

namespace RadiiPolynomial

section BlockNorm

/-! ### The product block-norm lemma under the max norm (no index) -/

/-- A row splits into its two columns: `‖R‖ ≤ ‖R ∘ inl‖ + ‖R ∘ inr‖`. -/
private theorem opNorm_le_add_inl_inr {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F] (R : E₁ × E₂ →L[𝕜] F) :
    ‖R‖ ≤ ‖R ∘L ContinuousLinearMap.inl 𝕜 E₁ E₂‖ + ‖R ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂‖ := by
  have hR : R = (R ∘L ContinuousLinearMap.inl 𝕜 E₁ E₂) ∘L ContinuousLinearMap.fst 𝕜 E₁ E₂ +
      (R ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂) ∘L ContinuousLinearMap.snd 𝕜 E₁ E₂ :=
    ContinuousLinearMap.ext fun x => by
      rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.mk_add_mk, add_zero,
        zero_add]
  refine (congrArg norm hR).trans_le ((ContinuousLinearMap.opNorm_add_le _ _).trans
    (add_le_add ?_ ?_))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le 𝕜 E₁ E₂))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le 𝕜 E₁ E₂))

/-- Under the max norm on both products, an operator `E₁ × E₂ → F₁ × F₂` has norm
at most the larger of its two row sums of block norms. -/
theorem opNorm_le_max_block {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup F₁]
    [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F₁]
    [NormedSpace 𝕜 F₂] (T : E₁ × E₂ →L[𝕜] F₁ × F₂) :
    ‖T‖ ≤ max (‖ContinuousLinearMap.fst 𝕜 F₁ F₂ ∘L T ∘L ContinuousLinearMap.inl 𝕜 E₁ E₂‖ +
        ‖ContinuousLinearMap.fst 𝕜 F₁ F₂ ∘L T ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂‖)
      (‖ContinuousLinearMap.snd 𝕜 F₁ F₂ ∘L T ∘L ContinuousLinearMap.inl 𝕜 E₁ E₂‖ +
        ‖ContinuousLinearMap.snd 𝕜 F₁ F₂ ∘L T ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂‖) := by
  have hT :
      T = (ContinuousLinearMap.fst 𝕜 F₁ F₂ ∘L T).prod (ContinuousLinearMap.snd 𝕜 F₁ F₂ ∘L T) :=
    ContinuousLinearMap.ext fun _ => rfl
  refine (congrArg norm hT).trans_le ?_
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  refine max_le_max ((opNorm_le_add_inl_inr _).trans_eq ?_) ((opNorm_le_add_inl_inr _).trans_eq ?_)
  · rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  · rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]

/-- The row form of `opNorm_le_max_block`: bounds on the four blocks `T (x, 0)`, `T (0, y)`,
read in each output coordinate, with nonnegative constants. -/
theorem opNorm_le_max_of_rows {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup F₁]
    [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F₁]
    [NormedSpace 𝕜 F₂] (T : E₁ × E₂ →L[𝕜] F₁ × F₂) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (h₁₁ : ∀ x, ‖(T (x, 0)).1‖ ≤ a * ‖x‖)
    (h₁₂ : ∀ y, ‖(T (0, y)).1‖ ≤ b * ‖y‖) (h₂₁ : ∀ x, ‖(T (x, 0)).2‖ ≤ c * ‖x‖)
    (h₂₂ : ∀ y, ‖(T (0, y)).2‖ ≤ d * ‖y‖) : ‖T‖ ≤ max (a + b) (c + d) :=
  (opNorm_le_max_block T).trans (max_le_max
    (add_le_add (ContinuousLinearMap.opNorm_le_bound _ ha h₁₁)
      (ContinuousLinearMap.opNorm_le_bound _ hb h₁₂))
    (add_le_add (ContinuousLinearMap.opNorm_le_bound _ hc h₂₁)
      (ContinuousLinearMap.opNorm_le_bound _ hd h₂₂)))

end BlockNorm

end RadiiPolynomial

end
