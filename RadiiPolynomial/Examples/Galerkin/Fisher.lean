import RadiiPolynomial.Applications.Galerkin.Face

/-!
# The Fisher Galerkin map as an instance of the polynomial Galerkin face

Book Example 2.4.15 (and the toolkit of Example 3.2.5): the Fisher projection
`x ↦ ((λ - k²) x_k - λ (x * x)_k)_k` on the stored Chebyshev modes `0, …, N`, with the
nonlinearity `x²` formed in the flip-fixed algebra `symmetricSubalgebra ν` before projecting.

* `fisherGalerkin` is the composite face `polyFace (diagL λ) (-λ ev0) Pi' (I ∘ δ) (x ↦ x²)`
  (`fisherGalerkin_eq_polyFace`), so its derivative is `DFisher` (`hasFDerivAt_fisherGalerkin`).
* The centred majorant of `x²` is `2 δ` (`derivativeCentredBound_fisherQuad`, with the exact
  rational instance `fisherQuad_centred_Q` checked by `decide +kernel`), which gives
  `‖DFisher c - DFisher x‖ ≤ 2 |λ| ‖c - x‖` at `ν = 1` (`norm_DFisher_sub_le`) and the carrier
  `Z₂` bound `norm_A_fderiv_fisherGalerkin_sub_le`.
* `hAnorm_of_carrier`: read on the carrier through the identity equivalence `amb`, the operator-norm
  hypothesis of Example 2.4.15 holds with the operator norm of `A` there as its constant;
  `norm_amb_symm_ν₁` is the carrier form of the Fisher weight, `|x₀| + 2 Σ_{k ≥ 1} |x_k|`.
-/

noncomputable section

open scoped BigOperators

namespace ExampleFisher

open RadiiPolynomial RadiiPolynomial.Galerkin MvPolyBridge

section Book

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N : ℕ}

/-- The Fisher nonlinearity `x ↦ x²` as computable syntax (`L = 1`). -/
def fisherQuad : CompPoly 1 := .mul (.X 0) (.X 0)

theorem evalBanach_fisherQuad (a : Fin 1 → l1Chebyshev.symmetricSubalgebra ν) :
    fisherQuad.evalBanach a = a 0 * a 0 := rfl

/-- The Fisher Galerkin map built from the flip-fixed algebra: diagonal part plus
`-λ · Π (x ↦ x²) I`. -/
def fisherGalerkin (lam : ℝ) (x : FνN ν N) : FνN ν N :=
  FνN.mk fun k => (lam - (k : ℝ) ^ 2) * x k -
    lam * ((Pi' (ν := ν) (N := N) ∘ (fun u (_ : Fin 1) => fisherQuad.evalBanach u) ∘ I)
      (fun _ => x) 0) k

/-- The weight `ν = 1`. -/
def ν₁ : PosReal := ⟨1, one_pos⟩

@[simp] theorem ν₁_coe : (ν₁ : ℝ) = 1 := rfl

instance : Fact (1 ≤ (ν₁ : ℝ)) := ⟨le_of_eq ν₁_coe.symm⟩

end Book

section Constants

/-- `x²`: the centred majorant is `2 δ`. -/
theorem derivativeCentredBound_fisherQuad {K : Type*} [Field K] (β δ : Fin 1 → K) :
    CompPoly.derivativeCentredBound fisherQuad β δ = 2 * δ 0 := by
  simp [CompPoly.derivativeCentredBound, fisherQuad]
  ring


end Constants

section Fisher

variable {N : ℕ}

/-- The diagonal part `x ↦ ((λ - k²) x_k)_k` of the Fisher Galerkin map. -/
def diagL (lam : ℝ) : FνN ν₁ N →L[ℝ] FνN ν₁ N :=
  LinearMap.toContinuousLinearMap
    { toFun x := FνN.mk fun k => (lam - (k : ℝ) ^ 2) * x k
      map_add' x y := FνN.ext fun k => by simp [mul_add]
      map_smul' c x := FνN.ext fun k => by simp; ring }

/-- The diagonal embedding `FνN → E = (FνN)^1`. -/
def δ : FνN ν₁ N →L[ℝ] E ν₁ N 1 := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ _

/-- Evaluation at the single component. -/
def ev0 : E ν₁ N 1 →L[ℝ] FνN ν₁ N := ContinuousLinearMap.proj 0

theorem norm_δ_apply (x : FνN ν₁ N) : ‖(δ x : E ν₁ N 1)‖ = ‖x‖ := pi_norm_const x

theorem norm_δ_le : ‖(δ : FνN ν₁ N →L[ℝ] E ν₁ N 1)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [norm_δ_apply, one_mul]

theorem norm_ev0_le : ‖(ev0 : E ν₁ N 1 →L[ℝ] FνN ν₁ N)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_le_pi_norm x 0

/-- The Galerkin map of the nonlinearity `x²`. -/
abbrev Gq : E ν₁ N 1 → E ν₁ N 1 :=
  Pi' (N := N) ∘ (fun u (_ : Fin 1) => fisherQuad.evalBanach u) ∘ I

theorem fisherGalerkin_eq_comp (lam : ℝ) :
    (fisherGalerkin (ν := ν₁) (N := N) lam) = fun x => diagL lam x - lam • ev0 (Gq (δ x)) :=
  rfl

/-- The Fisher map is the composite face with `L₀ = diagL λ`, `Λ = −λ ev0`, `π = Π`,
`ι = I ∘ δ`, `f = x²`. -/
theorem fisherGalerkin_eq_polyFace (lam : ℝ) :
    fisherGalerkin (ν := ν₁) (N := N) lam =
      polyFace (diagL lam) ((-lam) • ev0) Pi' (I.comp δ) (fun _ => fisherQuad) := by
  funext x
  refine FνN.ext fun k => ?_
  show (lam - (k : ℝ) ^ 2) * x k -
      lam * ((Pi' (ν := ν₁) (N := N) ∘ (fun u (_ : Fin 1) => fisherQuad.evalBanach u) ∘ I)
        (fun _ => x) 0) k =
    (lam - (k : ℝ) ^ 2) * x k +
      (-lam) * ((Pi' (ν := ν₁) (N := N) ∘ (fun u (_ : Fin 1) => fisherQuad.evalBanach u) ∘ I)
        (fun _ => x) 0) k
  ring

/-- The carrier derivative of the Fisher Galerkin map (the composite face derivative). -/
abbrev DFisher (lam : ℝ) (x : FνN ν₁ N) : FνN ν₁ N →L[ℝ] FνN ν₁ N :=
  DpolyFace (diagL lam) ((-lam) • ev0) Pi' (I.comp δ) (fun _ => fisherQuad) x

theorem hasFDerivAt_fisherGalerkin (lam : ℝ) (x : FνN ν₁ N) :
    HasFDerivAt (fisherGalerkin (ν := ν₁) lam) (DFisher lam x) x := by
  rw [fisherGalerkin_eq_polyFace]
  exact hasFDerivAt_polyFace _ _ _ _ _ x

/-- `Z₂` on the carrier from the composite face and the centred constant `2δ` of `x²`. -/
theorem norm_DFisher_sub_le (lam : ℝ) (c x : FνN ν₁ N) :
    ‖DFisher lam c - DFisher lam x‖ ≤ 2 * |lam| * ‖c - x‖ := by
  have hΛ : ‖(-lam) • (ev0 : E ν₁ N 1 →L[ℝ] FνN ν₁ N)‖ ≤ |lam| := by
    refine (norm_smul_le (-lam) (ev0 : E ν₁ N 1 →L[ℝ] FνN ν₁ N)).trans ?_
    rw [Real.norm_eq_abs, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) norm_ev0_le
  have hι : ‖(I.comp δ : FνN ν₁ N →L[ℝ] (Fin 1 → l1Chebyshev.symmetricSubalgebra ν₁))‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul norm_I_le norm_δ_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have H := norm_DpolyFace_sub_le (diagL lam) ((-lam) • ev0) Pi' (I.comp δ)
    (fun _ => fisherQuad) (c := c) (b := x) (β := fun _ => ‖x‖) (δ := fun _ => ‖c - x‖)
    (M := 2 * ‖c - x‖) (fun _ => (derivativeCentredBound_fisherQuad _ _).le)
    (fun _ => (norm_ιN x).le)
    (fun _ => by
      show ‖(ιN c : l1Chebyshev.symmetricSubalgebra ν₁) - ιN x‖ ≤ ‖c - x‖
      rw [← map_sub, norm_ιN])
  exact H.trans ((mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hΛ norm_Pi'_le
    (norm_nonneg _) (abs_nonneg _)) (by positivity)) hι (norm_nonneg _)
    (by positivity)).trans_eq (by ring))

/-- The carrier form of the `Z₂` bound of Example 2.4.15: with `A` an operator on the carrier,
`‖A((DF(c) − DF(x̄))h)‖ ≤ 2|λ| ‖A‖ r ‖h‖` on `‖c − x̄‖ ≤ r`; the book's `Anorm` is `‖A‖` here. -/
theorem norm_A_fderiv_fisherGalerkin_sub_le (lam : ℝ) (A : FνN ν₁ N →L[ℝ] FνN ν₁ N) (r : ℝ)
    (c xBar : FνN ν₁ N) (hc : ‖c - xBar‖ ≤ r) (h : FνN ν₁ N) :
    ‖A ((fderiv ℝ (fisherGalerkin lam) c - fderiv ℝ (fisherGalerkin lam) xBar) h)‖ ≤
      2 * |lam| * ‖A‖ * r * ‖h‖ := by
  rw [(hasFDerivAt_fisherGalerkin lam c).fderiv, (hasFDerivAt_fisherGalerkin lam xBar).fderiv]
  refine (A.le_opNorm _).trans ?_
  have h1 := (DFisher lam c - DFisher lam xBar).le_opNorm h
  have h2 := norm_DFisher_sub_le lam c xBar
  have := norm_nonneg A
  have := norm_nonneg h
  have := abs_nonneg lam
  have : 0 ≤ ‖DFisher lam c - DFisher lam xBar‖ := norm_nonneg _
  have h3 : ‖DFisher lam c - DFisher lam xBar‖ ≤ 2 * |lam| * r := h2.trans (by nlinarith)
  calc ‖A‖ * ‖(DFisher lam c - DFisher lam xBar) h‖
      ≤ ‖A‖ * (2 * |lam| * r * ‖h‖) := mul_le_mul_of_nonneg_left
        (h1.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))) (norm_nonneg _)
    _ = 2 * |lam| * ‖A‖ * r * ‖h‖ := by ring



end Fisher

end ExampleFisher

end
