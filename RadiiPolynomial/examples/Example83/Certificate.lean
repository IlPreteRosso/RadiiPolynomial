import RadiiPolynomial.examples.Example83.Algebra
import RadiiPolynomial.source.Tactic.PDerivSimp
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.Tactic.FinMatrixBound

/-!
# Example 8.3 — Certificate

Computer-assisted proof for the Lorenz IVP. Uses `data : StdIVPData` from Algebra.lean.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example83

noncomputable section

namespace Example83.Cert

/-! ## Z₀ -/

private def defectBlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  Array.ofFn fun (i : Fin (N + 1)) =>
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j i k

private lemma Array.getD_ofFn_fin {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

private lemma defectBlockCol_correct (l j : Fin L) (i k : Fin (N + 1)) :
    data.defect.finBlock l j i k = ((defectBlockCols l j k).getD (i : ℕ) 0 : ℝ) := by
  rw [defectBlockCols, Array.getD_ofFn_fin]
  have := blockDefectMatQ_correct
    (fun l m => data.A_finBlock l m) (fun m j => data.DF_finBlock m j)
    (fun l m (k : Fin (N + 1)) => A_col l m (k : ℕ))
    (fun m j (k : Fin (N + 1)) => DF_col m j (k : ℕ))
    (fun l m j i => by simp [IVP.StdIVPData.A_finBlock, data])
    (fun m j k i => by simp [IVP.StdIVPData.DF_finBlock, data])
    l j i k
  show ((if l = j then 1 else 0) - ∑ m, data.A_finBlock l m * data.DF_finBlock m j) i k = _
  exact this

lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val data.defect.finBlock ≤ (Z₀_bound : ℝ) := by
  finmatrix_bound
    (finiteBlockMatrixNorm_le_of_Q_le _ defectBlockCols ν_q
      (fun l j k i => defectBlockCol_correct l j i k) ν_val_eq_q)

/-! ## ‖A‖ bound -/

private def ABlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  A_col l j (k : ℕ)

lemma A_norm_le :
    ‖data.approxInverse.toCLM (ν := ν_val)‖ ≤
      (finiteBlockMatrixNormQ L N ABlockCols ν_q +
        IVP.StdIVPData.approxInverse_tailBound_q (N := N) : ℚ) := by
  finmatrix_bound
    (norm_toCLM_le_of_Q data.approxInverse ABlockCols ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N))
      (fun l j k i => data.A_finBlock_eq l j i k) ν_val_eq_q
      data.approxInverse_tailBound_eq)

/-! ## Y₀ bound -/

private noncomputable def F_abar : XL1 ν_val L :=
  ofCoeff (F data.abar) F_abar_mem

private lemma G_eq_toCLM_F_abar :
    data.G f x₀ data.abar = data.approxInverse.toCLM (ν := ν_val) F_abar := by
  funext l; apply l1Weighted.ext; intro n
  exact (data.G_coeff f x₀ data.abar l n).trans (by
    have := SystemBlockDiagData.toCoeff_toCLM (ν := ν_val) data.approxInverse F_abar l n
    simp only [toCoeff] at this; exact this.symm)

private lemma F_abar_toCoeff_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    toCoeff (ν := ν_val) F_abar l n = 0 := by
  simp [F_abar, toCoeff, ofCoeff, F,
    F_abar_support l n hn]

private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun l n => F_Q l n)
    (fun _l n => 1 / (n : ℚ)) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) :
    (|data.approxInverse.action (F data.abar) l n| * (ν_val : ℝ) ^ n : ℝ) ∈
      Y₀_eval l n {} :=
  systemBlockDiagActionEval_correct data.approxInverse (F data.abar)
    (fun l n => F_Q l n) ABlockCols (fun _l n => 1 / (n : ℚ)) ν_q
    (fun l j k i => data.A_finBlock_eq l j i k)
    (fun l n => F_bridge l n)
    (fun _l n hn => by simp [IVP.StdIVPData.approxInverse, if_neg (by omega : n ≠ 0)])
    ν_val_eq_q l n {}

lemma Y₀_le :
    Y₀_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  show ‖data.G f x₀ data.abar‖ ≤ _
  rw [G_eq_toCLM_F_abar]
  have hc : toCoeff (ν := ν_val) F_abar = F data.abar := by
    ext l n; simp [F_abar, toCoeff_ofCoeff]
  refine data.approxInverse.norm_toCLM_apply_le F_abar (2 * N + 1) (by omega)
    F_abar_toCoeff_support (by unfold Y₀_bound; positivity)
    (fun l => ?_)
  simp_rw [hc]; unfold Y₀_bound
  fin_cases l
  -- `finsum_bound` now requires a literal range endpoint, so unfold `N` first.
  all_goals simp only [N]
  all_goals finsum_bound using (Y₀_eval _) (fun k _ _ => Y₀_eval_correct _ k)

/-! ## Z₁ bound -/

private lemma Df_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Df h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
  have hpi : ∀ i : Fin L, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have hmul : ∀ (a b : l1Weighted ν_val), ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le
  have hC : (0 : ℝ) ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q : ℚ) := by unfold Z₁_bound ν_q N; norm_num
  fin_cases l
  · show ‖σ_val • (h 1 - h 0)‖ ≤ _
    have h1 : ‖σ_val • (h 1 - h 0)‖ ≤ |σ_val| * (‖h 1‖ + ‖h 0‖) :=
      (le_of_eq (norm_smul σ_val _)).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _))
    have h2 : |σ_val| * (‖h 1‖ + ‖h 0‖) ≤ 2 * |σ_val| * ‖h‖ :=
      (mul_le_mul_of_nonneg_left (add_le_add (hpi 1) (hpi 0)) (abs_nonneg _)).trans
        (by ring_nf; rfl)
    exact (h1.trans h2).trans (by
      unfold σ_val Z₁_bound ν_q N; push_cast; nlinarith [norm_nonneg h])
  · show ‖ρ_val • h 0 - h 1 - (data.abar 0 * h 2 + h 0 * data.abar 2)‖ ≤ _
    have h1 : ‖ρ_val • h 0 - h 1 - (data.abar 0 * h 2 + h 0 * data.abar 2)‖ ≤
        |ρ_val| * ‖h‖ + ‖h‖ + ‖data.abar 0‖ * ‖h‖ + ‖data.abar 2‖ * ‖h‖ := by
      have := norm_sub_le (ρ_val • h 0 - h 1) (data.abar 0 * h 2 + h 0 * data.abar 2)
      have := norm_sub_le (ρ_val • h 0) (h 1)
      have := norm_add_le (data.abar 0 * h 2) (h 0 * data.abar 2)
      have := (norm_smul ρ_val (h 0)).symm ▸ mul_le_mul_of_nonneg_left (hpi 0) (abs_nonneg ρ_val)
      nlinarith [hpi 1, hmul (data.abar 0) (h 2), hmul (h 0) (data.abar 2),
        hpi 2, hpi 0, norm_nonneg (data.abar 0), norm_nonneg (data.abar 2)]
    exact h1.trans (by
      have h4 : |ρ_val| = ρ_val := abs_of_nonneg (by unfold ρ_val; positivity)
      rw [h4]; unfold ρ_val Z₁_bound ν_q N; push_cast
      nlinarith [abar_norm_0_le, abar_norm_2_le, norm_nonneg h])
  · show ‖-(β_val • h 2) + (data.abar 0 * h 1 + h 0 * data.abar 1)‖ ≤ _
    have h1 : ‖-(β_val • h 2) + (data.abar 0 * h 1 + h 0 * data.abar 1)‖ ≤
        |β_val| * ‖h‖ + ‖data.abar 0‖ * ‖h‖ + ‖data.abar 1‖ * ‖h‖ := by
      have := norm_add_le (-(β_val • h 2)) (data.abar 0 * h 1 + h 0 * data.abar 1)
      have := norm_add_le (data.abar 0 * h 1) (h 0 * data.abar 1)
      have := (norm_neg (β_val • h 2)).symm ▸ (norm_smul β_val (h 2)).symm ▸
        mul_le_mul_of_nonneg_left (hpi 2) (abs_nonneg β_val)
      nlinarith [hmul (data.abar 0) (h 1), hmul (h 0) (data.abar 1),
        hpi 1, hpi 0, norm_nonneg (data.abar 0), norm_nonneg (data.abar 1)]
    exact h1.trans (by
      have h4 : |β_val| = β_val := abs_of_nonneg (by unfold β_val; positivity)
      rw [h4]; unfold β_val Z₁_bound ν_q N; push_cast
      nlinarith [abar_norm_0_le, abar_norm_1_le, norm_nonneg h])

lemma Z₁_le_cert :
    Z₁_norm (data.G f x₀) data.abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (data.composedApprox.toCLM (ν := ν_val)) ≤ (Z₁_bound : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (data.composedApprox.toCLM (ν := ν_val) -
      fderiv ℝ (data.G f x₀) data.abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  have hfin : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((data.composedApprox.toCLM (ν := ν_val) -
        fderiv ℝ (data.G f x₀) data.abar) h) l) n = 0 :=
    fun h l n hn => by
      simp only [sub_apply, Pi.sub_apply, l1Weighted.sub_toSeq, sub_eq_zero]
      exact composedApprox_eq_fderiv_G_fin h l n hn
  have htail : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((data.composedApprox.toCLM (ν := ν_val) -
        fderiv ℝ (data.G f x₀) data.abar) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Df h l)) n :=
    fun h l n hn => by
      have hc := data.composedApprox_toCLM_tail h l n hn
      have hf := fderiv_G_lorenz_tail h l n hn
      simp only [sub_apply, Pi.sub_apply, l1Weighted.sub_toSeq]
      show toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n -
          toCoeff (ν := ν_val) ((fderiv ℝ (data.G f x₀) data.abar) h) l n = _
      rw [hc, hf]; simp [toCoeff]
  exact IVP.ivp_Z₁_le data.composedApprox (data.G f x₀) data.abar Df hfin htail
    (by unfold Z₁_bound ν_q N; norm_num) Df_norm_le
    (by simp only [ν_val_eq_q]; unfold Z₁_bound ν_q N; push_cast; ring_nf; rfl)

/-! ## Z₂ bound -/

/-- System-level second pderiv Hessian table for Lorenz. -/
private def D₂_lorenz (l i j : Fin L) : ℚ :=
  if l = 1 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) then -1
  else if l = 2 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then 1
  else 0

private lemma hD₂_lorenz : ∀ (l i j : Fin L),
    MvPolynomial.pderiv j (MvPolynomial.pderiv i (f_spec l)) =
      MvPolynomial.C (D₂_lorenz l i j) := by
  intro l i j
  unfold f_spec
  fin_cases l <;> fin_cases i <;> fin_cases j <;>
    rw [← MvPolyBridge.CompPoly.pderiv_pderiv_toMvPoly] <;>
    simp (config := { decide := true }) [f_cpoly, D₂_lorenz]

private lemma Df_diff_norm_le (c : XL1 ν_val L) (h : XL1 ν_val L) (l : Fin L) :
    ‖((fderiv ℝ (fun x => f x l) c -
      fderiv ℝ (fun x => f x l) data.abar)) h‖ ≤ 2 * ‖c - data.abar‖ * ‖h‖ := by
  simp_rw [show ∀ x, f x l = MvPolyBridge.evalInBanach (f_spec l) x
    from fun x => f_eq_spec x l]
  exact MvPolyBridge.norm_fderiv_diff_system_of_const_second_pderiv f_spec c data.abar
    D₂_lorenz hD₂_lorenz
    (fun l => by
      fin_cases l <;>
        simp (config := { decide := true }) [D₂_lorenz, Fin.sum_univ_three, L] <;>
        norm_num)
    h l

lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (fderiv ℝ (data.G f x₀) c -
      fderiv ℝ (data.G f x₀) data.abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  exact IVP.ivp_Z₂_le data.approxInverse f x₀
    (IVP.ivpMap_mem_of_tailDiag_inv _ _ _ data.htail_diag_inv) data.abar
    (data.differentiable_G f x₀ differentiable_f_component)
    (fun l => differentiable_f_component l)
    ({1, 2} : Finset (Fin L))
    -- hzero: inactive component (l=0) has zero fderiv diff — derived from D₂
    (fun c h j hj => by
      have : j = 0 := by fin_cases j <;> simp_all (config := { decide := true })
      subst this
      simp_rw [show ∀ x, f x 0 = MvPolyBridge.evalInBanach (f_spec 0) x
        from fun x => f_eq_spec x 0]
      exact MvPolyBridge.fderiv_diff_zero_of_D₂_zero f_spec c data.abar
        D₂_lorenz hD₂_lorenz 0 (fun i j => by fin_cases i <;> fin_cases j <;> rfl) h)
    (by norm_num : (0 : ℝ) ≤ 2) Df_diff_norm_le
    (by unfold Z₂_bound; positivity)
    (fun l => Z₂_blockNorm_component_le data.approxInverse ABlockCols ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N)) {1, 2}
      (fun l j k i => data.A_finBlock_eq l j i k) ν_val_eq_q
      data.approxInverse_tailBound_eq (by native_decide) l)
    c hc

/-! ## Radii polynomial -/

private lemma radii_neg_icc :
    ∀ r ∈ Set.Icc (r_minus : ℝ) (r_minus : ℝ),
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) r < 0 := by
  unfold generalRadiiPolynomial Y₀_bound Z₀_bound Z₁_bound Z₂_bound r_minus
  leancert

lemma radii_neg :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 :=
  radii_neg_icc _ ⟨le_refl _, le_refl _⟩

/-! ## Main theorem -/

theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      data.G f x₀ xTilde = 0 :=
  data.existsUnique f x₀ differentiable_f_component
    (by unfold r_minus; positivity)
    (Y₀_le.trans (by unfold Y₀_bound; exact_mod_cast le_refl _))
    (data.Z₀_le Z₀_finBlockNorm_le)
    (Z₁_le_cert.trans (by unfold Z₁_bound; exact_mod_cast le_refl _))
    (fun c hc => Z₂_le_cert c hc)
    radii_neg

/-- Source-residual form of `main_theorem`: the unique validated point solves the
unpreconditioned IVP Taylor coefficient equations. -/
theorem ivp_main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      ∀ l n, IVP.ivpCoeffs f x₀ xTilde l n = 0 :=
  data.existsUnique_ivpCoeffs f x₀ differentiable_f_component
    (by unfold r_minus; positivity)
    (Y₀_le.trans (by unfold Y₀_bound; exact_mod_cast le_refl _))
    Z₀_finBlockNorm_le
    (Z₁_le_cert.trans (by unfold Z₁_bound; exact_mod_cast le_refl _))
    (fun c hc => Z₂_le_cert c hc)
    radii_neg

end Example83.Cert
