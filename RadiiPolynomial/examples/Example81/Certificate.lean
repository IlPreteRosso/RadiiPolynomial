import RadiiPolynomial.examples.Example81.Algebra
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.Tactic.FinMatrixBound

/-!
# Example 8.1 — Certificate

Computer-assisted proof for the scalar IVP:
  x' = x(x-1), x(0) = 1/2, N=10, ν=1

Uses `data : StdIVPData` from Algebra.lean for all standard constructions.

## Key simplification

The approximate inverse is the **exact** inverse of DF^(N)(ā) in ℚ, so the defect is
identically zero and Z₀ = 0.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example81

noncomputable section

namespace Example81.Cert

/-! ## Z₀ — Defect bound (exact inverse → zero defect) -/

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

/-! ## ‖A‖ bound (for Z₂) -/

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

/-! ## Y₀ bound: ‖G(ābar)‖ ≤ Y₀_bound -/

private noncomputable def F_abar : XL1 ν_val L :=
  ofCoeff (F_coeffs data.abar) F_coeffs_abar_mem

private lemma G_eq_toCLM_F_abar :
    data.G φ_scalar x₀ data.abar = data.approxInverse.toCLM (ν := ν_val) F_abar := by
  funext l; apply lpWeighted.ext; intro n
  exact (data.G_coeff φ_scalar x₀ data.abar l n).trans (by
    have := SystemBlockDiagData.toCoeff_toCLM (ν := ν_val) data.approxInverse F_abar l n
    simp only [toCoeff] at this; exact this.symm)

private lemma F_abar_toCoeff_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    toCoeff (ν := ν_val) F_abar l n = 0 := by
  simp [F_abar, toCoeff, ofCoeff, lpWeighted.mk, F_coeffs,
    F_coeffs_abar_support l n hn]

private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun _l n => F_coeffs_Q n)
    (fun _l n => 1 / (n : ℚ)) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) :
    (|data.approxInverse.action (F_coeffs data.abar) l n| * (ν_val : ℝ) ^ n : ℝ) ∈
      Y₀_eval l n {} :=
  systemBlockDiagActionEval_correct data.approxInverse (F_coeffs data.abar)
    (fun _l n => F_coeffs_Q n) ABlockCols (fun _l n => 1 / (n : ℚ)) ν_q
    (fun l j k i => data.A_finBlock_eq l j i k)
    (fun l n => F_coeffs_bridge l n)
    (fun _l n hn => by simp [IVP.StdIVPData.approxInverse, if_neg (by omega : n ≠ 0)])
    ν_val_eq_q l n {}

lemma Y₀_le :
    Y₀_norm (data.G φ_scalar x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  show ‖data.G φ_scalar x₀ data.abar‖ ≤ _
  rw [G_eq_toCLM_F_abar]
  have hc : toCoeff (ν := ν_val) F_abar = F_coeffs data.abar := by
    ext l n; simp [F_abar, toCoeff_ofCoeff]
  refine data.approxInverse.norm_toCLM_apply_le F_abar (2 * N + 1) (by omega)
    F_abar_toCoeff_support (by unfold Y₀_bound; positivity)
    (fun l => ?_)
  simp_rw [hc]; unfold Y₀_bound
  have hl : l = 0 := Subsingleton.elim l 0; subst hl
  finsum_bound using (Y₀_eval 0) (fun k _ _ => Y₀_eval_correct 0 k)

/-! ## Z₁ bound -/

/-- Dφ operator norm: ‖Dφ(h)₀‖ ≤ K*‖h‖ where K = ‖2ā₀-1‖. -/
private lemma Dφ_scalar_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Dφ_scalar h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
  have hl : l = 0 := Subsingleton.elim l 0; subst hl
  show ‖2 • (data.abar 0 * h 0) - h 0‖ ≤ _
  have heq : 2 • (data.abar 0 * h 0) - h 0 = (2 • data.abar 0 - 1) * h 0 := by ring
  rw [heq]
  have hpi := norm_le_pi_norm h (0 : Fin L)
  suffices hK : ‖2 • data.abar 0 - (1 : l1Weighted ν_val)‖ ≤ ((396482 / 725760 : ℚ) : ℝ) by
    calc ‖(2 • data.abar 0 - 1) * h 0‖
        ≤ ‖2 • data.abar 0 - (1 : l1Weighted ν_val)‖ * ‖h 0‖ := norm_mul_le _ _
      _ ≤ ((396482 / 725760 : ℚ) : ℝ) * ‖h 0‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ ((396482 / 725760 : ℚ) : ℝ) * ‖h‖ :=
          mul_le_mul_of_nonneg_left hpi (by norm_num)
      _ ≤ ((Z₁_bound * ((N : ℚ) + 1) / ν_q : ℚ) : ℝ) * ‖h‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact_mod_cast show (396482 : ℚ) / 725760 ≤ Z₁_bound * ((N : ℚ) + 1) / ν_q by
            norm_num [Z₁_bound, N, ν_q]
      _ = ↑Z₁_bound * (↑↑N + 1) / ↑ν_q * ‖h‖ := by push_cast; ring
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N two_abar_sub_one_support]
  show _ ≤ ((396482 / 725760 : ℚ) : ℝ)
  finsum_bound using
    (weightedTermEval two_abar_sub_one_Q ν_q)
    (fun k _ _ => weightedTermEval_correct two_abar_sub_one_Q ν_q k {}
      (hprec := by norm_num)
      (hf := two_abar_sub_one_toSeq k)
      (hν := ν_val_eq_q))

lemma Z₁_le_cert :
    Z₁_norm (data.G φ_scalar x₀) data.abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (data.composedApprox.toCLM (ν := ν_val)) ≤ (Z₁_bound : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (data.composedApprox.toCLM (ν := ν_val) -
      fderiv ℝ (data.G φ_scalar x₀) data.abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  have hfin : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((data.composedApprox.toCLM (ν := ν_val) -
        fderiv ℝ (data.G φ_scalar x₀) data.abar) h) l) n = 0 :=
    fun h l n hn => by
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, lpWeighted.sub_toSeq, sub_eq_zero]
      exact composedApprox_eq_fderiv_G_fin h l n hn
  have htail : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((data.composedApprox.toCLM (ν := ν_val) -
        fderiv ℝ (data.G φ_scalar x₀) data.abar) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ_scalar h l)) n :=
    fun h l n hn => by
      have hc := data.composedApprox_toCLM_tail h l n hn
      have hf := fderiv_G_scalar_tail h l n hn
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, lpWeighted.sub_toSeq]
      show toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n -
          toCoeff (ν := ν_val) ((fderiv ℝ (data.G φ_scalar x₀) data.abar) h) l n = _
      rw [hc, hf]; simp [toCoeff]
  exact IVP.ivp_Z₁_le data.composedApprox (data.G φ_scalar x₀) data.abar Dφ_scalar hfin htail
    (by unfold Z₁_bound ν_q N; norm_num) Dφ_scalar_norm_le
    (by simp only [ν_val_eq_q]; norm_num [Z₁_bound, ν_q, N])

/-! ## Z₂ bound -/

private lemma Dφ_diff_norm_le (c : XL1 ν_val L) (h : XL1 ν_val L) (l : Fin L) :
    ‖((fderiv ℝ (fun x => φ_scalar x l) c -
      fderiv ℝ (fun x => φ_scalar x l) data.abar)) h‖ ≤ 2 * ‖c - data.abar‖ * ‖h‖ := by
  have hl : l = 0 := Subsingleton.elim l 0; subst hl
  simp_rw [show ∀ x, φ_scalar x 0 = MvPolyBridge.evalInBanach (φ_scalar_spec 0) x
    from fun x => φ_scalar_eq_spec x 0]
  exact MvPolyBridge.norm_fderiv_diff_evalInBanach_of_const_second_pderiv _ c data.abar h
    (D₂ := fun _ _ => 2)
    (by intro i j; fin_cases i <;> fin_cases j <;> (simp [φ_scalar_spec]; try norm_cast))
    (by norm_num)

lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm (data.G φ_scalar x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (fderiv ℝ (data.G φ_scalar x₀) c -
      fderiv ℝ (data.G φ_scalar x₀) data.abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  exact IVP.ivp_Z₂_le data.approxInverse (data.G φ_scalar x₀) φ_scalar x₀ data.abar
    (data.differentiable_G φ_scalar x₀ differentiable_φ_scalar_component)
    (fun l => differentiable_φ_scalar_component l)
    (data.G_coeff φ_scalar x₀) ({0} : Finset (Fin L))
    (fun c h j hj => by
      have : j = 0 := Subsingleton.elim j 0
      subst this; simp at hj)
    (by norm_num : (0 : ℝ) ≤ 2) Dφ_diff_norm_le
    (by unfold Z₂_bound; positivity)
    (fun l => Z₂_blockNorm_component_le data.approxInverse ABlockCols ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N)) {0}
      (fun l j k i => data.A_finBlock_eq l j i k) ν_val_eq_q
      data.approxInverse_tailBound_eq (by native_decide) l)
    c hc

/-! ## Radii polynomial -/

private lemma radii_neg_icc :
    ∀ r ∈ Set.Icc (r_minus : ℝ) (r_minus : ℝ),
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) r < 0 := by
  unfold generalRadiiPolynomial Y₀_bound Z₀_bound Z₁_bound Z₂_bound r_minus
  fast_bound

lemma radii_neg :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 :=
  radii_neg_icc _ ⟨le_refl _, le_refl _⟩

/-! ## Main theorem -/

/-- **Theorem 8.1.7** (Scalar IVP): There exists a unique zero of the composed IVP map
G = A ∘ F near the approximate solution ābar, proving existence and uniqueness
of the ODE solution x(t) = Σ aₙtⁿ as a Taylor series on |t| < 1. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      data.G φ_scalar x₀ xTilde = 0 :=
  data.existsUnique φ_scalar x₀ differentiable_φ_scalar_component
    (by unfold r_minus; positivity)
    (Y₀_le.trans (by unfold Y₀_bound; exact_mod_cast le_refl _))
    (data.Z₀_le Z₀_finBlockNorm_le)
    (Z₁_le_cert.trans (by unfold Z₁_bound; exact_mod_cast le_refl _))
    (fun c hc => Z₂_le_cert c hc)
    radii_neg

end Example81.Cert
