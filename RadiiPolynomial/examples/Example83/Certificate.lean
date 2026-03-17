import RadiiPolynomial.examples.Example83.Algebra
import RadiiPolynomial.source.WitnessSpec
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.Tactic.FinMatrixBound

/-!
# Example 8.3 — Certificate

Computer-assisted proof for the Lorenz IVP:
  ẋ = f(x), x(0) = (1,0,0), σ=10, ρ=28, β=8/3, N=30, ν=3/20

## Architecture

Z₀ uses `defectOfBlockDiagOp` (zero tail) + per-block `finWeightedMatrixNorm_le_via_cols`.
Each defect block (l,j) = δ_{l,j}·I - ∑_m A_{l,m}·DF_{m,j} is computed in ℚ.

Y₀, Z₁, Z₂ require F_lorenz (TODO in Algebra.lean).
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example83

noncomputable section

namespace Example83.Cert

/-! ## Z₀ infrastructure — defect block columns via defectMatQ

For each block (l,j), the defect = δ_{l,j}·I - Σ_m A[l,m]·DF[m,j].
Each block product Σ_m A[l,m]·DF[m,j] is computed in ℚ via `defectMatQ` per-block. -/

/-- Column k of block defect (l,j) via `blockDefectMatQ`. -/
private def defectBlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  Array.ofFn fun (i : Fin (N + 1)) =>
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j i k

/-- `Array.getD` of `Array.ofFn` reduces when index is in range. -/
private lemma Array.getD_ofFn_fin {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

/-- Bridge: defect finBlock entries = ℚ-cast of defectBlockCols. -/
private lemma defectBlockCol_correct (l j : Fin L) (i k : Fin (N + 1)) :
    defect.finBlock l j i k = ((defectBlockCols l j k).getD (i : ℕ) 0 : ℝ) := by
  rw [defectBlockCols, Array.getD_ofFn_fin]
  -- Bridge: defect.finBlock = (if l=j then I else 0) - Σ_m A_finBlock * DF_finBlock
  -- And blockDefectMatQ computes the same from ℚ column arrays
  have := blockDefectMatQ_correct
    (fun l m => A_finBlock l m) (fun m j => DF_finBlock m j)
    (fun l m (k : Fin (N + 1)) => A_col l m (k : ℕ))
    (fun m j (k : Fin (N + 1)) => DF_col m j (k : ℕ))
    (fun l m j i => by simp [A_finBlock])
    (fun m j k i => by simp [DF_finBlock])
    l j i k
  show ((if l = j then 1 else 0) - ∑ m, A_finBlock l m * DF_finBlock m j) i k = _
  exact this

/-- Z₀ bound: finiteBlockMatrixNorm(defect) ≤ Z₀_bound.
Single `native_decide` via `finmatrix_bound` (replaces 9 per-block calls). -/
lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val defect.finBlock ≤ (Z₀_bound : ℝ) := by
  finmatrix_bound
    (finiteBlockMatrixNorm_le_of_Q_le _ defectBlockCols ν_q
      (fun l j k i => defectBlockCol_correct l j i k) ν_val_eq_q)

/-! ## ‖A‖ bound (needed for Z₂)

‖A.toCLM‖ ≤ finiteBlockMatrixNormQ(blockCols) + tailBound — computed, no named intermediate. -/

/-- Block columns of A.finBlock for `finmatrix_bound`. -/
private def ABlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  A_col l j (k : ℕ)

/-- ‖A.toCLM‖ bound — all intermediate values computed from data. -/
lemma A_norm_le :
    ‖approxInverse.toCLM (ν := ν_val)‖ ≤
      (finiteBlockMatrixNormQ L N ABlockCols ν_q + approxInverse_tailBound_q : ℚ) := by
  finmatrix_bound
    (norm_toCLM_le_of_Q approxInverse ABlockCols ν_q approxInverse_tailBound_q
      (fun l j k i => A_finBlock_eq l j i k) ν_val_eq_q approxInverse_tailBound_eq)

/-! ## Y₀ bound: ‖G_lorenz(ābar)‖ ≤ Y₀_bound

Uses ℚ bridges from Algebra.lean + `systemBlockDiagActionEval` for per-component evaluation. -/

/-- Embed F_coeffs(ābar) as an XL1 element. -/
private noncomputable def F_abar : XL1 ν_val L :=
  ofCoeff (F_coeffs abar) F_coeffs_abar_mem

/-- G_lorenz(ābar) = A.toCLM(F_abar). -/
private lemma G_lorenz_eq_toCLM_F_abar :
    G_lorenz abar = approxInverse.toCLM (ν := ν_val) F_abar := by
  funext l; apply lpWeighted.ext; intro n
  exact (G_lorenz_coeff abar l n).trans (by
    have := SystemBlockDiagData.toCoeff_toCLM (ν := ν_val) approxInverse F_abar l n
    simp only [toCoeff] at this; exact this.symm)

private lemma F_abar_toCoeff_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    toCoeff (ν := ν_val) F_abar l n = 0 := by
  simp [F_abar, toCoeff, ofCoeff, lpWeighted.mk, F_coeffs_abar_support l n hn]

/-- Per-term Y₀ evaluator. -/
private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun l n => F_coeffs_Q l n)
    (fun l n => 1 / (n : ℚ)) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) :
    (|approxInverse.action (F_coeffs abar) l n| * (ν_val : ℝ) ^ n : ℝ) ∈
      Y₀_eval l n {} :=
  systemBlockDiagActionEval_correct approxInverse (F_coeffs abar)
    (fun l n => F_coeffs_Q l n) ABlockCols (fun l n => 1 / (n : ℚ)) ν_q
    (fun l j k i => A_finBlock_eq l j i k)
    (fun l n => F_coeffs_bridge l n)
    (fun l n hn => by simp [approxInverse, if_neg (by omega : n ≠ 0)])
    ν_val_eq_q l n {}

lemma Y₀_le :
    Y₀_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  show ‖G_lorenz abar‖ ≤ _
  rw [G_lorenz_eq_toCLM_F_abar]
  have hc : toCoeff (ν := ν_val) F_abar = F_coeffs abar := by
    ext l n; simp [F_abar, toCoeff_ofCoeff]
  refine approxInverse.norm_toCLM_apply_le F_abar (2 * N + 1) (by omega)
    F_abar_toCoeff_support (by unfold Y₀_bound; positivity)
    (fun l => ?_)
  simp_rw [hc]; unfold Y₀_bound
  fin_cases l
  all_goals finsum_bound using (Y₀_eval _) (fun k _ _ => Y₀_eval_correct _ k)

/-! ## Z₁ bound via `IVP.ivp_Z₁_le`

Uses the generic Z₁ lemma from `IVP/Setup.lean`.
Equation-specific inputs: `hfin`, `htail` (from Algebra), `Dφ_lorenz_norm_le` (below). -/

/-- Dφ_lorenz operator norm bound: ‖Dφ_lorenz h l‖ ≤ K * ‖h‖ for each component.
K = Z₁_bound * (N+1) / ν = 62. Equation-specific (triangle + submultiplicativity). -/
private lemma Dφ_lorenz_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Dφ_lorenz h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
  have hpi : ∀ i : Fin L, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have hmul : ∀ (a b : l1Weighted ν_val), ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le
  have hC : (0 : ℝ) ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q : ℚ) := by unfold Z₁_bound ν_q N; norm_num
  fin_cases l
  · -- l = 0: ‖σ(h₁ - h₀)‖ ≤ 2σ‖h‖ ≤ K‖h‖
    show ‖σ_val • (h 1 - h 0)‖ ≤ _
    have h1 : ‖σ_val • (h 1 - h 0)‖ ≤ |σ_val| * (‖h 1‖ + ‖h 0‖) :=
      (le_of_eq (norm_smul σ_val _)).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _))
    have h2 : |σ_val| * (‖h 1‖ + ‖h 0‖) ≤ 2 * |σ_val| * ‖h‖ :=
      (mul_le_mul_of_nonneg_left (add_le_add (hpi 1) (hpi 0)) (abs_nonneg _)).trans
        (by ring_nf; rfl)
    exact (h1.trans h2).trans (by
      unfold σ_val Z₁_bound ν_q N; push_cast; nlinarith [norm_nonneg h])
  · -- l = 1: ‖ρh₀ - h₁ - (ā₀*h₂ + h₀*ā₂)‖ ≤ (ρ + 1 + ‖ā₀‖ + ‖ā₂‖)‖h‖ ≤ K‖h‖
    show ‖ρ_val • h 0 - h 1 - (abar 0 * h 2 + h 0 * abar 2)‖ ≤ _
    have h1 : ‖ρ_val • h 0 - h 1 - (abar 0 * h 2 + h 0 * abar 2)‖ ≤
        |ρ_val| * ‖h‖ + ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 2‖ * ‖h‖ := by
      have := norm_sub_le (ρ_val • h 0 - h 1) (abar 0 * h 2 + h 0 * abar 2)
      have := norm_sub_le (ρ_val • h 0) (h 1)
      have := norm_add_le (abar 0 * h 2) (h 0 * abar 2)
      have := (norm_smul ρ_val (h 0)).symm ▸ mul_le_mul_of_nonneg_left (hpi 0) (abs_nonneg ρ_val)
      nlinarith [hpi 1, hmul (abar 0) (h 2), hmul (h 0) (abar 2),
        hpi 2, hpi 0, norm_nonneg (abar 0), norm_nonneg (abar 2)]
    exact h1.trans (by
      have h4 : |ρ_val| = ρ_val := abs_of_nonneg (by unfold ρ_val; positivity)
      rw [h4]; unfold ρ_val Z₁_bound ν_q N; push_cast
      nlinarith [abar_norm_0_le, abar_norm_2_le, norm_nonneg h])
  · -- l = 2: ‖-βh₂ + (ā₀h₁ + h₀ā₁)‖ ≤ (β + ‖ā₀‖ + ‖ā₁‖)‖h‖ ≤ K‖h‖
    show ‖-(β_val • h 2) + (abar 0 * h 1 + h 0 * abar 1)‖ ≤ _
    have h1 : ‖-(β_val • h 2) + (abar 0 * h 1 + h 0 * abar 1)‖ ≤
        |β_val| * ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 1‖ * ‖h‖ := by
      have := norm_add_le (-(β_val • h 2)) (abar 0 * h 1 + h 0 * abar 1)
      have := norm_add_le (abar 0 * h 1) (h 0 * abar 1)
      have := (norm_neg (β_val • h 2)).symm ▸ (norm_smul β_val (h 2)).symm ▸
        mul_le_mul_of_nonneg_left (hpi 2) (abs_nonneg β_val)
      nlinarith [hmul (abar 0) (h 1), hmul (h 0) (abar 1),
        hpi 1, hpi 0, norm_nonneg (abar 0), norm_nonneg (abar 1)]
    exact h1.trans (by
      have h4 : |β_val| = β_val := abs_of_nonneg (by unfold β_val; positivity)
      rw [h4]; unfold β_val Z₁_bound ν_q N; push_cast
      nlinarith [abar_norm_0_le, abar_norm_1_le, norm_nonneg h])

lemma Z₁_le_cert :
    Z₁_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ (Z₁_bound : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  have hfin : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l) n = 0 :=
    fun h l n hn => by
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, lpWeighted.sub_toSeq, sub_eq_zero]
      exact composedApprox_eq_fderiv_G_fin h l n hn
  have htail : ∀ h : XL1 ν_val L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ_lorenz h l)) n :=
    fun h l n hn => by
      have hc := composedApprox_toCLM_tail h l n hn
      have hf := fderiv_G_lorenz_tail h l n hn
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, lpWeighted.sub_toSeq]
      show toCoeff (ν := ν_val) (composedApprox.toCLM (ν := ν_val) h) l n -
          toCoeff (ν := ν_val) ((fderiv ℝ G_lorenz abar) h) l n = _
      rw [hc, hf]; simp [toCoeff]
  exact IVP.ivp_Z₁_le composedApprox G_lorenz abar Dφ_lorenz hfin htail
    (by unfold Z₁_bound ν_q N; norm_num) Dφ_lorenz_norm_le
    (by simp only [ν_val_eq_q]; unfold Z₁_bound ν_q N; push_cast; ring_nf; rfl)

/-! ## Z₂ bound via `IVP.ivp_Z₂_le`

Uses the generic Z₂ lemma from `IVP/Setup.lean`.
Equation-specific inputs: `Dφ_diff_norm_le` (D²φ bound), `hzero` (sparsity), `hcomp_le` (block norms). -/

/-- Per-component bound on φ fderiv difference (bilinear Lorenz terms).
D²φ is constant for degree-2 systems, giving C=2. -/
private lemma Dφ_diff_norm_le (c : XL1 ν_val L) (h : XL1 ν_val L) (l : Fin L) :
    ‖((fderiv ℝ (fun x => φ_lorenz x l) c -
      fderiv ℝ (fun x => φ_lorenz x l) abar)) h‖ ≤ 2 * ‖c - abar‖ * ‖h‖ := by
  have hpi_c : ∀ i : Fin L, ‖(c - abar) i‖ ≤ ‖c - abar‖ := fun i => norm_le_pi_norm _ i
  have hpi_h : ∀ i : Fin L, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have hmul : ∀ (a b : l1Weighted ν_val), ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le
  fin_cases l
  · -- l = 0: difference = 0 (φ₀ is linear)
    show ‖(fderiv ℝ (fun x => φ_lorenz x 0) c - fderiv ℝ (fun x => φ_lorenz x 0) abar) h‖ ≤ _
    rw [fderiv_φ_diff_0]; simp; positivity
  · -- l = 1: ‖-((c₀-a₀)*h₂ + h₀*(c₂-a₂))‖ ≤ 2*‖c-a‖*‖h‖
    show ‖(fderiv ℝ (fun x => φ_lorenz x 1) c - fderiv ℝ (fun x => φ_lorenz x 1) abar) h‖ ≤ _
    rw [fderiv_φ_diff_1, norm_neg]
    have hca0 : ‖c 0 - abar 0‖ ≤ ‖c - abar‖ := by
      rw [show c 0 - abar 0 = (c - abar) 0 from by simp [Pi.sub_apply]]; exact hpi_c 0
    have hca2 : ‖c 2 - abar 2‖ ≤ ‖c - abar‖ := by
      rw [show c 2 - abar 2 = (c - abar) 2 from by simp [Pi.sub_apply]]; exact hpi_c 2
    exact (norm_add_le _ _).trans (add_le_add (hmul _ _) (hmul _ _)) |>.trans
      (add_le_add (mul_le_mul hca0 (hpi_h 2) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hpi_h 0) hca2 (norm_nonneg _) (norm_nonneg _))
      |>.trans (by ring_nf; rfl))
  · -- l = 2: ‖(c₀-a₀)*h₁ + h₀*(c₁-a₁)‖ ≤ 2*‖c-a‖*‖h‖
    show ‖(fderiv ℝ (fun x => φ_lorenz x 2) c - fderiv ℝ (fun x => φ_lorenz x 2) abar) h‖ ≤ _
    rw [fderiv_φ_diff_2]
    have hca0 : ‖c 0 - abar 0‖ ≤ ‖c - abar‖ := by
      rw [show c 0 - abar 0 = (c - abar) 0 from by simp [Pi.sub_apply]]; exact hpi_c 0
    have hca1 : ‖c 1 - abar 1‖ ≤ ‖c - abar‖ := by
      rw [show c 1 - abar 1 = (c - abar) 1 from by simp [Pi.sub_apply]]; exact hpi_c 1
    exact (norm_add_le _ _).trans (add_le_add (hmul _ _) (hmul _ _)) |>.trans
      (add_le_add (mul_le_mul hca0 (hpi_h 1) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hpi_h 0) hca1 (norm_nonneg _) (norm_nonneg _))
      |>.trans (by ring_nf; rfl))

set_option maxHeartbeats 800000 in
lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) := by
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (fderiv ℝ G_lorenz c - fderiv ℝ G_lorenz abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  exact IVP.ivp_Z₂_le approxInverse G_lorenz φ_lorenz x₀ abar
    differentiable_G_lorenz (fun l => differentiable_φ_lorenz_component l)
    G_lorenz_coeff_ivp ({1, 2} : Finset (Fin L))
    (fun c h j hj => by
      have : j = 0 := by fin_cases j <;> simp_all (config := { decide := true })
      subst this; rw [fderiv_φ_diff_0]; simp)
    (by norm_num : (0 : ℝ) ≤ 2) Dφ_diff_norm_le
    (by unfold Z₂_bound; positivity)
    (fun l => Z₂_blockNorm_component_le approxInverse ABlockCols ν_q
      approxInverse_tailBound_q {1, 2}
      (fun l j k i => A_finBlock_eq l j i k) ν_val_eq_q
      approxInverse_tailBound_eq (by native_decide) l)
    c hc

/-- Radii polynomial negativity at r₀. -/
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

/-- **Main theorem**: existence and uniqueness of a true solution near ābar. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (abar : XL1 ν_val L) (r_minus : ℝ),
      G_lorenz xTilde = 0 :=
  existsUnique (by unfold r_minus; positivity)
    (Y₀_le.trans (by unfold Y₀_bound; exact_mod_cast le_refl _))
    (Z₀_le Z₀_finBlockNorm_le)
    (Z₁_le_cert.trans (by unfold Z₁_bound; exact_mod_cast le_refl _))
    (fun c hc => Z₂_le_cert c hc)
    radii_neg

end Example83.Cert
