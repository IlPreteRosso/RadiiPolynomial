import RadiiPolynomial.Examples.IVP.Taylor.Example83.Algebra
import RadiiPolynomial.Tactic.PDerivSimp
import RadiiPolynomial.Certification
import RadiiPolynomial.Tactic.FinMatrixBound

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

/-- The Z₁ operator constant is the syntactic `CompPoly.derivativeBound` of the Lorenz
polynomial at the certified radii `(20, 26, 11)` of `ā`: per component `2σ`, `ρ + 1 + 20 + 11`,
`β + 20 + 26`, all `≤ Z₁_bound·(N+1)/ν = 62` — the same numbers the former hand proof produced
term by term. -/
private lemma Df_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Df h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
  rw [Df_eq_fderiv]
  refine IVP.ivp_Dφ_norm_le_of_compPoly f f_cpoly data.abar (fun _ _ => rfl)
    (fun i => ((![20, 26, 11] : Fin L → ℚ) i : ℝ)) ?_ ?_ h l
  · intro i
    fin_cases i
    · show ‖data.abar 0‖ ≤ ((![20, 26, 11] : Fin L → ℚ) 0 : ℝ)
      simpa using abar_norm_0_le
    · show ‖data.abar 1‖ ≤ ((![20, 26, 11] : Fin L → ℚ) 1 : ℝ)
      simpa using abar_norm_1_le
    · show ‖data.abar 2‖ ≤ ((![20, 26, 11] : Fin L → ℚ) 2 : ℝ)
      simpa using abar_norm_2_le
  · intro l
    fin_cases l <;>
      simp [MvPolyBridge.CompPoly.derivativeBound, f_cpoly, Fin.sum_univ_three] <;>
      norm_num [σ_q, ρ_q_val, β_q, Z₁_bound, ν_q, N]

/-- **Z₁ obligation** through the `Z₁` face: the finite Jacobian check
(`composedApprox_eq_fderiv_G_fin`), the derivative map `Df` and its syntactic bound
`Df_norm_le`. -/
lemma Z₁_le_cert :
    Z₁_norm (data.G f x₀) data.abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (data.composedApprox.toCLM (ν := ν_val)) ≤ (Z₁_bound : ℝ) :=
  data.Z₁_le_of_compPoly f_cpoly x₀ composedApprox_eq_fderiv_G_fin Df Df_eq_fderiv
    (by unfold Z₁_bound ν_q N; norm_num) Df_norm_le
    (by simp only [ν_val_eq_q]; unfold Z₁_bound ν_q N; push_cast; ring_nf; rfl)

/-! ## Z₂ bound -/

/-- **Z₂ obligation** through the `Z₂` socket: the first Lorenz equation is linear, so its
syntactic derivative Lipschitz constant is `0` and it is inactive; the other two are
bilinear with constant `2`, radius-free since the system has degree `≤ 2`. The exact-ℚ
block-norm check of the preconditioner restricted to the active rows is the one
`native_decide`. -/
lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) :=
  data.Z₂_le_of_compPoly f_cpoly x₀ {1, 2}
    (fun l => Z₂_blockNorm_component_le data.approxInverse ABlockCols ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N)) {1, 2}
      (fun l j k i => data.A_finBlock_eq l j i k) ν_val_eq_q
      data.approxInverse_tailBound_eq (by native_decide) l)
    (by unfold r_minus; positivity)
    (fun j hj _ _ => by
      have : j = 0 := by fin_cases j <;> simp_all (config := { decide := true })
      subst this
      simp (config := { decide := true })
        [MvPolyBridge.CompPoly.derivativeLipschitzBound, f_cpoly, Fin.sum_univ_three])
    (fun _ _ l => by
      fin_cases l <;>
        simp (config := { decide := true })
          [MvPolyBridge.CompPoly.derivativeLipschitzBound, f_cpoly, Fin.sum_univ_three] <;>
        norm_num)
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

/-- **Theorem 8.3** (Lorenz IVP): a unique zero of the composed IVP map `G = A ∘ F`
near the approximate solution `ābar`.

The coefficient nonlinearity and its differentiability witness are read off the
polynomial system `f_cpoly` by `IVP.StdIVPData.existsUnique_of_compPoly`; the example
supplies the initial condition, the radius and the four bounds. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      data.G f x₀ xTilde = 0 :=
  data.existsUnique_of_compPoly f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg

/-- Source-residual form of `main_theorem`: the unique validated point solves the
unpreconditioned IVP Taylor coefficient equations. `Z₀` enters in the finite-block
form the certificate proves. -/
theorem ivp_main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      ∀ l n, IVP.ivpCoeffs f x₀ xTilde l n = 0 :=
  data.existsUnique_ivpCoeffs_of_compPoly f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_cert Z₂_le_cert radii_neg

end Example83.Cert
