import RadiiPolynomial.Examples.IVP.Taylor.Example83.Algebra
import RadiiPolynomial.Certification
import RadiiPolynomial.Certification.IVP.Taylor

/-!
# Example 8.3 — Certificate

Computer-assisted proof for the Lorenz IVP. Uses `data : StdIVPData` from Algebra.lean.

## Routes through the Taylor certification adapter

`Z₀` and `Z₂` are read off the ν-free record `dataQ` of `data`
(`Certification/IVP/Taylor.lean`), each by one `decide +kernel`: `Z₀` through the grid slot
at grid denominator `10⁶⁰` (the exact-columns clause on these data is far heavier), `Z₂`
through the active-block evaluator at the computed scale `ν_q · DLipBoundQ`. The first Lorenz
equation is linear, so its syntactic derivative-Lipschitz constant is `0` and it is inactive;
the other two are bilinear, with syntactically affine partials, so the constant is `2` at
every radius and the computed active set is `{1, 2}`. `Z₁` keeps the recipe route
(`Z₁_bound`).
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example83

namespace Example83.Cert

/-- The ν-free stored rational fields of `data`, assembled field by field (not through
`IVP.StdIVPDataQ.ofStd data`, whose compiled code would depend on the real weight).
`IVP.StdIVPDataQ.toStdIVPData` realizes them at a specified weight. -/
private def dataQ : IVP.StdIVPDataQ L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := abar_Q
  ν_q := ν_q
  habar_size := fun l => by fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]

/-- The `Y₀` clause `dataQ.ChecksY₀ f_cpoly x₀_q Y₀_bound`, stated on the raw rational mass and
closed by `native_decide`. -/
private theorem y0_check :
    ∀ l, (∑ n ∈ Finset.Icc 0 (IVP.supportM f_cpoly N),
      |RadiiPolynomial.blockActionQ (N := N) (fun l j k => dataQ.A_col l j k.val)
        (fun _ n => 1 / (n : ℚ))
        (IVP.ivpCoeffsQ f_cpoly dataQ.abar_Q x₀_q) l n| * dataQ.ν_q ^ n) ≤ Y₀_bound := by
  native_decide

end Example83.Cert

noncomputable section

namespace Example83.Cert

/-! ## Z₀ -/

/-- The `Z₀` clause at the grid slot, grid denominator `10⁶⁰`. -/
private theorem z0_grid10 : dataQ.ChecksZ₀By .grid (10 ^ 60) Z₀_bound := by decide +kernel

lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val data.defect.finBlock ≤ (Z₀_bound : ℝ) :=
  dataQ.defectZBy_sound ν_val_eq_q .grid (10 ^ 60) z0_grid10

/-! ## Y₀ bound -/

lemma Y₀_le :
    Y₀_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  have hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ) := by
    intro l
    fin_cases l <;> norm_num [x₀, x₀_q]
  exact dataQ.Y₀_sound ν_val_eq_q f_cpoly x₀ x₀_q hx₀ y0_check

/-! ## Z₁ bound -/

/-- The Z₁ operator constant is the syntactic `CompPoly.derivativeBound` of the Lorenz
polynomial at the certified radii `(20, 26, 11)` of `ā`: per component `2σ`, `ρ + 1 + 20 + 11`,
`β + 20 + 26`, all `≤ Z₁_bound·(N+1)/ν = 62`. -/
private lemma Df_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Df h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
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
  data.Z₁_le_of_compPoly f_cpoly x₀ composedApprox_eq_fderiv_G_fin Df (fun _ _ => rfl)
    (by unfold Z₁_bound ν_q N; norm_num) Df_norm_le
    (by simp only [ν_val_eq_q]; unfold Z₁_bound ν_q N; push_cast; ring_nf; rfl)

/-! ## Z₂ bound -/

/-- The certificate radius is nonnegative. -/
private theorem hr₀ : (0 : ℚ) ≤ r_minus := by decide +kernel

/-- The `Z₂` clause at the certificate radius. -/
private theorem z2 : dataQ.ChecksZ₂ f_cpoly r_minus Z₂_bound := by decide +kernel

/-- **Z₂ obligation** through the `Z₂` clause of the Taylor adapter: the active-block evaluator
at the computed scale `ν_q · DLipBoundQ` and the computed active set (the first Lorenz equation
is linear, hence inactive; the other two are bilinear with constant `2`), one
`decide +kernel` (`z2`). -/
lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) :=
  dataQ.Z₂_sound ν_val_eq_q f_cpoly x₀ hr₀ z2 c hc

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
