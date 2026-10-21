import RadiiPolynomial.Examples.IVP.Taylor.Example81.Algebra
import RadiiPolynomial.Certification
import RadiiPolynomial.Certification.IVP.Taylor
import RadiiPolynomial.Tactic.FinMatrixBound

/-!
# Example 8.1 — Certificate

Computer-assisted proof for the scalar IVP:
  x' = x(x-1), x(0) = 1/2, N=10, ν=1

Uses `data : StdIVPData` from Algebra.lean for all standard constructions.

## Key simplification

The approximate inverse is the **exact** inverse of DF^(N)(ā) in ℚ, so the defect is
identically zero and Z₀ = 0.

## Routes through the Taylor certification adapter

`Z₀`, the exact column `Z₁` and `Z₂` are read off the ν-free record `dataQ` of `data`
(`Certification/IVP/Taylor.lean`), each by one `decide +kernel`: `Z₀ = 0` through the
exact-columns slot at grid denominator `10⁶⁰`; the kernel-column `Z₁` with the Jacobian
clause; `Z₂` through the active-block evaluator at the computed scale `ν_q · DLipBoundQ`.
The field `x² − x` is syntactically quadratic: its partial `2x − 1` is syntactically affine, so
the syntactic derivative-Lipschitz constant is `2` at every radius, and the single component is
active.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example81

noncomputable section

namespace Example81.Cert

/-! ## Z₀ — Defect bound (exact inverse → zero defect) -/

/-- The ν-free stored rational fields of `data`, packaged by `IVP.StdIVPDataQ.ofStd`.
`IVP.StdIVPDataQ.toStdIVPData` realizes them at a specified weight. -/
private def dataQ : IVP.StdIVPDataQ L N := IVP.StdIVPDataQ.ofStd data

/-- The `Z₀` clause at the exact-columns slot, grid denominator `10⁶⁰`. -/
private theorem z0_slot10 : dataQ.ChecksZ₀By .exactCols (10 ^ 60) Z₀_bound := by decide +kernel

lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val data.defect.finBlock ≤ (Z₀_bound : ℝ) :=
  dataQ.defectZBy_sound ν_val_eq_q .exactCols (10 ^ 60) z0_slot10

/-! ## ‖A‖ bound (for Z₂) -/

private def ABlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  A_col l j (k : ℕ)


/-! ## Y₀ bound: ‖G(ābar)‖ ≤ Y₀_bound -/

private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun _l n => F_Q n)
    (fun _l n => 1 / (n : ℚ)) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) :
    (|data.approxInverse.action (F data.abar) l n| * (ν_val : ℝ) ^ n : ℝ) ∈
      Y₀_eval l n {} :=
  systemBlockDiagActionEval_correct data.approxInverse (F data.abar)
    (fun _l n => F_Q n) ABlockCols (fun _l n => 1 / (n : ℚ)) ν_q
    (fun l j k i => data.A_finBlock_eq l j i k)
    (fun l n => F_bridge l n)
    (fun _l n hn => by simp [IVP.StdIVPData.approxInverse, ite_eq_right (by omega : n ≠ 0)])
    ν_val_eq_q l n {}

lemma Y₀_le :
    Y₀_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  show ‖data.G f x₀ data.abar‖ ≤ _
  refine IVP.ivp_Y₀_le data.approxInverse f x₀ _ data.abar (2 * N + 1) (by omega)
    F_abar_support (by unfold Y₀_bound; positivity) (fun l => ?_)
  unfold Y₀_bound
  have hl : l = 0 := Subsingleton.elim l 0; subst hl
  -- `finsum_bound` requires a literal range endpoint, so unfold `N` first.
  simp only [N]
  finsum_bound using (Y₀_eval 0) (fun k _ _ => Y₀_eval_correct 0 k)

/-! ## Z₁ bound -/



/-! ## Z₁ through the finite kernel column test (production certificate)

The comparison lemma `Z₁_le_cert` above certifies the recipe value
`Z₁_bound = ν/(N+1) · ‖2ā₀ − 1‖ = 396482/7983360 ≈ 0.0496636`. The exact
weighted column-sup of the Z₁ tail operator is strictly smaller; the lemma
below certifies the same rational bound through `IVP.StdIVPDataQ.Z₁ker_sound`: the
finite kernel column criterion transported to the production ℓ¹ carrier. The final validation and analytic corollaries
use this sharper bound; `Z₁_le_cert` and `Z₁_bound` remain available for comparison. -/

/-- Exact column-sup value of the Z₁ tail operator: the maximum
over `M ∈ [0..N]` of the exact ℚ column tail masses
`colTailQ two_abar_sub_one_Q ν_q N M 10`, attained at `M = 9`:
`1/22 + 1/312 + 1/3600 + 1/40320 + 31/13789440 = 482763031/9859449600
≈ 0.0489645` (exact ℚ computation; the kernel producer covers columns above `N`
by antitonicity of the finite column masses). Strictly below the recipe
`Z₁_bound = 396482/7983360 ≈ 0.0496636` (ratio ≈ 0.986). -/
def Z₁_exact_bound : ℚ := 482763031 / 9859449600

/-- The Jacobian clause and the kernel-column `Z₁` clause at `Z₁_exact_bound`. -/
private theorem z1_checks :
    dataQ.ChecksDF f_cpoly ∧ dataQ.ChecksZ₁ker f_cpoly Z₁_exact_bound := by
  decide +kernel

/-- **Exact Z₁ bound**: same LHS as `Z₁_le_cert`, with the
recipe `ν/(N+1) · ‖2ā₀ − 1‖` replaced by the exact weighted column-sup,
certified through the kernel-column `Z₁` clause (`IVP.StdIVPDataQ.Z₁ker_sound`) by one
`decide +kernel` (`z1_checks`) over the finite column range `M ≤ N`. -/
theorem Z₁_le_exact :
    Z₁_norm (data.G f x₀) data.abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (data.composedApprox.toCLM (ν := ν_val)) ≤ ((Z₁_exact_bound : ℚ) : ℝ) :=
  dataQ.Z₁ker_sound ν_val_eq_q f_cpoly x₀ z1_checks.1 z1_checks.2

/-! ## Z₂ bound -/

/-- The certificate radius is nonnegative. -/
private theorem hr₀ : (0 : ℚ) ≤ r_minus := by decide +kernel

/-- The `Z₂` clause at the certificate radius. -/
private theorem z2 : dataQ.ChecksZ₂ f_cpoly r_minus Z₂_bound := by decide +kernel

/-- **Z₂ obligation** through the `Z₂` clause of the Taylor adapter: the active-block evaluator
at the computed scale `ν_q · DLipBoundQ` (the syntactic derivative-Lipschitz constant of
`X² − X` at the radii `‖ā‖ + r₀`, which is `2`) and the computed active set, one
`decide +kernel` (`z2`). -/
lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm (data.G f x₀) data.abar
      (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) :=
  dataQ.Z₂_sound ν_val_eq_q f_cpoly x₀ hr₀ z2 c hc

/-! ## Radii polynomial -/



/-- Radii negativity at the production column bound, checked by exact rational arithmetic. -/
lemma radii_neg_exact :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_exact_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 := by
  norm_num [generalRadiiPolynomial, Y₀_bound, Z₀_bound, Z₁_exact_bound, Z₂_bound, r_minus]

/-! ## Main theorem -/

/-- **Theorem 8.1.7** (Scalar IVP): There exists a unique zero of the composed IVP map
G = A ∘ F near the approximate solution ābar, proving existence and uniqueness
of the ODE solution x(t) = Σ aₙtⁿ as a Taylor series on |t| < 1.

The coefficient nonlinearity and its differentiability witness are read off the
polynomial system `f_cpoly` by `IVP.StdIVPData.existsUnique_of_compPoly`; the example
supplies the initial condition, the radius and the four bounds. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      data.G f x₀ xTilde = 0 :=
  data.existsUnique_of_compPoly f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_exact Z₂_le_cert radii_neg_exact

/-- Source-residual form of `main_theorem`: the unique validated point solves the
unpreconditioned IVP Taylor coefficient equations. `Z₀` enters in the finite-block
form the certificate proves. -/
theorem ivp_main_theorem :
    ∃! xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ),
      ∀ l n, IVP.ivpCoeffs f x₀ xTilde l n = 0 :=
  data.existsUnique_ivpCoeffs_of_compPoly f_cpoly x₀ (by unfold r_minus; positivity)
    Y₀_le Z₀_finBlockNorm_le Z₁_le_exact Z₂_le_cert radii_neg_exact

end Example81.Cert
