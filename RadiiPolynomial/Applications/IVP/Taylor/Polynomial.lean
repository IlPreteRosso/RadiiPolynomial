import RadiiPolynomial.Applications.IVP.Taylor.Standard
import RadiiPolynomial.Applications.IVP.Taylor.Trajectory
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1

/-!
# CompPoly Adapter for Standard IVPs

Derives the symbolic specification, differentiability, and rational Jacobian bridge needed by
`StdIVPData.composedApprox_eq_fderiv_G_fin` from one computable polynomial system.

The certificate faces at the end of the file are the Taylor half of the pair shared with
`Applications/IVP/Chebyshev/Polynomial.lean`: they take the polynomial system in place of
the coefficient nonlinearity `IVP.banachField φ_cpoly` and its differentiability witness,
so the example layer states only numbers and bounds.
-/

open RadiiPolynomial MvPolyBridge

namespace IVP

variable {L : ℕ}

/-- Exact rational IVP residual of the stored approximate solution for a `CompPoly`
vector field and rational initial condition. -/
def ivpCoeffsQ
    (f_cpoly : Fin L → CompPoly L) (abar_Q : Fin L → Array ℚ) (x₀_q : Fin L → ℚ)
    (l : Fin L) (n : ℕ) : ℚ :=
  match n with
  | 0 => (abar_Q l).getD 0 0 - x₀_q l
  | n + 1 => ((n : ℚ) + 1) * (abar_Q l).getD (n + 1) 0 -
      (f_cpoly l).evalCoeff abar_Q n

end IVP

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- The real IVP residual at `d.abar` is the cast of `ivpCoeffsQ` when the vector
field comes from `CompPoly` and the initial condition is rational. -/
lemma StdIVPData.ivpCoeffs_abar_eq_cast_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ) (x₀_q : Fin L → ℚ)
    (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) (l : Fin L) (n : ℕ) :
    ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ d.abar l n =
      (ivpCoeffsQ f_cpoly d.abar_Q x₀_q l n : ℝ) := by
  cases n with
  | zero =>
      simp only [ivpCoeffs, ivpCoeffsQ]
      rw [d.abar_toSeq_eq, hx₀ l]
      push_cast
      rfl
  | succ n =>
      simp only [ivpCoeffs, ivpCoeffsQ]
      rw [d.abar_toSeq_eq,
        (f_cpoly l).toSeq_evalBanach d.abar d.abar_Q d.abar_toSeq_eq n]
      push_cast
      rfl

/-- `StdIVPData.composedApprox` agrees with the derivative of the IVP map on finite modes
when the vector field comes from a `CompPoly` system.

All structural witnesses are derived from `f_cpoly`; the caller supplies only the exact
finite Jacobian check against the stored numerical matrix. -/
lemma StdIVPData.composedApprox_eq_fderiv_G_fin_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    (hDF_nat : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) ((fderiv ℝ
        (d.G (fun a l => (f_cpoly l).evalBanach a) x₀) d.abar) h) l n :=
  d.composedApprox_eq_fderiv_G_fin
    (fun a l => (f_cpoly l).evalBanach a)
    (fun l => (f_cpoly l).toMvPoly) x₀
    (fun a l => compPoly_evalBanach_eq_evalInBanach (f_cpoly l) a)
    (fun l => differentiable_evalBanach_l1Weighted (f_cpoly l))
    (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
    (fun j m k => compPoly_Dφ_bridge f_cpoly
      (fun l => (f_cpoly l).toMvPoly) (fun _ => rfl)
      d.abar_Q d.abar d.abar_toSeq_eq j m k)
    hDF_nat h l n hn

/-! ## Certificate faces -/

/-- Existence and uniqueness of the coefficient zero of the preconditioned map, with the
coefficient nonlinearity and its differentiability witness read off one polynomial system,
and `Z₀` in the finite-block form the certificate proves (the operator form is derived by
`StdIVPData.Z₀_le`). Taylor counterpart of
`ChebyshevIVP.StdChebIVPData.existsUnique_of_compPoly`; same hypothesis list as its
source-residual sibling `existsUnique_ivpCoeffs_of_compPoly`. -/
theorem StdIVPData.existsUnique_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G (banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      d.G (banachField f_cpoly) x₀ xTilde = 0 :=
  d.existsUnique (banachField f_cpoly) x₀
    (fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    hr₀ hY₀ (d.Z₀_le hZ₀fin) hZ₁ hZ₂ h_radii

/-- The same statement at the source coefficient residual, with `Z₀` in the finite-block
form the certificate proves. Taylor counterpart of the Chebyshev face; the injectivity
bridge `G = 0 ↔ ivpCoeffs = 0` is supplied by `existsUnique_ivpCoeffs`. -/
theorem StdIVPData.existsUnique_ivpCoeffs_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G (banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      ∀ l n, ivpCoeffs (banachField f_cpoly) x₀ xTilde l n = 0 :=
  d.existsUnique_ivpCoeffs (banachField f_cpoly) x₀
    (fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii

/-- `Z₁` recipe bound with the coefficient nonlinearity and its differentiability witness
read off the polynomial system: `StdIVPData.Z₁_le` at `φ := banachField f_cpoly`. The
certificate supplies the finite Jacobian check in coefficient form (its
`composedApprox_eq_fderiv_G_fin`, itself `composedApprox_eq_fderiv_G_fin_of_compPoly` at
the stored matrix), its derivative map `Dφ` with the identification `hDφ`, and the bound
`‖Dφ h l‖ ≤ K ‖h‖` (by hand, or by `ivp_Dφ_norm_le_of_compPoly` from the syntax). -/
theorem StdIVPData.Z₁_le_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    (hfin : ∀ (h : XL1 ν L) (l : Fin L) (n : ℕ), n ≤ N →
      toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
        toCoeff (ν := ν) ((fderiv ℝ (d.G (banachField f_cpoly) x₀) d.abar) h) l n)
    (Dφ : (Fin L → l1Weighted ν) → Fin L → l1Weighted ν)
    (hDφ : ∀ h l, Dφ h l = (fderiv ℝ (fun a => banachField f_cpoly a l) d.abar) h)
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ_norm : ∀ (h : XL1 ν L) (l : Fin L), ‖Dφ h l‖ ≤ K * ‖h‖)
    {Z₁ : ℝ} (hZ₁ : (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁) :
    Z₁_norm (d.G (banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁ :=
  d.Z₁_le (banachField f_cpoly) x₀
    (fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    hfin Dφ hDφ hK hDφ_norm hZ₁

/-- `Z₁` exact-column bound with the coefficient nonlinearity and its differentiability
witness read off the polynomial system: `StdIVPData.Z₁_le_exact` at
`φ := banachField f_cpoly`. -/
theorem StdIVPData.Z₁_le_exact_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    (hfin : ∀ (h : XL1 ν L) (l : Fin L) (n : ℕ), n ≤ N →
      toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
        toCoeff (ν := ν) ((fderiv ℝ (d.G (banachField f_cpoly) x₀) d.abar) h) l n)
    (Dφ : (Fin L → l1Weighted ν) → Fin L → l1Weighted ν)
    (hDφ : ∀ h l, Dφ h l = (fderiv ℝ (fun a => banachField f_cpoly a l) d.abar) h)
    {C : ℝ} (hC : 0 ≤ C)
    (hDtail : ∀ (h : XL1 ν L) (l : Fin L),
      ∑' n, |l1Weighted.toSeq (shiftDivN (Dφ h l)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ C * ‖h‖)
    {Z₁ : ℝ} (hZ₁ : C ≤ Z₁) :
    Z₁_norm (d.G (banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁ :=
  d.Z₁_le_exact (banachField f_cpoly) x₀
    (fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    hfin Dφ hDφ hC hDtail hZ₁

/-- `Z₂` from syntax (Taylor face of `ChebyshevIVP.StdChebIVPData.Z₂_le_of_compPoly_max`).
On top of `IVP.ivp_Z₂_le`: the differentiability witnesses and the Lipschitz bound of the
derivative are derived from the polynomial system, the latter through the syntactic constant
`CompPoly.derivativeLipschitzBound` at the radii `max ‖cᵢ‖ ‖āᵢ‖` (no symmetrization on the
Taylor side, hence no factor `2`).

What a certificate supplies:
* `active` and `hcomp_le` — the components whose derivative can move at all, and the
  exact-ℚ block-norm check of the preconditioner restricted to them,
  `Z₂_blockNorm_component_le … (by native_decide)`, in the shape `B · ν · (…) ≤ Z₂`;
* `hinactive` — an inactive component has syntactic constant `0` (Lorenz: the linear first
  equation);
* `hB` — a bound `B` for the syntactic constant on the certificate ball. For the
  syntactically quadratic presentations in Examples 8.1 and 8.3, the partials have
  radius-independent syntactic Lipschitz bounds and `hB` reduces to `B = 2`
  (`simp; norm_num`). Semantic degree `≤ 2` after cancellation does not ensure this.
Nonnegativity of `B` and of `Z₂` is derived. The block-norm check comes first in the
argument list so that its `native_decide` is the first postponed tactic block of the
certificate lemma: `norm_num` consumes auxiliary declaration names, and the audited axiom
name `<lemma>._native.native_decide.ax_1_1` must not move. -/
theorem StdIVPData.Z₂_le_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    (active : Finset (Fin L)) {B Z₂_val : ℝ}
    (hcomp_le : ∀ l : Fin L,
      B * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν d.approxInverse.finBlock l j) +
        if l ∈ active then d.approxInverse.tailBound else 0) ≤ Z₂_val)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hinactive : ∀ j ∉ active, ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      (f_cpoly j).derivativeLipschitzBound (fun i => max ‖c i‖ ‖d.abar i‖) = 0)
    (hB : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀, ∀ l,
      (f_cpoly l).derivativeLipschitzBound (fun i => max ‖c i‖ ‖d.abar i‖) ≤ B) :
    ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G (banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ Z₂_val * r₀ := by
  intro c hc
  have hB0 : 0 ≤ B :=
    (CompPoly.derivativeLipschitzBound_nonneg (f_cpoly 0) _
      (fun i => le_max_of_le_left (norm_nonneg _))).trans
      (hB d.abar (Metric.mem_closedBall_self hr₀) 0)
  have hZ₂_nn : 0 ≤ Z₂_val :=
    le_trans (mul_nonneg (mul_nonneg hB0 ν.coe_nonneg) (add_nonneg
      (Finset.sum_nonneg fun j _ => blockEntryNorm_nonneg d.approxInverse.finBlock 0 j)
      (by split <;> [exact d.approxInverse.tailBound_nonneg_at 0; exact le_rfl])))
      (hcomp_le 0)
  have hlip : ∀ (h : XL1 ν L) (l : Fin L),
      ‖(fderiv ℝ (fun x => banachField f_cpoly x l) c
        - fderiv ℝ (fun x => banachField f_cpoly x l) d.abar) h‖ ≤
        (f_cpoly l).derivativeLipschitzBound (fun i => max ‖c i‖ ‖d.abar i‖)
          * ‖c - d.abar‖ * ‖h‖ :=
    fun h l => CompPoly.norm_fderiv_evalBanach_sub_le_max (f_cpoly l) c d.abar h
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (fderiv ℝ (d.G (banachField f_cpoly) x₀) c
      - fderiv ℝ (d.G (banachField f_cpoly) x₀) d.abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  exact ivp_Z₂_le d.approxInverse (banachField f_cpoly) x₀
    (ivpMap_mem_of_tailDiag_inv _ _ _ d.htail_diag_inv) d.abar
    (d.differentiable_G _ x₀
      fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    (fun l => MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l))
    c hc active
    (fun h j hj => norm_le_zero_iff.mp
      ((hlip h j).trans (by rw [hinactive j hj c hc]; simp)))
    hB0
    (fun h l => (hlip h l).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hB c hc l) (norm_nonneg _)) (norm_nonneg _)))
    hZ₂_nn hcomp_le

/-- A zero of the preconditioned map annihilates the source coefficient residual, with the
contraction `Z₀ < 1` that the bridge `ivpCoeffs_zero_of_G_zero` needs derived from the four
bounds. Same hypothesis list as `existsUnique_of_compPoly`, plus the zero; this is the
statement the complex-time and analyticity consumers of a named zero use. -/
theorem StdIVPData.ivpCoeffs_zero_of_compPoly_of_radii
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : Z₁_norm (d.G (banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) r₀,
      Z₂_norm (d.G (banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (xTilde : XL1 ν L) (hG : d.G (banachField f_cpoly) x₀ xTilde = 0) :
    ∀ l n, ivpCoeffs (banachField f_cpoly) x₀ xTilde l n = 0 :=
  d.ivpCoeffs_zero_of_G_zero (banachField f_cpoly) x₀
    (d.defect_finBlockNorm_lt_one_of_radii (banachField f_cpoly) x₀
      hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii) hG

end IVP
