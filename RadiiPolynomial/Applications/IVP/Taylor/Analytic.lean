import RadiiPolynomial.Applications.IVP.Taylor.Trajectory
import RadiiPolynomial.Applications.IVP.Taylor.Standard

/-!
# Generic glue: from StdIVPData certificate to analytic existence/uniqueness

Combines `StdIVPData.ivpCoeffs_zero_of_G_zero` (sequence-space F-zero bridge)
with `analytic_solution_unique` (function-space uniqueness via Picard-Lindelöf)
to give the full existence + uniqueness statement on `(-ν, ν)`.

## Surface

- `IVP.IsAnalyticSolution φ_cpoly x₀ R g` (`structure`): "g is an analytic
  solution of the IVP `ẋ = vectorField φ_cpoly x, x(0) = x₀` on `(-ν, ν)`
  with trajectory in `closedBall 0 R`." Three fields: `init`, `in_R`, `solves`.
- `IVP.x_analytic xTilde`: canonical analytic solution
  `t ↦ (eval(xTilde l, t))_l`.
- `StdIVPData.x_analytic_isAnalyticSolution`: existence half — `x_analytic`
  satisfies `IsAnalyticSolution`.
- `StdIVPData.analytic_eq_canonical`: pinning — any analytic solution equals
  `x_analytic` on the interval.
- `StdIVPData.analytic_unique`: any two analytic solutions agree.
- `StdIVPData.analytic_existsUnique`: existence + uniqueness packaged
  ("∃ unique modulo `Set.EqOn (Ioo)`" — strict `∃!` over `ℝ → Fin L → ℝ`
  doesn't hold because candidates can differ outside the interval).

Per-example `Analytic.lean` files become thin: only `Z₀_bound < 1` and the
φ ↔ `banachField φ_cpoly` bridge are per-example.
-/

open Set Metric RadiiPolynomial MvPolyBridge

noncomputable section

namespace IVP

variable {ν : PosReal} {L : ℕ}

/-- `g : ℝ → Fin L → ℝ` is an analytic solution of the polynomial IVP
`ẋ = vectorField φ_cpoly x, x(0) = x₀` on the open interval `(-ν, ν)` with
trajectory in `closedBall 0 R`.

Packaged as a `structure` so callers can write `hg.init`, `hg.in_R`,
`hg.solves` instead of the awkward `hg.1`, `hg.2.1`, `hg.2.2` of a flat
`And` definition. -/
structure IsAnalyticSolution
    (φ_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (R : ℝ)
    (g : ℝ → Fin L → ℝ) : Prop where
  /-- `g` satisfies the initial condition at `t = 0`. -/
  init : g 0 = x₀
  /-- The trajectory of `g` stays in `closedBall 0 R` on `(-ν, ν)`. -/
  in_R : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν, g t ∈ Metric.closedBall (0 : Fin L → ℝ) R
  /-- `g` satisfies the ODE at every `t ∈ (-ν, ν)`. -/
  solves : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν, HasDerivAt g (vectorField φ_cpoly (g t)) t

/-- The canonical analytic solution `t ↦ (eval(xTilde l, t))_l` for a sequence-
space zero `xTilde`. -/
def x_analytic (xTilde : XL1 ν L) : ℝ → Fin L → ℝ :=
  fun t l => l1Weighted.eval (xTilde l) t

end IVP

namespace IVP.StdIVPData

variable {ν : PosReal} {L N : ℕ} [NeZero L] (d : StdIVPData ν L N)

/-! ## Lower-level wrapper (takes the `IsAnalyticSolution` fields separately) -/

/-- Pinning at the field-level. Takes the `IsAnalyticSolution` data
unpackaged; used by the predicate-based theorems below and reusable for
callers that don't want to wrap into the structure. -/
theorem analytic_uniqueness_wrapper
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (φ_cpoly : Fin L → CompPoly L)
    (h_phi_eq : ∀ a l, banachField φ_cpoly a l = φ a l)
    (h_defect_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {r₀ : ℝ}
    (xTilde : XL1 ν L)
    (hxTilde_ball : xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀)
    (hG : d.G φ x₀ xTilde = 0)
    (g : ℝ → Fin L → ℝ)
    (hg_init : g 0 = x₀)
    (hg_in_R : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      g t ∈ Metric.closedBall (0 : Fin L → ℝ) (‖(d.abar : XL1 ν L)‖ + r₀))
    (hg_solves : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      HasDerivAt g (vectorField φ_cpoly (g t)) t) :
    Set.EqOn g (IVP.x_analytic xTilde) (Set.Ioo (-(ν : ℝ)) ν) := by
  -- F-zero bridge in `φ` form, then convert to banachField form via h_phi_eq.
  have hF_phi : ∀ l n, ivpCoeffs φ x₀ xTilde l n = 0 :=
    d.ivpCoeffs_zero_of_G_zero φ x₀ h_defect_lt_one hG
  have hF : ∀ l n, ivpCoeffs (banachField φ_cpoly) x₀ xTilde l n = 0 := fun l n => by
    have h_alg := hF_phi l n
    unfold ivpCoeffs at h_alg ⊢
    cases n with
    | zero => exact h_alg
    | succ k =>
      have h_phi_k : l1Weighted.toSeq (banachField φ_cpoly xTilde l) k =
                     l1Weighted.toSeq (φ xTilde l) k := by rw [h_phi_eq]
      linarith
  have hxTilde_norm_le : ‖xTilde‖ ≤ ‖(d.abar : XL1 ν L)‖ + r₀ := by
    have h_dist : dist xTilde d.abar ≤ r₀ := hxTilde_ball
    rw [dist_eq_norm] at h_dist
    have h_tri : ‖xTilde‖ ≤ ‖(d.abar : XL1 ν L)‖ + ‖xTilde - d.abar‖ := by
      have heq : (d.abar : XL1 ν L) + (xTilde - d.abar) = xTilde := by abel
      conv_lhs => rw [← heq]
      exact norm_add_le _ _
    linarith
  have hf_in_R : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      (fun l => l1Weighted.eval (xTilde l) t) ∈
        Metric.closedBall (0 : Fin L → ℝ) (‖(d.abar : XL1 ν L)‖ + r₀) := fun t ht => by
    have h_abs : |t| ≤ (ν : ℝ) := by rw [abs_le]; exact ⟨ht.1.le, ht.2.le⟩
    exact Metric.closedBall_subset_closedBall hxTilde_norm_le
      (IVP.eval_traj_in_closedBall xTilde h_abs)
  exact analytic_solution_unique φ_cpoly x₀ xTilde hF hf_in_R
    g hg_in_R hg_init hg_solves

/-! ## Predicate-based theorems -/

/-- **Existence**: `x_analytic xTilde` is an analytic solution of the IVP on
`(-ν, ν)` with trajectory bound `R = ‖d.abar‖ + r₀`. -/
theorem x_analytic_isAnalyticSolution
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (φ_cpoly : Fin L → CompPoly L)
    (h_phi_eq : ∀ a l, banachField φ_cpoly a l = φ a l)
    (h_defect_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {r₀ : ℝ}
    (xTilde : XL1 ν L)
    (hxTilde_ball : xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀)
    (hG : d.G φ x₀ xTilde = 0) :
    IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
      (‖(d.abar : XL1 ν L)‖ + r₀) (IVP.x_analytic xTilde) where
  init := by
    funext l
    show l1Weighted.eval (xTilde l) 0 = x₀ l
    rw [l1Weighted.eval_at_zero]
    have hF : ∀ l n, ivpCoeffs φ x₀ xTilde l n = 0 :=
      d.ivpCoeffs_zero_of_G_zero φ x₀ h_defect_lt_one hG
    have h0 := hF l 0
    unfold ivpCoeffs at h0
    linarith
  in_R := by
    intro t ht
    have h_abs : |t| ≤ (ν : ℝ) := by rw [abs_le]; exact ⟨ht.1.le, ht.2.le⟩
    have hxTilde_norm_le : ‖xTilde‖ ≤ ‖(d.abar : XL1 ν L)‖ + r₀ := by
      have h_dist : dist xTilde d.abar ≤ r₀ := hxTilde_ball
      rw [dist_eq_norm] at h_dist
      have h_tri : ‖xTilde‖ ≤ ‖(d.abar : XL1 ν L)‖ + ‖xTilde - d.abar‖ := by
        have heq : (d.abar : XL1 ν L) + (xTilde - d.abar) = xTilde := by abel
        conv_lhs => rw [← heq]
        exact norm_add_le _ _
      linarith
    exact Metric.closedBall_subset_closedBall hxTilde_norm_le
      (IVP.eval_traj_in_closedBall xTilde h_abs)
  solves := by
    intro t ht
    have h_abs : |t| < (ν : ℝ) := abs_lt.mpr ht
    have hF : ∀ l n, ivpCoeffs (banachField φ_cpoly) x₀ xTilde l n = 0 := fun l n => by
      have h_alg := d.ivpCoeffs_zero_of_G_zero φ x₀ h_defect_lt_one hG l n
      unfold ivpCoeffs at h_alg ⊢
      cases n with
      | zero => exact h_alg
      | succ k =>
        have h_phi_k : l1Weighted.toSeq (banachField φ_cpoly xTilde l) k =
                       l1Weighted.toSeq (φ xTilde l) k := by rw [h_phi_eq]
        linarith
    have ⟨h_per_comp, _⟩ := IVP.solves_ODE_of_F_zero φ_cpoly x₀ xTilde hF h_abs
    exact hasDerivAt_pi.mpr h_per_comp

/-- **Pinning**: any analytic solution agrees with `x_analytic xTilde` on
`(-ν, ν)`. -/
theorem analytic_eq_canonical
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (φ_cpoly : Fin L → CompPoly L)
    (h_phi_eq : ∀ a l, banachField φ_cpoly a l = φ a l)
    (h_defect_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {r₀ : ℝ}
    (xTilde : XL1 ν L)
    (hxTilde_ball : xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀)
    (hG : d.G φ x₀ xTilde = 0)
    (g : ℝ → Fin L → ℝ)
    (hg : IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
      (‖(d.abar : XL1 ν L)‖ + r₀) g) :
    Set.EqOn g (IVP.x_analytic xTilde) (Set.Ioo (-(ν : ℝ)) ν) :=
  d.analytic_uniqueness_wrapper φ x₀ φ_cpoly h_phi_eq h_defect_lt_one
    xTilde hxTilde_ball hG g hg.init hg.in_R hg.solves

/-- **Uniqueness**: any two analytic solutions agree on `(-ν, ν)`. -/
theorem analytic_unique
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (φ_cpoly : Fin L → CompPoly L)
    (h_phi_eq : ∀ a l, banachField φ_cpoly a l = φ a l)
    (h_defect_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {r₀ : ℝ}
    (xTilde : XL1 ν L)
    (hxTilde_ball : xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀)
    (hG : d.G φ x₀ xTilde = 0)
    (g₁ g₂ : ℝ → Fin L → ℝ)
    (h₁ : IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
      (‖(d.abar : XL1 ν L)‖ + r₀) g₁)
    (h₂ : IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
      (‖(d.abar : XL1 ν L)‖ + r₀) g₂) :
    Set.EqOn g₁ g₂ (Set.Ioo (-(ν : ℝ)) ν) :=
  (d.analytic_eq_canonical φ x₀ φ_cpoly h_phi_eq h_defect_lt_one
    xTilde hxTilde_ball hG g₁ h₁).trans
  (d.analytic_eq_canonical φ x₀ φ_cpoly h_phi_eq h_defect_lt_one
    xTilde hxTilde_ball hG g₂ h₂).symm

/-- **Existence + uniqueness on `(-ν, ν)`**. The `∃` paired with the
universal-uniqueness clause is the standard "∃! modulo `Set.EqOn`" pattern;
strict `∃!` over `ℝ → Fin L → ℝ` does not hold because candidates can differ
outside the interval. -/
theorem analytic_existsUnique
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (φ_cpoly : Fin L → CompPoly L)
    (h_phi_eq : ∀ a l, banachField φ_cpoly a l = φ a l)
    (h_defect_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {r₀ : ℝ}
    (xTilde : XL1 ν L)
    (hxTilde_ball : xTilde ∈ Metric.closedBall (d.abar : XL1 ν L) r₀)
    (hG : d.G φ x₀ xTilde = 0) :
    ∃ u : ℝ → Fin L → ℝ,
      IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
        (‖(d.abar : XL1 ν L)‖ + r₀) u ∧
      ∀ v : ℝ → Fin L → ℝ,
        IVP.IsAnalyticSolution (ν := ν) φ_cpoly x₀
          (‖(d.abar : XL1 ν L)‖ + r₀) v →
        Set.EqOn v u (Set.Ioo (-(ν : ℝ)) ν) :=
  ⟨IVP.x_analytic xTilde,
    d.x_analytic_isAnalyticSolution φ x₀ φ_cpoly h_phi_eq h_defect_lt_one
      xTilde hxTilde_ball hG,
    fun v hv => d.analytic_eq_canonical φ x₀ φ_cpoly h_phi_eq h_defect_lt_one
      xTilde hxTilde_ball hG v hv⟩

end IVP.StdIVPData
