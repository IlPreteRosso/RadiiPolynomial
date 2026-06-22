import RadiiPolynomial.examples.Example81.Certificate
import RadiiPolynomial.source.IVP.AnalyticGlue

/-!
# Example 8.1 — Analytic uniqueness corollary (function-space side)

Function-space lift of `Certificate.lean`'s `main_theorem`. The unique
sequence-space zero `xTilde` becomes the unique analytic solution of
`ẋ = x(x-1), x(0) = 1/2` on `(-ν, ν)` with trajectory in
`closedBall 0 R_traj`.

Per-example obligations are minimal: just `defect_norm_lt_one` (Z₀ < 1) and
the φ ↔ `banachField` bridge. Everything else is from the generic
`IVP.StdIVPData.analytic_*` API in `IVP/AnalyticGlue.lean`.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example81.Cert

open Example81

abbrev R_traj : ℝ := ‖(data.abar : XL1 ν_val L)‖ + (r_minus : ℝ)

private lemma defect_norm_lt_one :
    finiteBlockMatrixNorm ν_val data.defect.finBlock < 1 := by
  refine lt_of_le_of_lt Z₀_finBlockNorm_le ?_
  show (Z₀_bound : ℝ) < 1; unfold Z₀_bound; norm_num

private lemma banachField_eq_f (a : XL1 ν_val L) (l : Fin L) :
    banachField f_cpoly a l = f a l := rfl

/-- Canonical sequence-space zero from `main_theorem`. -/
def xTilde : XL1 ν_val L := main_theorem.exists.choose

private lemma xTilde_spec :
    xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ) ∧
    data.G f x₀ xTilde = 0 :=
  main_theorem.exists.choose_spec

lemma xTilde_ball : xTilde ∈ Metric.closedBall (data.abar : XL1 ν_val L) (r_minus : ℝ) :=
  xTilde_spec.1

lemma xTilde_G_zero : data.G f x₀ xTilde = 0 := xTilde_spec.2

/-- Canonical analytic solution `t ↦ (eval(xTilde l, t))_l`. -/
def x_analytic : ℝ → Fin L → ℝ := IVP.x_analytic xTilde

/-- **Existence**: `x_analytic` is an analytic solution. -/
theorem x_analytic_isAnalyticSolution :
    IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj x_analytic :=
  data.x_analytic_isAnalyticSolution f x₀ f_cpoly
    banachField_eq_f defect_norm_lt_one xTilde xTilde_ball xTilde_G_zero

/-- **Pinning**: any analytic candidate equals `x_analytic` on `(-ν, ν)`. -/
theorem analytic_eq_canonical
    (g : ℝ → Fin L → ℝ)
    (hg : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g) :
    Set.EqOn g x_analytic (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_eq_canonical f x₀ f_cpoly
    banachField_eq_f defect_norm_lt_one xTilde xTilde_ball xTilde_G_zero g hg

/-- **Function-space uniqueness**: any two analytic candidates agree. -/
theorem analytic_unique
    (g₁ g₂ : ℝ → Fin L → ℝ)
    (h₁ : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g₁)
    (h₂ : IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj g₂) :
    Set.EqOn g₁ g₂ (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_unique f x₀ f_cpoly
    banachField_eq_f defect_norm_lt_one xTilde xTilde_ball xTilde_G_zero
    g₁ g₂ h₁ h₂

/-- **Existence + uniqueness for Example 8.1** on `(-ν, ν)`. -/
theorem analytic_existsUnique :
    ∃ u : ℝ → Fin L → ℝ,
      IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj u ∧
      ∀ v : ℝ → Fin L → ℝ,
        IVP.IsAnalyticSolution (ν := ν_val) f_cpoly x₀ R_traj v →
        Set.EqOn v u (Set.Ioo (-(ν_val : ℝ)) ν_val) :=
  data.analytic_existsUnique f x₀ f_cpoly
    banachField_eq_f defect_norm_lt_one xTilde xTilde_ball xTilde_G_zero

end Example81.Cert
