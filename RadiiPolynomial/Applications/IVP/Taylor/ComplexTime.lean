import RadiiPolynomial.Applications.IVP.Taylor.Analyticity
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Analytic

/-!
# Complex-time reading of the Taylor IVP

IVP layer on top of `Geometric/Analytic.lean`: the same real coefficient arrays
that make the canonical Taylor trajectory real-analytic on `(-ν, ν)`
(`IVP.analyticOnNhd_x_analytic`, now in `Applications/IVP/Taylor/Analyticity.lean`)
synthesize a holomorphic `complexTrajectory` on the open complex disc `|z| < ν`
which solves the complexified polynomial vector field `complexVectorField` and
restricts to the real trajectory on `[-ν, ν]`.

Before this module production stated the real derivative identity on `(-ν, ν)` only.
The coefficient carrier, the certificate, and `IVP.IsAnalyticSolution` are all
unchanged: only the target algebra of the evaluation character moves from `ℝ` to `ℂ`.
Complex-time *uniqueness* is not stated.
-/

open scoped NNReal ENNReal Topology
open RadiiPolynomial MvPolyBridge

noncomputable section

namespace RadiiPolynomial.l1Weighted

variable {ν : PosReal} {L : ℕ}

/-- Complex evaluation needs no second proof of polynomial substitution: it is
the production naturality lemma `CompPoly.map_evalBanach` applied to `evalC`. -/
theorem complexEval_evalBanach (p : CompPoly L) (a : Fin L → l1Weighted ν)
    {z : ℂ} (hz : ‖z‖ ≤ (ν : ℝ)) :
    complexEval (p.evalBanach a) z = p.evalBanach (fun i => complexEval (a i) z) := by
  simp only [complexEval_eq_evalC _ z hz]
  exact CompPoly.map_evalBanach (l1Weighted.evalC ν z hz).toAlgHom p a

end RadiiPolynomial.l1Weighted

namespace IVP

variable {ν : PosReal} {L : ℕ}

/-- The complex-time trajectory synthesized from the real coefficient arrays. -/
def complexTrajectory (a : XL1 ν L) (z : ℂ) (l : Fin L) : ℂ :=
  l1Weighted.complexEval (a l) z

/-- The polynomial vector field interpreted in the complex target algebra. -/
def complexVectorField (φ : Fin L → CompPoly L) (x : Fin L → ℂ) (l : Fin L) : ℂ :=
  (φ l).evalBanach x

/-- Every component of the complex trajectory is holomorphic throughout the disc. -/
theorem analyticOnNhd_complexTrajectory (a : XL1 ν L) :
    AnalyticOnNhd ℂ (complexTrajectory a) (Metric.ball 0 (ν : ℝ)) :=
  AnalyticOnNhd.pi (fun l => l1Weighted.analyticOnNhd_complexEval (a l))

/-- The same coefficient norm bounds the complex trajectory on the closed disc. -/
theorem norm_complexTrajectory_le (a : XL1 ν L) {z : ℂ} (hz : ‖z‖ ≤ (ν : ℝ)) :
    ‖complexTrajectory a z‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
  intro l
  rw [complexTrajectory, l1Weighted.complexEval_eq_evalC _ _ hz]
  exact (l1Weighted.norm_evalC_le ν z hz (a l)).trans (norm_le_pi_norm a l)

/-- The complex trajectory restricts to the existing real trajectory. -/
theorem complexTrajectory_ofReal (a : XL1 ν L) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) :
    complexTrajectory a (t : ℂ) = fun l => (IVP.x_analytic a t l : ℂ) := by
  funext l
  rw [complexTrajectory, l1Weighted.complexEval_eq_evalC _ _ (by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using ht)]
  exact l1Weighted.evalC_ofReal ν t ht (a l)

/-- The real coefficient recurrence implies the complex-time differential equation. -/
theorem hasDerivAt_complexTrajectory_of_coefficients_zero
    (φ : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (a : XL1 ν L)
    (hF : ∀ l n, IVP.ivpCoeffs (IVP.banachField φ) x₀ a l n = 0)
    {z : ℂ} (hz : ‖z‖ < (ν : ℝ)) :
    HasDerivAt (complexTrajectory a) (complexVectorField φ (complexTrajectory a z)) z := by
  apply hasDerivAt_pi.mpr
  intro l
  have hseq : ∀ n, l1Omega.toSeq (derivShift (a l)) n =
      l1Weighted.toSeq (IVP.banachField φ a l) n := by
    intro n
    have hn := hF l (n + 1)
    simp only [IVP.ivpCoeffs] at hn
    rw [derivShift_apply]
    linarith
  have heval : l1Weighted.complexOmegaEval (derivShift (a l)) z =
      l1Weighted.complexEval (IVP.banachField φ a l) z := by
    apply tsum_congr
    intro n
    rw [hseq]
  have hpoly : l1Weighted.complexEval (IVP.banachField φ a l) z =
      complexVectorField φ (complexTrajectory a z) l :=
    l1Weighted.complexEval_evalBanach (φ l) a hz.le
  exact (heval.trans hpoly) ▸ l1Weighted.hasDerivAt_complexEval (a l) hz

/-- The zero-th coefficient equation gives the same initial value over the complex target. -/
theorem complexTrajectory_zero_of_coefficients_zero
    (φ : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (a : XL1 ν L)
    (hF : ∀ l n, IVP.ivpCoeffs (IVP.banachField φ) x₀ a l n = 0) :
    complexTrajectory a 0 = fun l => (x₀ l : ℂ) := by
  rw [← Complex.ofReal_zero, complexTrajectory_ofReal a
    (show |(0 : ℝ)| ≤ (ν : ℝ) by rw [abs_zero]; exact ν.2.le)]
  funext l
  have hzero := hF l 0
  simp only [IVP.ivpCoeffs] at hzero
  change (l1Weighted.eval (a l) 0 : ℂ) = (x₀ l : ℂ)
  rw [l1Weighted.eval_at_zero]
  exact congrArg (fun r : ℝ => (r : ℂ)) (sub_eq_zero.mp hzero)

end IVP
