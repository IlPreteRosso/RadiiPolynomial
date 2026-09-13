import RadiiPolynomial.Examples.IVP.Taylor.Example83.Analyticity
import RadiiPolynomial.Applications.IVP.Taylor.ComplexTime

/-!
# Example 8.3 — the complex-time Lorenz solution

The same real coefficient arrays that `Analyticity.lean` turns into a real-analytic
canonical solution give a holomorphic solution of the complexified Lorenz equation
on `|z| < 3/20` which restricts to the real solution on the interval.

Consumers of the generic `Applications/IVP/Taylor/ComplexTime.lean`. The
certificate, the competitor class `IVP.IsAnalyticSolution` and the public
surface of `Analytic.lean` are untouched; every theorem here carries exactly the
axiom set of `Example83.Cert.main_theorem`.
-/

open Set Metric RadiiPolynomial MvPolyBridge IVP

noncomputable section

namespace Example83.Cert

open Example83

/-- The certified sequence-space zero annihilates the whole Taylor coefficient
recurrence. Reusable: every complex-time statement about Lorenz needs it. The
contraction `Z₀ < 1` it rests on is derived by the library face from the same five
facts `main_theorem` consumed. -/
theorem lorenz_coefficients_zero :
    ∀ l n, ivpCoeffs (banachField Example83.f_cpoly) Example83.x₀
      Example83.Cert.xTilde l n = 0 :=
  Example83.data.ivpCoeffs_zero_of_compPoly_of_radii Example83.f_cpoly Example83.x₀
    (by unfold r_minus; positivity)
    Example83.Cert.Y₀_le Example83.Cert.Z₀_finBlockNorm_le Example83.Cert.Z₁_le_cert
    Example83.Cert.Z₂_le_cert Example83.Cert.radii_neg
    Example83.Cert.xTilde Example83.Cert.xTilde_G_zero

/-- The existing Lorenz coefficient certificate also supplies a holomorphic
solution of the complexified Lorenz equation throughout `|z| < 3/20`. -/
theorem lorenz_complex_ivp :
    AnalyticOnNhd ℂ (complexTrajectory Example83.Cert.xTilde)
      (Metric.ball 0 (Example83.ν_val : ℝ)) ∧
    complexTrajectory Example83.Cert.xTilde 0 = (fun l => (Example83.x₀ l : ℂ)) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) (Example83.ν_val : ℝ),
      HasDerivAt (complexTrajectory Example83.Cert.xTilde)
        (complexVectorField Example83.f_cpoly (complexTrajectory Example83.Cert.xTilde z)) z := by
  refine ⟨analyticOnNhd_complexTrajectory _,
    complexTrajectory_zero_of_coefficients_zero _ _ _ lorenz_coefficients_zero, ?_⟩
  intro z hz
  exact hasDerivAt_complexTrajectory_of_coefficients_zero _ _ _ lorenz_coefficients_zero
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- On the real interval the holomorphic Lorenz trajectory is the original
canonical real solution, with componentwise complex coercion. -/
theorem lorenz_complex_restricts_to_real {t : ℝ} (ht : |t| ≤ (Example83.ν_val : ℝ)) :
    complexTrajectory Example83.Cert.xTilde (t : ℂ) =
      fun l => (Example83.Cert.x_analytic t l : ℂ) :=
  complexTrajectory_ofReal _ ht

end Example83.Cert
