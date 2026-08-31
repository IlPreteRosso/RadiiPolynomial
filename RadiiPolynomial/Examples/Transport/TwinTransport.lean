import RadiiPolynomial.Core.Transport
import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Certificate

/-!
# The twin transports

The real instance: Example 14.2.1 — the book's Chebyshev twin of Example 8.1
(logistic IVP, ν = 2, N = 40, margin 74.7%) — is a complete machine-checked
certificate (`Example1421.Cert.main_existsUnique`), and its native margin
clears the bordered↔U budget (κ−1)/κ = 5/8 at κ = 8/3.

`twin_transports` packages the payoff: for EVERY transport equivalence `u`
of the twin's certificate space priced within the bordered↔U budget
(α·β ≤ 8/3), the conjugated problem has a unique zero in the transported
ball — no bound re-verified on the far side. The κ = 1 instance
`twin_scalar_certificate` (component collapse of the `Fin 1` system space)
exercises the theorem; realizing the bordered↔U instance itself needs the
bilateral↔bordered storage arrow, which the library does not yet carry
(only `borderedTU_equiv : l1Bordered ≃L l1Weighted` exists).
-/

namespace TwinTransport

open RadiiPolynomial ChebyshevIVP Example1421 Example1421.Cert

/-- The twin's margin buys any transport within the bordered↔U budget. -/
theorem twin_transports {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (u : XCheb ν_val L ≃L[ℝ] E') (w : XCheb ν_val L ≃L[ℝ] F')
    {f' : E' → F'} (hsquare : ∀ x, f' (u x) = w (data.G phi p₀ x))
    {α β : ℝ}
    (hα : ‖(u : XCheb ν_val L →L[ℝ] E')‖ ≤ α)
    (hβ : ‖(u.symm : E' →L[ℝ] XCheb ν_val L)‖ ≤ β)
    (hβpos : 0 < β) (hκ : α * β ≤ 8/3) :
    ∃! xTilde ∈ Metric.closedBall (u (ChebyshevIVP.StdChebIVPData.abar data))
        (((r_minus : ℚ) : ℝ) / β),
      f' xTilde = 0 := by
  have hr_pos : (0 : ℝ) < ((r_minus : ℚ) : ℝ) := by norm_num [r_minus]
  refine transport_radii_polynomial_of_margin u w hsquare hα hβ hβpos
    (r₁ := ((r_minus : ℚ) : ℝ) / β)
    (div_pos hr_pos hβpos)
    (r₀ := ((r_minus : ℚ) : ℝ))
    (by field_simp)
    (Y₀ := ((Y₀_bound : ℚ) : ℝ)) (Z₀ := ((Z₀_bound : ℚ) : ℝ))
    (Z₁ := ((Z₁_bound : ℚ) : ℝ)) (Z₂ := fun _ => ((Z₂_bound : ℚ) : ℝ))
    (A := ContinuousLinearMap.id ℝ (XCheb ν_val L))
    (A_dagger := data.composedApproxCLM)
    ?_ ?_ ?_ ?_ G_diff ?_ (fun _ _ h => h)
  · show ‖ContinuousLinearMap.id ℝ (XCheb ν_val L)
      (data.G phi p₀ (ChebyshevIVP.StdChebIVPData.abar data))‖ ≤ _
    rw [ContinuousLinearMap.id_apply]
    exact Y₀_le
  · rw [ContinuousLinearMap.id_comp]
    exact Z₀_le
  · rw [ContinuousLinearMap.id_comp]
    exact Z₁_le
  · intro c hc
    rw [ContinuousLinearMap.id_comp]
    exact Z₂_le c hc
  · -- α·β·p(r₀) + (α·β − 1)·r₀ < 0 from the 8/3 gate + monotonicity in κ
    have hgate := margin_clears_gate
    have hsum : (0 : ℝ) < generalRadiiPolynomial ((Y₀_bound : ℚ) : ℝ)
        ((Z₀_bound : ℚ) : ℝ) ((Z₁_bound : ℚ) : ℝ)
        (fun _ => ((Z₂_bound : ℚ) : ℝ)) ((r_minus : ℚ) : ℝ) + ((r_minus : ℚ) : ℝ) := by
      norm_num [generalRadiiPolynomial, Y₀_bound, Z₀_bound, Z₁_bound, Z₂_bound, r_minus]
    nlinarith [hgate, hsum, hκ]

/-! The κ = 1 instance: component collapse of the `Fin 1` system space —
the smallest genuine transport, exercising `twin_transports` end to end. -/

private noncomputable def expandCLM : l1Chebyshev ν_val →L[ℝ] XCheb ν_val L :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ _

noncomputable def finOneCollapse : XCheb ν_val L ≃L[ℝ] l1Chebyshev ν_val :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.proj 0) expandCLM
    (fun h => funext fun l => by rw [Subsingleton.elim l (0 : Fin L)]; rfl)
    (fun _ => rfl)

lemma norm_collapse_le :
    ‖(finOneCollapse : XCheb ν_val L →L[ℝ] l1Chebyshev ν_val)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
    rw [one_mul]
    exact norm_le_pi_norm h 0

lemma norm_collapse_symm_le :
    ‖(finOneCollapse.symm : l1Chebyshev ν_val →L[ℝ] XCheb ν_val L)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun l => le_refl _

/-- The transported twin at κ = 1: the certificate restated on the scalar
component, no bound re-verified. -/
theorem twin_scalar_certificate :
    ∃! xTilde ∈ Metric.closedBall
        (finOneCollapse (ChebyshevIVP.StdChebIVPData.abar data))
        (((r_minus : ℚ) : ℝ) / 1),
      (fun v => finOneCollapse (data.G phi p₀ (finOneCollapse.symm v))) xTilde = 0 :=
  twin_transports finOneCollapse finOneCollapse
    (f' := fun v => finOneCollapse (data.G phi p₀ (finOneCollapse.symm v)))
    (fun x => by rw [ContinuousLinearEquiv.symm_apply_apply])
    norm_collapse_le norm_collapse_symm_le one_pos (by norm_num)

end TwinTransport
