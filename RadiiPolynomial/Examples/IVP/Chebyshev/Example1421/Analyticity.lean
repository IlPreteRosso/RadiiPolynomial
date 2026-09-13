import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Analytic
import RadiiPolynomial.Applications.IVP.Chebyshev.Analyticity

/-!
# Example 14.2.1 — the certified solution is analytic across the endpoints

Example layer. `Analytic.lean` lifts the radius-one certificate to the function level
and stops at `IsSolution`: continuous on `[−1, 1]`, one-sided differentiable, unique in
the trajectory ball. The weight of the example is `ν = 2 > 1`, so the library face
`StdChebIVPData.analytic_solution_existsUnique_of_two_le_of_compPoly` applies verbatim and
the canonical solution of

  `u̇ = u² − u`,  `u(−1) = 1/2`

is real analytic on a neighbourhood of every point of `[−1, 1]`, the endpoints
included. Uniqueness is still stated against the original, weaker competitor class,
and no new certificate fact is used: the axiom set is the one of
`main_solution_existsUnique_radius_one`.

Closes the Chebyshev analyticity gap at the end-consumer level.
-/

open Metric Set RadiiPolynomial ChebyshevIVP Example1421
open scoped Topology

noncomputable section

namespace Example1421.Cert

/-- The existing radius-one certificate has an analytic canonical solution,
with uniqueness against the original, weaker class of competitors. -/
theorem analytic_solution_existsUnique_radius_one :
    ∃ g : ℝ → Fin Example1421.L → ℝ,
      AnalyticOnNhd ℝ g (Set.Icc (-1 : ℝ) 1) ∧
      ChebyshevIVP.IsSolution (IVP.vectorField Example1421.f_cpoly) Example1421.p₀ 1 g ∧
      ∀ g' : ℝ → Fin Example1421.L → ℝ,
        ChebyshevIVP.IsSolution (IVP.vectorField Example1421.f_cpoly) Example1421.p₀ 1 g' →
          Set.EqOn g' g (Set.Icc (-1 : ℝ) 1) :=
  Example1421.data.analytic_solution_existsUnique_of_two_le_of_compPoly Example1421.f_cpoly
    Example1421.p₀ Example1421.two_le_ν_val (by norm_num [r_minus])
    Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg R_traj_contractive_le_one

end Example1421.Cert
