import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Certificate
import RadiiPolynomial.Applications.IVP.Chebyshev.AnalyticPolynomial

/-!
# Example 14.2.1 — the certified solution as a function on `[-1, 1]`

Function-space lift of `Certificate.lean`'s `main_theorem`: the unique sequence-space
zero of the preconditioned Chebyshev map becomes the unique solution of

  `u̇ = u² − u`,  `u(−1) = 1/2`

on `[−1, 1]` whose trajectory stays in the certified ball. The vector field is
`IVP.vectorField f_cpoly`, the real right-hand side of the same polynomial syntax the
certificate interprets on coefficients.

Every structural obligation — the evaluation identity between the coefficient
nonlinearity and the vector field, differentiability of the preconditioned map, `Z₀ < 1`,
the Lipschitz constant of the vector field — is derived by the library faces
`StdChebIVPData.solution_existsUnique_of_compPoly` and
`solution_existsUnique_of_two_le_of_compPoly` from `f_cpoly` and the four certified bounds;
the faces also choose the Lipschitz constant of the vector field (the syntactic
`lipschitzBound` of `X² − X` at the trajectory radius). The example supplies only the
trajectory radius.

Three radii are recorded: `R_traj = 2(‖ā‖ + r₀)` (the non-contractive route),
`R_traj_contractive = ‖ā‖ + r₀` (evaluation is contractive at `ν = 2`), and the round
radius `R = 1`, which uses `abar_norm_le : ‖ā‖ ≤ 39/50` — the certificate's
`Sabar_norm_le` transported to the stored element, no additional `native_decide`.

No analyticity is claimed here — see `Analyticity.lean`.
-/

open scoped BigOperators
open Metric Set RadiiPolynomial ChebyshevIVP Example1421 MvPolyBridge

noncomputable section

namespace Example1421.Cert

local notation "ābar" => ChebyshevIVP.StdChebIVPData.abar data

/-! ## 1. Trajectory radii -/

/-- The original certified trajectory radius `2(‖ā‖ + r₀)`. -/
abbrev R_traj : ℝ := 2 * (‖ābar‖ + ((r_minus : ℚ) : ℝ))

/-- The improved trajectory radius `‖ā‖ + r₀`. At the example's weight `ν = 2`,
evaluation is contractive despite the doubled positive-mode storage convention. -/
abbrev R_traj_contractive : ℝ := ‖ābar‖ + ((r_minus : ℚ) : ℝ)

/-! ## 2. The main theorems -/

/-- **Example 14.2.1, at the level of functions.** The IVP `u̇ = u² − u`, `u(−1) = 1/2` has
a solution on `[−1, 1]` with trajectory in `closedBall 0 R_traj`, and every solution with
that trajectory bound agrees with it on `[−1, 1]`.

Every numerical input is the one `main_theorem` already certified (`Y₀_le`,
`Z₀_finBlockNorm_le`, `Z₁_le`, `Z₂_le`, `radii_neg`); nothing is added. Its axiom set is
exactly that of `main_theorem`. -/
theorem main_solution_existsUnique :
    ∃ g : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj g ∧
      ∀ g' : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj g' →
        Set.EqOn g' g (Icc (-1 : ℝ) 1) :=
  data.solution_existsUnique_of_compPoly f_cpoly p₀ (by norm_num [r_minus])
    Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg le_rfl

/-- **Contractive function-space radius.** At `ν = 2`, the same certified zero
produces a solution in the smaller trajectory ball of radius `‖ā‖ + r₀`. -/
theorem main_solution_existsUnique_contractive :
    ∃ g : ℝ → Fin L → ℝ,
      ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj_contractive g ∧
      ∀ g' : ℝ → Fin L → ℝ,
        ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj_contractive g' →
          Set.EqOn g' g (Icc (-1 : ℝ) 1) :=
  data.solution_existsUnique_of_two_le_of_compPoly f_cpoly p₀
    two_le_ν_val (by norm_num [r_minus])
    Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg le_rfl

/-! ## 3. Round trajectory radius

`‖ā‖ ≤ ‖S(ā)‖ ≤ 39/50`: the second inequality is the certificate's own exact-ℚ bound
`Sabar_norm_le`, the first is the bundle's `StdChebIVPData.norm_abar_le_norm_symmetrize`
(`ā` is stored on the indices `0..N` only). Hence `R_traj_contractive = ‖ā‖ + 10⁻⁶ ≤ 1`.
All statements have the same axioms as `main_theorem`. -/

/-- `39/50` is a certified rational upper bound for the stored candidate's norm. -/
lemma abar_norm_le : ‖ābar‖ ≤ ((39/50 : ℚ) : ℝ) :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun l =>
    (data.norm_abar_le_norm_symmetrize l).trans (Sabar_norm_le l)

lemma R_traj_contractive_le_one : R_traj_contractive ≤ 1 := by
  have h := abar_norm_le
  rw [show ((39/50 : ℚ) : ℝ) = 39/50 from by norm_num] at h
  have hr : ((r_minus : ℚ) : ℝ) = 1/1000000 := by norm_num [r_minus]
  simp only [R_traj_contractive, hr]
  linarith

/-- **Example 14.2.1 at radius `1`.** The contractive evaluation bound at `ν = 2`
halves the previous round trajectory ball. -/
theorem main_solution_existsUnique_radius_one :
    ∃ g : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ 1 g ∧
      ∀ g' : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ 1 g' →
        Set.EqOn g' g (Icc (-1 : ℝ) 1) :=
  data.solution_existsUnique_of_two_le_of_compPoly f_cpoly p₀
    two_le_ν_val (by norm_num [r_minus])
    Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg R_traj_contractive_le_one

end Example1421.Cert
