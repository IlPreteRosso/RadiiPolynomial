import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Certificate
import RadiiPolynomial.Applications.IVP.Chebyshev.Analytic

/-!
# Example 14.2.1 — the certified solution as a function on `[-1, 1]`

Function-space lift of `Certificate.lean`'s `main_existsUnique`: the unique sequence-space
zero of the preconditioned Chebyshev map becomes the unique solution of

  `u̇ = u² − u`,  `u(−1) = 1/2`

on `[−1, 1]` whose trajectory stays in the certified ball. This is the first Chebyshev
certificate in the repository that ends at a *function* rather than at a coefficient
sequence.

Two per-example obligations, and both are short:

* `hφ_eval` — the payoff of the multiplicative evaluation face. The stored nonlinearity is
  `phi a l = S(a l) · S(a l) − S(a l)` with `S = symmetrize`; evaluating it is
  `l1Chebyshev.eval_mul_of_isSymmetric` (which is `map_mul` of the Laurent character
  transported through the `T_k(cos θ) = cos kθ` dictionary) plus `eval_sub` and
  `eval_symmetrize`. No Cauchy product, no Mertens theorem.
* `f_lipschitzOnWith` — `u ↦ u² − u` is `(2R+1)`-Lipschitz on `closedBall 0 R`, from the
  factorisation `u² − u − (v² − v) = (u − v)(u + v − 1)`.

Two radii are recorded. `main_solution_existsUnique` uses the symbolic
`R_traj = 2(‖ā‖ + r₀)` and therefore rests on **exactly** the axioms of
`main_existsUnique` (mirroring `Example81/Analytic.lean`, which uses `‖ā‖ + r₀`).
`main_solution_existsUnique_radius_two` restates it at the round radius `R = 2` with
`K = 5`; it needs the extra exact-ℚ fold `abar_norm_le : ‖ā‖ ≤ 39/50` (so
`2(‖ā‖ + r₀) = 1.560002 ≤ 2`) and therefore carries one additional `native_decide`
axiom of its own.

No analyticity is claimed — see `Applications/IVP/Chebyshev/Analytic.lean`.
-/

open scoped BigOperators
open Metric Set RadiiPolynomial ChebyshevIVP Example1421

noncomputable section

namespace Example1421.Cert

local notation "ābar" => ChebyshevIVP.StdChebIVPData.abar data

/-! ## 1. The vector field -/

/-- The scalar vector field `u ↦ u² − u` of Example 14.2.1, in system form. -/
def f (u : Fin L → ℝ) : Fin L → ℝ := fun l => u l * u l - u l

/-- **The consumer payoff.** The coefficient nonlinearity evaluates to the vector field:
`u_{phi(a)_l}(t) = u_{a_l}(t)² − u_{a_l}(t)` on `[−1, 1]`. The product is discharged by
`eval_mul_of_isSymmetric` — the symmetrized element is symmetric by construction
(`symmetrize_isSymmetric`) and its T-series value is that of `a` itself
(`eval_symmetrize`). -/
lemma hφ_eval (a : XCheb ν_val L) (l : Fin L) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    l1Chebyshev.eval (phi a l) t = f (fun i => l1Chebyshev.eval (a i) t) l := by
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have hs := l1Chebyshev.symmetrize_isSymmetric (a l)
  show l1Chebyshev.eval (Ssym (a l) * Ssym (a l) - Ssym (a l)) t = _
  rw [l1Chebyshev.eval_sub _ _ ht', l1Chebyshev.eval_mul_of_isSymmetric _ _ hs hs ht',
    l1Chebyshev.eval_symmetrize]
  rfl

/-! ## 2. Lipschitz constant on a trajectory ball -/

/-- `u ↦ u² − u` is `(2R+1)`-Lipschitz on `closedBall 0 R`: the difference factors as
`(u − v)(u + v − 1)` and `|u + v − 1| ≤ 2R + 1` on the ball. -/
lemma f_lipschitzOnWith {R : ℝ} {K : NNReal} (hK : 2 * R + 1 ≤ (K : ℝ)) :
    LipschitzOnWith K f (closedBall (0 : Fin L → ℝ) R) := by
  have hbound : ∀ w ∈ closedBall (0 : Fin L → ℝ) R, ∀ l : Fin L, |w l| ≤ R := by
    intro w hw l
    have h := mem_closedBall.mp hw
    rw [dist_zero_right] at h
    have := norm_le_pi_norm w l
    rw [Real.norm_eq_abs] at this
    linarith
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  have hdnn : (0 : ℝ) ≤ dist u v := dist_nonneg
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  rw [dist_pi_le_iff (by positivity)]
  intro l
  have hul := hbound u hu l
  have hvl := hbound v hv l
  have hd : |u l - v l| ≤ dist u v := by
    have := dist_le_pi_dist u v l
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq, show f u l - f v l = (u l - v l) * (u l + v l - 1) by simp only [f]; ring,
    abs_mul]
  have hfac : |u l + v l - 1| ≤ (K : ℝ) := by
    rw [abs_le] at hul hvl ⊢
    constructor <;> linarith [hul.1, hul.2, hvl.1, hvl.2]
  nlinarith [abs_nonneg (u l - v l), abs_nonneg (u l + v l - 1)]

/-! ## 3. The main theorem -/

/-- The certified trajectory radius `2(‖ā‖ + r₀)` (numerically `≈ 1.560002`; the factor `2`
is the storage convention `u_a = a₀ + 2∑ a_k T_k`). -/
abbrev R_traj : ℝ := 2 * (‖ābar‖ + ((r_minus : ℚ) : ℝ))

/-- The finite defect block is a strict contraction (`Z₀ = 10⁻¹⁶ < 1`): the injectivity
input of the F-zero bridge. -/
lemma defect_norm_lt_one : finiteBlockMatrixNorm ν_val data.defect.finBlock < 1 := by
  refine lt_of_le_of_lt Z₀_finBlockNorm_le ?_
  show ((Z₀_bound : ℚ) : ℝ) < 1
  norm_num [Z₀_bound]

/-- **Example 14.2.1, at the level of functions.** The IVP `u̇ = u² − u`, `u(−1) = 1/2` has
a solution on `[−1, 1]` with trajectory in `closedBall 0 R_traj`, and every solution with
that trajectory bound agrees with it on `[−1, 1]`.

Every numerical input is the one `main_existsUnique` already certified (`Y₀_le`, `Z₀_le`,
`Z₁_le`, `Z₂_le`, `radii_neg`, `G_diff`); the only additions are the evaluation identity
`hφ_eval` and the Lipschitz constant. Its axiom set is exactly that of
`main_existsUnique`. -/
theorem main_solution_existsUnique :
    ∃ g : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution f p₀ R_traj g ∧
      ∀ g' : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution f p₀ R_traj g' →
        Set.EqOn g' g (Icc (-1 : ℝ) 1) :=
  data.solution_existsUnique phi p₀ f hφ_eval defect_norm_lt_one G_diff
    (by norm_num [r_minus]) Y₀_le Z₀_le Z₁_le Z₂_le radii_neg
    (f_lipschitzOnWith (K := Real.toNNReal (2 * R_traj + 1))
      (by rw [Real.coe_toNNReal']; exact le_max_left _ _))
    le_rfl

/-! ## 4. The same statement at the round radius `R = 2`

`‖ā‖ ≤ ‖S(ā)‖ ≤ 39/50`: the second inequality is the certificate's own exact-ℚ bound
`Sabar_norm_le`, the first holds because `ā` is stored on the modes `0..N` only
(`l1Chebyshev.norm_le_norm_symmetrize_of_neg_eq_zero`). So `R_traj = 2(‖ā‖ + 10⁻⁶) ≤ 2`
with NO axiom beyond `main_existsUnique`'s. -/

/-- The stored candidate has no negative modes (`embedNatToInt`). -/
private lemma abar_toSeq_neg (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (ābar l) (-((n : ℤ) + 1)) = 0 := by
  show lpAlgRingData.toReal (-((n : ℤ) + 1))
    (ChebyshevIVP.embedNatToInt (data.abar_seq l) (-((n : ℤ) + 1))) = _
  rw [(Int.negSucc_eq n).symm]
  simp [ChebyshevIVP.embedNatToInt, lpAlgRingData.toReal_zero]

/-- `‖ā l‖ ≤ ‖S(ā l)‖ ≤ 39/50` — the certificate's bound transported to the stored element. -/
private lemma abar_norm_component_le (l : Fin L) : ‖ābar l‖ ≤ ((39/50 : ℚ) : ℝ) :=
  (l1Chebyshev.norm_le_norm_symmetrize_of_neg_eq_zero (ābar l) (abar_toSeq_neg l)).trans
    (Sabar_norm_le l)

/-- `‖ā‖ ≤ 39/50` — the numerical candidate's norm, in exact ℚ. -/
lemma abar_norm_le : ‖ābar‖ ≤ ((39/50 : ℚ) : ℝ) :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).mpr abar_norm_component_le

lemma R_traj_le_two : R_traj ≤ 2 := by
  have h := abar_norm_le
  rw [show ((39/50 : ℚ) : ℝ) = 39/50 from by norm_num] at h
  have hr : ((r_minus : ℚ) : ℝ) = 1/1000000 := by norm_num [r_minus]
  simp only [R_traj, hr]
  linarith

/-- **Example 14.2.1 at radius `2`.** Same statement as `main_solution_existsUnique`, with
the round trajectory bound `R = 2` and Lipschitz constant `K = 5`. -/
theorem main_solution_existsUnique_radius_two :
    ∃ g : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution f p₀ 2 g ∧
      ∀ g' : ℝ → Fin L → ℝ, ChebyshevIVP.IsSolution f p₀ 2 g' →
        Set.EqOn g' g (Icc (-1 : ℝ) 1) :=
  data.solution_existsUnique phi p₀ f hφ_eval defect_norm_lt_one G_diff
    (by norm_num [r_minus]) Y₀_le Z₀_le Z₁_le Z₂_le radii_neg
    (f_lipschitzOnWith (R := 2) (K := 5) (by norm_num))
    R_traj_le_two

end Example1421.Cert
