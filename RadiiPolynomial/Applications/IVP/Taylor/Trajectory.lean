import RadiiPolynomial.Applications.IVP.Taylor.Operator
import RadiiPolynomial.Applications.IVP.VectorField
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvaluationDerivative
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# f-F Bridge: Sequence-Space Zeros to Function-Space Solutions

This file establishes the analytic content of the radii-polynomial / Taylor-method
correspondence: a zero `a` of the sequence-space residual `F` on `(ℓ¹_ν)^L` yields the
solution `t ↦ (eval(a_l, t))_l` of the ODE `ẋ = f(x)` on the open interval `(-ν, ν)`, unique
among solutions that stay in a closed ball containing it. The analyticity of this solution is
proved in `Applications/IVP/Taylor/Analyticity.lean`, not here.

## The bridge in classical terms

Given a polynomial vector field `f : ℝ^L → ℝ^L`, encode it as a CompPoly `φ_cpoly`.
This single AST yields two interpretations of the same polynomial:
  - `vectorField φ_cpoly : ℝ^L → ℝ^L` — the original f, evaluated pointwise.
  - `banachField φ_cpoly : (ℓ¹_ν)^L → (ℓ¹_ν)^L` — the Cauchy-product version
    acting on Taylor coefficient sequences.

The IVP residual map is `F(a)_l_n = ivpCoeffs (banachField φ_cpoly) x₀ a l n`,
encoding both the initial condition `a_l_0 = x₀_l` and the recurrence
`(n+1)·a_l_(n+1) = (banachField φ_cpoly a)_l_n`.

The forward bridge `solves_ODE_of_F_zero` shows that `F(a) = 0` implies the function
`x(t) := (eval(a_1, t), ..., eval(a_L, t))` satisfies `ẋ(t) = f(x(t))` on `(-ν, ν)`,
with `x(0) = x₀`.

The two analytical engines are:
  - `l1Weighted.hasDerivAt_eval`: term-by-term differentiation gives
    `(d/dt) eval(a_l, t) = (l1Omega.eval (derivShift a_l)) t`, where
    `derivShift a_l` is the sequence `n ↦ (n+1) · a_l_(n+1)`.
  - `MvPolyBridge.eval_evalBanach`: pointwise evaluation commutes with substitution
    in the polynomial — `eval((banachField φ_cpoly a) l, t) = (φ_cpoly l).evalBanach
    (i ↦ eval(a_i, t)) = (vectorField φ_cpoly (i ↦ eval(a_i, t))) l`.

The recurrence `F(a) = 0` glues these together: it states the sequences
`derivShift a_l` and `(banachField φ_cpoly a) l` are pointwise equal, so their
evaluations agree, so `(d/dt) eval(a_l, t) = f(x(t))_l`.
-/

open RadiiPolynomial MvPolyBridge

namespace IVP

variable {ν : PosReal} {L : ℕ}

/-- The Banach-algebra interpretation of the same CompPoly: arithmetic on Taylor
coefficient sequences with Cauchy product for multiplication. This is the coefficient
nonlinearity `φ` of `Applications/IVP/Taylor/Operator.lean`. -/
noncomputable def banachField (φ_cpoly : Fin L → CompPoly L) (a : XL1 ν L) (l : Fin L) :
    l1Weighted ν :=
  (φ_cpoly l).evalBanach a

/-- **Forward bridge** (book Lemma 8.1.4, forward direction).

If `F(a) = 0` — the IVP residual `ivpCoeffs (banachField φ_cpoly) x₀ a` vanishes at
every component and every Taylor mode — then for every `|t| < ν`, the function
`t ↦ (eval(a_l, t))_l` is differentiable at `t` with derivative `f(x(t))_l`, and
satisfies the initial condition `x(0) = x₀`.

The proof is a direct application of the two analytical engines and the IVP recurrence:

1. `hasDerivAt_eval` gives the formal differentiation
   `(d/dt) eval(a_l, t) = l1Omega.eval (derivShift a_l) t`.
2. `F(a)_l_(n+1) = 0` says `(n+1)·a_l_(n+1) - (banachField φ_cpoly a)_l_n = 0`, i.e.,
   `derivShift a_l` and `banachField φ_cpoly a l` agree as ℕ-indexed sequences.
   Their evaluations therefore agree.
3. `eval_evalBanach` (naturality for universal geometric evaluation) collapses the Banach-algebra evaluation to
   pointwise evaluation: `eval((banachField φ_cpoly a) l, t) = vectorField φ_cpoly
   (i ↦ eval(a_i, t)) l = f(x(t))_l`.
4. `F(a)_l_0 = 0` says `a_l_0 = x₀_l`, and `eval(a_l, 0) = a_l_0` by `eval_at_zero`. -/
theorem solves_ODE_of_F_zero
    (φ_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (a : XL1 ν L)
    (hF : ∀ l n, ivpCoeffs (banachField φ_cpoly) x₀ a l n = 0)
    {t : ℝ} (ht : |t| < ν) :
    (∀ l, HasDerivAt (fun s => l1Weighted.eval (a l) s)
            (vectorField φ_cpoly (fun i => l1Weighted.eval (a i) t) l) t) ∧
    (∀ l, l1Weighted.eval (a l) 0 = x₀ l) := by
  refine ⟨fun l => ?_, fun l => ?_⟩
  · -- Step 1: term-by-term differentiation of eval(a_l, ·) at t
    have h_deriv : HasDerivAt (fun s => l1Weighted.eval (a l) s)
                    (l1Omega.eval (derivShift (a l)) t) t :=
      l1Weighted.hasDerivAt_eval (a l) ht
    -- Step 2: F(a)_l_(n+1) = 0 ⟹ derivShift a_l and banachField a l agree pointwise
    have h_seq_eq : ∀ n, l1Omega.toSeq (derivShift (a l)) n =
                       l1Weighted.toSeq (banachField φ_cpoly a l) n := fun n => by
      have hF_n := hF l (n + 1)
      simp only [ivpCoeffs] at hF_n
      rw [derivShift_apply]
      linarith
    -- Pointwise equality of sequences ⟹ equality of evaluations
    have h_eval_eq : l1Omega.eval (derivShift (a l)) t =
                    l1Weighted.eval (banachField φ_cpoly a l) t := by
      unfold l1Omega.eval l1Weighted.eval
      exact tsum_congr fun n => by rw [h_seq_eq]
    -- Step 3: naturality of evaluation (`eval_evalBanach`) collapses Banach eval to pointwise
    have h_mertens : l1Weighted.eval (banachField φ_cpoly a l) t =
                    vectorField φ_cpoly (fun i => l1Weighted.eval (a i) t) l :=
      eval_evalBanach _ a ht.le
    rwa [h_eval_eq, h_mertens] at h_deriv
  · -- Step 4: initial condition from F(a)_l_0 = 0
    have hF_0 := hF l 0
    simp only [ivpCoeffs] at hF_0
    rw [l1Weighted.eval_at_zero]
    -- hF_0 : toSeq (a l) 0 - x₀ l = 0
    -- Note: eval_at_zero gives eval (a l) 0 = seq (a l) 0 = l1Weighted.toSeq (a l) 0
    linarith

/-- **Function-space uniqueness lift** (the Picard-Lindelöf side of the bridge).

Given a CompPoly nonlinearity `φ_cpoly`, an initial condition `x₀`, and a Taylor
coefficient sequence `a` with `F(a) = 0`, the function `t ↦ eval(a · , t)`
is the unique solution to the IVP `ẋ = f(x), x(0) = x₀` on `(-ν, ν)` among solutions
whose trajectory stays in the closed ball of radius `R`, provided its own trajectory stays
there too (`hf_in_R`). Analyticity of `g` or of `t ↦ eval(a · , t)` is not asserted.

Where the Lipschitz constant comes from: on `closedBall 0 R` the polynomial vector field
is Lipschitz with the explicit syntactic constant `Σ_l |lipschitzBound (φ_cpoly l) R|`
(`exists_lipschitz_vectorField_closedBall`, no compactness or mean-value argument). The
user only supplies the radius `R`, typically `‖ā‖_ν + r₀` from the radii polynomial output
(so that both `eval(a, ·)` and the candidate solution `g` provably stay inside).

The proof composes:
- `solves_ODE_of_F_zero` (forward bridge): `eval(a, ·)` is a solution.
- `hasDerivAt_pi`: assemble per-component derivatives into a Pi-type derivative.
- `exists_lipschitz_vectorField_closedBall`: the syntactic Lipschitz K on the closed ball.
- `ODE_solution_unique_of_mem_Ioo` (Mathlib's Grönwall-based uniqueness theorem): two
  solutions on the same Lipschitz domain agree if they agree at one point. -/
theorem analytic_solution_unique
    (φ_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (a : XL1 ν L)
    (hF : ∀ l n, ivpCoeffs (banachField φ_cpoly) x₀ a l n = 0)
    {R : ℝ}
    (hf_in_R : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      (fun l => l1Weighted.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) R)
    (g : ℝ → Fin L → ℝ)
    (hg_in_R : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      g t ∈ Metric.closedBall (0 : Fin L → ℝ) R)
    (hg_init : g 0 = x₀)
    (hg_solves : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      HasDerivAt g (vectorField φ_cpoly (g t)) t) :
    Set.EqOn g (fun t => fun l => l1Weighted.eval (a l) t)
      (Set.Ioo (-(ν : ℝ)) ν) := by
  have hν : (0 : ℝ) < ν := ν.2
  have h_zero_mem : (0 : ℝ) ∈ Set.Ioo (-(ν : ℝ)) ν := ⟨by linarith, hν⟩
  -- Lipschitz constant on the closed ball, read off the polynomial syntax
  obtain ⟨K, hLip⟩ := exists_lipschitz_vectorField_closedBall φ_cpoly R
  -- Forward bridge: eval(a, ·) is a solution
  have h_eval_solves : ∀ t ∈ Set.Ioo (-(ν : ℝ)) ν,
      HasDerivAt (fun s => fun l => l1Weighted.eval (a l) s)
        (vectorField φ_cpoly (fun l => l1Weighted.eval (a l) t)) t := by
    intro t ht
    have h_abs : |t| < (ν : ℝ) := abs_lt.mpr ht
    have ⟨h_per_comp, _⟩ := solves_ODE_of_F_zero φ_cpoly x₀ a hF h_abs
    exact hasDerivAt_pi.mpr h_per_comp
  -- IC: eval(a, ·)(0) = x₀ (forced by F(a)_l_0 = 0)
  have h_eval_init : (fun l => l1Weighted.eval (a l) 0) = x₀ := by
    funext l
    have h_abs : |(0 : ℝ)| < (ν : ℝ) := by rw [abs_zero]; exact hν
    have ⟨_, h_init⟩ := solves_ODE_of_F_zero φ_cpoly x₀ a hF h_abs
    exact h_init l
  -- Grönwall-based uniqueness
  exact ODE_solution_unique_of_mem_Ioo
    (v := fun _ => vectorField φ_cpoly)
    (s := fun _ => Metric.closedBall (0 : Fin L → ℝ) R) (K := K)
    (fun _ _ => hLip) h_zero_mem
    (fun t ht => ⟨hg_solves t ht, hg_in_R t ht⟩)
    (fun t ht => ⟨h_eval_solves t ht, hf_in_R t ht⟩)
    (by rw [hg_init, h_eval_init])

/-- **Per-component trajectory bound.** On the closed interval `|t| ≤ ν` the `l`-th
component of the trajectory `t ↦ (eval(a_l, t))_l` is bounded by the weighted norm `‖a_l‖`
of its own coefficient sequence (`l1Weighted.abs_eval_le`). The box face
`eval_traj_in_box` and the sup-norm ball face `eval_traj_in_closedBall` are its two
packagings. -/
lemma abs_eval_traj_le (a : XL1 ν L) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) (l : Fin L) :
    |l1Weighted.eval (a l) t| ≤ ‖a l‖ :=
  l1Weighted.abs_eval_le (a l) ht

/-- **Box face of the trajectory bound.** On `|t| ≤ ν` the trajectory
`t ↦ (eval(a_l, t))_l` stays in the coordinate box `∏_l [-‖a_l‖, ‖a_l‖]`, one radius per
component. It keeps the per-component information that the sup-norm ball
`eval_traj_in_closedBall` (radius `‖a‖ = max_l ‖a_l‖`) discards; the box lies inside that
ball, so it refines the enclosure without touching the uniqueness side of
`analytic_solution_unique`. -/
lemma eval_traj_in_box (a : XL1 ν L) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) :
    (fun l => l1Weighted.eval (a l) t) ∈
      Set.pi Set.univ fun l => Metric.closedBall (0 : ℝ) ‖a l‖ :=
  Set.mem_univ_pi.mpr fun l => by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_eval_traj_le a ht l

/-- **Box face around a certified centre.** If `a` lies in the closed ball of radius `r`
around `ā` (the radii-polynomial output `xTilde ∈ closedBall ā r₀`), then on `|t| ≤ ν` the
trajectory of `a` stays in the box `∏_l [-(‖ā_l‖ + r), ‖ā_l‖ + r]`: each component keeps
its own centre norm `‖ā_l‖`, where the ball face charges every component `‖ā‖ + r`. -/
lemma eval_traj_in_box_of_mem_closedBall {a abar : XL1 ν L} {r : ℝ}
    (ha : a ∈ Metric.closedBall abar r) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) :
    (fun l => l1Weighted.eval (a l) t) ∈
      Set.pi Set.univ fun l => Metric.closedBall (0 : ℝ) (‖abar l‖ + r) := by
  refine Set.pi_mono (fun l _ => ?_) (eval_traj_in_box a ht)
  exact Metric.closedBall_subset_closedBall ((norm_le_insert' (a l) (abar l)).trans
    (add_le_add le_rfl ((norm_le_pi_norm (a - abar) l).trans (mem_closedBall_iff_norm.mp ha))))

/-- The pointwise trajectory `t ↦ (eval(a_l, t))_l` of an `XL1` element stays
within the closed ball of radius `‖a‖` (the XL1 sup-of-ℓ¹ norm) on the closed interval
`|t| ≤ ν`. Used to discharge the trajectory hypothesis `hf_in_R` in
`analytic_solution_unique`: take `R = ‖a‖`, or any larger value.

For any `xTilde ∈ closedBall ā r₀` from the radii polynomial, this gives the
explicit trajectory radius `R = ‖ā‖ + r₀` via the triangle inequality. Corollary of the
per-component bound `abs_eval_traj_le`; the box faces `eval_traj_in_box` and
`eval_traj_in_box_of_mem_closedBall` keep one radius per component. -/
lemma eval_traj_in_closedBall (a : XL1 ν L) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) :
    (fun l => l1Weighted.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) ‖a‖ := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  exact fun l => (abs_eval_traj_le a ht l).trans (norm_le_pi_norm a l)

/-- The derivative of a `CompPoly` component of `banachField` at any point `a`, as a sum of
left multiplications by the partial derivatives evaluated at `a`. -/
theorem fderiv_banachField_apply' (f_cpoly : Fin L → CompPoly L) (a h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) a) h =
      ∑ m : Fin L, ((f_cpoly l).pderiv m).evalBanach a * h m := by
  have hfun : (fun a : XL1 ν L => IVP.banachField f_cpoly a l) =
      fun a => MvPolynomial.aeval a (f_cpoly l).toMvPoly :=
    funext fun a => compPoly_evalBanach_eq_aeval (f_cpoly l) a
  rw [hfun, fderiv_aeval]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← CompPoly.pderiv_toMvPoly, ← compPoly_evalBanach_eq_aeval]

end IVP
