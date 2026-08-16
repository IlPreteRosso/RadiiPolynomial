import RadiiPolynomial.Applications.IVP.Taylor.Operator
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvaluationDerivative
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# f-F Bridge: Sequence-Space Zeros to Function-Space Solutions

This file establishes the analytic content of the radii-polynomial / Taylor-method
correspondence: a zero of the sequence-space residual `F` on `(ℓ¹_ν)^L` corresponds
to an analytic solution of the ODE `ẋ = f(x)` on the open interval `(-ν, ν)`.

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

/-- The polynomial vector field `f : ℝ^L → ℝ^L` derived from a CompPoly representation.
This is the original ODE right-hand side recovered from its symbolic encoding. -/
noncomputable def vectorField (φ_cpoly : Fin L → CompPoly L) (x : Fin L → ℝ) (l : Fin L) :
    ℝ :=
  (φ_cpoly l).evalBanach x

/-- The Banach-algebra interpretation of the same CompPoly: arithmetic on Taylor
coefficient sequences with Cauchy product for multiplication. This is `φ` in the
Setup-IVP notation. -/
noncomputable def banachField (φ_cpoly : Fin L → CompPoly L) (a : XL1 ν L) (l : Fin L) :
    l1Weighted ν :=
  (φ_cpoly l).evalBanach a

/-- The vector field `vectorField φ_cpoly : ℝ^L → ℝ^L` is `C^∞` at every point.
Polynomial maps are smooth; this feeds into Picard-Lindelöf via Mathlib's
`ContDiffOn.exists_lipschitzOnWith` for the function-space uniqueness lift. -/
theorem contDiff_vectorField (φ_cpoly : Fin L → CompPoly L) (l : Fin L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => vectorField φ_cpoly x l) :=
  MvPolyBridge.contDiff_evalBanach (φ_cpoly l)

/-- The full vector field `vectorField φ_cpoly : ℝ^L → (Fin L → ℝ)` is `C^∞`. -/
theorem contDiff_vectorField_pi (φ_cpoly : Fin L → CompPoly L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => vectorField φ_cpoly x) :=
  contDiff_pi.mpr (contDiff_vectorField φ_cpoly)

/-- The vector field is differentiable. (Derived from `contDiff_vectorField`.) -/
theorem differentiable_vectorField (φ_cpoly : Fin L → CompPoly L) (l : Fin L) :
    Differentiable ℝ (fun x : Fin L → ℝ => vectorField φ_cpoly x l) :=
  MvPolyBridge.differentiable_evalBanach (φ_cpoly l)

/-- The full vector field is differentiable. -/
theorem differentiable_vectorField_pi (φ_cpoly : Fin L → CompPoly L) :
    Differentiable ℝ (fun x : Fin L → ℝ => vectorField φ_cpoly x) :=
  differentiable_pi.mpr (differentiable_vectorField φ_cpoly)

/-- On any closed ball in `ℝ^L`, the polynomial vector field is Lipschitz with some
constant. Existence form — the explicit constant comes from `ContDiffOn.exists_lipschitzOnWith`,
applied to the smooth function on the (compact, convex) closed ball. -/
theorem exists_lipschitz_vectorField_closedBall
    (φ_cpoly : Fin L → CompPoly L) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun x : Fin L → ℝ => vectorField φ_cpoly x)
                  (Metric.closedBall (0 : Fin L → ℝ) R) :=
  (contDiff_vectorField_pi φ_cpoly).contDiffOn.exists_lipschitzOnWith
    (by decide) (convex_closedBall _ _) (isCompact_closedBall _ _)

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
3. `eval_evalBanach` (Mertens-recursive) collapses the Banach-algebra evaluation to
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
    -- Step 3: Mertens-recursive bridge collapses Banach eval to pointwise
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
coefficient sequence `a` with `F(a) = 0`, the analytic function `t ↦ eval(a · , t)`
is the unique solution to the IVP `ẋ = f(x), x(0) = x₀` on `(-ν, ν)` among solutions
whose trajectory stays in the closed ball of radius `R`.

Where the Lipschitz constant comes from: the polynomial vector field is `C^∞`
(`contDiff_vectorField_pi`), so on the compact convex `closedBall 0 R` it is Lipschitz
with *some* constant — extracted by Mathlib's `ContDiffOn.exists_lipschitzOnWith`
(itself proved via the Mean Value Inequality). The user only supplies the radius `R`,
typically `‖ā‖_ν + r₀` from the radii polynomial output (so that both `eval(a, ·)` and
the candidate solution `g` provably stay inside).

The proof composes:
- `solves_ODE_of_F_zero` (forward bridge): `eval(a, ·)` is a solution.
- `hasDerivAt_pi`: assemble per-component derivatives into a Pi-type derivative.
- `exists_lipschitz_vectorField_closedBall`: extract Lipschitz K on the closed ball.
- `ODE_solution_unique_of_mem_Ioo` (Mathlib's Picard-Lindelöf via Grönwall): two
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
  -- Lipschitz constant on the closed ball, from ContDiff + compactness + convexity
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
  -- Picard-Lindelöf via Grönwall
  exact ODE_solution_unique_of_mem_Ioo
    (v := fun _ => vectorField φ_cpoly)
    (s := fun _ => Metric.closedBall (0 : Fin L → ℝ) R) (K := K)
    (fun _ _ => hLip) h_zero_mem
    (fun t ht => ⟨hg_solves t ht, hg_in_R t ht⟩)
    (fun t ht => ⟨h_eval_solves t ht, hf_in_R t ht⟩)
    (by rw [hg_init, h_eval_init])

/-- The pointwise trajectory `t ↦ (eval(a_l, t))_l` of an `XL1` element stays
within the closed ball of radius `‖a‖` (the XL1 sup-of-ℓ¹ norm) on the disk
`|t| ≤ ν`. Used to discharge the trajectory hypothesis `hf_in_R` in
`analytic_solution_unique`: take `R = ‖a‖`, or any larger value.

For any `xTilde ∈ closedBall ā r₀` from the radii polynomial, this gives the
explicit trajectory radius `R = ‖ā‖ + r₀` via the triangle inequality. -/
lemma eval_traj_in_closedBall (a : XL1 ν L) {t : ℝ} (ht : |t| ≤ (ν : ℝ)) :
    (fun l => l1Weighted.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) ‖a‖ := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro l
  show |l1Weighted.eval (a l) t| ≤ ‖a‖
  exact (l1Weighted.abs_eval_le (a l) ht).trans (norm_le_pi_norm a l)

end IVP
