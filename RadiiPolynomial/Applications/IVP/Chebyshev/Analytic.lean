import RadiiPolynomial.Applications.IVP.Chebyshev.Trajectory
import RadiiPolynomial.Applications.IVP.Chebyshev.Standard

/-!
# Generic glue: from a `StdChebIVPData` certificate to a certified solution on `[-1, 1]`

Combines the sequence-space existence/uniqueness theorem `StdChebIVPData.existsUnique`
(a zero of the preconditioned map `G` inside a ball around the numerical candidate) with
the f-F bridge of `Chebyshev/Trajectory.lean` (`solves_ODE_of_F_zero`, `solution_unique`)
into the function-level statement: the IVP `u̇ = f(u)`, `u(-1) = p` has a solution on
`[-1, 1]`, and it is the only one that stays in the trajectory ball.

## Surface

- `ChebyshevIVP.StdChebIVPData.chebyshevIvpCoeffs_zero_of_G_zero` — the F-zero bridge:
  `G(a) = 0` forces every coefficient equation `F(a)_{l,k}` to vanish, given that the
  finite defect block has norm `< 1` (which the radii polynomial's `Z₀ < 1` supplies).
  Mirrors `IVP.StdIVPData.ivpCoeffs_zero_of_G_zero`.
- `ChebyshevIVP.StdChebIVPData.neg_modes_zero_of_G_zero` — the negative modes of a zero of
  `G` vanish, straight from the pass-through identity `G(a)_k = a_k` for `k < 0`
  (`embedWithPassThrough`); no injectivity argument is involved.
- `ChebyshevIVP.IsSolution f p R g` (`structure`) — "`g` solves `u̇ = f(u)`, `u(-1) = p`
  on `[-1, 1]` with trajectory in `closedBall 0 R`". Four fields: `init`, `cont`, `in_R`,
  `solves` (the last is the one-sided `HasDerivWithinAt … (Ici t)` form on `[-1, 1)`, which
  is what Mathlib's endpoint uniqueness theorem consumes).
- `ChebyshevIVP.x_sol xTilde` — the canonical solution `t ↦ (u_{xTilde l}(t))_l` read off a
  sequence-space zero through `l1Chebyshev.eval` (book (14.9)).
- `StdChebIVPData.x_sol_isSolution` / `x_sol_hasDerivAt` / `solution_eq_canonical` /
  `solution_existsUnique`.
- The parallel declarations ending in `_of_two_le` use contractive evaluation at
  weights `ν ≥ 2`, replacing the trajectory radius `2(‖ā‖ + r₀)` by `‖ā‖ + r₀`.

**No analyticity is claimed.** The conclusion is `C¹` on the interval plus uniqueness in
the trajectory ball; Taylor's `IsAnalyticSolution` / `analytic_existsUnique` names are
deliberately *not* mirrored, because a Bernstein-ellipse statement would need machinery
that is in neither the book nor this repository. The `IsSolution` naming records the
weaker claim.
-/

open RadiiPolynomial Set Metric

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L N : ℕ}

/-- `g : ℝ → Fin L → ℝ` solves the IVP `u̇ = f(u)`, `u(-1) = p` on `[-1, 1]` with trajectory
in `closedBall 0 R`.

Packaged as a `structure` so callers write `hg.init`, `hg.cont`, `hg.in_R`, `hg.solves`.
The ODE field is the one-sided form on `[-1, 1)`: the initial time is the *endpoint*
`t = -1`, so the derivative is taken within `Ici t`, exactly the hypothesis shape of
`ODE_solution_unique_of_mem_Icc_right`. -/
structure IsSolution (f : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) (R : ℝ)
    (g : ℝ → Fin L → ℝ) : Prop where
  /-- The initial condition, at the left endpoint `t = -1`. -/
  init : g (-1) = p
  /-- `g` is continuous on `[-1, 1]`. -/
  cont : ContinuousOn g (Icc (-1 : ℝ) 1)
  /-- The trajectory stays in `closedBall 0 R` on `[-1, 1]`. -/
  in_R : ∀ t ∈ Icc (-1 : ℝ) 1, g t ∈ closedBall (0 : Fin L → ℝ) R
  /-- `g` solves the ODE from the right at every `t ∈ [-1, 1)`. -/
  solves : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt g (f (g t)) (Ici t) t

/-- The canonical solution `t ↦ (u_{xTilde l}(t))_l` attached to a sequence-space zero,
each component read as the T-series of book (14.9) (`l1Chebyshev.eval`). -/
def x_sol [Fact (1 ≤ (ν : ℝ))] (xTilde : XCheb ν L) : ℝ → Fin L → ℝ :=
  fun t l => l1Chebyshev.eval (xTilde l) t

namespace StdChebIVPData

variable [NeZero L] [Fact (1 ≤ (ν : ℝ))] (d : StdChebIVPData ν L N)
  (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)

/-! ### The F-zero bridge -/

/-- Non-negative modes of `G(a)` are the preconditioned coefficient equations. -/
lemma G_toSeq_natCast (a : XCheb ν L) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (d.G φ p a l) (↑n : ℤ)
      = d.approxInverse.action (chebyshevIvpCoeffs φ p a) l n := by
  show lpOneAlg.toRealSeq (d.G φ p a l) (↑n : ℤ) = _
  simp [lpOneAlg.toRealSeq, G, chebyshevIvpMap, embedWithPassThrough,
    lpAlgRingData.toReal_ofReal]

/-- Negative modes of `G(a)` are those of `a` (`embedWithPassThrough`): the IVP equations
do not constrain them. -/
lemma G_toSeq_negSucc (a : XCheb ν L) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (d.G φ p a l) (Int.negSucc m)
      = l1Chebyshev.toSeq (a l) (Int.negSucc m) := by
  show lpOneAlg.toRealSeq (d.G φ p a l) (Int.negSucc m) = _
  simp only [lpOneAlg.toRealSeq, G, chebyshevIvpMap, embedWithPassThrough]
  rfl

/-- **F-zero bridge** (Chebyshev mirror of `IVP.StdIVPData.ivpCoeffs_zero_of_G_zero`).
`d.G φ p a = 0` forces the raw coefficient equations `chebyshevIvpCoeffs φ p a` to vanish,
provided the finite defect block has operator norm `< 1` — which is precisely what the
radii polynomial's `Z₀ < 1` gives.

`G = approxInverse.action ∘ chebyshevIvpCoeffs` on the non-negative modes, so `G a = 0`
gives action-zero; `finite_block_injective_of_defect_norm_lt_one` inverts the finite block
and `seq_zero_of_action_zero` inverts the `1/(2k)` tail. -/
lemma chebyshevIvpCoeffs_zero_of_G_zero
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    {a : XCheb ν L} (hG : d.G φ p a = 0) :
    ∀ l k, chebyshevIvpCoeffs φ p a l k = 0 := by
  have h_action : ∀ l n, d.approxInverse.action (chebyshevIvpCoeffs φ p a) l n = 0 :=
    fun l n => by rw [← d.G_toSeq_natCast φ p a l n, congrFun hG l]; simp
  refine SystemBlockDiagData.seq_zero_of_action_zero d.approxInverse
    (finite_block_injective_of_defect_norm_lt_one d.approxInverse d.approxDeriv hZ₀_lt_one)
    (fun l n hn => ?_) h_action
  rw [d.htail_diag_inv l n hn]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact one_div_ne_zero (by simpa using hn0)

/-- Negative modes of a zero of `G` vanish, directly from the pass-through identity. -/
lemma neg_modes_zero_of_G_zero {a : XCheb ν L} (hG : d.G φ p a = 0) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (a l) (Int.negSucc m) = 0 := by
  rw [← d.G_toSeq_negSucc φ p a l m, congrFun hG l]; simp

/-! ### From a certified zero to a certified solution -/

variable (f : (Fin L → ℝ) → Fin L → ℝ) (xTilde : XCheb ν L)

/-- The trajectory of a point of the certificate ball stays in `closedBall 0 R` as soon as
`R` dominates `2(‖ā‖ + r₀)`. The factor `2` is the storage convention of book (14.9). -/
lemma x_sol_mem_closedBall {r₀ R : ℝ}
    (hball : xTilde ∈ closedBall (abar d) r₀) (hR : 2 * (‖abar d‖ + r₀) ≤ R)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    x_sol xTilde t ∈ closedBall (0 : Fin L → ℝ) R := by
  have hnorm : ‖xTilde‖ ≤ ‖abar d‖ + r₀ := by
    have h := mem_closedBall.mp hball
    rw [dist_eq_norm] at h
    have := norm_add_le (abar d) (xTilde - abar d)
    rw [add_sub_cancel] at this
    linarith
  exact closedBall_subset_closedBall (by linarith)
    (eval_traj_in_closedBall xTilde ht)

/-- At weights `ν ≥ 2`, the trajectory of a point of the certificate ball stays in
`closedBall 0 R` as soon as `R` dominates `‖ā‖ + r₀`. -/
lemma x_sol_mem_closedBall_of_two_le (hν : (2 : ℝ) ≤ (ν : ℝ)) {r₀ R : ℝ}
    (hball : xTilde ∈ closedBall (abar d) r₀) (hR : ‖abar d‖ + r₀ ≤ R)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    x_sol xTilde t ∈ closedBall (0 : Fin L → ℝ) R := by
  have hnorm : ‖xTilde‖ ≤ ‖abar d‖ + r₀ := by
    have h := mem_closedBall.mp hball
    rw [dist_eq_norm] at h
    have := norm_add_le (abar d) (xTilde - abar d)
    rw [add_sub_cancel] at this
    linarith
  exact closedBall_subset_closedBall (hnorm.trans hR)
    (eval_traj_in_closedBall_of_two_le hν xTilde ht)

/-- **Existence**: the T-series of a certified zero solves the IVP on `[-1, 1]`. -/
theorem x_sol_isSolution
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1) {r₀ R : ℝ}
    (hball : xTilde ∈ closedBall (abar d) r₀) (hG : d.G φ p xTilde = 0)
    (hR : 2 * (‖abar d‖ + r₀) ≤ R) :
    IsSolution f p R (x_sol xTilde) := by
  obtain ⟨hinit, hcont, hderiv, -⟩ :=
    solves_ODE_of_F_zero φ p xTilde f (fun l t ht => hφ xTilde l t ht)
      (d.chebyshevIvpCoeffs_zero_of_G_zero φ p hZ₀_lt_one hG)
  exact ⟨funext hinit, hcont, fun t ht => d.x_sol_mem_closedBall xTilde hball hR ht, hderiv⟩

/-- **Sharper existence at weights `ν ≥ 2`**: the T-series of a certified zero
solves the IVP in any trajectory ball whose radius dominates `‖ā‖ + r₀`. -/
theorem x_sol_isSolution_of_two_le
    (hν : (2 : ℝ) ≤ (ν : ℝ))
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1) {r₀ R : ℝ}
    (hball : xTilde ∈ closedBall (abar d) r₀) (hG : d.G φ p xTilde = 0)
    (hR : ‖abar d‖ + r₀ ≤ R) :
    IsSolution f p R (x_sol xTilde) := by
  obtain ⟨hinit, hcont, hderiv, -⟩ :=
    solves_ODE_of_F_zero φ p xTilde f (fun l t ht => hφ xTilde l t ht)
      (d.chebyshevIvpCoeffs_zero_of_G_zero φ p hZ₀_lt_one hG)
  exact ⟨funext hinit, hcont,
    fun t ht => d.x_sol_mem_closedBall_of_two_le xTilde hν hball hR ht, hderiv⟩

/-- The canonical solution is two-sided differentiable in the interior `(-1, 1)`; the
`IsSolution` field only records the one-sided derivative that uniqueness consumes. -/
theorem x_sol_hasDerivAt
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    (hG : d.G φ p xTilde = 0) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (x_sol xTilde) (f (x_sol xTilde t)) t :=
  (solves_ODE_of_F_zero φ p xTilde f (fun l t ht => hφ xTilde l t ht)
    (d.chebyshevIvpCoeffs_zero_of_G_zero φ p hZ₀_lt_one hG)).2.2.2 t ht

/-- **Pinning**: any solution staying in the trajectory ball agrees with the canonical one
on `[-1, 1]` (Picard–Lindelöf from the endpoint `t = -1`). -/
theorem solution_eq_canonical
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1) {K : NNReal} {r₀ R : ℝ}
    (hf_lip : LipschitzOnWith K f (closedBall (0 : Fin L → ℝ) R))
    (hball : xTilde ∈ closedBall (abar d) r₀) (hG : d.G φ p xTilde = 0)
    (hR : 2 * (‖abar d‖ + r₀) ≤ R)
    (g : ℝ → Fin L → ℝ) (hg : IsSolution f p R g) :
    EqOn g (x_sol xTilde) (Icc (-1 : ℝ) 1) :=
  solution_unique φ p xTilde f (fun l t ht => hφ xTilde l t ht)
    (d.chebyshevIvpCoeffs_zero_of_G_zero φ p hZ₀_lt_one hG) hf_lip
    (fun _ ht => d.x_sol_mem_closedBall xTilde hball hR ht)
    g hg.cont (fun t ht => hg.in_R t (Ico_subset_Icc_self ht)) hg.solves hg.init

/-- **Sharper pinning at weights `ν ≥ 2`**: uniqueness holds in any trajectory
ball whose radius dominates `‖ā‖ + r₀`. -/
theorem solution_eq_canonical_of_two_le
    (hν : (2 : ℝ) ≤ (ν : ℝ))
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1) {K : NNReal} {r₀ R : ℝ}
    (hf_lip : LipschitzOnWith K f (closedBall (0 : Fin L → ℝ) R))
    (hball : xTilde ∈ closedBall (abar d) r₀) (hG : d.G φ p xTilde = 0)
    (hR : ‖abar d‖ + r₀ ≤ R)
    (g : ℝ → Fin L → ℝ) (hg : IsSolution f p R g) :
    EqOn g (x_sol xTilde) (Icc (-1 : ℝ) 1) :=
  solution_unique φ p xTilde f (fun l t ht => hφ xTilde l t ht)
    (d.chebyshevIvpCoeffs_zero_of_G_zero φ p hZ₀_lt_one hG) hf_lip
    (fun _ ht => d.x_sol_mem_closedBall_of_two_le xTilde hν hball hR ht)
    g hg.cont (fun t ht => hg.in_R t (Ico_subset_Icc_self ht)) hg.solves hg.init

end StdChebIVPData

namespace StdChebIVPData

variable [NeZero L] [Fact (1 ≤ (ν : ℝ))] (d : StdChebIVPData ν L N)
  (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
  (f : (Fin L → ℝ) → Fin L → ℝ)

/-- **Existence + uniqueness on `[-1, 1]`**, straight from the four radii-polynomial
bounds. The `∃` paired with the universal clause is the "∃! modulo `Set.EqOn`" pattern of
`IVP.StdIVPData.analytic_existsUnique`: candidates may differ outside `[-1, 1]`.

`hφ` is the only equation-specific input beyond the certificate: it says the coefficient
nonlinearity `φ` evaluates to the vector field `f` of the ODE, which on the Chebyshev side
is `l1Chebyshev.eval_mul_of_isSymmetric` applied to the symmetrized element.
No analyticity is asserted — see the module docstring. -/
theorem solution_existsUnique
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    (hG_diff : Differentiable ℝ (d.G φ p))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G φ p (abar d)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (XCheb ν L) - d.composedApproxCLM‖ ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall (abar d) r₀,
      ‖fderiv ℝ (d.G φ p) c - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {K : NNReal} {R : ℝ}
    (hf_lip : LipschitzOnWith K f (closedBall (0 : Fin L → ℝ) R))
    (hR : 2 * (‖abar d‖ + r₀) ≤ R) :
    ∃ g : ℝ → Fin L → ℝ, IsSolution f p R g ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution f p R g' → EqOn g' g (Icc (-1 : ℝ) 1) := by
  obtain ⟨xTilde, hball, hG⟩ :=
    (d.existsUnique φ p hG_diff hr₀ hY₀ hZ₀ hZ₁ hZ₂ h_radii).exists
  exact ⟨x_sol xTilde,
    d.x_sol_isSolution φ p f xTilde hφ hZ₀_lt_one hball hG hR,
    fun g' hg' => d.solution_eq_canonical φ p f xTilde hφ hZ₀_lt_one hf_lip hball hG hR g' hg'⟩

/-- **Sharper existence + uniqueness at weights `ν ≥ 2`.** This is
`solution_existsUnique` with the contractive trajectory bound `‖ā‖ + r₀` in
place of `2(‖ā‖ + r₀)`. -/
theorem solution_existsUnique_of_two_le
    (hν : (2 : ℝ) ≤ (ν : ℝ))
    (hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hZ₀_lt_one : finiteBlockMatrixNorm ν d.defect.finBlock < 1)
    (hG_diff : Differentiable ℝ (d.G φ p))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G φ p (abar d)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (XCheb ν L) - d.composedApproxCLM‖ ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall (abar d) r₀,
      ‖fderiv ℝ (d.G φ p) c - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {K : NNReal} {R : ℝ}
    (hf_lip : LipschitzOnWith K f (closedBall (0 : Fin L → ℝ) R))
    (hR : ‖abar d‖ + r₀ ≤ R) :
    ∃ g : ℝ → Fin L → ℝ, IsSolution f p R g ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution f p R g' → EqOn g' g (Icc (-1 : ℝ) 1) := by
  obtain ⟨xTilde, hball, hG⟩ :=
    (d.existsUnique φ p hG_diff hr₀ hY₀ hZ₀ hZ₁ hZ₂ h_radii).exists
  exact ⟨x_sol xTilde,
    d.x_sol_isSolution_of_two_le φ p f xTilde hν hφ hZ₀_lt_one hball hG hR,
    fun g' hg' => d.solution_eq_canonical_of_two_le φ p f xTilde hν hφ hZ₀_lt_one
      hf_lip hball hG hR g' hg'⟩

end StdChebIVPData

end ChebyshevIVP

end
