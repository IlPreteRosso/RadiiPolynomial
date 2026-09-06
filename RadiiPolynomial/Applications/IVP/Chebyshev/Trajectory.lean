import RadiiPolynomial.Applications.IVP.Chebyshev.Operator
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.EvaluationBounds
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Chebyshev f-F bridge: sequence-space zeros to solutions of the IVP on `[-1, 1]`

A stored Chebyshev element `a : l1Chebyshev ν` is read as the function of book (14.9),
`u_a(t) = a₀ + 2 ∑_{k ≥ 1} a_k T_k(t)` (`l1Chebyshev.eval`, modes `k ≥ 0` only). The
zero-finding map `chebyshevIvpCoeffs φ p` (book (14.11)) was *derived* by integrating that
series termwise, so its zeros are read back the same way — the **integral-equation route**:

* `chebAntideriv`, `hasDerivAt_chebAntideriv` — book (14.3), the antiderivative of `T_{k+1}`
  (absent from Mathlib);
* `chebyshevIntegrate := -chebyshevShiftDiv` — the coefficient-level integration operator,
  `(∫c)_k = (c_{k-1} - c_{k+1}) / (2k)` for `k ≥ 1`, `(∫c)_0 = 0`;
* `integral_eval` — **termwise integration**, `∫_{-1}^t u_c = u_{∫c}(t) - u_{∫c}(-1)`: the
  Σ/∫ interchange the book skips (p. 328), proved by dominated convergence under the
  constant dominant `|c_{k+1}|` (`intervalIntegral.hasSum_integral_of_dominated_convergence`),
  then one reindexing of the ℕ-sum;
* `eval_eq_integral_of_F_zero` — `F(a) = 0 ⟹ u_{a_l}(t) = p_l + ∫_{-1}^t u_{φ(a)_l}`: rows
  `k ≥ 1` of `F` identify `a` with `∫φ(a)` on the positive modes, row 0 with
  `eval_at_neg_one` fixes the constant;
* `solves_ODE_of_F_zero` — by the fundamental theorem of calculus, the trajectory
  `t ↦ (u_{a_l}(t))_l` is continuous on `[-1, 1]`, right-differentiable on `[-1, 1)` and
  differentiable on `(-1, 1)` with derivative `f(u(t))`, and `u(-1) = p`;
* `solution_unique` — any solution of the IVP that stays in a ball on which `f` is
  Lipschitz agrees with the trajectory on `[-1, 1]` (Mathlib's one-sided
  `ODE_solution_unique_of_mem_Icc_right`, the initial time being the endpoint `-1`);
* `eval_traj_in_closedBall` — the trajectory radius `2‖a‖` (the factor 2 is the storage
  convention: `‖symmetrize a‖ ≤ 2‖a‖`).
* `eval_traj_in_closedBall_of_two_le` — at weights `ν ≥ 2`, evaluation is contractive
  already on the production storage carrier, so the trajectory radius improves to `‖a‖`.

The nonlinearity enters only through the hypothesis `hφ : u_{φ(a)_l}(t) = f(u(t))_l` on
`[-1, 1]`, which a concrete example discharges with `eval_mul_of_isSymmetric` and friends.
Mirrors `Applications/IVP/Taylor/Trajectory.lean`, which is untouched.
-/

open RadiiPolynomial Set Polynomial.Chebyshev
open scoped BigOperators Topology

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L : ℕ}

/-! ### Antiderivatives of the Chebyshev polynomials (book (14.3)) -/

/-- `A_k(t) := T_{k+2}(t) / (2(k+2)) - T_k(t) / (2k)`, an antiderivative of `T_{k+1}` — book
(14.3) in ℕ-shifted form. Lean's `x / 0 = 0` kills the `T_0 / 0` term at `k = 0`, so the
formula is uniform in `k`. -/
def chebAntideriv (k : ℕ) (t : ℝ) : ℝ :=
  (T ℝ ((k + 2 : ℕ) : ℤ)).eval t / (2 * ((k + 2 : ℕ) : ℝ)) -
    (T ℝ (k : ℤ)).eval t / (2 * (k : ℝ))

/-- `A_k' = T_{k+1}`, from `T_n' = n U_{n-1}` and `2 T_{n+2} = U_{n+2} - U_n`. -/
theorem hasDerivAt_chebAntideriv (k : ℕ) (t : ℝ) :
    HasDerivAt (chebAntideriv k) ((T ℝ ((k + 1 : ℕ) : ℤ)).eval t) t := by
  have h1 := ((T ℝ ((k + 2 : ℕ) : ℤ)).hasDerivAt t).div_const (2 * ((k + 2 : ℕ) : ℝ))
  have h2 := ((T ℝ (k : ℤ)).hasDerivAt t).div_const (2 * (k : ℝ))
  rw [T_derivative_eq_U] at h1 h2
  refine (h1.sub h2).congr_deriv ?_
  have h3 := congrArg (Polynomial.eval t) (two_mul_T_eq_U_sub_U ℝ ((k : ℤ) - 1))
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_sub, Int.cast_natCast,
    Polynomial.eval_natCast] at h3 ⊢
  rw [show (k : ℤ) - 1 + 2 = ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h3
  rw [show ((k + 2 : ℕ) : ℤ) - 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
  cases k with
  | zero => simp [U_neg_one] at h3 ⊢; linarith
  | succ k =>
    push_cast at h3 ⊢
    field_simp
    linear_combination -h3

/-- `∫_{-1}^t T_{k+1} = A_k(t) - A_k(-1)`. -/
theorem integral_T_succ (k : ℕ) (t : ℝ) :
    ∫ s in (-1 : ℝ)..t, (T ℝ ((k + 1 : ℕ) : ℤ)).eval s
      = chebAntideriv k t - chebAntideriv k (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_chebAntideriv k s)
    ((Polynomial.continuous _).intervalIntegrable _ _)

private lemma abs_T_div_two_mul_le {u : ℝ} (hu : |u| ≤ 1) (n : ℤ) (d : ℕ) :
    |(T ℝ n).eval u / (2 * (d : ℝ))| ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 := abs_eval_T_real_le_one n hu
    have h2 : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr hd
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * d),
      div_le_div_iff₀ (by positivity) two_pos]
    nlinarith

private lemma abs_chebAntideriv_le {u : ℝ} (hu : |u| ≤ 1) (k : ℕ) : |chebAntideriv k u| ≤ 1 := by
  unfold chebAntideriv
  have := abs_T_div_two_mul_le hu ((k + 2 : ℕ) : ℤ) (k + 2)
  have := abs_T_div_two_mul_le hu (k : ℤ) k
  linarith [abs_sub ((T ℝ ((k + 2 : ℕ) : ℤ)).eval u / (2 * ((k + 2 : ℕ) : ℝ)))
    ((T ℝ (k : ℤ)).eval u / (2 * (k : ℝ)))]

/-! ### The coefficient-level integration operator -/

section Integrate

variable [Fact (1 ≤ (ν : ℝ))]

/-- **Coefficient-level integration**: `(∫c)_k = (c_{k-1} - c_{k+1}) / (2k)` for `k ≥ 1`
and `(∫c)_0 = 0` (book (14.3) applied termwise to (14.9)). This is `-chebyshevShiftDiv`,
the sign being the one in rows `k ≥ 1` of `chebyshevIvpCoeffs`:
`2k a_k + c_{k+1} - c_{k-1} = 0 ⟺ a_k = (∫c)_k`. -/
def chebyshevIntegrate (c : l1Chebyshev ν) : l1Chebyshev ν := -chebyshevShiftDiv c

@[simp] lemma chebyshevIntegrate_toSeq_zero (c : l1Chebyshev ν) :
    l1Chebyshev.toSeq (chebyshevIntegrate c) 0 = 0 := by
  rw [chebyshevIntegrate, l1Chebyshev.toSeq_neg]
  show -(lpOneAlg.toRealSeq (chebyshevShiftDiv c) 0) = 0
  rw [chebyshevShiftDiv_toSeq, chebyshevShiftDiv_seq_zero, neg_zero]

lemma chebyshevIntegrate_toSeq_succ (c : l1Chebyshev ν) (k : ℕ) :
    l1Chebyshev.toSeq (chebyshevIntegrate c) ((k + 1 : ℕ) : ℤ)
      = (l1Chebyshev.toSeq c (k : ℤ) - l1Chebyshev.toSeq c ((k + 2 : ℕ) : ℤ))
          / (2 * ((k + 1 : ℕ) : ℝ)) := by
  rw [chebyshevIntegrate, l1Chebyshev.toSeq_neg]
  show -(lpOneAlg.toRealSeq (chebyshevShiftDiv c) _) = _
  rw [chebyshevShiftDiv_toSeq, chebyshevShiftDiv_seq_pos c (k + 1) k.succ_ne_zero,
    show ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
    show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring]
  ring

/-! ### Termwise integration of the T-series -/

private lemma norm_term_le (c : l1Chebyshev ν) {g : ℝ} (hg : |g| ≤ 1) (m : ℕ) :
    ‖l1Chebyshev.toSeq c (m : ℤ) * g‖ ≤ ‖c (m : ℤ)‖ := by
  rw [norm_fiber_natCast, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul le_rfl (hg.trans (one_le_pow₀ Fact.out)) (abs_nonneg _) (abs_nonneg _)

/-- Any series `∑ c_{k+s} g_k` with `|g_k| ≤ 1` converges absolutely. -/
private lemma summable_of_bounded (c : l1Chebyshev ν) (g : ℕ → ℝ) (hg : ∀ k, |g k| ≤ 1)
    (s : ℕ) : Summable (fun k : ℕ => l1Chebyshev.toSeq c ((k + s : ℕ) : ℤ) * g k) :=
  Summable.of_norm_bounded
    ((summable_norm_natCast c).comp_injective (add_left_injective s))
    (fun k => norm_term_le c (hg k) (k + s))

/-- The antiderivative series regrouped: `∑ c_{k+1} A_k = u_{∫c} - c₀ t / 2`. -/
private lemma tsum_chebAntideriv (c : l1Chebyshev ν) {u : ℝ} (hu : |u| ≤ 1) :
    ∑' k : ℕ, l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * chebAntideriv k u
      = ∑' m : ℕ, l1Chebyshev.toSeq (chebyshevIntegrate c) ((m + 1 : ℕ) : ℤ)
          * (T ℝ ((m + 1 : ℕ) : ℤ)).eval u - l1Chebyshev.toSeq c 0 * u / 2 := by
  have hS1 : Summable (fun k : ℕ => l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ)
      * ((T ℝ ((k + 2 : ℕ) : ℤ)).eval u / (2 * ((k + 2 : ℕ) : ℝ)))) :=
    summable_of_bounded c _ (fun k => (abs_T_div_two_mul_le hu _ _).trans (by norm_num)) 1
  have hS2 : Summable (fun k : ℕ => l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ)
      * ((T ℝ (k : ℤ)).eval u / (2 * (k : ℝ)))) :=
    summable_of_bounded c _ (fun k => (abs_T_div_two_mul_le hu _ _).trans (by norm_num)) 1
  have hS3 : Summable (fun m : ℕ => l1Chebyshev.toSeq c (m : ℤ)
      * ((T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ)))) :=
    (summable_of_bounded c (fun m => (T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ)))
      (fun k => (abs_T_div_two_mul_le hu _ _).trans (by norm_num)) 0).congr
      (fun m => by rw [Nat.add_zero])
  have hS4 : Summable (fun m : ℕ => l1Chebyshev.toSeq c ((m + 2 : ℕ) : ℤ)
      * ((T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ)))) :=
    summable_of_bounded c _ (fun k => (abs_T_div_two_mul_le hu _ _).trans (by norm_num)) 2
  have e1 : ∀ k : ℕ, l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * chebAntideriv k u
      = l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ)
          * ((T ℝ ((k + 2 : ℕ) : ℤ)).eval u / (2 * ((k + 2 : ℕ) : ℝ)))
        - l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * ((T ℝ (k : ℤ)).eval u / (2 * (k : ℝ))) :=
    fun k => by unfold chebAntideriv; ring
  have e2 : ∀ m : ℕ, l1Chebyshev.toSeq (chebyshevIntegrate c) ((m + 1 : ℕ) : ℤ)
        * (T ℝ ((m + 1 : ℕ) : ℤ)).eval u
      = l1Chebyshev.toSeq c (m : ℤ)
          * ((T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ)))
        - l1Chebyshev.toSeq c ((m + 2 : ℕ) : ℤ)
          * ((T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ))) :=
    fun m => by rw [chebyshevIntegrate_toSeq_succ]; ring
  rw [tsum_congr e1, hS1.tsum_sub hS2, tsum_congr e2, hS3.tsum_sub hS4, hS3.tsum_eq_zero_add,
    hS2.tsum_eq_zero_add]
  have e3 : (∑' k : ℕ, l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ)
      * ((T ℝ ((k + 1 + 1 : ℕ) : ℤ)).eval u / (2 * ((k + 1 + 1 : ℕ) : ℝ))))
      = ∑' k : ℕ, l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ)
          * ((T ℝ ((k + 2 : ℕ) : ℤ)).eval u / (2 * ((k + 2 : ℕ) : ℝ))) := rfl
  have e4 : (∑' k : ℕ, l1Chebyshev.toSeq c ((k + 1 + 1 : ℕ) : ℤ)
      * ((T ℝ ((k + 1 : ℕ) : ℤ)).eval u / (2 * ((k + 1 : ℕ) : ℝ))))
      = ∑' m : ℕ, l1Chebyshev.toSeq c ((m + 2 : ℕ) : ℤ)
          * ((T ℝ ((m + 1 : ℕ) : ℤ)).eval u / (2 * ((m + 1 : ℕ) : ℝ))) := rfl
  rw [e3, e4]
  simp only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, mul_zero, div_zero, T_one,
    Polynomial.eval_X, mul_one]
  ring

/-- **Termwise integration** (the lemma the book skips, p. 328):
`∫_{-1}^t u_c(s) ds = u_{∫c}(t) - u_{∫c}(-1)` for `t ∈ [-1, 1]`.

Route: dominated convergence under the constant dominant `‖c_{k+1}‖` interchanges `∫` and
`∑` (`intervalIntegral.hasSum_integral_of_dominated_convergence`), each term integrates by
(14.3) (`integral_T_succ`), and the antiderivative series regroups to the T-series of
`chebyshevIntegrate c` by one shift of the ℕ-sum (`tsum_chebAntideriv`). -/
theorem integral_eval (c : l1Chebyshev ν) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∫ s in (-1 : ℝ)..t, l1Chebyshev.eval c s
      = l1Chebyshev.eval (chebyshevIntegrate c) t
        - l1Chebyshev.eval (chebyshevIntegrate c) (-1) := by
  have hle : (-1 : ℝ) ≤ t := ht.1
  have hsn : Summable (fun k : ℕ => ‖c ((k + 1 : ℕ) : ℤ)‖) :=
    (summable_norm_natCast c).comp_injective (add_left_injective 1)
  have hbound : ∀ k : ℕ, ∀ s ∈ Icc (-1 : ℝ) 1,
      ‖l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s‖
        ≤ ‖c ((k + 1 : ℕ) : ℤ)‖ :=
    fun k s hs => norm_term_le c (abs_eval_T_real_le_one _ (abs_le.mpr hs)) (k + 1)
  -- (a) the interchange
  have hsum : HasSum
      (fun k : ℕ => ∫ s in (-1 : ℝ)..t,
        l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s)
      (∫ s in (-1 : ℝ)..t, ∑' k : ℕ,
        l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => ‖c ((k + 1 : ℕ) : ℤ)‖)
      (fun k => (continuous_const.mul (Polynomial.continuous _)).aestronglyMeasurable)
      (fun k => Filter.Eventually.of_forall fun s hs => ?_)
      (Filter.Eventually.of_forall fun _ _ => hsn) intervalIntegrable_const
      (Filter.Eventually.of_forall fun s hs => (l1Chebyshev.summable_eval c ?_).hasSum)
    · rw [uIoc_of_le hle] at hs
      exact hbound k s ⟨hs.1.le, hs.2.trans ht.2⟩
    · rw [uIoc_of_le hle] at hs
      exact abs_le.mpr ⟨hs.1.le, hs.2.trans ht.2⟩
  -- (b) integrability of the tail and the split of the integral
  have hcont : ContinuousOn (fun s => ∑' k : ℕ,
      l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s) (Icc (-1) 1) :=
    continuousOn_tsum (fun k => continuousOn_const.mul (Polynomial.continuousOn _)) hsn
      (fun k s hs => hbound k s hs)
  have hint : IntervalIntegrable (fun s => 2 * ∑' k : ℕ,
      l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s)
      MeasureTheory.volume (-1) t :=
    (continuousOn_const.mul (hcont.mono (by
      rw [uIcc_of_le hle]; exact Icc_subset_Icc le_rfl ht.2))).intervalIntegrable
  have h1 : ∫ s in (-1 : ℝ)..t, l1Chebyshev.eval c s
      = l1Chebyshev.toSeq c 0 * (t + 1) + 2 * ∑' k : ℕ, ∫ s in (-1 : ℝ)..t,
          l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s := by
    simp only [l1Chebyshev.eval]
    rw [intervalIntegral.integral_add intervalIntegrable_const hint,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hsum.tsum_eq,
      smul_eq_mul]
    ring
  -- (c) each term by (14.3)
  have h2 : ∀ k : ℕ, (∫ s in (-1 : ℝ)..t,
        l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval s)
      = l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * chebAntideriv k t
        - l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * chebAntideriv k (-1) := fun k => by
    rw [intervalIntegral.integral_const_mul, integral_T_succ, mul_sub]
  have hA : ∀ u : ℝ, |u| ≤ 1 →
      Summable (fun k : ℕ => l1Chebyshev.toSeq c ((k + 1 : ℕ) : ℤ) * chebAntideriv k u) :=
    fun u hu => summable_of_bounded c _ (abs_chebAntideriv_le hu) 1
  -- (d) regroup
  rw [h1, tsum_congr h2, (hA t (abs_le.mpr ht)).tsum_sub (hA (-1) (by norm_num)),
    tsum_chebAntideriv c (abs_le.mpr ht), tsum_chebAntideriv c (by norm_num)]
  simp only [l1Chebyshev.eval, chebyshevIntegrate_toSeq_zero]
  ring

end Integrate

/-! ### The bridge: `F(a) = 0 ⟹` integral equation `⟹` ODE -/

section Bridge

variable [Fact (1 ≤ (ν : ℝ))]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- Evaluation reads the modes `k ≥ 1` identically: two elements agreeing there have
T-series differing by the constant `a₀ - b₀`. -/
lemma eval_eq_of_toSeq_succ_eq {a b : l1Chebyshev ν}
    (h : ∀ k : ℕ, l1Chebyshev.toSeq a ((k + 1 : ℕ) : ℤ) = l1Chebyshev.toSeq b ((k + 1 : ℕ) : ℤ))
    (t : ℝ) :
    l1Chebyshev.eval a t = l1Chebyshev.toSeq a 0
      + (l1Chebyshev.eval b t - l1Chebyshev.toSeq b 0) := by
  simp only [l1Chebyshev.eval, h]; ring

variable (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ) (a : XCheb ν L)

/-- Rows `k ≥ 1` of `F(a) = 0`: `a` agrees with `∫φ(a)` on the positive modes. -/
lemma toSeq_succ_eq_integrate_of_F_zero (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0)
    (l : Fin L) (k : ℕ) :
    l1Chebyshev.toSeq (a l) ((k + 1 : ℕ) : ℤ)
      = l1Chebyshev.toSeq (chebyshevIntegrate (φ a l)) ((k + 1 : ℕ) : ℤ) := by
  have h := hF l (k + 1)
  simp only [chebyshevIvpCoeffs] at h
  rw [chebyshevIntegrate_toSeq_succ]
  push_cast at h ⊢
  field_simp
  linarith

/-- Row 0 of `F(a) = 0` is the initial condition `u_{a_l}(-1) = p_l` (book (14.12)). -/
lemma eval_neg_one_of_F_zero (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0) (l : Fin L) :
    l1Chebyshev.eval (a l) (-1) = p l := by
  have h := hF l 0
  simp only [chebyshevIvpCoeffs] at h
  rw [l1Chebyshev.eval_at_neg_one,
    tsum_congr (fun k => mul_comm (l1Chebyshev.toSeq (a l) ((k + 1 : ℕ) : ℤ)) ((-1 : ℝ) ^ (k + 1)))]
  linarith

/-- **The integral equation** (book (14.8)): `F(a) = 0 ⟹ u_{a_l}(t) = p_l + ∫_{-1}^t u_{φ(a)_l}`
on `[-1, 1]`. -/
theorem eval_eq_integral_of_F_zero (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0) (l : Fin L)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    l1Chebyshev.eval (a l) t = p l + ∫ s in (-1 : ℝ)..t, l1Chebyshev.eval (φ a l) s := by
  have e := eval_eq_of_toSeq_succ_eq (toSeq_succ_eq_integrate_of_F_zero φ p a hF l)
  rw [integral_eval _ ht, ← eval_neg_one_of_F_zero φ p a hF l, e t, e (-1)]
  ring

/-- The primitive `u ↦ ∫_{-1}^u g` of a function continuous on `[-1, 1]` has derivative `g t`
within `[-1, 1]` at every `t ∈ [-1, 1]` (extend `g` continuously off the interval, then FTC). -/
private lemma hasDerivWithinAt_primitive {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (fun u => ∫ s in (-1 : ℝ)..u, g s) (g t) (Icc (-1 : ℝ) 1) t := by
  have h01 : (-1 : ℝ) ≤ 1 := by norm_num
  set G : ℝ → ℝ := IccExtend h01 (fun x : Icc (-1 : ℝ) 1 => g x) with hG
  have hGc : Continuous G :=
    Continuous.Icc_extend' (hg.comp_continuous continuous_subtype_val (fun x => x.2))
  have hGg : ∀ x ∈ Icc (-1 : ℝ) 1, G x = g x := fun x hx => IccExtend_of_mem h01 _ hx
  have hd : HasDerivAt (fun u => ∫ s in (-1 : ℝ)..u, G s) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
  rw [hGg t ht] at hd
  have heq : ∀ u ∈ Icc (-1 : ℝ) 1, (∫ s in (-1 : ℝ)..u, g s) = ∫ s in (-1 : ℝ)..u, G s :=
    fun u hu => intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le hu.1] at hs
      exact (hGg s ⟨hs.1, hs.2.trans hu.2⟩).symm
  exact hd.hasDerivWithinAt.congr heq (heq t ht)

variable (f : (Fin L → ℝ) → Fin L → ℝ)

/-- One component of the forward bridge: `u_{a_l}` has derivative `f(u(t))_l` within `[-1, 1]`. -/
theorem hasDerivWithinAt_eval_of_F_zero
    (hφ : ∀ l t, t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0) (l : Fin L) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (fun s => l1Chebyshev.eval (a l) s)
      (f (fun i => l1Chebyshev.eval (a i) t) l) (Icc (-1 : ℝ) 1) t := by
  have hd := hasDerivWithinAt_primitive (l1Chebyshev.continuousOn_eval (φ a l)) ht
  rw [hφ l t ht] at hd
  exact (hd.const_add (p l)).congr (fun u hu => eval_eq_integral_of_F_zero φ p a hF l hu)
    (eval_eq_integral_of_F_zero φ p a hF l ht)

/-- **Forward bridge** (the Chebyshev analogue of book Lemma 8.1.4). If `F(a) = 0` and the
nonlinearity evaluates pointwise (`hφ`), the trajectory `u(t) := (u_{a_l}(t))_l` satisfies
`u(-1) = p`, is continuous on `[-1, 1]`, solves `u̇ = f(u)` from the right on `[-1, 1)` and
in the two-sided sense on `(-1, 1)`. The one-sided form is what
`ODE_solution_unique_of_mem_Icc_right` consumes. -/
theorem solves_ODE_of_F_zero
    (hφ : ∀ l t, t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0) :
    (∀ l, l1Chebyshev.eval (a l) (-1) = p l) ∧
    ContinuousOn (fun t l => l1Chebyshev.eval (a l) t) (Icc (-1 : ℝ) 1) ∧
    (∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt (fun s l => l1Chebyshev.eval (a l) s)
      (f (fun i => l1Chebyshev.eval (a i) t)) (Ici t) t) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun s l => l1Chebyshev.eval (a l) s)
      (f (fun i => l1Chebyshev.eval (a i) t)) t) := by
  refine ⟨eval_neg_one_of_F_zero φ p a hF,
    continuousOn_pi.mpr fun l => l1Chebyshev.continuousOn_eval (a l),
    fun t ht => hasDerivWithinAt_pi.mpr fun l => ?_, fun t ht => hasDerivAt_pi.mpr fun l => ?_⟩
  · exact HasDerivWithinAt.mono_of_mem_nhdsWithin
      (hasDerivWithinAt_eval_of_F_zero φ p a f hφ hF l (Ico_subset_Icc_self ht))
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl))
  · exact HasDerivWithinAt.hasDerivAt
      (hasDerivWithinAt_eval_of_F_zero φ p a f hφ hF l (Ioo_subset_Icc_self ht))
      (Icc_mem_nhds ht.1 ht.2)

/-- **Uniqueness from the endpoint** (Picard–Lindelöf via Grönwall, one-sided at `t = -1`).
Any `g` continuous on `[-1, 1]`, solving `ġ = f(g)` from the right on `[-1, 1)` inside a
closed ball on which `f` is Lipschitz, with `g(-1) = p`, agrees with the trajectory of a
zero of `F` that stays in the same ball. -/
theorem solution_unique
    (hφ : ∀ l t, t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (φ a l) t = f (fun i => l1Chebyshev.eval (a i) t) l)
    (hF : ∀ l k, chebyshevIvpCoeffs φ p a l k = 0)
    {K : NNReal} {R : ℝ} (hf_lip : LipschitzOnWith K f (Metric.closedBall 0 R))
    (hin : ∀ t ∈ Icc (-1 : ℝ) 1,
      (fun l => l1Chebyshev.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) R)
    (g : ℝ → Fin L → ℝ) (hg_cont : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hg_in : ∀ t ∈ Ico (-1 : ℝ) 1, g t ∈ Metric.closedBall (0 : Fin L → ℝ) R)
    (hg' : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt g (f (g t)) (Ici t) t)
    (hg_init : g (-1) = p) :
    Set.EqOn g (fun t l => l1Chebyshev.eval (a l) t) (Icc (-1 : ℝ) 1) := by
  obtain ⟨hinit, hcont, hderiv, -⟩ := solves_ODE_of_F_zero φ p a f hφ hF
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f)
    (s := fun _ => Metric.closedBall (0 : Fin L → ℝ) R) (K := K)
    (fun _ _ => hf_lip) hg_cont hg' hg_in hcont hderiv
    (fun t ht => hin t (Ico_subset_Icc_self ht))
    (by rw [hg_init]; exact (funext hinit).symm)

/-- The trajectory of `a` stays in the closed ball of radius `2‖a‖` on `[-1, 1]`. The factor
`2` is the storage convention `u_a = a₀ + 2∑ a_k T_k` (`abs_eval_le_two_mul_norm`); on
symmetric elements it drops (`abs_eval_le_norm_of_isSymmetric`). -/
lemma eval_traj_in_closedBall (a : XCheb ν L) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (fun l => l1Chebyshev.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) (2 * ‖a‖) := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  intro l
  show |l1Chebyshev.eval (a l) t| ≤ 2 * ‖a‖
  exact (l1Chebyshev.abs_eval_le_two_mul_norm (a l) (abs_le.mpr ht)).trans
    (by linarith [norm_le_pi_norm a l])

/-- At weights `ν ≥ 2`, the trajectory of `a` stays in the closed ball of radius
`‖a‖` on `[-1, 1]`.  The production storage evaluation is contractive at these
weights, so no factor `2` is needed. -/
lemma eval_traj_in_closedBall_of_two_le (hν : (2 : ℝ) ≤ (ν : ℝ))
    (a : XCheb ν L) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (fun l => l1Chebyshev.eval (a l) t) ∈ Metric.closedBall (0 : Fin L → ℝ) ‖a‖ := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (norm_nonneg a)]
  intro l
  show |l1Chebyshev.eval (a l) t| ≤ ‖a‖
  exact (l1Chebyshev.abs_eval_le_norm_of_two_le hν (a l) (abs_le.mpr ht)).trans
    (norm_le_pi_norm a l)

end Bridge

end ChebyshevIVP

end
