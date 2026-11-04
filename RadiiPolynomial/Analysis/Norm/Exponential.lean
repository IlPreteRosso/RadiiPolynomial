import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exponential estimates in Banach algebras

`NormedSpace.exp` on a complete normed algebra `𝔸` is Mathlib's; it carries no scalar field
(it is defined through `expSeries ℚ`). This file collects the estimates a radii polynomial
certificate with an exponential nonlinearity consumes.

* Over real scalars `[NormedAlgebra ℝ 𝔸]` (every normed `ℂ`-algebra is one, by Mathlib's instance
  `NormedAlgebra.complexToReal`):
  - `map_exp_of_continuous`: a continuous ring homomorphism commutes with `exp` (Mathlib's
    `NormedSpace.map_exp` needs `[NormedAlgebra ℚ 𝔸]`; the route `NormedSpace.map_exp_of_mem_ball`
    at the full radius needs nothing more);
  - `norm_exp_sub_exp_le`: `‖e^x − e^y‖ ≤ e^(‖c‖ + r) ‖x − y‖` on the closed ball `B̄(c, r)`
    (commutative and complete; no unit-norm normalization: the mean value inequality on
    `hasFDerivAt_exp` with the multiplication bound `‖e^w h‖ ≤ e^‖w‖ ‖h‖`).
* The finite-Taylor contract over `RCLike` scalars `𝕂` (the scalar occurs in the statements):
  `norm_taylorTerm_sub_le` propagates one-step defects `‖x P_n/(n+1) − P_(n+1)‖ ≤ ρ_n` into term
  errors `‖xⁿ/n! − P_n‖ ≤ ε_n` (`ε_(n+1) ≥ m ε_n/(n+1) + ρ_n`), `norm_exp_sub_sum_le` adds the
  tail `∑_(n > J) mⁿ/n!`, and `tsum_pow_div_factorial_tail_le` bounds that tail by
  `m^(J+1)/(J+1)! · (J+2)/(J+2−m)`.
-/

open scoped Nat

noncomputable section

namespace RadiiPolynomial.NormHelpers

/-! ### A continuous ring homomorphism commutes with `exp` -/

section MapExp

variable {𝔸 𝔹 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormedRing 𝔹]
  [Algebra ℝ 𝔹]

/-- **A continuous ring homomorphism commutes with the exponential** (no `ℚ`-algebra instance on
the source; Mathlib's `NormedSpace.map_exp_of_mem_ball` at the full radius over `ℝ`). -/
theorem map_exp_of_continuous {F : Type*} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F)
    (hf : Continuous f) (x : 𝔸) : f (NormedSpace.exp x) = NormedSpace.exp (f x) :=
  NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) f hf x
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

end MapExp

/-! ### The derivative-difference bound over real scalars -/

/-- Multiplication by `exp w` has bound `exp ‖w‖`; no unit-norm normalization is needed. -/
private theorem norm_exp_mul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (w h : 𝔸) :
    ‖NormedSpace.exp w * h‖ ≤ Real.exp ‖w‖ * ‖h‖ := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) w).mul_right h
  have ht := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖w‖).mul_right ‖h‖
  rw [← Real.exp_eq_exp_ℝ] at ht
  refine hs.norm_le_of_bounded ht fun n => ?_
  have hp : ‖w ^ n * h‖ ≤ ‖w‖ ^ n * ‖h‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [pow_succ', mul_assoc] using
        (norm_mul_le w (w ^ n * h)).trans
          (mul_le_mul_of_nonneg_left ih (norm_nonneg w))
  rw [smul_mul_assoc, norm_smul, norm_inv, RCLike.norm_natCast]
  simpa only [smul_eq_mul, mul_assoc] using
    mul_le_mul_of_nonneg_left hp (inv_nonneg.2 (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ _))

/-- **The derivative-difference bound** (the `Z₂` socket): on the closed ball `B̄(c, r)`,
`‖e^x − e^y‖ ≤ e^(‖c‖ + r) ‖x − y‖` (mean value inequality on `hasFDerivAt_exp`). -/
theorem norm_exp_sub_exp_le {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {c x y : 𝔸} {r : ℝ} (hx : ‖x - c‖ ≤ r) (hy : ‖y - c‖ ≤ r) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ ≤ Real.exp (‖c‖ + r) * ‖x - y‖ := by
  have hball : ∀ w ∈ Metric.closedBall c r, ‖w‖ ≤ ‖c‖ + r := fun w hw => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    exact (norm_le_norm_add_norm_sub' w c).trans (by linarith)
  have hderiv : ∀ w ∈ Metric.closedBall c r, HasFDerivWithinAt NormedSpace.exp
      (NormedSpace.exp w • (1 : 𝔸 →L[ℝ] 𝔸)) (Metric.closedBall c r) w :=
    fun w _ => (hasFDerivAt_exp (𝕂 := ℝ)).hasFDerivWithinAt
  have hmul : ∀ w : 𝔸, ‖NormedSpace.exp w • (1 : 𝔸 →L[ℝ] 𝔸)‖ ≤ Real.exp ‖w‖ := by
    intro w
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun h => ?_
    change ‖NormedSpace.exp w * h‖ ≤ Real.exp ‖w‖ * ‖h‖
    exact norm_exp_mul_le w h
  have hbound : ∀ w ∈ Metric.closedBall c r,
      ‖NormedSpace.exp w • (1 : 𝔸 →L[ℝ] 𝔸)‖ ≤ Real.exp (‖c‖ + r) := fun w hw =>
    (hmul w).trans (Real.exp_le_exp.2 (hball w hw))
  exact (convex_closedBall c r).norm_image_sub_le_of_norm_hasFDerivWithin_le (x := y) (y := x)
    hderiv hbound (by rwa [Metric.mem_closedBall, dist_eq_norm])
    (by rwa [Metric.mem_closedBall, dist_eq_norm])

/-! ### The finite-Taylor contract -/

section Taylor

variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- **Propagation of one-step defects.** With `‖x‖ ≤ m`, `P 0 = 1`, one-step defects
`‖x P_n/(n+1) − P_(n+1)‖ ≤ ρ_n` and term errors with `0 ≤ ε 0` and
`m ε_n/(n+1) + ρ_n ≤ ε_(n+1)` (`n < J`), every term satisfies `‖xⁿ/n! − P_n‖ ≤ ε_n` (`n ≤ J`). -/
theorem norm_taylorTerm_sub_le {x : 𝔸} {P : ℕ → 𝔸} {m : ℝ} {ρ ε : ℕ → ℝ} {J : ℕ}
    (hm : ‖x‖ ≤ m) (hP0 : P 0 = 1) (hε0 : 0 ≤ ε 0)
    (hstep : ∀ n < J, ‖((n : 𝕂) + 1)⁻¹ • (x * P n) - P (n + 1)‖ ≤ ρ n)
    (hε : ∀ n < J, m * ε n / (n + 1) + ρ n ≤ ε (n + 1)) :
    ∀ n ≤ J, ‖((n ! : 𝕂))⁻¹ • x ^ n - P n‖ ≤ ε n := by
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
  intro n
  induction n with
  | zero => intro _; simpa [hP0] using hε0
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hrec : ((((n + 1) ! : ℕ) : 𝕂))⁻¹ • x ^ (n + 1) =
        ((n : 𝕂) + 1)⁻¹ • (x * (((n ! : 𝕂))⁻¹ • x ^ n)) := by
      rw [mul_smul_comm, smul_smul, pow_succ', Nat.factorial_succ, Nat.cast_mul, mul_inv]
      push_cast
      ring_nf
    have hsplit : ((((n + 1) ! : ℕ) : 𝕂))⁻¹ • x ^ (n + 1) - P (n + 1) =
        ((n : 𝕂) + 1)⁻¹ • (x * (((n ! : 𝕂))⁻¹ • x ^ n - P n)) +
          (((n : 𝕂) + 1)⁻¹ • (x * P n) - P (n + 1)) := by
      rw [hrec, mul_sub, smul_sub]; abel
    rw [hsplit]
    have hn1 : ‖((n : 𝕂) + 1)⁻¹‖ = ((n : ℝ) + 1)⁻¹ := by
      rw [norm_inv, show ((n : 𝕂) + 1) = ((n + 1 : ℕ) : 𝕂) by push_cast; ring,
        RCLike.norm_natCast]
      push_cast; ring
    refine (norm_add_le _ _).trans ((add_le_add ?_ (hstep n (by omega))).trans (hε n (by omega)))
    rw [norm_smul, hn1, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_mul hm ih' (norm_nonneg _) hm0)) (by positivity)

variable [CompleteSpace 𝔸]

/-- **The finite-Taylor contract**: term errors `‖xⁿ/n! − P_n‖ ≤ ε_n` (`n ≤ J`) and `‖x‖ ≤ m` give
`‖e^x − ∑_(n ≤ J) P_n‖ ≤ ∑_(n ≤ J) ε_n + ∑_(n > J) mⁿ/n!`. -/
theorem norm_exp_sub_sum_le {x : 𝔸} {P : ℕ → 𝔸} {m : ℝ} {ε : ℕ → ℝ} (J : ℕ) (hm : ‖x‖ ≤ m)
    (hP : ∀ n ≤ J, ‖((n ! : 𝕂))⁻¹ • x ^ n - P n‖ ≤ ε n) :
    ‖NormedSpace.exp x - ∑ n ∈ Finset.range (J + 1), P n‖ ≤
      ∑ n ∈ Finset.range (J + 1), ε n + ∑' n, m ^ (n + (J + 1)) / (n + (J + 1))! := by
  set f : ℕ → 𝔸 := fun n => ((n ! : 𝕂))⁻¹ • x ^ n with hf
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) x
  have hsplit := (hsum.summable.sum_add_tsum_nat_add (J + 1)).symm
  rw [hsum.tsum_eq] at hsplit
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
  have hreal : Summable fun n => m ^ (n + (J + 1)) / ((n + (J + 1))! : ℝ) :=
    (summable_nat_add_iff (J + 1)).2 (Real.summable_pow_div_factorial m)
  have htail : ‖∑' n, f (n + (J + 1))‖ ≤ ∑' n, m ^ (n + (J + 1)) / (n + (J + 1))! := by
    refine tsum_of_norm_bounded hreal.hasSum fun n => ?_
    rw [hf, norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left ((norm_pow_le' x (by omega)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hm _)) (by positivity)
  have hfin : ‖∑ n ∈ Finset.range (J + 1), (f n - P n)‖ ≤ ∑ n ∈ Finset.range (J + 1), ε n :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn =>
      hP n (by rw [Finset.mem_range] at hn; omega))
  rw [show NormedSpace.exp x - ∑ n ∈ Finset.range (J + 1), P n =
      ∑ n ∈ Finset.range (J + 1), (f n - P n) + ∑' n, f (n + (J + 1)) by
    rw [hsplit, Finset.sum_sub_distrib]; abel]
  exact (norm_add_le _ _).trans (add_le_add hfin htail)

end Taylor

/-- **The tail majorant**: `∑_(n > J) mⁿ/n! ≤ m^(J+1)/(J+1)! · (J+2)/(J+2−m)` (`0 ≤ m < J + 2`),
by comparison with the geometric series of ratio `m/(J+2)`. -/
theorem tsum_pow_div_factorial_tail_le {m : ℝ} (J : ℕ) (hm0 : 0 ≤ m) (hm : m < J + 2) :
    ∑' n, m ^ (n + (J + 1)) / ((n + (J + 1))! : ℝ) ≤
      m ^ (J + 1) / (J + 1)! * ((J + 2) / (J + 2 - m)) := by
  have hJ : (0 : ℝ) < J + 2 := by positivity
  have hq0 : 0 ≤ m / (J + 2) := div_nonneg hm0 hJ.le
  have hq1 : m / (J + 2) < 1 := (div_lt_one hJ).2 hm
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (m ^ (J + 1) / (J + 1)!)
  have hval : m ^ (J + 1) / (J + 1)! * (1 - m / (J + 2))⁻¹ =
      m ^ (J + 1) / (J + 1)! * ((J + 2) / (J + 2 - m)) := by
    congr 1
    field_simp
  rw [← hval]
  refine hasSum_le (fun n => ?_) ((summable_nat_add_iff (J + 1)).2
    (Real.summable_pow_div_factorial m)).hasSum hgeom
  have hfac : (((J + 1)! : ℕ) : ℝ) * ((J + 1 + 1 : ℕ) : ℝ) ^ n ≤ ((J + 1 + n)! : ℕ) := by
    exact_mod_cast Nat.factorial_mul_pow_le_factorial
  rw [show n + (J + 1) = J + 1 + n by ring, div_pow, pow_add]
  have hpos : (0 : ℝ) < ((J + 1)! : ℕ) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((J + 1 + n)! : ℕ))]
  refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left hfac
    (by positivity : (0 : ℝ) ≤ m ^ (J + 1) / ((J + 1)! : ℕ) * (m ^ n / (J + 2) ^ n)))
  push_cast; field_simp; ring

end RadiiPolynomial.NormHelpers
