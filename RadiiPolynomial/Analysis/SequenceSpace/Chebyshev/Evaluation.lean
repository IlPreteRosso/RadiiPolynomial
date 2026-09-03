import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.Polynomial

/-!
# Evaluation of a Chebyshev element as a function of `t`

A stored element `a : l1Chebyshev ν` is read as the function of book (14.9),

  `u_a(t) = a₀ + 2 ∑_{k ≥ 1} a_k T_k(t)`,

through the modes `k ≥ 0` only (`l1Chebyshev.eval`). The book gives no
convergence lemma for this series, no evaluation bound (the Chebyshev analogue
of Prop. 8.1.3) and no multiplicativity; here they are:

* `summable_eval` — absolute convergence on `|t| ≤ 1` from `|T_k(t)| ≤ 1` and
  `Σ|a_k| ≤ Σ|a_k| ν^k < ∞` (this is where `1 ≤ ν` enters);
* `continuousOn_eval`, `eval_at_neg_one`, `eval_at_one`, `eval_symmetrize`,
  linearity `eval_add / eval_sub / eval_smul / eval_neg`, `eval_one`;
* the bound `abs_eval_le_norm_symmetrize : |u_a(t)| ≤ ‖symmetrize a‖`, with the
  corollaries `abs_eval_le_two_mul_norm` and `abs_eval_le_norm_of_isSymmetric`;
* the dictionary `evalLaurentC_circle_eq_eval`: for symmetric `a`
  (`a₋ₖ = aₖ`) the bilateral Laurent character of `Chebyshev/UnitLift.lean` on
  the unit circle is the T-series, `∑_{k ∈ ℤ} aₖ e^{ikθ} = u_a(cos θ)`
  (book Thm 14.1.3 p. 325); multiplicativity `eval_mul_of_isSymmetric` is then
  `map_mul` of the character transported by the dictionary — no Cauchy product
  is expanded anywhere in this file.

Also here: the symmetric elements are closed under `0`, `1`, `+`, `-`, `•`
and `*` (`l1Chebyshev.IsSymmetric.mul` reindexes the convolution by `k ↦ -k`).

Every claim is machine-checked below; `[Fact (1 ≤ (ν : ℝ))]` is assumed
exactly where the ring structure or the domination `1 ≤ ν^k` needs it.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

open Polynomial.Chebyshev

variable {ν : PosReal}

/-! ### The symmetric elements are closed under the algebra operations -/

theorem isSymmetric_zero : (0 : l1Chebyshev ν).IsSymmetric := fun k => by
  show toSeq 0 (-k) = toSeq 0 k
  rw [toSeq_zero, toSeq_zero]

theorem IsSymmetric.add {f g : l1Chebyshev ν} (hf : f.IsSymmetric) (hg : g.IsSymmetric) :
    (f + g).IsSymmetric := fun k => by
  show toSeq (f + g) (-k) = toSeq (f + g) k
  rw [toSeq_add, toSeq_add, show toSeq f (-k) = toSeq f k from hf k,
    show toSeq g (-k) = toSeq g k from hg k]

theorem IsSymmetric.neg {f : l1Chebyshev ν} (hf : f.IsSymmetric) : (-f).IsSymmetric := fun k => by
  show toSeq (-f) (-k) = toSeq (-f) k
  rw [toSeq_neg, toSeq_neg, show toSeq f (-k) = toSeq f k from hf k]

theorem IsSymmetric.sub {f g : l1Chebyshev ν} (hf : f.IsSymmetric) (hg : g.IsSymmetric) :
    (f - g).IsSymmetric := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem IsSymmetric.smul (r : ℝ) {f : l1Chebyshev ν} (hf : f.IsSymmetric) :
    (r • f).IsSymmetric := fun k => by
  show toSeq (r • f) (-k) = toSeq (r • f) k
  rw [toSeq_smul, toSeq_smul, show toSeq f (-k) = toSeq f k from hf k]

/-- The unit of the bilateral algebra is the single at mode `0`. -/
lemma toSeq_one (k : ℤ) : toSeq (1 : l1Chebyshev ν) k = if k = 0 then 1 else 0 := by
  show lpOneAlg.toRealSeq 1 k = _
  rw [lpOneAlg.toRealSeq_one_fun]
  simp [DiscreteConvolution.addDelta, Pi.single_apply]

theorem isSymmetric_one : (1 : l1Chebyshev ν).IsSymmetric := fun k => by
  show toSeq 1 (-k) = toSeq 1 k
  rw [toSeq_one, toSeq_one]
  simp only [neg_eq_zero]

/-- **Symmetric elements are closed under convolution**: negation permutes the
fibers `i ↦ -i` of the bilateral Cauchy product, and both factors are invariant. -/
theorem IsSymmetric.mul [Fact (1 ≤ (ν : ℝ))] {f g : l1Chebyshev ν}
    (hf : f.IsSymmetric) (hg : g.IsSymmetric) : (f * g).IsSymmetric := fun k => by
  show toSeq (f * g) (-k) = toSeq (f * g) k
  rw [toSeq_mul_tsum, toSeq_mul_tsum,
    ← (Equiv.neg ℤ).tsum_eq (fun i => toSeq f (-k - i) * toSeq g i)]
  refine tsum_congr fun i => ?_
  show toSeq f (-k - -i) * toSeq g (-i) = toSeq f (k - i) * toSeq g i
  rw [show -k - -i = -(k - i) by ring, show toSeq f (-(k - i)) = toSeq f (k - i) from hf _,
    show toSeq g (-i) = toSeq g i from hg i]

/-! ### Evaluation: the T-series (14.9) -/

/-- **Evaluation** of a Chebyshev element as the function of book (14.9),
`u_a(t) = a₀ + 2 ∑_{k ≥ 1} a_k T_k(t)`, reading only the modes `k ≥ 0`. -/
def eval (a : l1Chebyshev ν) (t : ℝ) : ℝ :=
  toSeq a 0 + 2 * ∑' k : ℕ, toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t

private lemma summable_norm_succ (a : l1Chebyshev ν) :
    Summable (fun k : ℕ => ‖a ((k + 1 : ℕ) : ℤ)‖) :=
  (summable_norm_natCast a).comp_injective (add_left_injective 1)

lemma eval_symmetrize (a : l1Chebyshev ν) (t : ℝ) : eval (symmetrize a) t = eval a t := by
  simp only [eval, symmetrize_toSeq, Int.natAbs_natCast, Int.natAbs_zero, Nat.cast_zero]

lemma eval_smul (r : ℝ) (a : l1Chebyshev ν) (t : ℝ) : eval (r • a) t = r * eval a t := by
  simp only [eval, toSeq_smul, mul_assoc]
  rw [tsum_mul_left]; ring

lemma eval_neg (a : l1Chebyshev ν) (t : ℝ) : eval (-a) t = -eval a t := by
  simp only [eval, toSeq_neg, neg_mul]
  rw [tsum_neg]; ring

lemma eval_one (t : ℝ) : eval (1 : l1Chebyshev ν) t = 1 := by
  unfold eval
  rw [toSeq_one, if_pos rfl, tsum_congr (fun k => by
    rw [toSeq_one, if_neg (by omega : ((k + 1 : ℕ) : ℤ) ≠ 0), zero_mul]), tsum_zero]
  ring

lemma eval_at_one (a : l1Chebyshev ν) :
    eval a 1 = toSeq a 0 + 2 * ∑' k : ℕ, toSeq a ((k + 1 : ℕ) : ℤ) := by
  simp only [eval, T_eval_one, mul_one]

/-- `T_k(-1) = (-1)^k` (book (14.2)): row 0 of `chebyshevIvpCoeffs`. -/
lemma eval_at_neg_one (a : l1Chebyshev ν) :
    eval a (-1) = toSeq a 0 + 2 * ∑' k : ℕ, toSeq a ((k + 1 : ℕ) : ℤ) * (-1) ^ (k + 1) := by
  unfold eval
  congr 2
  exact tsum_congr fun k => by rw [T_eval_neg_one, Int.coe_negOnePow, Int.natAbs_natCast]

section Analytic

variable [Fact (1 ≤ (ν : ℝ))]

private lemma norm_term_le (a : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) (k : ℕ) :
    ‖toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t‖ ≤ ‖a ((k + 1 : ℕ) : ℤ)‖ := by
  rw [norm_fiber_natCast, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul le_rfl ((abs_eval_T_real_le_one _ ht).trans (one_le_pow₀ Fact.out))
    (abs_nonneg _) (abs_nonneg _)

/-- The T-series converges absolutely on `|t| ≤ 1`: `|T_k(t)| ≤ 1 ≤ ν^k`. -/
theorem summable_eval (a : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t) :=
  Summable.of_norm_bounded (summable_norm_succ a) (norm_term_le a ht)

lemma eval_add (a b : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    eval (a + b) t = eval a t + eval b t := by
  simp only [eval, toSeq_add, add_mul]
  rw [(summable_eval a ht).tsum_add (summable_eval b ht)]; ring

lemma eval_sub (a b : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    eval (a - b) t = eval a t - eval b t := by
  rw [sub_eq_add_neg, eval_add a (-b) ht, eval_neg, sub_eq_add_neg]

/-- The function `u_a` is continuous on `[-1, 1]` (uniform convergence under the
constant dominant `‖a_{k+1}‖`). -/
theorem continuousOn_eval (a : l1Chebyshev ν) :
    ContinuousOn (fun t => eval a t) (Set.Icc (-1) 1) := by
  unfold eval
  refine continuousOn_const.add (continuousOn_const.mul ?_)
  exact continuousOn_tsum (fun k => continuousOn_const.mul (Polynomial.continuousOn _))
    (summable_norm_succ a) (fun k t ht => norm_term_le a (abs_le.mpr ht) k)

/-! ### The evaluation bound (the Chebyshev Prop. 8.1.3 the book does not state) -/

/-- `‖symmetrize a‖ = |a₀| + 2 ∑_{k ≥ 1} |a_k| ν^k`: the bilateral norm of the
`|k|`-fold reads the modes `k ≥ 0` once at `0` and twice elsewhere. -/
theorem norm_symmetrize_eq (a : l1Chebyshev ν) :
    ‖symmetrize a‖ = |toSeq a 0|
      + 2 * ∑' k : ℕ, |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1) := by
  have hfib : ∀ k : ℤ, ‖(symmetrize a) k‖ = |toSeq a (k.natAbs : ℤ)| * (ν : ℝ) ^ k.natAbs :=
    fun k => by rw [norm_fiber, symmetrize_toSeq]
  have hs1 : Summable (fun n : ℕ => ‖(symmetrize a) (n : ℤ)‖) :=
    summable_norm_natCast (symmetrize a)
  have hs2 : Summable (fun n : ℕ => ‖(symmetrize a) (-((n : ℤ) + 1))‖) :=
    (lpOneAlg.summable_norm (symmetrize a)).comp_injective (fun n m h => by omega)
  rw [lpOneAlg.norm_eq_tsum,
    tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ‖(symmetrize a) k‖) hs1 hs2,
    hs1.tsum_eq_zero_add]
  have h0 : ‖(symmetrize a) ((0 : ℕ) : ℤ)‖ = |toSeq a 0| := by rw [hfib]; simp
  have hp : ∀ n : ℕ, ‖(symmetrize a) ((n + 1 : ℕ) : ℤ)‖
      = |toSeq a ((n + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (n + 1) :=
    fun n => by rw [hfib, Int.natAbs_natCast]
  have hn : ∀ n : ℕ, ‖(symmetrize a) (-((n : ℤ) + 1))‖
      = |toSeq a ((n + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (n + 1) :=
    fun n => by rw [hfib, show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]
  rw [h0, tsum_congr hp, tsum_congr hn]; ring

/-- For an element stored on the modes `k ≥ 0` only, `‖a‖ ≤ ‖symmetrize a‖`: the
`|k|`-fold doubles every positive mode and drops nothing. (Certificates store their
candidates this way, so their symmetrized norm bounds also bound the stored norm.) -/
theorem norm_le_norm_symmetrize_of_neg_eq_zero (a : l1Chebyshev ν)
    (h : ∀ n : ℕ, toSeq a (-((n : ℤ) + 1)) = 0) : ‖a‖ ≤ ‖symmetrize a‖ := by
  have hs1 : Summable (fun n : ℕ => ‖a (n : ℤ)‖) := summable_norm_natCast a
  have hs2 : Summable (fun n : ℕ => ‖a (-((n : ℤ) + 1))‖) :=
    (lpOneAlg.summable_norm a).comp_injective (fun n m h => by omega)
  have hneg : ∀ n : ℕ, ‖a (-((n : ℤ) + 1))‖ = 0 := fun n => by
    rw [norm_fiber, h n, abs_zero, zero_mul]
  rw [norm_symmetrize_eq, lpOneAlg.norm_eq_tsum,
    tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ‖a k‖) hs1 hs2,
    tsum_congr hneg, tsum_zero, add_zero, hs1.tsum_eq_zero_add]
  have h0 : ‖a ((0 : ℕ) : ℤ)‖ = |toSeq a 0| := by rw [norm_fiber_natCast]; simp
  have hp : ∀ n : ℕ, ‖a ((n + 1 : ℕ) : ℤ)‖
      = |toSeq a ((n + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (n + 1) :=
    fun n => norm_fiber_natCast a (n + 1)
  rw [h0, tsum_congr hp]
  have hnn : 0 ≤ ∑' k : ℕ, |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1) :=
    tsum_nonneg (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
  linarith

/-- **Evaluation bound**: `|u_a(t)| ≤ ‖symmetrize a‖` on `|t| ≤ 1` — the Chebyshev
analogue of book Prop. 8.1.3, which the book does not state. -/
theorem abs_eval_le_norm_symmetrize (a : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    |eval a t| ≤ ‖symmetrize a‖ := by
  rw [norm_symmetrize_eq, eval]
  have hsn : Summable (fun k : ℕ =>
      ‖toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (norm_term_le a ht) (summable_norm_succ a)
  have hw : Summable (fun k : ℕ => |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1)) :=
    (summable_norm_succ a).congr (fun k => norm_fiber_natCast a (k + 1))
  have h1 : ‖∑' k : ℕ, toSeq a ((k + 1 : ℕ) : ℤ) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval t‖
      ≤ ∑' k : ℕ, |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1) := by
    refine (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (fun k => ?_) hw)
    have := norm_term_le a ht k
    rwa [norm_fiber_natCast] at this
  rw [Real.norm_eq_abs] at h1
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_two]; linarith

/-- `|u_a(t)| ≤ 2‖a‖` on `|t| ≤ 1` (via `‖symmetrize a‖ ≤ 2‖a‖`). -/
theorem abs_eval_le_two_mul_norm (a : l1Chebyshev ν) {t : ℝ} (ht : |t| ≤ 1) :
    |eval a t| ≤ 2 * ‖a‖ :=
  (abs_eval_le_norm_symmetrize a ht).trans (symmetrize_norm_le a)

/-- On symmetric elements the bound is contractive: `|u_a(t)| ≤ ‖a‖`. -/
theorem abs_eval_le_norm_of_isSymmetric (a : l1Chebyshev ν) (ha : a.IsSymmetric) {t : ℝ}
    (ht : |t| ≤ 1) : |eval a t| ≤ ‖a‖ := by
  have h := abs_eval_le_norm_symmetrize a ht
  rwa [symmetrize_eq_self_of_isSymmetric a ha] at h

end Analytic

/-! ### The dictionary: Laurent character on the circle = T-series at `cos θ` -/

section Dictionary

open Complex

variable (ν) [Fact (1 ≤ (ν : ℝ))]

private lemma exp_zpow_add_exp_zpow_neg (θ : ℝ) (k : ℤ) :
    exp (θ * I) ^ k + exp (θ * I) ^ (-k) = 2 * ((Real.cos (k * θ) : ℝ) : ℂ) := by
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> push_cast <;> ring

private lemma summable_circle (θ : ℝ) (a : l1Chebyshev ν) :
    Summable (fun k : ℤ => ((toSeq a k : ℝ) : ℂ) * exp (θ * I) ^ k) := by
  refine Summable.of_norm_bounded (lpOneAlg.summable_norm a) (fun k => ?_)
  rw [norm_mul, norm_zpow, norm_exp_ofReal_mul_I, one_zpow, mul_one, Complex.norm_real,
    norm_fiber, Real.norm_eq_abs]
  exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ Fact.out)

/-- **The dictionary** (book Thm 14.1.3): for symmetric `a`, the bilateral Laurent
character at `z = e^{iθ}` is the T-series at `cos θ`,
`∑_{k ∈ ℤ} aₖ e^{ikθ} = a₀ + 2 ∑_{k ≥ 1} aₖ cos kθ = u_a(cos θ)`. -/
theorem evalLaurentC_circle_eq_eval (a : l1Chebyshev ν) (ha : a.IsSymmetric) (θ : ℝ) :
    evalLaurentC ν (exp (θ * I)) (evalLaurentC_circle ν θ) a
      = ((eval a (Real.cos θ) : ℝ) : ℂ) := by
  rw [evalLaurentC_apply]
  show ∑' k : ℤ, ((toSeq a k : ℝ) : ℂ) * exp (θ * I) ^ k = _
  have hs := summable_circle ν θ a
  have hs1 : Summable (fun n : ℕ => ((toSeq a (n : ℤ) : ℝ) : ℂ) * exp (θ * I) ^ (n : ℤ)) :=
    hs.comp_injective Nat.cast_injective
  have hs2 : Summable (fun n : ℕ =>
      ((toSeq a (-((n : ℤ) + 1)) : ℝ) : ℂ) * exp (θ * I) ^ (-((n : ℤ) + 1))) :=
    hs.comp_injective (fun n m h => by omega)
  have hs1' : Summable (fun n : ℕ =>
      ((toSeq a ((n + 1 : ℕ) : ℤ) : ℝ) : ℂ) * exp (θ * I) ^ ((n + 1 : ℕ) : ℤ)) :=
    hs1.comp_injective (add_left_injective 1)
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ((toSeq a k : ℝ) : ℂ) * exp (θ * I) ^ k)
    hs1 hs2, hs1.tsum_eq_zero_add, add_assoc, ← hs1'.tsum_add hs2]
  rw [eval, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_ofNat,
    ← tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun n => ?_
    have hsym : toSeq a (-((n : ℤ) + 1)) = toSeq a ((n + 1 : ℕ) : ℤ) := by
      have h := ha ((n + 1 : ℕ) : ℤ)
      push_cast at h ⊢
      exact h
    rw [hsym, show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, ← mul_add,
      exp_zpow_add_exp_zpow_neg, T_real_cos, Complex.ofReal_mul]
    ring

variable {ν}

/-- **Multiplicativity of the T-series on symmetric elements**: `map_mul` of the
Laurent character transported through the dictionary — no Cauchy product. -/
theorem eval_mul_of_isSymmetric (a b : l1Chebyshev ν) (ha : a.IsSymmetric)
    (hb : b.IsSymmetric) {t : ℝ} (ht : |t| ≤ 1) :
    eval (a * b) t = eval a t * eval b t := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hcos : Real.cos (Real.arccos t) = t := Real.cos_arccos h1 h2
  apply Complex.ofReal_injective
  rw [← hcos, Complex.ofReal_mul, ← evalLaurentC_circle_eq_eval ν a ha,
    ← evalLaurentC_circle_eq_eval ν b hb, ← evalLaurentC_circle_eq_eval ν (a * b) (ha.mul hb),
    map_mul]

end Dictionary

end l1Chebyshev

end RadiiPolynomial

end
