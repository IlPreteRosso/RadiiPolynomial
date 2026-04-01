import RadiiPolynomial.source.lpSpace.LpOneBanachAlgebra
import RadiiPolynomial.source.lpSpace.CauchyProduct
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# From Coefficient Space to Analytic Functions

Bridges the coefficient space ℓ¹_ν to analytic functions via power series evaluation.

## Main Results

* `l1Weighted.toPowerSeries`: Embedding ℓ¹_ν ↪ ℝ⟦X⟧
* `l1Weighted.eval`: Evaluation at points in the disk |z| ≤ ν
* `l1Weighted.eval_mul`: Evaluation is a ring homomorphism (Mertens' theorem)
-/

open scoped BigOperators NNReal ENNReal
open RadiiPolynomial

noncomputable section

variable {ν : PosReal}

namespace l1Weighted

private abbrev seq (a : l1Weighted ν) := lpWeighted.toSeq a

/-! ## Formal Power Series Embedding -/

def toPowerSeries (a : l1Weighted ν) : PowerSeries ℝ :=
  PowerSeries.mk (seq a)

@[simp]
theorem coeff_toPowerSeries (a : l1Weighted ν) (n : ℕ) :
    (PowerSeries.coeff n) (toPowerSeries a) = seq a n :=
  PowerSeries.coeff_mk n _

theorem coeff_mul_eq_cauchyProduct (a b : l1Weighted ν) (n : ℕ) :
    (PowerSeries.coeff n) (toPowerSeries a * toPowerSeries b) =
    CauchyProduct (seq a) (seq b) n := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_toPowerSeries, CauchyProduct.apply]

/-! ## Analytic Evaluation -/

private lemma norm_term_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]; gcongr

theorem summable_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => seq a n * z ^ n :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simp only [Real.norm_eq_abs]; exact norm_term_le hz n

private theorem summable_norm_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => ‖seq a n * z ^ n‖ :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simp only [Real.norm_eq_abs, abs_abs]; exact norm_term_le hz n

/-- Evaluate an ℓ¹_ν sequence as a power series at z ∈ ℝ. -/
def eval (a : l1Weighted ν) (z : ℝ) : ℝ :=
  ∑' n, seq a n * z ^ n

/-! ## Mertens' Theorem -/

/-- Evaluation is multiplicative: eval(a * b, z) = eval(a, z) * eval(b, z). -/
theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z * eval b z = eval (a * b) z := by
  unfold eval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_eval a hz) (summable_norm_eval b hz)]
  congr 1; ext n
  rw [show seq (a * b) n = CauchyProduct (seq a) (seq b) n from rfl,
    CauchyProduct.apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  rw [mul_mul_mul_comm, ← pow_add, hkl]

/-- eval(a, 0) = a₀. -/
theorem eval_at_zero (a : l1Weighted ν) : eval a 0 = seq a 0 := by
  unfold eval
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- eval is additive. -/
theorem eval_add (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (a + b) z = eval a z + eval b z := by
  show ∑' n, seq (a + b) n * z ^ n = (∑' n, seq a n * z ^ n) + ∑' n, seq b n * z ^ n
  simp_rw [show ∀ n, seq (a + b) n = seq a n + seq b n from lpWeighted.add_toSeq a b, add_mul]
  exact (summable_eval a hz).tsum_add (summable_eval b hz)

/-- eval respects subtraction. -/
theorem eval_sub (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (a - b) z = eval a z - eval b z := by
  show ∑' n, seq (a - b) n * z ^ n = (∑' n, seq a n * z ^ n) - ∑' n, seq b n * z ^ n
  simp_rw [show ∀ n, seq (a - b) n = seq a n - seq b n from lpWeighted.sub_toSeq a b, sub_mul]
  exact (summable_eval a hz).tsum_sub (summable_eval b hz)

/-- eval respects scalar multiplication. -/
theorem eval_smul (r : ℝ) (a : l1Weighted ν) (z : ℝ) :
    eval (r • a) z = r * eval a z := by
  show ∑' n, seq (r • a) n * z ^ n = r * ∑' n, seq a n * z ^ n
  simp_rw [show ∀ n, seq (r • a) n = r * seq a n from lpWeighted.smul_toSeq r a, mul_assoc]
  rw [tsum_mul_left]

end l1Weighted

end
