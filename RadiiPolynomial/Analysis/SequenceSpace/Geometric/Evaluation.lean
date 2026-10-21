import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Algebra

/-!
# From Coefficient Space to Analytic Functions

Bridges the coefficient space ℓ¹_ν to analytic functions via power series evaluation.

## Main Results

* `l1Weighted.eval`: Evaluation `∑' n, aₙ zⁿ` at a real point `z` (defined for every `z` by
  `tsum`; summability and the algebra laws are proved for `|z| ≤ ν`)
* `l1Weighted.aeval_of_norm_le_apply_real`: The universal arrow's real series formula
* `l1Weighted.eval_mul`: Pointwise multiplicativity from the universal arrow's `map_mul`
-/

open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

namespace l1Weighted

private abbrev seq (a : l1Weighted ν) := l1Weighted.toSeq a

/-! ## Analytic Evaluation -/

private lemma norm_term_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]; gcongr

theorem summable_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => seq a n * z ^ n :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simpa only [Real.norm_eq_abs] using norm_term_le hz n

private theorem summable_norm_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => ‖seq a n * z ^ n‖ :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simpa only [Real.norm_eq_abs, abs_abs] using norm_term_le hz n

/-- Evaluate an ℓ¹_ν sequence as a power series at z ∈ ℝ. -/
def eval (a : l1Weighted ν) (z : ℝ) : ℝ :=
  ∑' n, seq a n * z ^ n

/-- The universal geometric evaluation is the coordinate power series on its admissible disc.
This identity uses only the universal series formula and coefficient identification. -/
theorem aeval_of_norm_le_apply_real (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    aeval_of_norm_le ν z hz a = eval a z := by
  change (∑' n, lpOneAlg.toRealSeq a n • z ^ n) =
    ∑' n, toSeq a n * z ^ n
  simp only [← toSeq_eq_toRealSeq, smul_eq_mul]

/-- eval(a, 0) = a₀. -/
theorem eval_at_zero (a : l1Weighted ν) : eval a 0 = seq a 0 := by
  unfold eval
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp





/-- eval is additive. -/
theorem eval_add (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (a + b) z = eval a z + eval b z := by
  show ∑' n, seq (a + b) n * z ^ n = (∑' n, seq a n * z ^ n) + ∑' n, seq b n * z ^ n
  simp_rw [show ∀ n, seq (a + b) n = seq a n + seq b n from l1Weighted.add_toSeq a b, add_mul]
  exact (summable_eval a hz).tsum_add (summable_eval b hz)


/-- eval respects scalar multiplication. -/
theorem eval_smul (r : ℝ) (a : l1Weighted ν) (z : ℝ) :
    eval (r • a) z = r * eval a z := by
  show ∑' n, seq (r • a) n * z ^ n = r * ∑' n, seq a n * z ^ n
  simp_rw [show ∀ n, seq (r • a) n = r * seq a n from l1Weighted.smul_toSeq r a, mul_assoc]
  rw [tsum_mul_left]

/-! ## Analytic continuity and norm bound

The coordinate series gives a direct continuous-linear bound on the admissible disc.
The universal-arrow series bridge above does not use this bound or multiplicativity. -/

/-- Pointwise evaluation `a ↦ eval a z` as a continuous ℝ-linear map (no
multiplicativity assumed). The opnorm bound is 1: `|eval a z| ≤ ‖a‖`. -/
private def evalCLM (z : ℝ) (hz : |z| ≤ ν) : l1Weighted ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => eval a z
      map_add' := fun a b => eval_add a b hz
      map_smul' := fun r a => eval_smul r a z }
    1
    (fun a => by
      show ‖eval a z‖ ≤ 1 * ‖a‖
      rw [one_mul, l1Weighted.norm_eq_tsum]
      unfold eval
      refine (norm_tsum_le_tsum_norm (summable_norm_eval a hz)).trans ?_
      refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eval a hz)
        (l1Weighted.summable_weighted a)
      simp only [Real.norm_eq_abs]; exact norm_term_le hz n)

@[simp] private theorem evalCLM_apply (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    evalCLM z hz a = eval a z := rfl


/-- The pointwise evaluation bound: `|eval a z| ≤ ‖a‖_ν` on the disk of convergence.
Repackages the pre-Mertens continuous-linear bound as a direct estimate, useful for
trajectory bounds (see `Applications/IVP/Taylor/Trajectory.lean`). -/
lemma abs_eval_le (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    |eval a z| ≤ ‖a‖ := by
  have h_le : ‖evalCLM z hz a‖ ≤ ‖evalCLM z hz‖ * ‖a‖ := (evalCLM z hz).le_opNorm a
  have h_opn : ‖evalCLM z hz‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have : ‖evalCLM z hz a‖ ≤ ‖a‖ :=
    h_le.trans (mul_le_of_le_one_left (norm_nonneg _) h_opn)
  show |eval a z| ≤ _
  rw [show |eval a z| = ‖evalCLM z hz a‖ from rfl]
  exact this

/-! ## Finite sums and multiplicativity -/



/-- Coordinate evaluation is multiplicative on its admissible disc, as the real
instance of the universal geometric algebra homomorphism. -/
theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z * eval b z = eval (a * b) z := by
  simpa only [aeval_of_norm_le_apply_real] using
    (map_mul (aeval_of_norm_le ν z hz) a b).symm

end l1Weighted

end RadiiPolynomial

end
