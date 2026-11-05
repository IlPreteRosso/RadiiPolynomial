import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval

/-!
# From Coefficient Space to Analytic Functions

Bridges the coefficient space ℓ¹_ν to analytic functions via power series evaluation.

## Main Results

* `l1Weighted.eval`: Evaluation `∑' n, aₙ zⁿ` at a real point `z` (defined for every `z` by
  `tsum`; summability, the norm bound and multiplicativity are proved for `|z| ≤ ν`)
* `l1Weighted.aeval_of_norm_le_apply_real`: The universal arrow's real series formula
* `l1Weighted.abs_eval_le`: `|eval a z| ≤ ‖a‖` from the universal arrow's contractivity
* `l1Weighted.eval_mul`: Pointwise multiplicativity from the universal arrow's `map_mul`
-/

open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

namespace l1Weighted

/-! ## Analytic Evaluation -/

private lemma norm_term_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]; gcongr

/-- The coordinate power series `∑ aₙ zⁿ` is summable on the admissible disc `|z| ≤ ν`. -/
theorem summable_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => toSeq a n * z ^ n :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simpa only [Real.norm_eq_abs] using norm_term_le hz n

/-- Evaluate an ℓ¹_ν sequence as a power series at z ∈ ℝ. -/
def eval (a : l1Weighted ν) (z : ℝ) : ℝ :=
  ∑' n, toSeq a n * z ^ n

/-- The universal geometric evaluation is the coordinate power series on its admissible disc.
This identity uses only the universal series formula and coefficient identification. -/
theorem aeval_of_norm_le_apply_real (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    aeval_of_norm_le ν z hz a = eval a z := by
  change (∑' n, lpOneAlg.toRealSeq a n • z ^ n) =
    ∑' n, toSeq a n * z ^ n
  simp only [← toSeq_eq_toRealSeq, smul_eq_mul]

/-- eval(a, 0) = a₀. -/
theorem eval_at_zero (a : l1Weighted ν) : eval a 0 = toSeq a 0 := by
  unfold eval
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-! ## The norm bound

The evaluation bound on the admissible disc is the contractivity of the universal geometric
evaluation, read through the series bridge `aeval_of_norm_le_apply_real`. -/

/-- The pointwise evaluation bound: `|eval a z| ≤ ‖a‖_ν` on the disk of convergence, the real
instance of the contractivity `lpOneAlg.norm_geomAeval_of_norm_le_apply_le` of the universal
geometric evaluation; useful for trajectory bounds
(see `Applications/IVP/Taylor/Trajectory.lean`). -/
lemma abs_eval_le (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    |eval a z| ≤ ‖a‖ := by
  rw [← aeval_of_norm_le_apply_real z hz, ← Real.norm_eq_abs]
  exact lpOneAlg.norm_geomAeval_of_norm_le_apply_le ℝ ν z hz a

/-! ## Multiplicativity -/



/-- Coordinate evaluation is multiplicative on its admissible disc, as the real
instance of the universal geometric algebra homomorphism. -/
theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z * eval b z = eval (a * b) z := by
  simpa only [aeval_of_norm_le_apply_real] using
    (map_mul (aeval_of_norm_le ν z hz) a b).symm

end l1Weighted

end RadiiPolynomial

end
