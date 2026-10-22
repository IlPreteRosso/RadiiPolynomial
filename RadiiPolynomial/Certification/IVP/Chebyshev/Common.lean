import RadiiPolynomial.Applications.IVP.Chebyshev.Polynomial

/-!
# Chebyshev certification adapter: basis-direction rows

`FCe` (column `mn` of the raw `c`-rows on the basis vector `e_mn`) and the coefficient facts on
basis directions shared by the `Z₂` and `Z₁` bridges: `FCseq_eq_zero_of_nat`,
`FAseq_eq_zero_of_nat`, `toSeq_pi_single_nat`, `toSeq_pi_single_negSucc_nat`,
`FCseq_single_nat`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge

namespace ChebyshevIVP

/-- Column `mn` of the raw `c`-rows (`c_{k+2} − c_k`) on the basis vector `e_mn`. -/
def FCe (mn : ℕ) : ℕ → ℚ
  | 0 => 0
  | (k + 1) => (if k + 2 = mn then 1 else 0) - (if k = mn then 1 else 0)

section RowHelpers

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The raw `c`-rows vanish on a direction with no nonnegative modes. -/
theorem FCseq_eq_zero_of_nat (v : l1Chebyshev ν) (hv : ∀ n : ℕ, l1Chebyshev.toSeq v n = 0)
    (k : ℕ) : FCseq v k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
      show l1Chebyshev.toSeq v (↑(k + 2) : ℤ) - l1Chebyshev.toSeq v (↑k : ℤ) = 0
      rw [hv, hv, sub_zero]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The raw `a`-rows vanish on a direction with no nonnegative modes. -/
theorem FAseq_eq_zero_of_nat (v : l1Chebyshev ν) (hv : ∀ n : ℕ, l1Chebyshev.toSeq v n = 0)
    (k : ℕ) : FAseq v k = 0 := by
  cases k with
  | zero =>
      show -(l1Chebyshev.toSeq v 0) - 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) *
        l1Chebyshev.toSeq v (↑(n + 1) : ℤ) = 0
      simp only [show l1Chebyshev.toSeq v 0 = 0 from hv 0, hv, mul_zero, tsum_zero]
      ring
  | succ k =>
      show 2 * ((k : ℝ) + 1) * l1Chebyshev.toSeq v (↑(k + 1) : ℤ) = 0
      rw [hv, mul_zero]

theorem toSeq_pi_single_nat {L : ℕ} (j l : Fin L) (m : ℤ) (n : ℕ) :
    l1Chebyshev.toSeq ((Pi.single j (l1Chebyshev.single (ν := ν) m 1) :
      Fin L → l1Chebyshev ν) l) n = if l = j ∧ (n : ℤ) = m then 1 else 0 := by
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same, l1Chebyshev.toSeq_single]
    simp
  · rw [Pi.single_eq_of_ne hl, l1Chebyshev.toSeq_zero, ite_eq_right (fun h => hl h.1)]

theorem toSeq_pi_single_negSucc_nat {L : ℕ} (j l : Fin L) (m : ℕ) (n : ℕ) :
    l1Chebyshev.toSeq ((Pi.single j (l1Chebyshev.single (ν := ν) (Int.negSucc m) 1) :
      Fin L → l1Chebyshev ν) l) n = 0 := by
  rw [toSeq_pi_single_nat, ite_eq_right (fun h => by have := h.2; omega)]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem FCseq_single_nat (mn k : ℕ) :
    FCseq (ν := ν) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) k = (FCe mn k : ℝ) := by
  cases k with
  | zero => simp [FCseq, FCe]
  | succ k' =>
    show l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑(k' + 2) : ℤ)
          - l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑k' : ℤ) = _
    rw [l1Chebyshev.toSeq_single, l1Chebyshev.toSeq_single,
      show FCe mn (k' + 1)
        = (if k' + 2 = mn then 1 else 0) - (if k' = mn then 1 else 0) from rfl]
    simp only [Nat.cast_inj, Rat.cast_sub, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one,
      Rat.cast_zero]

end RowHelpers

end ChebyshevIVP
