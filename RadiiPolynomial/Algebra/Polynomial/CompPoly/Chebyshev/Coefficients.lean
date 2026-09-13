import RadiiPolynomial.Algebra.Polynomial.CompPoly.Laurent
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered

/-!
# Computable coefficients and completed Chebyshev polynomial evaluation

The finite Laurent interpreter agrees with `CompPoly.evalBanach` on finitely supported
rational inputs in the completed bilateral algebra. Its array specialization agrees with
evaluation on symmetrized nonnegative stored coefficients. No hypothesis on the negative
stored input modes is needed, since `symmetrize` reads only nonnegative modes.
-/

open scoped BigOperators
open RadiiPolynomial

namespace MvPolyBridge.CompPoly

variable {L : ℕ} {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- Correctness against the completed Laurent algebra for rational inputs with support bounds. -/
theorem toSeq_evalBanach_laurent_of_coeffs (p : CompPoly L)
    (a : Fin L → l1Chebyshev ν) (radii : Fin L → ℕ) (seqs : Fin L → ℤ → ℚ)
    (ha : ∀ i n, l1Chebyshev.toSeq (a i) n = (seqs i n : ℝ))
    (hs : ∀ i n, radii i < n.natAbs → seqs i n = 0) (n : ℤ) :
    l1Chebyshev.toSeq (p.evalBanach a) n = (p.evalLaurentCoeffSeq radii seqs n : ℝ) := by
  induction p generalizing n with
  | C r =>
      rw [evalBanach, Algebra.algebraMap_eq_smul_one, l1Chebyshev.toSeq_smul]
      change (r : ℝ) * lpOneAlg.toRealSeq (1 : l1Chebyshev ν) n = _
      rw [lpOneAlg.toRealSeq_one_fun]
      simp only [evalLaurentCoeffSeq]
      split_ifs <;> simp_all [DiscreteConvolution.addDelta]
  | X i => exact ha i n
  | add p q ihp ihq => simp [evalBanach, evalLaurentCoeffSeq, ihp, ihq]
  | sub p q ihp ihq => simp [evalBanach, evalLaurentCoeffSeq, ihp, ihq]
  | mul p q ihp ihq =>
      rw [evalBanach, l1Chebyshev.toSeq_mul_eq_finsum
        (p.evalBanach a) (q.evalBanach a) n
        (laurentModes (q.laurentRadius radii))]
      · simp [evalLaurentCoeffSeq, ihp, ihq]
      · intro k hk
        rw [ihq]
        rw [q.evalLaurentCoeffSeq_eq_zero_of_radius_lt radii seqs hs k
          (by have := (mem_laurentModes_iff (q.laurentRadius radii) k).not.mp hk; omega)]
        exact Rat.cast_zero
  | neg p ih => simp [evalBanach, evalLaurentCoeffSeq, ih]
  | smul r p ih => simp [evalBanach, evalLaurentCoeffSeq, ih]

/-- The array interpreter agrees with polynomial evaluation on symmetrized stored data.
Only the nonnegative stored coefficients must agree with the zero-padded rational arrays. -/
theorem toSeq_evalBanach_cheb_of_coeffs (p : CompPoly L)
    (a : Fin L → l1Chebyshev ν) (arrs : Fin L → Array ℚ)
    (ha : ∀ i (k : ℕ), l1Chebyshev.toSeq (a i) (k : ℤ) = ((arrs i).getD k 0 : ℝ))
    (n : ℤ) :
    l1Chebyshev.toSeq (p.evalBanach (fun i => l1Chebyshev.symmetrize (a i))) n =
      (p.evalChebCoeff arrs n : ℝ) := by
  apply p.toSeq_evalBanach_laurent_of_coeffs
  · intro i k
    rw [l1Chebyshev.symmetrize_toSeq, ha]
  · intro i k hk
    simp [Array.getD, show ¬k.natAbs < (arrs i).size by omega]

end MvPolyBridge.CompPoly
