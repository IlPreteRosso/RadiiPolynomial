import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core

/-!
# Finite Laurent coefficients for computable polynomials

Finite support makes bilateral multiplication computable. `laurentRadius` propagates
input support bounds through the unchanged `CompPoly` syntax, and `evalLaurentCoeffSeq`
uses those bounds to evaluate each convolution as a finite sum. Its result is independent
of the choice of valid support bounds.

`evalChebCoeff` specializes this interpreter to zero-padded nonnegative arrays, read
symmetrically at `|k|`. Correctness in the completed Chebyshev algebra is proved in
`CompPoly.Chebyshev.Coefficients`.
-/

open scoped BigOperators

namespace MvPolyBridge.CompPoly

variable {L : ℕ}

/-- A support bound for the Laurent polynomial obtained from bounded inputs.
The bound need not be sharp: addition takes a maximum and multiplication adds radii. -/
def laurentRadius : CompPoly L → (Fin L → ℕ) → ℕ
  | .C _, _ => 0
  | .X i, radii => radii i
  | .add p q, radii => max (p.laurentRadius radii) (q.laurentRadius radii)
  | .sub p q, radii => max (p.laurentRadius radii) (q.laurentRadius radii)
  | .mul p q, radii => p.laurentRadius radii + q.laurentRadius radii
  | .neg p, radii => p.laurentRadius radii
  | .smul _ p, radii => p.laurentRadius radii

/-- The integer modes from `-R` to `R`, with a computable finite presentation. -/
def laurentModes (R : ℕ) : Finset ℤ :=
  (Finset.range (2 * R + 1)).image (fun k : ℕ => (k : ℤ) - R)

/-- Membership in the computable mode set is the corresponding absolute-value bound. -/
theorem mem_laurentModes_iff (R : ℕ) (n : ℤ) :
    n ∈ laurentModes R ↔ n.natAbs ≤ R := by
  simp only [laurentModes, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · intro hn
    refine ⟨(n + R).toNat, ?_, ?_⟩ <;> omega

/-- Computable Laurent evaluation, summing over the second factor's support bound.
Correctness requires each input sequence to vanish outside its supplied radius. -/
def evalLaurentCoeffSeq : CompPoly L → (Fin L → ℕ) → (Fin L → ℤ → ℚ) → ℤ → ℚ
  | .C r, _, _, n => if n = 0 then r else 0
  | .X i, _, seqs, n => seqs i n
  | .add p q, radii, seqs, n =>
      p.evalLaurentCoeffSeq radii seqs n + q.evalLaurentCoeffSeq radii seqs n
  | .sub p q, radii, seqs, n =>
      p.evalLaurentCoeffSeq radii seqs n - q.evalLaurentCoeffSeq radii seqs n
  | .mul p q, radii, seqs, n =>
      ∑ k ∈ laurentModes (q.laurentRadius radii),
        p.evalLaurentCoeffSeq radii seqs (n - k) * q.evalLaurentCoeffSeq radii seqs k
  | .neg p, radii, seqs, n => -(p.evalLaurentCoeffSeq radii seqs n)
  | .smul r p, radii, seqs, n => r * p.evalLaurentCoeffSeq radii seqs n

/-- Laurent evaluation of zero-padded nonnegative arrays extended symmetrically at `|k|`.
Array sizes give conservative support bounds, including for empty arrays. -/
def evalChebCoeff (p : CompPoly L) (arrs : Fin L → Array ℚ) : ℤ → ℚ :=
  p.evalLaurentCoeffSeq (fun i => (arrs i).size) (fun i n => (arrs i).getD n.natAbs 0)

/-- Finite support is propagated by the computable Laurent interpreter. -/
theorem evalLaurentCoeffSeq_eq_zero_of_radius_lt (p : CompPoly L)
    (radii : Fin L → ℕ) (seqs : Fin L → ℤ → ℚ)
    (hs : ∀ i n, radii i < n.natAbs → seqs i n = 0)
    (n : ℤ) (hn : p.laurentRadius radii < n.natAbs) :
    p.evalLaurentCoeffSeq radii seqs n = 0 := by
  induction p generalizing n with
  | C r => simp [evalLaurentCoeffSeq, show n ≠ 0 by intro h; subst n; simp [laurentRadius] at hn]
  | X i => exact hs i n hn
  | add p q ihp ihq =>
      simp only [laurentRadius] at hn
      simp [evalLaurentCoeffSeq, ihp n (lt_of_le_of_lt (le_max_left _ _) hn),
        ihq n (lt_of_le_of_lt (le_max_right _ _) hn)]
  | sub p q ihp ihq =>
      simp only [laurentRadius] at hn
      simp [evalLaurentCoeffSeq, ihp n (lt_of_le_of_lt (le_max_left _ _) hn),
        ihq n (lt_of_le_of_lt (le_max_right _ _) hn)]
  | mul p q ihp ihq =>
      apply Finset.sum_eq_zero
      intro k hk
      have hk' := (mem_laurentModes_iff (q.laurentRadius radii) k).mp hk
      have htri := Int.natAbs_add_le (n - k) k
      simp only [sub_add_cancel] at htri
      have hp : p.laurentRadius radii < (n - k).natAbs := by
        simp only [laurentRadius] at hn
        omega
      simp [ihp (n - k) hp]
  | neg p ih => simp [evalLaurentCoeffSeq, ih n hn]
  | smul r p ih => simp [evalLaurentCoeffSeq, ih n hn]



/-- The array interpreter vanishes beyond the propagated array-size bound. -/
theorem evalChebCoeff_eq_zero_of_radius_lt (p : CompPoly L)
    (arrs : Fin L → Array ℚ) (n : ℤ)
    (hn : p.laurentRadius (fun i => (arrs i).size) < n.natAbs) :
    p.evalChebCoeff arrs n = 0 := by
  apply p.evalLaurentCoeffSeq_eq_zero_of_radius_lt _ _ _ n hn
  intro i k hk
  simp [Array.getD, show ¬k.natAbs < (arrs i).size by omega]

end MvPolyBridge.CompPoly
