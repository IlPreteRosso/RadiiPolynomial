import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Generic MvPolynomial Derivative Bounds

Degree-drop and constant-second-derivative lemmas independent of the weighted sequence model,
and the simp lemma `C_ofNat_eq` normalizing numeral constants `C n` to the numeral `n`.
-/

open MvPolynomial (C X pderiv)

namespace MvPolynomial

/-- `C` sends a numeral `n ≥ 2` to the same numeral of `MvPolynomial σ R`; stated in Mathlib's
`ofNat(n)` form (as `Polynomial.C_ofNat`), so that `simp` fires on literal numerals. -/
@[simp] theorem C_ofNat_eq {σ R : Type*} [CommSemiring R] (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.C (ofNat(n) : R) = (ofNat(n) : MvPolynomial σ R) :=
  map_ofNat MvPolynomial.C n

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Each partial derivative drops the total degree by at least one. -/
theorem totalDegree_pderiv_le [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  refine Finset.sup_le fun s hs => ?_
  have h : s + Finsupp.single i 1 ∈ p.support := by
    rw [mem_support_iff, coeff_pderiv] at hs
    exact mem_support_iff.mpr (left_ne_zero_of_mul hs)
  have hle := le_totalDegree h
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hle
  simpa using Nat.sub_le_sub_right hle 1

theorem totalDegree_pderiv_pderiv_eq_zero [DecidableEq σ] (i j : σ)
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 2) :
    (pderiv i (pderiv j p)).totalDegree = 0 := by
  have h1 := totalDegree_pderiv_le j p
  have h2 := totalDegree_pderiv_le i (pderiv j p)
  omega

theorem pderiv_pderiv_eq_C_of_totalDegree_le_two [DecidableEq σ] (i j : σ)
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 2) :
    ∃ c : R, pderiv i (pderiv j p) = C c := by
  have h := totalDegree_pderiv_pderiv_eq_zero i j p hp
  exact ⟨(pderiv i (pderiv j p)).coeff 0, (totalDegree_eq_zero_iff_eq_C).mp h⟩

end MvPolynomial
