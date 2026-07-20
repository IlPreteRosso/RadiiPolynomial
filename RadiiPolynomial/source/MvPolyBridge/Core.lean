import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Generic MvPolynomial Derivative Bounds

Degree-drop and constant-second-derivative lemmas independent of the weighted sequence model.
-/

open MvPolynomial (C X pderiv)

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Each partial derivative drops the total degree by at least one. -/
theorem totalDegree_pderiv_le [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h : coeff s p * ↑(s i) = 0
  · simp [h]
  · refine (totalDegree_monomial _ h).le.trans ?_
    have hi : 1 ≤ s i := by
      rcases Nat.eq_zero_or_pos (s i) with h' | h'
      · exfalso; simp [h'] at h
      · exact h'
    have hle : Finsupp.single i 1 ≤ s := fun j => by
      simp only [Finsupp.single_apply]
      split_ifs with hij
      · subst hij; exact hi
      · exact Nat.zero_le _
    have hsum : (s - Finsupp.single i 1).sum (fun _ => id) + 1 =
        s.sum (fun _ => id) := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp [Finsupp.sum_single_index]
    have h1 : (s - Finsupp.single i 1).sum (fun _ => id) ≤
        s.sum (fun _ => id) - 1 := by omega
    show (s - Finsupp.single i 1).sum (fun _ => id) ≤ p.totalDegree - 1
    exact h1.trans (Nat.sub_le_sub_right (le_totalDegree hs) 1)

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
  exact ⟨coeff 0 (pderiv i (pderiv j p)), (totalDegree_eq_zero_iff_eq_C).mp h⟩

lemma totalDegree_C_le (a : R) : (C a : MvPolynomial σ R).totalDegree ≤ 0 :=
  le_of_eq (totalDegree_C a)

lemma totalDegree_X_le [Nontrivial R] (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 :=
  le_of_eq (totalDegree_X i)

lemma totalDegree_add_le (p q : MvPolynomial σ R) :
    (p + q).totalDegree ≤ p.totalDegree + q.totalDegree :=
  (totalDegree_add _ _).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

lemma totalDegree_sub_le {R : Type*} [CommRing R] (p q : MvPolynomial σ R) :
    (p - q).totalDegree ≤ p.totalDegree + q.totalDegree :=
  (totalDegree_sub _ _).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

lemma totalDegree_neg_le {R : Type*} [CommRing R] (p : MvPolynomial σ R) :
    (-p).totalDegree ≤ p.totalDegree :=
  le_of_eq (totalDegree_neg _)

end MvPolynomial
