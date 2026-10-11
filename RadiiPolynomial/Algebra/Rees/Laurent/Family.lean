import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Data.Int.ModEq

/-!
# The Laurent/|k|-filtered Rees family

For a commutative ring `R`, the Rees family `U R ⊆ R[X][T;T⁻¹]` is the `R[X]`-subalgebra of Laurent
polynomials `∑ⱼ pⱼ Tʲ` with `X ^ |j| ∣ pⱼ` for every `j`. Here `X` is the Rees parameter `h` and `T`
is the Laurent variable; `U R` is the Rees algebra `∑ₙ Xⁿ Fₙ` of the increasing filtration
`Fₙ = {supp ⊆ [-n, n]}` of `R[T;T⁻¹]` (not Mathlib's `I`-adic `reesAlgebra`).

## Main definitions

* `U R`: the Rees family, as a `Subalgebra R[X] R[X][T;T⁻¹]`.
* `z j = X ^ |j| • Tʲ`: the atoms; `u = z 1 + z (-1)`; `q m`: the stored-Chebyshev atoms.
* `JN N = (z (N + 1), z (-(N + 1)))`: the tail ideal; `aN N k = 2 (N + 1 - |k|)`: the annihilator
  exponent (ℕ-truncated); `SN R N`: the coefficientwise right-hand side of the membership criterion.

## Main results

* `z_mul_z_eq`, `z_mul_z`: the structure constants `z i * z j = X ^ (|i| + |j| - |i + j|) • z (i + j)`.
* `mem_JN_iff`: `f ∈ JN N ↔ ∀ j, X ^ max |j| (2N + 2 - |j|) ∣ f.coeff j`.
* `smul_z_mem_JN_iff`: the annihilator profile `p • z j ∈ JN N ↔ X ^ aN N j ∣ p`, for every `j`.
* `contraction_fails`, `tail_span_not_ideal` (`[Nontrivial R]`), `u_pow_even_not_mem` (`[CharZero R]`):
  the boundaries of the construction.

Generic Laurent lemmas: `coeff_single_eq` (any semiring) and `dvd_coeff_mul` (divisibility
propagation through the Laurent product, any commutative semiring and any `x`).

Promoted from the S028a/slice-20 sources by unit L003-ReesLaurent (see `RENAMES.md`).
-/

noncomputable section

namespace RadiiPolynomial.Rees.Laurent

open Polynomial LaurentPolynomial

section Generic

/-- Coefficient of a Laurent monomial (non-deprecated form). -/
theorem coeff_single_eq {S : Type*} [Semiring S] {a a' : ℤ} {b : S} :
    (AddMonoidAlgebra.single a b : S[T;T⁻¹]).coeff a' = if a = a' then b else 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Divisibility propagation through the Laurent product. -/
theorem dvd_coeff_mul {S : Type*} [CommSemiring S] (x : S) {α β γ : ℤ → ℕ} {f g : S[T;T⁻¹]}
    (hf : ∀ i, x ^ α i ∣ f.coeff i) (hg : ∀ k, x ^ β k ∣ g.coeff k)
    (hγ : ∀ i k, γ (i + k) ≤ α i + β k) (j : ℤ) : x ^ γ j ∣ (f * g).coeff j := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun k _ => ?_
  dsimp only
  split_ifs with h
  · subst h
    exact (pow_dvd_pow _ (hγ i k)).trans (by rw [pow_add]; exact mul_dvd_mul (hf i) (hg k))
  · exact dvd_zero _

end Generic

section General

variable {R : Type*} [CommRing R]

variable (R) in
/-- The based Rees family `U = ⊕_j X^{|j|} R[X] T^j` inside `R[X][T;T⁻¹]`. -/
def U : Subalgebra R[X] (R[X])[T;T⁻¹] where
  carrier := {f | ∀ j : ℤ, (X : R[X]) ^ j.natAbs ∣ f.coeff j}
  mul_mem' {f g} hf hg j :=
    dvd_coeff_mul (X : R[X]) (α := fun i => i.natAbs) (β := fun k => k.natAbs) hf hg
      (fun i k => Int.natAbs_add_le i k) j
  add_mem' {f g} hf hg j := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact dvd_add (hf j) (hg j)
  algebraMap_mem' p j := by
    classical
    rw [LaurentPolynomial.algebraMap_apply, ← LaurentPolynomial.single_eq_C,
      coeff_single_eq]
    split_ifs with h
    · subst h; simp
    · exact dvd_zero _

theorem mem_U_iff (f : (R[X])[T;T⁻¹]) :
    f ∈ U R ↔ ∀ j : ℤ, (X : R[X]) ^ j.natAbs ∣ f.coeff j := Iff.rfl

/-- The based atoms `z j = X^{|j|} T^j`. -/
def z (j : ℤ) : U R :=
  ⟨AddMonoidAlgebra.single j ((X : R[X]) ^ j.natAbs), fun k => by
    classical
    rw [coeff_single_eq]
    split_ifs with h
    · subst h; exact dvd_rfl
    · exact dvd_zero _⟩

theorem coe_z (j : ℤ) :
    ((z j : U R) : (R[X])[T;T⁻¹]) = AddMonoidAlgebra.single j ((X : R[X]) ^ j.natAbs) := rfl

theorem coe_z_apply (j k : ℤ) :
    ((z j : U R) : (R[X])[T;T⁻¹]).coeff k = if k = j then (X : R[X]) ^ j.natAbs else 0 := by
  classical
  rw [coe_z, coeff_single_eq]
  simp only [eq_comm]

/-- The tail-generated ideal. -/
def JN (N : ℕ) : Ideal (U R) := Ideal.span {z ((N : ℤ) + 1), z (-((N : ℤ) + 1))}

/-- The annihilator exponent (the one exponent of the family). -/
def aN (N : ℕ) (k : ℤ) : ℕ := 2 * (N + 1 - k.natAbs)

/-- `u = z 1 + z (-1)`. -/
def u : U R := z 1 + z (-1)

/-- The stored-Chebyshev atoms. -/
def q (m : ℕ) : U R := if m = 0 then 1 else z (m : ℤ) + z (-(m : ℤ))

/-! ### Structure constants -/

theorem coe_smul_U (p : R[X]) (f : U R) :
    ((p • f : U R) : (R[X])[T;T⁻¹]) = p • (f : (R[X])[T;T⁻¹]) := rfl

theorem z_mul_z_eq {i j k : ℤ} {e : ℕ} (hk : i + j = k)
    (he : e + k.natAbs = i.natAbs + j.natAbs) :
    (z i : U R) * z j = ((X : R[X]) ^ e) • z k := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_smul_U, coe_z, coe_z, coe_z, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.smul_single', hk, ← pow_add, ← pow_add, he]

theorem z_mul_z (i j : ℤ) :
    (z i : U R) * z j =
      ((X : R[X]) ^ (i.natAbs + j.natAbs - (i + j).natAbs)) • z (i + j) :=
  z_mul_z_eq rfl (by have := Int.natAbs_add_le i j; omega)

theorem z_mul_z_of_nonneg {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) :
    (z i : U R) * z j = z (i + j) := by
  rw [z_mul_z_eq (e := 0) rfl (by omega), pow_zero, one_smul]

theorem z_mul_z_of_nonpos {i j : ℤ} (hi : i ≤ 0) (hj : j ≤ 0) :
    (z i : U R) * z j = z (i + j) := by
  rw [z_mul_z_eq (e := 0) rfl (by omega), pow_zero, one_smul]

theorem z_mul_z_opposite {i j : ℤ} (hi : 0 ≤ i) (hj : j ≤ 0) :
    (z i : U R) * z j = ((X : R[X]) ^ (2 * min i.natAbs j.natAbs)) • z (i + j) :=
  z_mul_z_eq rfl (by omega)

theorem z_zero : (z 0 : U R) = 1 := by
  apply Subtype.ext
  rw [coe_z]
  simp only [Int.natAbs_zero, pow_zero]
  rfl

/-- The positive half is generated by `x = z 1`, and `x ^ n = z n`. -/
theorem z_one_pow (n : ℕ) : (z 1 : U R) ^ n = z (n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, z_zero]
  | succ n ih => rw [pow_succ, ih, z_mul_z_of_nonneg (by omega) (by omega), Nat.cast_succ]

/-! ### The membership criterion -/

variable (R) in
/-- The right-hand side of the criterion, as an ideal of `U`. -/
def SN (N : ℕ) : Ideal (U R) where
  carrier := {f | ∀ j : ℤ,
    (X : R[X]) ^ (max j.natAbs (2 * N + 2 - j.natAbs)) ∣ (f : (R[X])[T;T⁻¹]).coeff j}
  add_mem' {f g} hf hg j := by
    rw [Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact dvd_add (hf j) (hg j)
  zero_mem' j := by
    rw [Subalgebra.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact dvd_zero _
  smul_mem' c {f} hf j := by
    rw [smul_eq_mul, Subalgebra.coe_mul]
    exact dvd_coeff_mul (X : R[X]) (α := fun i => i.natAbs)
      (β := fun k => max k.natAbs (2 * N + 2 - k.natAbs))
      (γ := fun j => max j.natAbs (2 * N + 2 - j.natAbs)) ((mem_U_iff _).1 c.2) hf
      (fun i k => by
        have h1 := Int.natAbs_add_le i k
        have h2 : k.natAbs ≤ i.natAbs + (i + k).natAbs := by
          have := Int.natAbs_add_le (-i) (i + k)
          rw [Int.natAbs_neg, neg_add_cancel_left] at this
          exact this
        omega) j

theorem z_mem_SN (N : ℕ) (j : ℤ) (hj : N < j.natAbs) : (z j : U R) ∈ SN R N := by
  intro k
  rw [coe_z_apply]
  split_ifs with h
  · subst h
    exact pow_dvd_pow _ (by omega)
  · exact dvd_zero _

theorem JN_le_SN (N : ℕ) : JN (R := R) N ≤ SN R N := by
  rw [JN, Ideal.span_le]
  intro f hf
  rcases hf with rfl | rfl
  · exact z_mem_SN N _ (by omega)
  · exact z_mem_SN N _ (by omega)

theorem z_mem_JN_pos (N : ℕ) : (z ((N : ℤ) + 1) : U R) ∈ JN N :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem z_mem_JN_neg (N : ℕ) : (z (-((N : ℤ) + 1)) : U R) ∈ JN N :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem coe_smul_z_mul_z (g : R[X]) (i j : ℤ) :
    ((g • ((z i : U R) * z (j - i)) : U R) : (R[X])[T;T⁻¹]) =
      AddMonoidAlgebra.single j ((X : R[X]) ^ (i.natAbs + (j - i).natAbs) * g) := by
  rw [coe_smul_U, Subalgebra.coe_mul, coe_z, coe_z, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.smul_single', add_sub_cancel, pow_add, mul_comm g]

theorem exists_single_mem_JN (N : ℕ) (j : ℤ) (r : R[X])
    (hr : (X : R[X]) ^ (max j.natAbs (2 * N + 2 - j.natAbs)) ∣ r) :
    ∃ w ∈ JN (R := R) N, (w : (R[X])[T;T⁻¹]) = AddMonoidAlgebra.single j r := by
  obtain ⟨g, rfl⟩ := hr
  rcases le_or_gt 0 j with hj | hj
  · refine ⟨g • ((z ((N : ℤ) + 1) : U R) * z (j - ((N : ℤ) + 1))),
      Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_right _ _ (z_mem_JN_pos N)), ?_⟩
    rw [coe_smul_z_mul_z]
    congr 3
    omega
  · refine ⟨g • ((z (-((N : ℤ) + 1)) : U R) * z (j - -((N : ℤ) + 1))),
      Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_right _ _ (z_mem_JN_neg N)), ?_⟩
    rw [coe_smul_z_mul_z]
    congr 3
    omega

/-- The membership criterion for `J_N`. -/
theorem mem_JN_iff (N : ℕ) (f : U R) :
    f ∈ JN N ↔ ∀ j : ℤ,
      (X : R[X]) ^ (max j.natAbs (2 * N + 2 - j.natAbs)) ∣ (f : (R[X])[T;T⁻¹]).coeff j := by
  refine ⟨fun hf => JN_le_SN N hf, fun hf => ?_⟩
  choose w hw hwf using fun j => exists_single_mem_JN (R := R) N j _ (hf j)
  have hsum : f = ∑ j ∈ (f : (R[X])[T;T⁻¹]).coeff.support, w j := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp_rw [hwf]
    exact (AddMonoidAlgebra.sum_coeff_single _).symm
  rw [hsum]
  exact Ideal.sum_mem _ fun j _ => hw j

/-! ### The annihilator profile -/

theorem coe_smul_z_apply (p : R[X]) (j k : ℤ) :
    ((p • (z j : U R) : U R) : (R[X])[T;T⁻¹]).coeff k =
      if k = j then p * (X : R[X]) ^ j.natAbs else 0 := by
  rw [coe_smul_U, coe_z, AddMonoidAlgebra.smul_single', coeff_single_eq]
  simp only [eq_comm]

theorem X_pow_add_dvd_mul_X_pow_iff (a b : ℕ) (p : R[X]) :
    (X : R[X]) ^ (a + b) ∣ p * X ^ b ↔ (X : R[X]) ^ a ∣ p := by
  constructor
  · intro h
    rw [Polynomial.X_pow_dvd_iff] at h ⊢
    intro d hd
    have := h (d + b) (by omega)
    rwa [Polynomial.coeff_mul_X_pow] at this
  · intro h
    rw [pow_add]
    exact mul_dvd_mul_right h _

/-- Every tail atom lies in `J_N`. -/
theorem z_mem_JN_of_tail {N : ℕ} {j : ℤ} (h : N < j.natAbs) : (z j : U R) ∈ JN N :=
  (mem_JN_iff N _).2 fun k => z_mem_SN N j h k

/-- The annihilator of the class of `z j` in `U / J_N` is `(X ^ aN N j)`, for every `j` (for a tail
index both sides hold: `z j ∈ J_N` and `aN N j = 0`). -/
theorem smul_z_mem_JN_iff {N : ℕ} {j : ℤ} (p : R[X]) :
    p • (z j : U R) ∈ JN N ↔ (X : R[X]) ^ (aN N j) ∣ p := by
  rw [mem_JN_iff]
  constructor
  · intro H
    have hj := H j
    rw [coe_smul_z_apply, ite_eq_left rfl,
      show max j.natAbs (2 * N + 2 - j.natAbs) = aN N j + j.natAbs by unfold aN; omega] at hj
    exact (X_pow_add_dvd_mul_X_pow_iff _ _ _).1 hj
  · intro H k
    rw [coe_smul_z_apply]
    split_ifs with hk
    · subst hk
      rw [show max k.natAbs (2 * N + 2 - k.natAbs) = aN N k + k.natAbs by unfold aN; omega]
      exact (X_pow_add_dvd_mul_X_pow_iff _ _ _).2 H
    · exact dvd_zero _

/-! ### The constant term `X^{2N+2}` -/

/-- `z_{-(N+1)} z_{N+1} = X^{2N+2} z_0`. -/
theorem z_neg_mul_z (N : ℕ) :
    (z (-((N : ℤ) + 1)) : U R) * z ((N : ℤ) + 1) = ((X : R[X]) ^ (2 * N + 2)) • z 0 :=
  z_mul_z_eq (by ring) (by omega)

theorem coe_smul_one_apply (p : R[X]) (k : ℤ) :
    ((p • (1 : U R) : U R) : (R[X])[T;T⁻¹]).coeff k = if k = 0 then p else 0 := by
  rw [← z_zero, coe_smul_z_apply]
  simp

/-- `X^{2N+2} · 1 ∈ J_N`. -/
theorem X_pow_smul_one_mem_JN (N : ℕ) : ((X : R[X]) ^ (2 * N + 2)) • (1 : U R) ∈ JN N := by
  rw [← z_zero, ← z_neg_mul_z]
  exact Ideal.mul_mem_right _ _ (z_mem_JN_neg N)

/-- The positive-half contraction fails. -/
theorem contraction_fails [Nontrivial R] (N : ℕ) :
    ¬ ∃ g : U R, (∀ j < 0, (g : (R[X])[T;T⁻¹]).coeff j = 0) ∧
      g * z ((N : ℤ) + 1) = ((X : R[X]) ^ (2 * N + 2)) • (1 : U R) := by
  rintro ⟨g, hneg, hg⟩
  have h0 := congrArg (fun f : U R => (f : (R[X])[T;T⁻¹]).coeff 0) hg
  rw [coe_smul_one_apply, ite_eq_left rfl, Subalgebra.coe_mul, coe_z,
    AddMonoidAlgebra.coeff_mul_single_apply, hneg _ (by omega), zero_mul] at h0
  exact (Polynomial.monic_X_pow (R := R) (2 * N + 2)).ne_zero h0.symm

/-- The tail span is not an ideal. -/
theorem tail_span_not_ideal [Nontrivial R] (N : ℕ) :
    ∃ f g : U R, (∀ j : ℤ, j.natAbs ≤ N → (f : (R[X])[T;T⁻¹]).coeff j = 0) ∧
      ¬ (∀ j : ℤ, j.natAbs ≤ N → ((f * g : U R) : (R[X])[T;T⁻¹]).coeff j = 0) := by
  refine ⟨z (-((N : ℤ) + 1)), z ((N : ℤ) + 1), fun j hj => ?_, fun H => ?_⟩
  · rw [coe_z_apply, ite_eq_right (by omega)]
  · have h0 := H 0 (by simp)
    rw [z_neg_mul_z, z_zero, coe_smul_one_apply, ite_eq_left rfl] at h0
    exact (Polynomial.monic_X_pow (R := R) (2 * N + 2)).ne_zero h0

/-! ### The stored-Chebyshev profile -/

theorem q_of_ne_zero {m : ℕ} (hm : m ≠ 0) : (q m : U R) = z (m : ℤ) + z (-(m : ℤ)) := by
  rw [q, ite_eq_right hm]

theorem q_zero : (q 0 : U R) = 1 := by
  rw [q, ite_eq_left rfl]

/-- The annihilator of the class of the stored-Chebyshev atom `q m` in `U / J_N`, for
`m ≤ N`: it is `(X ^ (2 (N + 1 - m)))`. -/
theorem smul_q_mem_JN_iff {N m : ℕ} (hm : m ≤ N) (p : R[X]) :
    p • (q m : U R) ∈ JN N ↔ (X : R[X]) ^ (2 * (N + 1 - m)) ∣ p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [q_zero, ← z_zero, smul_z_mem_JN_iff]
    rfl
  · have ha : ∀ j : ℤ, j.natAbs = m → aN N j = 2 * (N + 1 - m) := fun j hj => by
      unfold aN; omega
    rw [q_of_ne_zero (by omega), smul_add]
    constructor
    · intro H
      rw [mem_JN_iff] at H
      have hj := H (m : ℤ)
      rw [Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coe_smul_z_apply,
        coe_smul_z_apply, ite_eq_left rfl, ite_eq_right (by omega), add_zero,
        show max (m : ℤ).natAbs (2 * N + 2 - (m : ℤ).natAbs) = 2 * (N + 1 - m) + (m : ℤ).natAbs
          by omega] at hj
      exact (X_pow_add_dvd_mul_X_pow_iff _ _ _).1 hj
    · intro H
      refine Ideal.add_mem _ ((smul_z_mem_JN_iff p).2 ?_) ((smul_z_mem_JN_iff p).2 ?_)
      · rwa [ha _ (by omega)]
      · rwa [ha _ (by omega)]

/-- The attainment identity `q_{N+1} q_{N+1-m} - q_{2N+2-m} = X^{2(N+1-m)} q_m`, for
`1 ≤ m ≤ N`. -/
theorem q_mul_q_sub {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    (q (N + 1) : U R) * q (N + 1 - m) - q (2 * N + 2 - m) =
      ((X : R[X]) ^ (2 * (N + 1 - m))) • q m := by
  rw [q_of_ne_zero (show N + 1 ≠ 0 by omega), q_of_ne_zero (show N + 1 - m ≠ 0 by omega),
    q_of_ne_zero (show 2 * N + 2 - m ≠ 0 by omega), q_of_ne_zero (show m ≠ 0 by omega)]
  have h1 : (z ((N + 1 : ℕ) : ℤ) : U R) * z ((N + 1 - m : ℕ) : ℤ) =
      ((X : R[X]) ^ 0) • z ((2 * N + 2 - m : ℕ) : ℤ) := z_mul_z_eq (by omega) (by omega)
  have h2 : (z ((N + 1 : ℕ) : ℤ) : U R) * z (-((N + 1 - m : ℕ) : ℤ)) =
      ((X : R[X]) ^ (2 * (N + 1 - m))) • z (m : ℤ) := z_mul_z_eq (by omega) (by omega)
  have h3 : (z (-((N + 1 : ℕ) : ℤ)) : U R) * z ((N + 1 - m : ℕ) : ℤ) =
      ((X : R[X]) ^ (2 * (N + 1 - m))) • z (-(m : ℤ)) := z_mul_z_eq (by omega) (by omega)
  have h4 : (z (-((N + 1 : ℕ) : ℤ)) : U R) * z (-((N + 1 - m : ℕ) : ℤ)) =
      ((X : R[X]) ^ 0) • z (-((2 * N + 2 - m : ℕ) : ℤ)) := z_mul_z_eq (by omega) (by omega)
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, pow_zero, one_smul, one_smul, smul_add]
  abel

/-- `q_{N+1}^2 - q_{2N+2} = 2 X^{2N+2}`. -/
theorem q_sq_sub (N : ℕ) :
    (q (N + 1) : U R) ^ 2 - q (2 * N + 2) = ((2 : R[X]) * X ^ (2 * N + 2)) • (1 : U R) := by
  rw [q_of_ne_zero (show N + 1 ≠ 0 by omega), q_of_ne_zero (show 2 * N + 2 ≠ 0 by omega)]
  have h1 : (z ((N + 1 : ℕ) : ℤ) : U R) * z ((N + 1 : ℕ) : ℤ) =
      ((X : R[X]) ^ 0) • z ((2 * N + 2 : ℕ) : ℤ) := z_mul_z_eq (by omega) (by omega)
  have h2 : (z ((N + 1 : ℕ) : ℤ) : U R) * z (-((N + 1 : ℕ) : ℤ)) =
      ((X : R[X]) ^ (2 * N + 2)) • z 0 := z_mul_z_eq (by omega) (by omega)
  have h3 : (z (-((N + 1 : ℕ) : ℤ)) : U R) * z ((N + 1 : ℕ) : ℤ) =
      ((X : R[X]) ^ (2 * N + 2)) • z 0 := z_mul_z_eq (by omega) (by omega)
  have h4 : (z (-((N + 1 : ℕ) : ℤ)) : U R) * z (-((N + 1 : ℕ) : ℤ)) =
      ((X : R[X]) ^ 0) • z (-((2 * N + 2 : ℕ) : ℤ)) := z_mul_z_eq (by omega) (by omega)
  rw [sq, add_mul, mul_add, mul_add, h1, h2, h3, h4, pow_zero, one_smul, one_smul, z_zero,
    mul_smul, two_smul]
  abel

/-! ### The `u`-powers -/

theorem coe_u : ((u : U R) : (R[X])[T;T⁻¹]) =
    AddMonoidAlgebra.single 1 (X : R[X]) + AddMonoidAlgebra.single (-1) (X : R[X]) := by
  rw [u, Subalgebra.coe_add, coe_z, coe_z]
  simp

/-- The coefficients of `u ^ n` (binomial normal form). -/
theorem u_pow_coeff (n : ℕ) (j : ℤ) :
    ((u ^ n : U R) : (R[X])[T;T⁻¹]).coeff j =
      if (n : ℤ) ≡ j [ZMOD 2] ∧ j.natAbs ≤ n then
        (Nat.choose n ((n + j).toNat / 2) : R[X]) * X ^ n else 0 := by
  classical
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((AddMonoidAlgebra.single (1 : ℤ) (X : R[X])) ^ k *
        (AddMonoidAlgebra.single (-1 : ℤ) (X : R[X])) ^ (n - k) *
        ((n.choose k : ℕ) : (R[X])[T;T⁻¹])).coeff j =
      if 2 * (k : ℤ) - n = j then (n.choose k : R[X]) * X ^ n else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.natCast_def,
      AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, coeff_single_eq]
    have e : k • (1 : ℤ) + (n - k) • (-1 : ℤ) + 0 = 2 * (k : ℤ) - n := by
      simp only [nsmul_eq_mul, mul_one, mul_neg, add_zero]
      omega
    rw [e]
    split_ifs
    · rw [← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    · rfl
  rw [Subalgebra.coe_pow, coe_u, add_pow, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_congr rfl hterm]
  split_ifs with hc
  · simp only [Int.ModEq] at hc
    rw [Finset.sum_eq_single ((n + j).toNat / 2)]
    · rw [ite_eq_left (by omega)]
    · intro b _ hb
      rw [ite_eq_right (by omega)]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [ite_eq_right]
    intro h
    apply hc
    simp only [Int.ModEq]
    omega

/-- `u ^ (2N+1) ∈ J_N` over every commutative ring. -/
theorem u_pow_odd_mem (N : ℕ) : (u : U R) ^ (2 * N + 1) ∈ JN N := by
  rw [mem_JN_iff]
  intro j
  rw [u_pow_coeff]
  split_ifs with hc
  · simp only [Int.ModEq] at hc
    exact (pow_dvd_pow _ (by omega)).trans (dvd_mul_left _ _)
  · exact dvd_zero _

/-- `u ^ (2N) ∉ J_N` in characteristic zero. -/
theorem u_pow_even_not_mem [CharZero R] (N : ℕ) : (u : U R) ^ (2 * N) ∉ JN N := by
  rw [mem_JN_iff]
  intro H
  have h0 := H 0
  rw [u_pow_coeff, ite_eq_left (by simp only [Int.ModEq]; omega),
    show (((2 * N : ℕ) : ℤ) + (0 : ℤ)).toNat / 2 = N by omega, Polynomial.X_pow_dvd_iff] at h0
  have h1 := h0 (2 * N) (by omega)
  rw [Polynomial.coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self, ← Polynomial.C_eq_natCast,
    Polynomial.coeff_C_zero] at h1
  exact (Nat.choose_pos (by omega : N ≤ 2 * N)).ne' (Nat.cast_eq_zero.1 h1)

end General

end RadiiPolynomial.Rees.Laurent
