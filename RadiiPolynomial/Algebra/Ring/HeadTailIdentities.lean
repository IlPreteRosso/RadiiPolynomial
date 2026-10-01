import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Head/tail identities for an idempotent in any ring

Let `A` be a ring, `P ∈ A` an idempotent (the head) and `Q = 1 - P` its complement
(the tail). Three identities describe how a head/tail-split preconditioner acts on a
head/tail-split operator. They are pure ring identities: no norm, no inverse, no
commutativity of `A`, and the hypotheses are stated in Mathlib vocabulary
(`IsIdempotentElem`, `Commute`). The bounded-operator transport lives in
`Operators/HeadTail.lean`; this module imports Mathlib only.

Main declarations:
* `HeadTail.composition_identity_ring` — for `R P = 0`:
  `(M P + R)(P L Q + Q L) = M P L Q + R L`.
* `HeadTail.defect_identity_ring` — for `Λ` commuting with `P` and `G P = 0`:
  `(M P + G)((P (Λ + L) P + Q Λ Q) - (Λ + L)) = -(M P L Q + G Q L)`.
* `HeadTail.inverse_defect_ring` — for `G P = 0` and `G Λ Q = Q`:
  `1 - (M P + G)(P (Λ + L) P + Q Λ Q) = P - M P (Λ + L) P`.
-/

namespace RadiiPolynomial

namespace HeadTail

/-- **(T34, L001.)** Composition identity for an idempotent head `P` in any ring:
if `R P = 0` then `(M P + R)(P L (1 - P) + (1 - P) L) = M P L (1 - P) + R L`. -/
theorem composition_identity_ring {A : Type*} [Ring A] (P M R L : A)
    (hP : IsIdempotentElem P) (hRP : R * P = 0) :
    (M * P + R) * (P * L * (1 - P) + (1 - P) * L) = M * P * L * (1 - P) + R * L := by
  have hPQ : P * (1 - P) = 0 := hP.mul_one_sub_self
  have hRQ : R * (1 - P) = R := by rw [mul_sub, mul_one, hRP, sub_zero]
  rw [add_mul, mul_add, mul_add]
  simp only [mul_assoc, ← mul_assoc P P, hP.eq, ← mul_assoc P (1 - P), hPQ,
    ← mul_assoc R P, hRP, ← mul_assoc R (1 - P), hRQ, zero_mul, mul_zero, add_zero, zero_add]

/-- **(T35, L001.)** Defect identity: with `P` idempotent, `Λ` commuting with `P` and
`G P = 0`, the split approximate inverse `P (Λ + L) P + (1 - P) Λ (1 - P)` misses
`Λ + L` by `-(M P L (1 - P) + G (1 - P) L)` after the preconditioner `M P + G`. -/
theorem defect_identity_ring {A : Type*} [Ring A] (P M G Λ L : A)
    (hP : IsIdempotentElem P) (hΛ : Commute Λ P) (hG : G * P = 0) :
    (M * P + G) * ((P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L)) =
      -(M * P * L * (1 - P) + G * (1 - P) * L) := by
  have h1 : P * Λ * P = P * Λ := by rw [mul_assoc, hΛ.eq, ← mul_assoc, hP.eq]
  have key : (P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L) = P * L * P - L := by
    have e : (1 - P) * Λ * (1 - P) = Λ - Λ * P - P * Λ + P * Λ * P := by noncomm_ring
    rw [e, mul_add, add_mul, h1, hΛ.eq]
    abel
  have h3 : M * P * (P * L * P) = M * P * L * P := by
    simp only [← mul_assoc]; rw [mul_assoc M P P, hP.eq]
  have h4 : G * (P * L * P) = 0 := by
    simp only [← mul_assoc]; rw [hG, zero_mul, zero_mul]
  rw [key, add_mul, mul_sub, mul_sub, h3, h4, mul_sub (M * P * L), mul_one, mul_sub G, mul_one,
    sub_mul, hG, zero_mul, sub_zero]
  abel

/-- **(T36, L001.)** Inverse-defect identity: with `P` idempotent, `G P = 0` and
`G Λ (1 - P) = 1 - P`, `1 - (M P + G)(P (Λ + L) P + (1 - P) Λ (1 - P)) = P - M P (Λ + L) P`.
No commutation of `Λ` with `P` is needed. -/
theorem inverse_defect_ring {A : Type*} [Ring A] (P M G Λ L : A)
    (hP : IsIdempotentElem P) (hG : G * P = 0) (hGΛ : G * Λ * (1 - P) = 1 - P) :
    1 - (M * P + G) * (P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) =
      P - M * P * (Λ + L) * P := by
  have hPQ : P * (1 - P) = 0 := hP.mul_one_sub_self
  have hGQ : G * (1 - P) = G := by rw [mul_sub, mul_one, hG, sub_zero]
  have t1 : M * P * (P * (Λ + L) * P) = M * P * (Λ + L) * P := by
    simp only [← mul_assoc]; rw [mul_assoc M P P, hP.eq]
  have t2 : M * P * ((1 - P) * Λ * (1 - P)) = 0 := by
    simp only [← mul_assoc]; rw [mul_assoc M P (1 - P), hPQ, mul_zero, zero_mul, zero_mul]
  have t3 : G * (P * (Λ + L) * P) = 0 := by
    simp only [← mul_assoc]; rw [hG, zero_mul, zero_mul]
  have t4 : G * ((1 - P) * Λ * (1 - P)) = 1 - P := by
    simp only [← mul_assoc]; rw [hGQ, hGΛ]
  rw [add_mul (M * P) G, mul_add (M * P), mul_add G, t1, t2, t3, t4]
  abel

end HeadTail

end RadiiPolynomial
