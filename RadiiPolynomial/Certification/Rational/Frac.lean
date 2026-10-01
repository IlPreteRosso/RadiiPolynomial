import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Gcd-free rational fractions

`QF` stores a rational number as a numerator/denominator pair that is never normalized, so
kernel-reduced certificate arithmetic performs no gcd computation. `QF.subMul` is the one
arithmetic step (`a − b·c` with `b c : ℚ`), and `QF.ceilAbs S a` rounds `|a|` upward onto the
grid `1/S` with one natural-number division.

- `QF.toRat_subMul`: semantics of `subMul`
- `QF.abs_toRat_le`: `|a| ≤ ceilAbs S a / S` for `0 < S`
-/

namespace RadiiPolynomial.Certification.Rational

/-- Gcd-free fraction `num / den` (never normalized). -/
structure QF where
  num : ℤ
  den : ℕ
  den_pos : 0 < den

namespace QF

/-- Semantic value. -/
def toRat (a : QF) : ℚ := (a.num : ℚ) / (a.den : ℚ)
def zero : QF := ⟨0, 1, Nat.one_pos⟩
def one : QF := ⟨1, 1, Nat.one_pos⟩

/-- `a − b·c` for rationals `b c`, no gcd: `(a.n·b.d·c.d − b.n·c.n·a.d) / (a.d·b.d·c.d)`. -/
def subMul (a : QF) (b c : ℚ) : QF :=
  ⟨a.num * ((b.den * c.den : ℕ) : ℤ) - b.num * c.num * (a.den : ℤ), a.den * (b.den * c.den),
    Nat.mul_pos a.den_pos (Nat.mul_pos b.den_pos c.den_pos)⟩

/-- `⌈|a|·S⌉` (one `Nat` ceiling division). -/
def ceilAbs (S : ℕ) (a : QF) : ℕ := (a.num.natAbs * S + (a.den - 1)) / a.den

theorem den_ne (a : QF) : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'

@[simp] theorem toRat_zero : zero.toRat = 0 := by simp [toRat, zero]
@[simp] theorem toRat_one : one.toRat = 1 := by simp [toRat, one]

theorem toRat_subMul (a : QF) (b c : ℚ) : (subMul a b c).toRat = a.toRat - b * c := by
  have ha := a.den_ne
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have hc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  conv_rhs => rw [← Rat.num_div_den b, ← Rat.num_div_den c]
  simp only [toRat, subMul]
  push_cast
  field_simp

theorem natAbs_mul_le_ceilAbs (S : ℕ) (a : QF) : a.num.natAbs * S ≤ ceilAbs S a * a.den := by
  unfold ceilAbs
  have h := Nat.lt_div_mul_add (a := a.num.natAbs * S + (a.den - 1)) a.den_pos
  have hd := a.den_pos
  generalize a.num.natAbs * S = x at h ⊢
  generalize (x + (a.den - 1)) / a.den * a.den = y at h ⊢
  omega

/-- Upward rounding onto the grid `1/S`. -/
theorem abs_toRat_le (S : ℕ) (hS : 0 < S) (a : QF) :
    |a.toRat| ≤ ((ceilAbs S a : ℕ) : ℚ) / (S : ℚ) := by
  have hd : (0 : ℚ) < a.den := by exact_mod_cast a.den_pos
  have hS' : (0 : ℚ) < S := by exact_mod_cast hS
  have key : ((a.num.natAbs : ℕ) : ℚ) * S ≤ (ceilAbs S a : ℚ) * a.den := by
    exact_mod_cast natAbs_mul_le_ceilAbs S a
  rw [toRat, abs_div, abs_of_pos hd, div_le_div_iff₀ hd hS', ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]
  exact key

end QF

end RadiiPolynomial.Certification.Rational
