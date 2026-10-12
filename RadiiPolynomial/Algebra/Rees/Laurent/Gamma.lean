import RadiiPolynomial.Algebra.Rees.Laurent.Family
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The exponent and gamma layer of the Rees family

One cancellation length `eps k j = |k - j| + |j| - |k|` with `z (k - j) * z j = X ^ eps k j • z k`
(`z_sub_mul_z`), its arithmetic on head × tail (`|k| ≤ N < |j|`) against the ONE annihilator exponent
`aN` of `Family` (`aN_le_eps`, `eps_sub_aN`, attainment at `jstar N k = sgn' k * (N + 1)`), and the
ONE gamma `gammaW ν N k = ν ^ (2|k|) / ν ^ (2(N + 1))` over real `ν` (with the inverse bound
`gammaW_inv_le`: `γ_N(k)⁻¹ ≤ ν ^ (2(N + 1))` for real `ν ≥ 1`), with the carrier-free identities
`gammaW_eq_eval_annihilator` (`Γ = eval_{1/ν} (X ^ aN N k)`), `weight_eq` / `weight_eq_rees` (the
column-weight identity) and `eval_eps_div_eval_aN`; the Fourier unit
`Analysis/SequenceSpace/Fourier/GammaLeakage.lean` consumes `gammaW_eq_eval_annihilator` and
`weight_eq_rees`.

Nothing analytic lands here: no norm, no `ℓ¹` carrier, no `Fact`. Of the library modules, this
module imports `Family` only.
-/

noncomputable section

namespace RadiiPolynomial.Rees.Laurent

open Polynomial LaurentPolynomial

section Exponents

/-- The cancellation length of `z_{k−j} z_j = X^{ε} z_k` in the based Rees family:
`ε(k, j) = |k − j| + |j| − |k|`. -/
def eps (k j : ℤ) : ℕ := (k - j).natAbs + j.natAbs - k.natAbs

/-- The ℕ-subtraction in `eps` is exact (`|k| ≤ |k − j| + |j|`). -/
theorem eps_spec (k j : ℤ) :
    (eps k j : ℤ) = (k - j).natAbs + j.natAbs - k.natAbs := by
  unfold eps; omega

/-- The sign `sgn' k ∈ {−1, 1}` (`sgn' 0 = 1`). -/
def sgn' (k : ℤ) : ℤ := if k < 0 then -1 else 1

/-- The attaining tail index `j* = sgn'(k) (N + 1)`. -/
def jstar (N : ℕ) (k : ℤ) : ℤ := sgn' k * ((N : ℤ) + 1)

/-- On head × tail, the annihilator exponent is at most the cancellation length. -/
theorem aN_le_eps {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    aN N k ≤ eps k j := by
  unfold aN eps; omega

/-- The closed form `ε − a_N = 2(|j| − N − 1 + max(−sgn'(j) k, 0))`. -/
theorem eps_sub_aN {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    (eps k j : ℤ) - aN N k = 2 * ((j.natAbs : ℤ) - N - 1 + max (-(sgn' j) * k) 0) := by
  rw [eps_spec]
  unfold aN sgn'
  split_ifs with hs
  · rw [max_def]; split_ifs <;> omega
  · rw [max_def]; split_ifs <;> omega

/-- The minimum is attained at `j* = sgn'(k)(N + 1)`. -/
theorem eps_jstar {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) : eps k (jstar N k) = aN N k := by
  unfold eps aN jstar sgn'
  split_ifs <;> omega

/-- `j*` lies in the tail. -/
theorem jstar_tail (N : ℕ) (k : ℤ) : N < (jstar N k).natAbs := by
  unfold jstar sgn'
  split_ifs <;> omega

/-- `a_N(k) = min_{|j| > N} ε(k, j)`, stated as the pair lower bound + attainment. -/
theorem aN_eq_min {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) :
    (∀ j : ℤ, N < j.natAbs → aN N k ≤ eps k j)
      ∧ (N < (jstar N k).natAbs ∧ eps k (jstar N k) = aN N k) :=
  ⟨fun _ hj => aN_le_eps hk hj, jstar_tail N k, eps_jstar hk⟩

end Exponents

section Gamma

/-- The one gamma `Γ_{N,k}(ν) = ν^{2|k|} / ν^{2(N+1)}`. -/
def gammaW (ν : ℝ) (N : ℕ) (k : ℤ) : ℝ := ν ^ (2 * k.natAbs) / ν ^ (2 * (N + 1))

theorem gammaW_pos {ν : ℝ} (hν : 0 < ν) (N : ℕ) (k : ℤ) : 0 < gammaW ν N k :=
  div_pos (pow_pos hν _) (pow_pos hν _)

/-- The inverse gamma is at most `ν ^ (2(N + 1))` for real `ν ≥ 1`. -/
theorem gammaW_inv_le {ν : ℝ} (hν : 1 ≤ ν) (N : ℕ) (k : ℤ) :
    (gammaW ν N k)⁻¹ ≤ ν ^ (2 * (N + 1)) := by
  rw [gammaW, inv_div]
  exact div_le_self (pow_nonneg (zero_le_one.trans hν) _) (one_le_pow₀ hν)

/-- For a head index `|k| ≤ N` and `0 < ν`, `Γ_k` is the annihilator monomial of `z_k`
evaluated at `h = 1/ν`. -/
theorem gammaW_eq_eval_annihilator (ν : ℝ) (hν : 0 < ν) {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) :
    gammaW ν N k = Polynomial.eval (1 / ν) ((Polynomial.X : Polynomial ℝ) ^ aN N k) := by
  rw [eval_pow, eval_X, gammaW, aN,
    show 2 * (N + 1) = 2 * k.natAbs + 2 * (N + 1 - k.natAbs) by omega, pow_add, div_pow, one_pow]
  have : ν ^ (2 * k.natAbs) ≠ 0 := pow_ne_zero _ hν.ne'
  field_simp

/-- The Γ-rescaled column weight is a Rees exponent:
`ν^{|k|} / (γ_N(k) ν^{|j|}) = ν^{|k−j|} (ν⁻¹)^{ε(k,j) − a_N(k)}` on head × tail. -/
theorem weight_eq {ν : ℝ} (hν : 0 < ν) {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    ν ^ k.natAbs / (gammaW ν N k * ν ^ j.natAbs) = ν ^ (k - j).natAbs * (ν⁻¹) ^ (eps k j - aN N k) := by
  have hle := aN_le_eps hk hj
  have hexp : (eps k j - aN N k) + (k.natAbs + 2 * (N + 1))
      = (k - j).natAbs + (2 * k.natAbs + j.natAbs) := by
    unfold eps aN at hle ⊢; omega
  have key : ν ^ (eps k j - aN N k) * ν ^ (k.natAbs + 2 * (N + 1))
      = ν ^ (k - j).natAbs * ν ^ (2 * k.natAbs + j.natAbs) := by
    rw [← pow_add, hexp, pow_add]
  rw [gammaW, inv_pow, div_eq_iff (by positivity)]
  field_simp
  rw [pow_add, pow_add] at key
  linear_combination key

/-- The analytic weight identity exposes the surviving Rees quotient exponent. -/
theorem weight_eq_rees (ν : ℝ) (hν : 0 < ν) {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    ν ^ k.natAbs / (gammaW ν N k * ν ^ j.natAbs) = ν ^ (k - j).natAbs * Polynomial.eval (1 / ν) ((Polynomial.X : Polynomial ℝ) ^ (eps k j - aN N k)) := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, one_div] using weight_eq hν hk hj

end Gamma

section Atoms

variable {R : Type*} [CommRing R]

theorem z_sub_mul_z (k j : ℤ) :
    (z (k - j) : U R) * z j = (X : R[X]) ^ eps k j • (z k : U R) := by
  apply z_mul_z_eq (sub_add_cancel k j)
  have h := eps_spec k j
  omega

theorem X_pow_eps_split {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    (X : R[X]) ^ eps k j =
      (X : R[X]) ^ aN N k * (X : R[X]) ^ (eps k j - aN N k) := by
  rw [← pow_add, Nat.add_sub_of_le (aN_le_eps hk hj)]

theorem X_pow_eps_smul_z_mem_JN {N : ℕ} {k j : ℤ}
    (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    (X : R[X]) ^ eps k j • (z k : U R) ∈ JN N := by
  apply (smul_z_mem_JN_iff _).mpr
  exact ⟨(X : R[X]) ^ (eps k j - aN N k), X_pow_eps_split hk hj⟩

theorem z_mul_z_jstar {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) :
    (z (k - jstar N k) : U R) * z (jstar N k) =
      (X : R[X]) ^ aN N k • (z k : U R) := by
  rw [z_sub_mul_z, eps_jstar hk]

end Atoms

/-- The ratio of the evaluated cancellation and annihilator monomials. -/
theorem eval_eps_div_eval_aN (ν : ℝ) (hν : 0 < ν) {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    Polynomial.eval (1 / ν) ((Polynomial.X : Polynomial ℝ) ^ eps k j) / Polynomial.eval (1 / ν) ((Polynomial.X : Polynomial ℝ) ^ aN N k) = Polynomial.eval (1 / ν) ((Polynomial.X : Polynomial ℝ) ^ (eps k j - aN N k)) := by
  rw [X_pow_eps_split (R := ℝ) hk hj, Polynomial.eval_mul, mul_div_cancel_left₀]
  rw [Polynomial.eval_pow, Polynomial.eval_X]
  have hv : (1 / ν) ≠ 0 := one_div_ne_zero hν.ne'
  exact pow_ne_zero _ hv

end RadiiPolynomial.Rees.Laurent
