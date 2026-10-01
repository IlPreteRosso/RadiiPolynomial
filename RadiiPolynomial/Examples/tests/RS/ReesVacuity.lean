import RadiiPolynomial.Algebra.Rees.Laurent
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Int.Interval

/-!
# Rees family — vacuity and nonvacuity tests (L003 T50)

Small-index witnesses of the Rees-family API over `ℚ`, `ℂ` and `ℝ`: the S028a `ReesEuler` vacuity
theorems, the slice-20 `N = 1` identities, the slice-23 sanity instance and the S028a `ReesGamma`
vacuity theorems at `ν = 2` (no `PosReal`, no `Fact`), plus nonvacuity witnesses for the primary
faces of `smul_z_mem_JN_iff`, `PH_mem_JN`, `head_coeff_dvd_of_mem_JN`, `head_coeff_dvd_PH_mul_tail`
and `PH_z_mul_z_head`. Outside the default build; run explicitly.
-/

noncomputable section

namespace RadiiPolynomial.Tests.RS.Rees

open Polynomial LaurentPolynomial
open RadiiPolynomial.Rees.Laurent

/-! ### Euler vacuity (S028a `ReesEuler` :534–:598) -/

theorem vacuity_delta_z_two :
    deltaU ℚ (z 2) = (2 : ℚ[X]) • (z 2 : U ℚ) := deltaU_z 2

theorem vacuity_z_two_ne_zero : (z 2 : U ℚ) ≠ 0 := z_ne_zero 2

theorem vacuity_delta_nonzero : deltaU ℚ ≠ 0 := by
  intro h
  have hc := congrArg (fun d : Derivation ℚ[X] (U ℚ) (U ℚ) =>
    ((d (z 2) : U ℚ) : (ℚ[X])[T;T⁻¹]).coeff 2) h
  simp only [coeff_deltaU, coe_z_apply, ite_true, Derivation.zero_apply,
    Subalgebra.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have he := congrArg (fun p : ℚ[X] => p.coeff 2) hc
  norm_num at he

theorem vacuity_z_two_JN : (z 2 : U ℚ) ∈ JN 1 := z_mem_JN_of_tail (by decide)

theorem vacuity_delta_z_two_JN : deltaU ℚ (z 2) ∈ JN 1 := deltaU_mem_JN vacuity_z_two_JN

theorem vacuity_PH_zero : PH (Finset.Icc (-1) 1) (z 0 : U ℚ) = (z 0 : U ℚ) := by
  rw [PH_z, ite_eq_left (by decide)]

theorem vacuity_z_zero_ne_zero : (z 0 : U ℚ) ≠ 0 := z_ne_zero 0

theorem vacuity_PH_two : PH (Finset.Icc (-1) 1) (z 2 : U ℚ) = 0 := by
  rw [PH_z, ite_eq_right (by decide)]

theorem vacuity_qDelta_X : qDelta (X : ℚ[X]) = (deltaU ℚ).toLinearMap := by
  rw [qDelta, Polynomial.map_X, Polynomial.aeval_X]

theorem vacuity_qDelta_X_sq :
    qDelta ((X : ℚ[X]) ^ 2) (z 2 : U ℚ) = Polynomial.C (4 : ℚ) • (z 2 : U ℚ) := by
  rw [qDelta_z]
  norm_num

theorem vacuity_z_two_tail : (z 2 : U ℚ) ∈ tailMod 1 := by
  intro j hj
  rw [coe_z_apply, ite_eq_right (show j ≠ 2 by intro he; subst j; norm_num at hj)]

theorem vacuity_tail_preimage_mem :
    Polynomial.C (1 / 2 : ℚ) • (z 2 : U ℚ) ∈ tailMod 1 :=
  (tailMod 1).smul_mem _ vacuity_z_two_tail

theorem vacuity_tail_preimage :
    deltaU ℚ (Polynomial.C (1 / 2 : ℚ) • (z 2 : U ℚ)) = (z 2 : U ℚ) := by
  rw [deltaU_smul, deltaU_z, smul_smul, ← Polynomial.C_eq_intCast,
    ← Polynomial.C_mul]
  norm_num

theorem vacuity_kernel_mem : (X : ℚ[X]) ^ 4 • (1 : U ℚ) ∈ JN 1 :=
  X_pow_smul_one_mem_JN 1

theorem vacuity_kernel_ne_zero : (X : ℚ[X]) ^ 4 • (1 : U ℚ) ≠ 0 :=
  X_pow_smul_one_ne_zero 1

theorem vacuity_kernel_delta : deltaU ℚ ((X : ℚ[X]) ^ 4 • (1 : U ℚ)) = 0 :=
  deltaU_X_pow_smul_one 1

theorem vacuity_Fourier_pos :
    qDelta (Polynomial.C Complex.I * Polynomial.X) (z 1 : U ℂ) =
      Polynomial.C Complex.I • (z 1 : U ℂ) := by
  rw [qDelta_z]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Int.cast_one, mul_one]

theorem vacuity_Fourier_neg :
    qDelta (Polynomial.C Complex.I * Polynomial.X) (z (-1) : U ℂ) =
      -(Polynomial.C Complex.I • (z (-1) : U ℂ)) := by
  rw [qDelta_z]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Int.cast_neg, Int.cast_one, mul_neg, mul_one, Polynomial.C_neg]
  -- `simp only [neg_smul]` does not rewrite this goal in this default-instance test context (the
  -- source proof ran under the S028a local selection); close by term application.
  exact neg_smul (Polynomial.C Complex.I) (z (-1) : U ℂ)

/-! ### Family `N = 1` identities (slice 20, RF :453–:469) -/

section FamilyN1

variable {R : Type*} [CommRing R]

/-- `u² = z 2 + 2X² · 1 + z (-2)`. -/
theorem u_sq_eq : (u : U R) ^ 2 = z 2 + ((2 : R[X]) * X ^ 2) • (1 : U R) + z (-2) := by
  have h1 : (z 1 : U R) * z 1 = ((X : R[X]) ^ 0) • z 2 := z_mul_z_eq (by norm_num) (by norm_num)
  have h2 : (z 1 : U R) * z (-1) = ((X : R[X]) ^ 2) • z 0 := z_mul_z_eq (by norm_num) (by norm_num)
  have h3 : (z (-1) : U R) * z 1 = ((X : R[X]) ^ 2) • z 0 := z_mul_z_eq (by norm_num) (by norm_num)
  have h4 : (z (-1) : U R) * z (-1) = ((X : R[X]) ^ 0) • z (-2) :=
    z_mul_z_eq (by norm_num) (by norm_num)
  rw [u, sq, add_mul, mul_add, mul_add, h1, h2, h3, h4, pow_zero, one_smul, one_smul, z_zero,
    mul_smul, two_smul]
  abel

/-- `u² ∉ J_1` in characteristic zero. -/
theorem u_sq_not_mem_J1 [CharZero R] : (u : U R) ^ 2 ∉ JN 1 :=
  u_pow_even_not_mem 1

/-- `u³ ∈ J_1` over every commutative ring. -/
theorem u_cube_mem_J1 : (u : U R) ^ 3 ∈ JN 1 :=
  u_pow_odd_mem 1

end FamilyN1

/-! ### The sanity instance `N = 1` (slice 23, RB :854) -/

theorem sanity_N1 :
    aN 1 0 = 4 ∧ jstar 1 0 = 2 ∧ eps 0 2 = 4 ∧ eps 0 (-2) = 4
      ∧ eps 1 2 = 2 ∧ aN 1 1 = 2 ∧ eps (-1) 2 = 4 ∧ aN 1 (-1) = 2 ∧ eps (-1) 2 ≠ aN 1 (-1) := by
  decide

/-! ### Gamma vacuity at `ν = 2` (S028a `ReesGamma` :90–:145; `nuTwo` replaced by `(2 : ℝ)`) -/

theorem vacuity_gamma_two : gammaW 2 1 0 = 1 / 16 := by
  norm_num [gammaW]

theorem vacuity_weight_two_left :
    (2 : ℝ) ^ (0 : ℤ).natAbs /
      (gammaW 2 1 0 * (2 : ℝ) ^ (2 : ℤ).natAbs) = 4 := by
  rw [vacuity_gamma_two]
  norm_num

theorem vacuity_weight_two_right :
    (2 : ℝ) ^ ((0 : ℤ) - 2).natAbs * Polynomial.eval (1 / (2 : ℝ))
      ((Polynomial.X : Polynomial ℝ) ^ (eps 0 2 - aN 1 0)) = 4 := by
  rw [sanity_N1.1, sanity_N1.2.2.1]
  norm_num

theorem vacuity_weight_three_left :
    (2 : ℝ) ^ (0 : ℤ).natAbs /
      (gammaW 2 1 0 * (2 : ℝ) ^ (3 : ℤ).natAbs) = 2 := by
  rw [vacuity_gamma_two]
  norm_num

theorem vacuity_weight_three_right :
    (2 : ℝ) ^ ((0 : ℤ) - 3).natAbs * Polynomial.eval (1 / (2 : ℝ))
      ((Polynomial.X : Polynomial ℝ) ^ (eps 0 3 - aN 1 0)) = 2 := by
  rw [sanity_N1.1]
  norm_num [eps]

theorem vacuity_gamma_profile_positive :
    ∀ k ∈ Finset.Icc (-(1 : ℤ)) 1, 0 < gammaW 2 1 k :=
  fun k _ => gammaW_pos (by norm_num : (0 : ℝ) < 2) 1 k

theorem vacuity_gamma_profile_rees :
    ∀ k ∈ Finset.Icc (-(1 : ℤ)) 1,
      ((X : ℝ[X]) ^ aN 1 k).eval (1 / (2 : ℝ)) ≤ gammaW 2 1 k := by
  intro k hk
  have hk' : k.natAbs ≤ 1 := by rw [Finset.mem_Icc] at hk; omega
  rw [← gammaW_eq_eval_annihilator 2 (by norm_num : (0 : ℝ) < 2) hk']

theorem vacuity_half_profile_positive :
    ∀ k ∈ Finset.Icc (-(1 : ℤ)) 1, 0 < gammaW 2 1 k / 2 := by
  intro k _
  exact div_pos (gammaW_pos (by norm_num : (0 : ℝ) < 2) 1 k) (by norm_num)

theorem vacuity_half_profile_fails :
    ¬ ∀ k ∈ Finset.Icc (-(1 : ℤ)) 1,
      ((X : ℝ[X]) ^ aN 1 k).eval (1 / (2 : ℝ)) ≤ gammaW 2 1 k / 2 := by
  intro h
  have hc := h 0 (by decide)
  rw [← gammaW_eq_eval_annihilator 2 (by norm_num : (0 : ℝ) < 2) (by decide),
    vacuity_gamma_two] at hc
  norm_num at hc

/-! ### Nonvacuity witnesses for the primary faces (each hypothesis satisfied, conclusion term nonzero) -/

/-- `smul_z_mem_JN_iff` (primary, no head bound) at the tail index `j = 2`, `N = 1`, `p = 1`. -/
theorem nonvac_smul_z_mem_JN_iff : (1 : ℚ[X]) • (z 2 : U ℚ) ∈ JN 1 :=
  (smul_z_mem_JN_iff (N := 1) (j := 2) (1 : ℚ[X])).2 (by rw [show aN 1 2 = 0 by decide, pow_zero])

theorem nonvac_smul_z_ne_zero : (1 : ℚ[X]) • (z 2 : U ℚ) ≠ 0 := by
  rw [one_smul]
  exact z_ne_zero 2

/-- `PH_mem_JN` (primary, any head) at `H = {0}`, `f = X⁴ • 1 ∈ J₁`. -/
theorem nonvac_PH_mem_JN : PH {0} ((X : ℚ[X]) ^ 4 • (1 : U ℚ)) ∈ JN 1 :=
  PH_mem_JN {0} (X_pow_smul_one_mem_JN 1)

theorem nonvac_PH_mem_JN_ne_zero : PH {0} ((X : ℚ[X]) ^ 4 • (1 : U ℚ)) ≠ 0 := by
  rw [← z_zero, map_smul, PH_z, ite_eq_left (Finset.mem_singleton_self 0), z_zero]
  exact X_pow_smul_one_ne_zero 1

/-- `head_coeff_dvd_of_mem_JN` (primary, no head bound) at `f = X⁴ • 1 ∈ J₁`, `k = 0`. -/
theorem nonvac_head_coeff_dvd_of_mem_JN :
    (X : ℚ[X]) ^ (aN 1 0 + (0 : ℤ).natAbs) ∣ (((X : ℚ[X]) ^ 4 • (1 : U ℚ) : U ℚ) : (ℚ[X])[T;T⁻¹]).coeff 0 :=
  head_coeff_dvd_of_mem_JN (X_pow_smul_one_mem_JN 1) 0

theorem nonvac_head_coeff_ne_zero :
    (((X : ℚ[X]) ^ 4 • (1 : U ℚ) : U ℚ) : (ℚ[X])[T;T⁻¹]).coeff 0 ≠ 0 := by
  rw [coe_smul_one_apply, ite_eq_left rfl]
  exact pow_ne_zero _ Polynomial.X_ne_zero

/-- `head_coeff_dvd_PH_mul_tail` (primary, any head, `t ∈ J_N`, no head bound) at `H = {0}`,
`b = z (-2)`, `t = z 2 ∈ J₁`, `k = 0`. -/
theorem nonvac_head_coeff_dvd_PH_mul_tail :
    (X : ℚ[X]) ^ (aN 1 0 + (0 : ℤ).natAbs) ∣
      ((PH {0} ((z (-2) : U ℚ) * z 2) : U ℚ) : (ℚ[X])[T;T⁻¹]).coeff 0 :=
  head_coeff_dvd_PH_mul_tail {0} (z (-2)) vacuity_z_two_JN 0

theorem nonvac_PH_mul_tail_coeff_ne_zero :
    ((PH {0} ((z (-2) : U ℚ) * z 2) : U ℚ) : (ℚ[X])[T;T⁻¹]).coeff 0 ≠ 0 := by
  rw [coeff_PH, ite_eq_left (Finset.mem_singleton_self 0),
    z_mul_z_eq (e := 4) (k := 0) (by norm_num) (by norm_num), coe_smul_z_apply, ite_eq_left rfl]
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ Polynomial.X_ne_zero)

/-- `PH_z_mul_z_head` (primary, any head containing `k`) at `H = {0}`, `k = 0`, `j = 2`. -/
theorem nonvac_PH_z_mul_z_head :
    PH {0} ((z (0 - 2) : U ℚ) * z 2) = (X : ℚ[X]) ^ eps 0 2 • (z 0 : U ℚ) :=
  PH_z_mul_z_head (Finset.mem_singleton_self 0)

theorem nonvac_PH_z_mul_z_head_ne_zero : (X : ℚ[X]) ^ eps 0 2 • (z 0 : U ℚ) ≠ 0 := by
  rw [z_zero, show eps 0 2 = 2 * 1 + 2 by decide]
  exact X_pow_smul_one_ne_zero 1

end RadiiPolynomial.Tests.RS.Rees
