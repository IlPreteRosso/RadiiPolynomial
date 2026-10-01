import RadiiPolynomial.Algebra.Rees.Laurent
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval

/-!
# Rees family — countermodels of the decision-bearing hypotheses (L003 T51)

For each decision-bearing hypothesis named in TARGET_SHEET §7 a compiled countermodel: the
conclusion fails at the displayed instance once the hypothesis is dropped. Typeclass boundaries
(`[Nontrivial R]`, `[CharZero R]`, `[Algebra ℚ R]`) are refuted at `PUnit`, `ZMod 2` and `ℤ`.
The section `Redundancy` proves three of the hypotheses that §7 expects to be REDUNDANT (kept in the
interfaces for consumer stability). Outside the default build; run explicitly.
-/

noncomputable section

namespace RadiiPolynomial.Tests.RS.Rees

open Polynomial LaurentPolynomial
open RadiiPolynomial.Rees.Laurent

/-! ### The trivial ring: every element of `U PUnit` is equal -/

theorem U_PUnit_eq (f g : U PUnit) : f = g :=
  U_ext (fun _ => Subsingleton.elim _ _)

/-! ### Family -/

/-- `z_mem_JN_of_tail`, hypothesis `N < |j|`: `z 0 = 1 ∉ J₁` over `ℚ`. -/
theorem cm_z_mem_JN_of_tail_h : (z 0 : U ℚ) ∉ JN 1 := by
  intro h
  have h0 := (mem_JN_iff 1 _).1 h 0
  rw [coe_z_apply, ite_eq_left rfl, Int.natAbs_zero, pow_zero,
    show max 0 (2 * 1 + 2 - 0) = 4 by decide] at h0
  have := (Polynomial.X_pow_dvd_iff.1 h0) 0 (by decide)
  rw [Polynomial.coeff_one_zero] at this
  exact one_ne_zero this

/-- `contraction_fails`, `[Nontrivial R]`: over `PUnit` the contraction exists (`g = 0`). -/
theorem cm_contraction_PUnit (N : ℕ) :
    ∃ g : U PUnit, (∀ j < 0, (g : (PUnit[X])[T;T⁻¹]).coeff j = 0) ∧
      g * z ((N : ℤ) + 1) = ((X : PUnit[X]) ^ (2 * N + 2)) • (1 : U PUnit) :=
  ⟨0, fun _ _ => Subsingleton.elim _ _, U_PUnit_eq _ _⟩

/-- `tail_span_not_ideal`, `[Nontrivial R]`: over `PUnit` every coefficient vanishes. -/
theorem cm_tail_span_PUnit (N : ℕ) (f g : U PUnit) :
    ∀ j : ℤ, j.natAbs ≤ N → ((f * g : U PUnit) : (PUnit[X])[T;T⁻¹]).coeff j = 0 :=
  fun _ _ => Subsingleton.elim _ _

/-- `q_mul_q_sub`, hypothesis `1 ≤ m`: at `m = 0`, `N = 0` over `ℚ` the identity fails
(`2X² · 1` against `X² · 1`). -/
theorem cm_q_mul_q_sub_hm :
    ¬ ((q (0 + 1) : U ℚ) * q (0 + 1 - 0) - q (2 * 0 + 2 - 0) =
      ((X : ℚ[X]) ^ (2 * (0 + 1 - 0))) • q 0) := by
  intro h
  have h2 := q_sq_sub (R := ℚ) 0
  rw [sq] at h2
  rw [h2, q_zero] at h
  have hc := congrArg (fun f : U ℚ => (f : (ℚ[X])[T;T⁻¹]).coeff 0) h
  simp only [coe_smul_one_apply, ite_true] at hc
  have hX : (X : ℚ[X]) ^ 2 ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  apply hX
  linear_combination hc

/-- `q_mul_q_sub`, hypothesis `m ≤ N`: at `m = N + 1 = 1` over `ℚ` the left side is `0`, the right
side `q 1 ≠ 0`. -/
theorem cm_q_mul_q_sub_hmN :
    ¬ ((q (0 + 1) : U ℚ) * q (0 + 1 - 1) - q (2 * 0 + 2 - 1) =
      ((X : ℚ[X]) ^ (2 * (0 + 1 - 1))) • q 1) := by
  intro h
  -- `sub_self _` with an unannotated argument does not unify here (the goal's subtraction is
  -- `AddSubgroupClass.sub`); use `sub_self` on the ambient Laurent algebra through `Subtype.ext`.
  rw [show 0 + 1 - 1 = 0 from rfl, q_zero, mul_one, show 2 * 0 + 2 - 1 = 0 + 1 from rfl,
    show (q (0 + 1) : U ℚ) - q (0 + 1) = 0 from
      Subtype.ext (sub_self ((q (0 + 1) : U ℚ) : (ℚ[X])[T;T⁻¹])),
    show 2 * (0 + 1 - 1) = 0 from rfl, pow_zero, one_smul] at h
  have hc := congrArg (fun f : U ℚ => (f : (ℚ[X])[T;T⁻¹]).coeff 1) h
  simp only [q_of_ne_zero (show (1 : ℕ) ≠ 0 by decide), Subalgebra.coe_add,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coe_z_apply, Subalgebra.coe_zero,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact Polynomial.X_ne_zero (R := ℚ) (by simpa using hc.symm)

/-- `u_pow_even_not_mem`, `[CharZero R]`: over `ZMod 2`, `u² ∈ J₁` (`u² = z 2 + z (-2)`). -/
theorem cm_u_sq_mem_J1_ZMod2 : (u : U (ZMod 2)) ^ (2 * 1) ∈ JN 1 := by
  rw [mem_JN_iff]
  intro j
  rw [u_pow_coeff]
  split_ifs with hc
  · simp only [Int.ModEq] at hc
    rcases (show j = -2 ∨ j = 0 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (pow_dvd_pow _ (by decide)).trans (dvd_mul_left _ _)
    · have h2 : ((Nat.choose (2 * 1) ((((2 * 1 : ℕ) : ℤ) + 0).toNat / 2) : ℕ) : (ZMod 2)[X]) = 0 := by
        rw [← Polynomial.C_eq_natCast, show (((Nat.choose (2 * 1) ((((2 * 1 : ℕ) : ℤ) + 0).toNat / 2)) : ℕ) :
          ZMod 2) = 0 by decide, map_zero]
      rw [h2, zero_mul]
      exact dvd_zero _
    · exact (pow_dvd_pow _ (by decide)).trans (dvd_mul_left _ _)
  · exact dvd_zero _

/-! ### Euler -/

/-- `[Nontrivial R]` in `X_pow_smul_one_ne_zero`: over `PUnit` the element is `0`. -/
theorem cm_X_pow_smul_one_PUnit (N : ℕ) : (X : PUnit[X]) ^ (2 * N + 2) • (1 : U PUnit) = 0 :=
  U_PUnit_eq _ _

/-- `[Nontrivial R]` in `X_pow_smul_one_not_mem_tailMod`: over `PUnit` it lies in the tail module. -/
theorem cm_X_pow_smul_one_mem_tailMod_PUnit (N : ℕ) :
    (X : PUnit[X]) ^ (2 * N + 2) • (1 : U PUnit) ∈ tailMod N := by
  rw [cm_X_pow_smul_one_PUnit]
  exact (tailMod N).zero_mem

/-- `[Nontrivial R]` in `deltaU_not_injOn_JN`: over `PUnit`, `deltaU` is injective on `J_N`. -/
theorem cm_deltaU_injOn_PUnit (N : ℕ) : Set.InjOn (deltaU PUnit) (JN (R := PUnit) N : Set (U PUnit)) :=
  fun f _ g _ _ => U_PUnit_eq f g

/-- `[Nontrivial R]` in `no_inv_X_pow`: over `PUnit`, `X • 1 = 1`. -/
theorem cm_no_inv_X_pow_PUnit : ∃ f : U PUnit, (X : PUnit[X]) ^ 1 • f = 1 :=
  ⟨1, U_PUnit_eq _ _⟩

/-- `no_inv_X_pow`, hypothesis `1 ≤ a`: at `a = 0`, `X⁰ • 1 = 1`. -/
theorem cm_no_inv_X_pow_ha : ∃ f : U ℚ, (X : ℚ[X]) ^ 0 • f = 1 :=
  ⟨1, by rw [pow_zero, one_smul]⟩

/-- `[Nontrivial R]` in `z_ne_zero`: over `PUnit`, `z 0 = 0`. -/
theorem cm_z_eq_zero_PUnit : (z 0 : U PUnit) = 0 := U_PUnit_eq _ _

/-- `qDelta_bijOn_tail`, hypothesis `hunit`: over `ℤ` with `sym = X`, `N = 1`, `qDelta X` is not
bijective on the coordinate tail (`2` is not a unit of `ℤ`). -/
theorem cm_qDelta_X_not_bijOn_int :
    ¬ Set.BijOn (qDelta (X : ℤ[X])) (tailMod (R := ℤ) 1 : Set (U ℤ)) (tailMod (R := ℤ) 1 : Set (U ℤ)) := by
  rw [qDelta_bijOn_tail_iff]
  intro h
  have h2 := h 2 (by decide)
  rw [Polynomial.eval_X, Int.cast_ofNat, Int.isUnit_iff] at h2
  omega

/-- `deltaU_bijOn_tail`, `[Algebra ℚ R]`: over `ℤ`, `N = 1`, `deltaU` is not bijective on the tail. -/
theorem cm_deltaU_not_bijOn_int :
    ¬ Set.BijOn (deltaU ℤ) (tailMod (R := ℤ) 1 : Set (U ℤ)) (tailMod (R := ℤ) 1 : Set (U ℤ)) := by
  intro h
  apply cm_qDelta_X_not_bijOn_int
  simpa only [qDelta, Polynomial.map_X, Polynomial.aeval_X, Derivation.coeFn_coe] using h

/-! ### Gamma -/

/-- `aN_le_eps`, hypothesis `N < |j|`: `N = 0`, `k = j = 0`. -/
theorem cm_aN_le_eps_hj : ¬ aN 0 0 ≤ eps 0 0 := by decide

/-- `eps_sub_aN`, hypothesis `N < |j|`: `N = 1`, `k = 1`, `j = 0`. -/
theorem cm_eps_sub_aN_hj :
    ¬ ((eps 1 0 : ℤ) - aN 1 1 = 2 * (((0 : ℤ).natAbs : ℤ) - 1 - 1 + max (-(sgn' 0) * 1) 0)) := by
  decide

/-- `eps_sub_aN`, hypothesis `|k| ≤ N`: `N = 0`, `k = -2`, `j = 1`. -/
theorem cm_eps_sub_aN_hk :
    ¬ ((eps (-2) 1 : ℤ) - aN 0 (-2) = 2 * (((1 : ℤ).natAbs : ℤ) - 0 - 1 + max (-(sgn' 1) * (-2)) 0)) := by
  decide

/-- `gammaW_eq_eval_annihilator`, hypothesis `|k| ≤ N`: `ν = 2`, `N = 0`, `k = 2`. -/
theorem cm_gammaW_eq_eval_hk :
    gammaW 2 0 2 ≠ Polynomial.eval (1 / (2 : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ aN 0 2) := by
  rw [show aN 0 2 = 0 by decide]
  norm_num [gammaW]

/-- `weight_eq`, hypothesis `N < |j|`: `ν = 2`, `N = 0`, `k = j = 0`. -/
theorem cm_weight_eq_hj :
    (2 : ℝ) ^ (0 : ℤ).natAbs / (gammaW 2 0 0 * (2 : ℝ) ^ (0 : ℤ).natAbs) ≠
      (2 : ℝ) ^ ((0 : ℤ) - 0).natAbs * ((2 : ℝ)⁻¹) ^ (eps 0 0 - aN 0 0) := by
  rw [show eps 0 0 - aN 0 0 = 0 by decide]
  norm_num [gammaW]

/-- `weight_eq`, hypothesis `|k| ≤ N`: `ν = 2`, `N = 0`, `k = 2`, `j = 1`. -/
theorem cm_weight_eq_hk :
    (2 : ℝ) ^ (2 : ℤ).natAbs / (gammaW 2 0 2 * (2 : ℝ) ^ (1 : ℤ).natAbs) ≠
      (2 : ℝ) ^ ((2 : ℤ) - 1).natAbs * ((2 : ℝ)⁻¹) ^ (eps 2 1 - aN 0 2) := by
  rw [show eps 2 1 - aN 0 2 = 0 by decide]
  norm_num [gammaW]

/-- `eval_eps_div_eval_aN`, hypothesis `0 < ν` (DECISIVE): `ν = 0`, `N = 0`, `k = 0`, `j = 1`. -/
theorem cm_eval_eps_div_eval_aN_hν :
    Polynomial.eval (1 / (0 : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ eps 0 1) /
        Polynomial.eval (1 / (0 : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ aN 0 0) ≠
      Polynomial.eval (1 / (0 : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ (eps 0 1 - aN 0 0)) := by
  rw [show eps 0 1 = 2 by decide, show aN 0 0 = 2 by decide]
  norm_num

/-- `X_pow_eps_smul_z_mem_JN`, hypothesis `N < |j|`: over `ℚ`, `N = 0`, `k = j = 0`: `z 0 ∉ J₀`. -/
theorem cm_X_pow_eps_smul_z_mem_JN_hj : (X : ℚ[X]) ^ eps 0 0 • (z 0 : U ℚ) ∉ JN 0 := by
  rw [show eps 0 0 = 0 by decide, pow_zero, one_smul]
  intro h
  have h0 := (mem_JN_iff 0 _).1 h 0
  rw [coe_z_apply, ite_eq_left rfl, Int.natAbs_zero, pow_zero,
    show max 0 (2 * 0 + 2 - 0) = 2 by decide] at h0
  have := (Polynomial.X_pow_dvd_iff.1 h0) 0 (by decide)
  rw [Polynomial.coeff_one_zero] at this
  exact one_ne_zero this

/-- `PH_z_mul_z_head`, hypothesis `k ∈ H`: over `ℚ`, `H = ∅`, `k = j = 1`. -/
theorem cm_PH_z_mul_z_head_hk :
    PH (∅ : Finset ℤ) ((z (1 - 1) : U ℚ) * z 1) ≠ (X : ℚ[X]) ^ eps 1 1 • (z 1 : U ℚ) := by
  rw [z_sub_mul_z, map_smul, PH_z, ite_eq_right (Finset.notMem_empty 1), smul_zero,
    show eps 1 1 = 0 by decide, pow_zero, one_smul]
  exact fun h => z_ne_zero 1 (Eq.symm h)

/-! ### Redundancy (hypotheses expected REDUNDANT in §7; interfaces keep them) -/

/-- `aN_le_eps` holds without `|k| ≤ N`. -/
theorem red_aN_le_eps_hk {N : ℕ} {k j : ℤ} (hj : N < j.natAbs) : aN N k ≤ eps k j := by
  unfold aN eps; omega

/-- `eps_jstar` holds without `|k| ≤ N`. -/
theorem red_eps_jstar (N : ℕ) (k : ℤ) : eps k (jstar N k) = aN N k := by
  unfold eps aN jstar sgn'
  split_ifs <;> omega

/-- `z_mul_z_jstar` holds without `|k| ≤ N` (via `red_eps_jstar`). -/
theorem red_z_mul_z_jstar {R : Type*} [CommRing R] (N : ℕ) (k : ℤ) :
    (z (k - jstar N k) : U R) * z (jstar N k) = (X : R[X]) ^ aN N k • (z k : U R) := by
  rw [z_sub_mul_z, red_eps_jstar]

end RadiiPolynomial.Tests.RS.Rees
