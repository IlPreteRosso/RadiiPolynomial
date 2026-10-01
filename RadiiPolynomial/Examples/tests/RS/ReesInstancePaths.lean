import RadiiPolynomial.Algebra.Rees.Laurent
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Rees family — instance-path consumer probes in a rich import context (L003 T53, CTX-RICH)

The installed half of the instance-path duty: each consumer probe is stated with terms elaborated in
THIS context (default instances, the S028a C2 closure: the Chebyshev algebra and the weighted-`ℓ¹`
universal property, ideal quotients, eigenspaces) and proved (i) by term application of the named
target and (ii) by rewriting (`rw` and `simp only`) with the named target.

* zero: Z1 `deltaU_one`, Z2 `deltaU_X_pow_smul_one`, Z3 `X_pow_smul_one_ne_zero`, Z4 `z_ne_zero`;
* cutoff: C1 `PH_z`, C4 `coeff_PH`; C2 `PH_comp_one_sub` and C3 `PH_qDelta_tail` in the
  selection-consumer section (`attribute [local instance] Rees.Laurent.instUAddCommGroup
  Rees.Laurent.instUZero`; under default instances these operator identities are not statable);
* diagonal: D1 `diagU_z`, D2 `qDelta_z`, D3 `deltaU_eq_diagU`, D4 the value law of `diagAlgHom`,
  D5a `PH_apply_sub_PH_apply`, D5b `PH_sub_apply`, D6 `PH_qDelta_tail_apply` (default instances);
* ideal maps (DERIVED): I1/I2 via `Ideal.Quotient.eq_zero_iff_mem`, I3 via `Ideal.map_id`,
  I4 via `deltaU_mem_JN`.

The zero-bearing targets (Z1–Z4, C1) are stored with the selected zero of `Euler`'s local instance
selection; `ipw_zero_*` record the `rfl` witnesses between the default and the selected zero.
Outside the default build; run explicitly.
-/

noncomputable section

namespace RadiiPolynomial.Tests.RS.Rees

open Polynomial LaurentPolynomial
open RadiiPolynomial.Rees.Laurent

section Default

variable {R : Type*} [CommRing R]

/-! ### Instance-path witnesses (default zero vs the T18 selection) -/

theorem ipw_zero_rfl : (0 : U R) = @Zero.zero (U R) ((instUAddCommGroup (R := R)).toZero) := rfl

theorem ipw_zero_reducible :
    (0 : U R) = @Zero.zero (U R) ((instUAddCommGroup (R := R)).toZero) := by
  with_reducible_and_instances rfl

theorem ipw_zero_existing : (0 : U R) = @Zero.zero (U R) (U R).toRing.toAddCommGroup.toZero := rfl

/-! ### Zero probes -/

theorem probe_Z1_app : deltaU R 1 = 0 := deltaU_one

theorem probe_Z1_rw : deltaU R 1 = 0 := by rw [deltaU_one]

theorem probe_Z1_simp : deltaU R 1 = 0 := by simp only [deltaU_one]

theorem probe_Z2_app (N : ℕ) : deltaU R ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 :=
  deltaU_X_pow_smul_one N

theorem probe_Z2_rw (N : ℕ) : deltaU R ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 := by
  rw [deltaU_X_pow_smul_one]

theorem probe_Z2_simp (N : ℕ) : deltaU R ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 := by
  simp only [deltaU_X_pow_smul_one]

theorem probe_Z3_app [Nontrivial R] (N : ℕ) : (X : R[X]) ^ (2 * N + 2) • (1 : U R) ≠ 0 :=
  X_pow_smul_one_ne_zero N

theorem probe_Z3_rw [Nontrivial R] (N : ℕ) : (X : R[X]) ^ (2 * N + 2) • (1 : U R) ≠ 0 := by
  rw [ne_eq, eq_false (X_pow_smul_one_ne_zero N)]; exact not_false

theorem probe_Z3_simp [Nontrivial R] (N : ℕ) : (X : R[X]) ^ (2 * N + 2) • (1 : U R) ≠ 0 := by
  simp only [ne_eq, X_pow_smul_one_ne_zero N, not_false_eq_true]

theorem probe_Z4_app [Nontrivial R] (j : ℤ) : (z j : U R) ≠ 0 := z_ne_zero j

theorem probe_Z4_rw [Nontrivial R] (j : ℤ) : (z j : U R) ≠ 0 := by
  rw [ne_eq, eq_false (z_ne_zero j)]; exact not_false

theorem probe_Z4_simp [Nontrivial R] (j : ℤ) : (z j : U R) ≠ 0 := by
  simp only [ne_eq, z_ne_zero j, not_false_eq_true]

/-! ### Cutoff probes (default instances) -/

theorem probe_C1_app (H : Finset ℤ) (j : ℤ) :
    PH H (z j : U R) = if j ∈ H then (z j : U R) else 0 := PH_z H j

theorem probe_C1_rw (H : Finset ℤ) (j : ℤ) :
    PH H (z j : U R) = if j ∈ H then (z j : U R) else 0 := by rw [PH_z]

theorem probe_C1_simp (H : Finset ℤ) (j : ℤ) :
    PH H (z j : U R) = if j ∈ H then (z j : U R) else 0 := by simp only [PH_z]

theorem probe_C4_app (H : Finset ℤ) (f : U R) (j : ℤ) :
    ((PH H f : U R) : R[X][T;T⁻¹]).coeff j = if j ∈ H then (f : R[X][T;T⁻¹]).coeff j else 0 :=
  coeff_PH H f j

theorem probe_C4_rw (H : Finset ℤ) (f : U R) (j : ℤ) :
    ((PH H f : U R) : R[X][T;T⁻¹]).coeff j = if j ∈ H then (f : R[X][T;T⁻¹]).coeff j else 0 := by
  rw [coeff_PH]

theorem probe_C4_simp (H : Finset ℤ) (f : U R) (j : ℤ) :
    ((PH H f : U R) : R[X][T;T⁻¹]).coeff j = if j ∈ H then (f : R[X][T;T⁻¹]).coeff j else 0 := by
  simp only [coeff_PH]

/-! ### Diagonal probes (default instances) -/

theorem probe_D1_app (lam : ℤ → R[X]) (j : ℤ) : diagU lam (z j : U R) = lam j • (z j : U R) :=
  diagU_z lam j

theorem probe_D1_rw (lam : ℤ → R[X]) (j : ℤ) : diagU lam (z j : U R) = lam j • (z j : U R) := by
  rw [diagU_z]

theorem probe_D1_simp (lam : ℤ → R[X]) (j : ℤ) : diagU lam (z j : U R) = lam j • (z j : U R) := by
  simp only [diagU_z]

theorem probe_D2_app (sym : Polynomial R) (j : ℤ) :
    qDelta sym (z j : U R) = Polynomial.C (sym.eval (j : R)) • (z j : U R) := qDelta_z sym j

theorem probe_D2_rw (sym : Polynomial R) (j : ℤ) :
    qDelta sym (z j : U R) = Polynomial.C (sym.eval (j : R)) • (z j : U R) := by rw [qDelta_z]

theorem probe_D2_simp (sym : Polynomial R) (j : ℤ) :
    qDelta sym (z j : U R) = Polynomial.C (sym.eval (j : R)) • (z j : U R) := by
  simp only [qDelta_z]

theorem probe_D3_app : (deltaU R).toLinearMap = diagU (fun k => (k : R[X])) := deltaU_eq_diagU

theorem probe_D3_rw : (deltaU R).toLinearMap = diagU (fun k => (k : R[X])) := by
  rw [deltaU_eq_diagU]

theorem probe_D3_simp : (deltaU R).toLinearMap = diagU (fun k => (k : R[X])) := by
  simp only [deltaU_eq_diagU]

/-- D4: the named target is the DEF `diagAlgHom` (value law by `rfl`, T28). -/
theorem probe_D4_app (lam : ℤ → R[X]) : diagAlgHom (R := R) lam = diagU lam := rfl

theorem probe_D4_rw (lam : ℤ → R[X]) : diagAlgHom (R := R) lam = diagU lam := by
  rw [diagAlgHom]; rfl

theorem probe_D4_simp (lam : ℤ → R[X]) : diagAlgHom (R := R) lam = diagU lam := by
  simp only [diagAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

theorem probe_D5a_app (H : Finset ℤ) (f : U R) : PH (R := R) H (f - PH (R := R) H f) = 0 :=
  PH_apply_sub_PH_apply H f

theorem probe_D5a_rw (H : Finset ℤ) (f : U R) : PH (R := R) H (f - PH (R := R) H f) = 0 := by
  rw [PH_apply_sub_PH_apply]

theorem probe_D5a_simp (H : Finset ℤ) (f : U R) : PH (R := R) H (f - PH (R := R) H f) = 0 := by
  simp only [PH_apply_sub_PH_apply]

theorem probe_D5b_app (H : Finset ℤ) (f : U R) :
    PH (R := R) H f - PH (R := R) H (PH (R := R) H f) = 0 := PH_sub_apply H f

theorem probe_D5b_rw (H : Finset ℤ) (f : U R) :
    PH (R := R) H f - PH (R := R) H (PH (R := R) H f) = 0 := by rw [PH_sub_apply]

theorem probe_D5b_simp (H : Finset ℤ) (f : U R) :
    PH (R := R) H f - PH (R := R) H (PH (R := R) H f) = 0 := by simp only [PH_sub_apply]

theorem probe_D6_app (H : Finset ℤ) (sym : Polynomial R) (f : U R) :
    PH (R := R) H (qDelta sym (f - PH (R := R) H f)) = 0 := PH_qDelta_tail_apply H sym f

theorem probe_D6_rw (H : Finset ℤ) (sym : Polynomial R) (f : U R) :
    PH (R := R) H (qDelta sym (f - PH (R := R) H f)) = 0 := by rw [PH_qDelta_tail_apply]

theorem probe_D6_simp (H : Finset ℤ) (sym : Polynomial R) (f : U R) :
    PH (R := R) H (qDelta sym (f - PH (R := R) H f)) = 0 := by simp only [PH_qDelta_tail_apply]

/-! ### Ideal-map probes (DERIVED, named bridges) -/

theorem probe_I1_app (N : ℕ) : Ideal.Quotient.mk (JN N) (z ((N : ℤ) + 1) : U R) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (z_mem_JN_pos N)

theorem probe_I1_rw (N : ℕ) : Ideal.Quotient.mk (JN N) (z ((N : ℤ) + 1) : U R) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]; exact z_mem_JN_pos N

theorem probe_I2_app (N : ℕ) : Ideal.Quotient.mk (JN N) ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (X_pow_smul_one_mem_JN N)

theorem probe_I2_rw (N : ℕ) : Ideal.Quotient.mk (JN N) ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]; exact X_pow_smul_one_mem_JN N

theorem probe_I3_app (N : ℕ) : (JN (R := R) N).map (RingHom.id (U R)) = JN N := Ideal.map_id _

theorem probe_I3_rw (N : ℕ) : (JN (R := R) N).map (RingHom.id (U R)) = JN N := by
  rw [Ideal.map_id]

/-- I3 membership consequence. -/
theorem probe_I3_mem (N : ℕ) : (z ((N : ℤ) + 1) : U R) ∈ (JN (R := R) N).map (RingHom.id (U R)) := by
  rw [Ideal.map_id]; exact z_mem_JN_pos N

theorem probe_I4_app (N : ℕ) (f : U R) :
    Ideal.Quotient.mk (JN N) f = 0 → Ideal.Quotient.mk (JN N) (deltaU R f) = 0 :=
  fun h => Ideal.Quotient.eq_zero_iff_mem.mpr (deltaU_mem_JN (Ideal.Quotient.eq_zero_iff_mem.mp h))

theorem probe_I4_rw (N : ℕ) (f : U R) :
    Ideal.Quotient.mk (JN N) f = 0 → Ideal.Quotient.mk (JN N) (deltaU R f) = 0 := by
  intro h; rw [Ideal.Quotient.eq_zero_iff_mem] at h ⊢; exact deltaU_mem_JN h

end Default

/-! ### Selection-consumer context (CTX-SEL): the operator-level probes C2/C3 -/

section Selection

variable {R : Type*} [CommRing R]

attribute [local instance] Rees.Laurent.instUAddCommGroup Rees.Laurent.instUZero

theorem probe_C2_app (H : Finset ℤ) :
    (PH (R := R) H : U R →ₗ[R[X]] U R) ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) = 0 :=
  PH_comp_one_sub H

theorem probe_C2_rw (H : Finset ℤ) :
    (PH (R := R) H : U R →ₗ[R[X]] U R) ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) = 0 := by
  rw [PH_comp_one_sub]

theorem probe_C2_simp (H : Finset ℤ) :
    (PH (R := R) H : U R →ₗ[R[X]] U R) ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) = 0 := by
  simp only [PH_comp_one_sub]

theorem probe_C3_app (H : Finset ℤ) (sym : Polynomial R) :
    PH H ∘ₗ qDelta sym ∘ₗ (1 - PH H) = 0 :=
  PH_qDelta_tail H sym

theorem probe_C3_rw (H : Finset ℤ) (sym : Polynomial R) :
    PH H ∘ₗ qDelta sym ∘ₗ (1 - PH H) = 0 := by
  rw [PH_qDelta_tail]

theorem probe_C3_simp (H : Finset ℤ) (sym : Polynomial R) :
    PH H ∘ₗ qDelta sym ∘ₗ (1 - PH H) = 0 := by
  simp only [PH_qDelta_tail]

end Selection

end RadiiPolynomial.Tests.RS.Rees
