import RadiiPolynomial.Algebra.Rees.Laurent
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Scalar

/-!
# Rees family — old-shape witnesses (L003 T52)

Each theorem `old_<name>` states the proposition of a superseded scratch declaration (S028a freeze
`ReesEuler`/`ReesGamma`, slice-20 `ReesFamily`, slice-23 `ReesBridge`) and proves it by application
of the promoted API. No frozen scratch constant is imported or revalidated; the symbols are mapped:

* `ReesBridge.gammaW ν ↦ gammaW (ν : ℝ)` (for `ν : PosReal`), `GammaNote N ν k ↦ gammaW ν N k`
  (literal `ν ^ (2 * k.natAbs) / ν ^ (2 * (N + 1))`);
* `ReesBridge.aN ↦ aN`, `FiltrationProbe.aN ↦ aN`, `ReesBridge.eps ↦ eps`, `ReesBridge.sgn' ↦ sgn'`,
  `ReesBridge.jstar ↦ jstar`; `ReesBridge.winZ N ↦ Finset.Icc (-(N : ℤ)) N`;
* the old `R[X]`-specialized `coeff_single_eq`, `dvd_coeff_mul` (at `x := X`), `diagL`, `deltaL R`
  `↦` the generalized declarations at `S := R[X]` (`deltaL R ↦ deltaL R[X]`).

Contents: (a) the S028b-consumed interface shapes T4f/T4g (and `eval_eps_div_eval_aN`) at
`(ν : PosReal)`; (b) `GammaNote`/`gamma_eq_eval`; (c) `aN_agree`, `gammaW_eq_GammaNote` (`rfl`);
(d) `smul_z_mem_JN_iff_reesAN`; (e) the cross-context `rfl` witness of the T18 selection in this
default-instance context; (f) the FALLBACK shapes of `smul_z_mem_JN_iff`, `PH_mem_JN`,
`head_coeff_dvd_of_mem_JN`, `head_coeff_dvd_PH_mul_tail`, `PH_z_mul_z_head`; (g) the old
specializations of the generic Laurent lemmas; (h) the slice-23 exponent definitions (`rfl`).
Outside the default build; run explicitly.
-/

noncomputable section

namespace RadiiPolynomial.Tests.RS.Rees

open Polynomial LaurentPolynomial
open RadiiPolynomial.Rees.Laurent

/-! ### (a) S028b-consumed interface shapes at `ν : PosReal` -/

/-- T4f (S028a `ReesGamma.gammaW_eq_eval_annihilator`, GA:39). -/
theorem old_gammaW_eq_eval_annihilator (ν : PosReal) {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) :
    gammaW (ν : ℝ) N k =
      Polynomial.eval (1 / (ν : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ aN N k) :=
  gammaW_eq_eval_annihilator (ν : ℝ) ν.2 hk

/-- T4g (S028a `ReesGamma.weight_eq_rees`, GA:45). -/
theorem old_weight_eq_rees (ν : PosReal) {N : ℕ} {k j : ℤ}
    (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    (ν : ℝ) ^ k.natAbs / (gammaW (ν : ℝ) N k * (ν : ℝ) ^ j.natAbs) =
      (ν : ℝ) ^ (k - j).natAbs * Polynomial.eval (1 / (ν : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ (eps k j - aN N k)) :=
  weight_eq_rees (ν : ℝ) ν.2 hk hj

/-- S028a `ReesGamma.eval_eps_div_eval_aN` (GA:53). -/
theorem old_eval_eps_div_eval_aN (ν : PosReal) {N : ℕ} {k j : ℤ}
    (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    Polynomial.eval (1 / (ν : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ eps k j) /
      Polynomial.eval (1 / (ν : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ aN N k) =
      Polynomial.eval (1 / (ν : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ (eps k j - aN N k)) :=
  eval_eps_div_eval_aN (ν : ℝ) ν.2 hk hj

/-- slice-23 `ReesBridge.weight_eq` (RB:796) at `{ν : PosReal}`. -/
theorem old_weight_eq {ν : PosReal} {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (hj : N < j.natAbs) :
    (ν : ℝ) ^ k.natAbs / (gammaW (ν : ℝ) N k * (ν : ℝ) ^ j.natAbs)
      = (ν : ℝ) ^ (k - j).natAbs * ((ν : ℝ)⁻¹) ^ (eps k j - aN N k) :=
  weight_eq ν.2 hk hj

/-- slice-23 `ReesBridge.gammaW_pos` (RB:328) at `{ν : PosReal}`. -/
theorem old_gammaW_pos {ν : PosReal} (N : ℕ) (k : ℤ) : 0 < gammaW (ν : ℝ) N k :=
  gammaW_pos ν.2 N k

/-! ### (b) slice-20 `GammaNote` and `gamma_eq_eval` (RF:476/:479) -/

/-- `GammaNote N ν k` is the merged `gammaW ν N k`. -/
theorem old_GammaNote (N : ℕ) (ν : ℝ) (k : ℤ) :
    ν ^ (2 * k.natAbs) / ν ^ (2 * (N + 1)) = gammaW ν N k := rfl

theorem old_gamma_eq_eval {N : ℕ} {k : ℤ} (ν : ℝ) (hν : 0 < ν) (hk : k.natAbs ≤ N) :
    ((X : ℝ[X]) ^ (aN N k)).eval (1 / ν) = ν ^ (2 * k.natAbs) / ν ^ (2 * (N + 1)) :=
  (gammaW_eq_eval_annihilator ν hν hk).symm

/-! ### (c) S028a glue (GA:6, GA:9) -/

/-- `aN_agree`: the two scratch `aN` are the one `aN`. -/
theorem old_aN_agree (N : ℕ) (k : ℤ) : aN N k = 2 * (N + 1 - k.natAbs) := rfl

/-- `gammaW_eq_GammaNote`. -/
theorem old_gammaW_eq_GammaNote (ν : PosReal) (N : ℕ) (k : ℤ) :
    gammaW (ν : ℝ) N k = (ν : ℝ) ^ (2 * k.natAbs) / (ν : ℝ) ^ (2 * (N + 1)) := rfl

/-! ### (d) GA:12 -/

theorem old_smul_z_mem_JN_iff_reesAN {R : Type*} [CommRing R] {N : ℕ} {k : ℤ}
    (_hk : k.natAbs ≤ N) (p : R[X]) :
    p • (z k : U R) ∈ JN N ↔ (X : R[X]) ^ aN N k ∣ p :=
  smul_z_mem_JN_iff p

/-! ### (e) the T18 selection, cross-context (default instances here) -/

/-- The default zero of `U R` in this context is definitionally the selected zero. -/
theorem old_zero_selection_cross_context {R : Type*} [CommRing R] :
    (0 : U R) = @Zero.zero (U R) ((instUAddCommGroup (R := R)).toZero) := rfl

/-! ### (f) FALLBACK shapes, by application of the PROVED-primary faces -/

section Fallback

variable {R : Type*} [CommRing R]

/-- T13 fallback (source RF:260). -/
theorem old_smul_z_mem_JN_iff {N : ℕ} {j : ℤ} (_h : j.natAbs ≤ N) (p : R[X]) :
    p • (z j : U R) ∈ JN N ↔ (X : R[X]) ^ (aN N j) ∣ p :=
  smul_z_mem_JN_iff p

/-- T34 (a) fallback (source EU:422). -/
theorem old_PH_mem_JN {N : ℕ} {f : U R} (hf : f ∈ JN N) :
    PH (Finset.Icc (-(N : ℤ)) N) f ∈ JN N :=
  PH_mem_JN _ hf

/-- T34 (b) fallback (source EU:431). -/
theorem old_head_coeff_dvd_of_mem_JN {N : ℕ} {f : U R}
    (hf : f ∈ JN N) {k : ℤ} (_hk : k.natAbs ≤ N) :
    (X : R[X]) ^ (aN N k + k.natAbs) ∣
      ((f : U R) : (R[X])[T;T⁻¹]).coeff k :=
  head_coeff_dvd_of_mem_JN hf k

/-- T34 (c) fallback (source EU:440). -/
theorem old_head_coeff_dvd_PH_mul_tail {N : ℕ} (b : U R) {t : U R}
    (ht : t ∈ tailMod N) {k : ℤ} (_hk : k.natAbs ≤ N) :
    (X : R[X]) ^ (aN N k + k.natAbs) ∣
      ((PH (Finset.Icc (-(N : ℤ)) N) (b * t) : U R) : (R[X])[T;T⁻¹]).coeff k :=
  head_coeff_dvd_PH_mul_tail _ b (tailMod_le_JN N ht) k

/-- T47 fallback (source GA:22 with `winZ N` unfolded to `Finset.Icc (-(N : ℤ)) N`). -/
theorem old_PH_z_mul_z_head {N : ℕ} {k j : ℤ} (hk : k.natAbs ≤ N) (_hj : N < j.natAbs) :
    PH (Finset.Icc (-(N : ℤ)) N) ((z (k - j) : U R) * z j) =
      (X : R[X]) ^ eps k j • (z k : U R) :=
  PH_z_mul_z_head (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

end Fallback

/-! ### (g) old specializations of the generic Laurent lemmas -/

section Generic

variable {R : Type*} [CommRing R]

/-- RF:42 over `R[X]`. -/
theorem old_coeff_single_eq {a a' : ℤ} {b : R[X]} :
    (AddMonoidAlgebra.single a b : (R[X])[T;T⁻¹]).coeff a' = if a = a' then b else 0 :=
  coeff_single_eq

/-- RF:48 at `x := X`. -/
theorem old_dvd_coeff_mul {α β γ : ℤ → ℕ} {f g : (R[X])[T;T⁻¹]}
    (hf : ∀ i, (X : R[X]) ^ α i ∣ f.coeff i) (hg : ∀ k, (X : R[X]) ^ β k ∣ g.coeff k)
    (hγ : ∀ i k, γ (i + k) ≤ α i + β k) (j : ℤ) : (X : R[X]) ^ γ j ∣ (f * g).coeff j :=
  dvd_coeff_mul X hf hg hγ j

/-- EU:39 over `R[X]`. -/
theorem old_coeff_diagL (lam : ℤ → R[X]) (f : (R[X])[T;T⁻¹]) (j : ℤ) :
    (diagL lam f).coeff j = lam j * f.coeff j :=
  coeff_diagL lam f j

/-- EU:42 over `R[X]`. -/
theorem old_diagL_single (lam : ℤ → R[X]) (j : ℤ) (p : R[X]) :
    diagL lam (AddMonoidAlgebra.single j p) = AddMonoidAlgebra.single j (lam j * p) :=
  diagL_single lam j p

/-- EU:77 (old `deltaL R` = new `deltaL R[X]`). -/
theorem old_coeff_deltaL (f : (R[X])[T;T⁻¹]) (j : ℤ) :
    (deltaL R[X] f).coeff j = (j : R[X]) * f.coeff j :=
  coeff_deltaL f j

end Generic

/-! ### (h) slice-23 exponent definitions (RB:735/:745/:748/:751) -/

theorem old_RB_eps (k j : ℤ) : eps k j = (k - j).natAbs + j.natAbs - k.natAbs := rfl

theorem old_RB_aN (N : ℕ) (k : ℤ) : aN N k = 2 * (N + 1 - k.natAbs) := rfl

theorem old_RB_sgn' (k : ℤ) : sgn' k = if k < 0 then -1 else 1 := rfl

theorem old_RB_jstar (N : ℕ) (k : ℤ) : jstar N k = sgn' k * ((N : ℤ) + 1) := rfl

end RadiiPolynomial.Tests.RS.Rees
