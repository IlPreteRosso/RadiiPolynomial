import RadiiPolynomial.Applications.Fourier.Quadratic
import RadiiPolynomial.Applications.Fourier.IkData

/-!
# The Helmholtz–Duffing family on `ℓ²` (book §10.1)

The equation `u'' + c₁ u' + c₂ u − u² = c₃ cos t` (book (10.1)) with the `2π`-periodic ansatz
`u = ∑ aₙ e^{int}` becomes the raw Fourier map (book §10.1, `F_n`)
`F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ`, `b_{±1} = 1/2`.
This module instantiates the quadratic Fourier family `RadiiPolynomial.Fourier.Quadratic`
(`Applications/Fourier/Quadratic.lean`: the maps `G`, `DG`, `rawF`, the defect identity, the four
bound faces, the head certificate `Cert`, the radii-polynomial existence and the transfer of
zeros, the reflections) at the Duffing symbol and forcing, for every real `(c₁, c₂, c₃)`, head
`headF N` and weight `ν ≥ 1`. It proves, on the bilateral geometric carrier
`X = X₂ ℂ ν = ℓ²_m(ℤ; ℂ)` (`m_k = ν ^ |k|`), that every certificate whose four bounds satisfy the
radii inequality yields a unique zero of the raw Fourier map in the closed ball of radius `r₀`
around the candidate, and that this zero is conjugate-symmetric (`conj ã₋ₙ = ãₙ`) when the
candidate is.

## The Duffing data

* The symbol `duffing c₁ c₂ n = −n² + i c₁ n + c₂`: its norm identity, the tail witness
  inequality, the nonvanishing and square summability of its tail symbol on the head
  `headF N = Icc (−N) N`, and the tail-sum producer for `T2` through the comparison with the
  first-order symbol data of `Applications/Fourier/IkData.lean`, under
  `−(N+1)(N+2) ≤ c₂ < (N+1)²`. Its pointwise step `duffing_lower_linear` holds under
  `−(N+1)(N+2) ≤ c₂` alone (the integer-tail factorization; the lower bound is the sharp one for
  that comparison, and for `c₂ ≥ (N+1)²` the factor `κ` is `≤ 0`); the sum also needs
  `c₂ < (N+1)²` (`κ > 0`, summability).
* The forcing `forcing c₃ = (c₃/2)(δ₁ + δ₋₁)` and the identification `rawF_duffing` of the family's
  raw map with the book's `F_n`.
* The symmetries: the symbol and the forcing are conjugate-symmetric for real parameters
  (`duffing_conj`, `coeff_forcing_conj`) and even without damping (`duffing_neg` at `c₁ = 0`,
  `coeff_forcing_neg`), the premises of `rawF_conjRefl` and `rawF_refl`.

## The existence theorems

`duffing_existsUnique` is the family's `existsUnique_rawF` at the Duffing data, for a certificate
`Cert (headF N) (duffing c₁ c₂) ν`; conjugate symmetry is `duffing_existsUnique_real` (book
Prop 10.1.2 route: raw uniqueness, the isometry `conjRefl` and the equivariance `rawF_conjRefl`,
not `R`-equivariance of `M`).
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.Fourier.Duffing

open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.WeightedLp.Bilateral RadiiPolynomial.Fourier.Quadratic
  RadiiPolynomial.Fourier.IkData

/-- The moderate constant `C = 1` of the geometric carrier weight against itself (`ν ≥ 1`). -/
local notation "hC" => Fourier.moderate_geomFiberZ

/-! ### A. The Duffing symbol and its producers -/

section DuffingSymbol

/-- The Duffing symbol `μ_n = -n² + i c₁ n + c₂` (real parameters, as complex). -/
def duffing (c₁ c₂ : ℝ) (n : ℤ) : ℂ := -(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂

/-- `|μ_n|² = (n² - c₂)² + c₁² n²`. -/
theorem sq_norm_duffing (c₁ c₂ : ℝ) (n : ℤ) :
    ‖duffing c₁ c₂ n‖ ^ 2 = ((n : ℝ) ^ 2 - c₂) ^ 2 + c₁ ^ 2 * (n : ℝ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [duffing, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, sq]
  ring

/-- The witness inequality: on the tail `|n| > N`, `(N+1)² > c₂` gives
`|μ_{N+1}|² ≤ |μ_n|²` (increasing in `n²` above `c₂`; no sign assumption on `c₁`). -/
theorem duffing_min {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    ∀ n ∉ headZ N, ‖duffing c₁ c₂ ((N : ℤ) + 1)‖ ≤ ‖duffing c₁ c₂ n‖ := fun n hn => by
  simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
  have ha : ((N : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs (n : ℝ)]
    have : (N : ℝ) + 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    exact pow_le_pow_left₀ (by positivity) this 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [sq_norm_duffing, sq_norm_duffing]
  push_cast
  have h1 : 0 < ((N : ℝ) + 1) ^ 2 - c₂ := by linarith
  have h2 : ((N : ℝ) + 1) ^ 2 - c₂ ≤ (n : ℝ) ^ 2 - c₂ := by linarith
  nlinarith [mul_le_mul h2 h2 h1.le (h1.le.trans h2), mul_le_mul_of_nonneg_left ha (sq_nonneg c₁)]

theorem duffing_succ_ne_zero {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    duffing c₁ c₂ ((N : ℤ) + 1) ≠ 0 := fun h => by
  have e := sq_norm_duffing c₁ c₂ ((N : ℤ) + 1)
  rw [h, norm_zero] at e
  push_cast at e
  have h1 : 0 < ((N : ℝ) + 1) ^ 2 - c₂ := by linarith
  nlinarith [mul_pos h1 h1, sq_nonneg (c₁ * ((N : ℝ) + 1))]

/-- **The summability hypothesis of `tailDiagInf` at the Duffing symbol**: `Summable ‖d‖²`
(`|μ_n|⁻² ≲ n⁻⁴`); the sum is not computed. -/
theorem summable_sq_tailSymbol_duffing {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    Summable fun n : ℤ => ‖tailSymbol (headZ N) (duffing c₁ c₂) n‖ ^ 2 := by
  set a : ℝ := ((N : ℝ) + 1) ^ 2
  set δ : ℝ := a - c₂
  have hδ : 0 < δ := by simp only [δ, a]; linarith
  have hK : 0 < a + |c₂| := by positivity
  set ε : ℝ := δ / (a + |c₂|)
  have hε : 0 < ε := div_pos hδ hK
  -- on the tail: `ε n² ≤ n² - c₂ ≤ |μ_n|`
  have hlow : ∀ n ∉ headZ N, ε * (n : ℝ) ^ 2 ≤ ‖duffing c₁ c₂ n‖ := fun n hn => by
    simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
    have ha : a ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs (n : ℝ)]
      have : (N : ℝ) + 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) this 2
    have hpos : 0 ≤ (n : ℝ) ^ 2 - c₂ := by simp only [δ, a] at hδ ha ⊢; linarith
    have hkey : δ * (n : ℝ) ^ 2 ≤ (a + |c₂|) * ((n : ℝ) ^ 2 - c₂) := by
      rcases le_or_gt 0 c₂ with hc | hc
      · rw [abs_of_nonneg hc]; simp only [δ]; nlinarith
      · rw [abs_of_neg hc]; simp only [δ]; nlinarith
    have hsq : ((n : ℝ) ^ 2 - c₂) ≤ ‖duffing c₁ c₂ n‖ := by
      refine (pow_le_pow_iff_left₀ hpos (norm_nonneg _) two_ne_zero).1 ?_
      rw [sq_norm_duffing]; nlinarith [sq_nonneg (c₁ * n)]
    refine le_trans ?_ hsq
    rw [show ε * (n : ℝ) ^ 2 = δ * (n : ℝ) ^ 2 / (a + |c₂|) by simp only [ε]; ring,
      div_le_iff₀ hK, mul_comm _ (a + |c₂|)]
    exact hkey
  have hg : Summable fun n : ℤ => (ε ^ 2)⁻¹ * (1 / (n : ℝ) ^ 4) :=
    (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hg
  rw [norm_tailSymbol]
  split_ifs with hn
  · rw [sq, mul_zero]; positivity
  · have hn0 : (n : ℝ) ≠ 0 := by
      simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
      exact_mod_cast (show n ≠ 0 by rintro rfl; rw [abs_zero] at hn; omega)
    have hl := hlow n hn
    have hεn : 0 < ε * (n : ℝ) ^ 2 := by positivity
    rw [inv_pow, one_div, ← mul_inv, show (ε ^ 2 * (n : ℝ) ^ 4) = (ε * (n : ℝ) ^ 2) ^ 2 by ring]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hεn.le hl 2)

variable {c₁ c₂ : ℝ} {N : ℕ}

/-- The Duffing tail symbol on the `Finset` head is square summable (the summability hypothesis
of `tailDiagInf`, through the head bridge). -/
theorem summable_sq_tailSymbol_duffing_headF (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    Summable fun k => ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 := by
  rw [tailSymbol_headF]
  exact summable_sq_tailSymbol_duffing hN

/-- The Duffing symbol does not vanish off the head. -/
theorem duffing_ne_zero (hN : c₂ < ((N : ℝ) + 1) ^ 2) : ∀ k ∉ headF N, duffing c₁ c₂ k ≠ 0 :=
  fun k hk => norm_pos_iff.1 ((norm_pos_iff.2 (duffing_succ_ne_zero hN)).trans_le
    (duffing_min hN k fun h => hk (mem_headF.2 h)))

/-- The Duffing tail symbol is bounded by `|μ_{N+1}|⁻¹` (the witness bound
`norm_tailSymbol_le_of_witness`). -/
theorem norm_tailSymbol_duffing_le (hN : c₂ < ((N : ℝ) + 1) ^ 2) (k : ℤ) :
    ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ≤
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖⁻¹ := by
  rw [tailSymbol_headF]
  exact norm_tailSymbol_le_of_witness _ _ (duffing_succ_ne_zero hN) (duffing_min hN) k

/-- **The linear lower bound** under `−(N+1)(N+2) ≤ c₂`: on the tail, `κ |k| ≤ |μ_k|` with
`κ = (N + 1) − c₂/(N + 1)`. For `c₂ < (N+1)²`: from `|μ_k| ≥ k² − c₂` and, on the integer tail
`|k| ≥ N + 1`, `k² − c₂ − κ|k| = (|k| − (N+1)) (|k| + c₂/(N+1))`: the product vanishes at
`|k| = N + 1` and both factors are nonnegative for `|k| ≥ N + 2`, where `c₂/(N+1) ≥ −(N+2)`. For
`c₂ ≥ (N+1)²` the factor `κ` is `≤ 0` and the bound is trivial. -/
theorem duffing_lower_linear (hc₂ : -(((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤ c₂) :
    ∀ k ∉ headZ N, ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) * ‖ik k‖ ≤ ‖duffing c₁ c₂ k‖ :=
  fun k hk => by
  rcases lt_or_ge c₂ (((N : ℝ) + 1) ^ 2) with hN | hN
  swap
  · have hκ : (N : ℝ) + 1 - c₂ / ((N : ℝ) + 1) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ (by positivity)]
      nlinarith
    exact (mul_nonpos_of_nonpos_of_nonneg hκ (norm_nonneg _)).trans (norm_nonneg _)
  simp only [headZ, Set.mem_ofPred_eq, not_le] at hk
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht : (N : ℝ) + 1 ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hk
  have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have hpos : 0 ≤ (k : ℝ) ^ 2 - c₂ := by nlinarith
  have hsq : (k : ℝ) ^ 2 - c₂ ≤ ‖duffing c₁ c₂ k‖ := by
    refine (pow_le_pow_iff_left₀ hpos (norm_nonneg _) two_ne_zero).1 ?_
    rw [sq_norm_duffing]
    nlinarith [sq_nonneg (c₁ * k)]
  refine le_trans ?_ hsq
  rw [norm_ik, Int.cast_abs]
  have hfac : 0 ≤ (|(k : ℝ)| - ((N : ℝ) + 1)) * (|(k : ℝ)| + c₂ / ((N : ℝ) + 1)) := by
    rcases (show |k| = (N : ℤ) + 1 ∨ (N : ℤ) + 2 ≤ |k| by generalize |k| = m at hk ⊢; omega)
      with h | h
    · rw [show |(k : ℝ)| = (N : ℝ) + 1 by rw [← Int.cast_abs, h]; push_cast; ring, sub_self,
        zero_mul]
    · have h2 : (N : ℝ) + 2 ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h
      have h3 : -((N : ℝ) + 2) ≤ c₂ / ((N : ℝ) + 1) := by
        rw [le_div_iff₀ ha]
        nlinarith
      exact mul_nonneg (by linarith) (by linarith)
  have key : (k : ℝ) ^ 2 - c₂ - ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) * |(k : ℝ)| =
      (|(k : ℝ)| - ((N : ℝ) + 1)) * (|(k : ℝ)| + c₂ / ((N : ℝ) + 1)) := by
    rw [hk2]
    field_simp
    ring
  nlinarith [hfac, key]

/-- **The tail-sum producer for `T2`** (UPPER; comparison with the `ik` data):
under `−(N+1)(N+2) ≤ c₂ < (N+1)²`,
`∑' ‖d‖² ≤ κ⁻² ∑' ‖tailSymbol (headZ N) ik‖² = κ⁻² · 2 psi1 N ≤ 4 / ((2N + 1) κ²)`. -/
theorem tsum_sq_tailSymbol_duffing_le (hN : c₂ < ((N : ℝ) + 1) ^ 2)
    (hc₂ : -(((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤ c₂) :
    ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤
      4 / ((2 * N + 1) * ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2) := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hκ0 : 0 < (N : ℝ) + 1 - c₂ / ((N : ℝ) + 1) := by
    rw [sub_pos, div_lt_iff₀ ha]
    nlinarith
  have hterm : ∀ k, ‖tailSymbol (headZ N) (duffing c₁ c₂) k‖ ^ 2 ≤
      (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹ * ‖tailSymbol (headZ N) ik k‖ ^ 2 := fun k => by
    rw [norm_tailSymbol, norm_tailSymbol]
    split_ifs with hk
    · simp
    · have hl := duffing_lower_linear (c₁ := c₁) hc₂ k hk
      have hik : 0 < ‖ik k‖ := by
        simp only [headZ, Set.mem_ofPred_eq, not_le] at hk
        rw [norm_ik]
        exact_mod_cast (by omega : (0 : ℤ) < |k|)
      have hp := mul_pos hκ0 hik
      rw [inv_pow, inv_pow, ← mul_inv, ← mul_pow]
      exact inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le hl 2)
  rw [tailSymbol_headF]
  refine (Summable.tsum_le_tsum hterm (summable_sq_tailSymbol_duffing hN)
    ((summable_sq_tailSymbol_ik N).mul_left _)).trans ?_
  rw [tsum_mul_left, (hasSum_sq_tailSymbol_ik N).tsum_eq]
  have h2N : (0 : ℝ) < 2 * N + 1 := by positivity
  have hp := (le_div_iff₀ h2N).1 (RadiiPolynomial.WeightedLp.psi1_le N)
  rw [le_div_iff₀ (mul_pos h2N (pow_pos hκ0 2)),
    show (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹ * (2 * RadiiPolynomial.WeightedLp.psi1 N) *
        ((2 * N + 1) * ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2) =
      2 * (RadiiPolynomial.WeightedLp.psi1 N * (2 * N + 1)) *
        (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2 * (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹) by
      ring,
    mul_inv_cancel₀ (pow_ne_zero 2 hκ0.ne'), mul_one]
  linarith

/-- **Real parameters make the symbol conjugate-symmetric**: `μ₋ₙ = conj μₙ`. -/
theorem duffing_conj (c₁ c₂ : ℝ) (n : ℤ) :
    duffing c₁ c₂ (-n) = starRingEnd ℂ (duffing c₁ c₂ n) := by
  simp only [duffing, map_add, map_neg, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_intCast, Int.cast_neg]
  ring

/-- **Without damping the symbol is even**: `μ₋ₙ = μₙ` at `c₁ = 0`. -/
theorem duffing_neg (c₂ : ℝ) (n : ℤ) : duffing 0 c₂ (-n) = duffing 0 c₂ n := by
  simp [duffing]

variable {ν : PosReal}

/-- **The forcing** `g = c₃ b = (c₃/2)(δ₁ + δ₋₁)` (book: `b_{±1} = 1/2`). -/
def forcing (c₃ : ℝ) : X₂ ℂ ν := ((c₃ / 2 : ℝ) : ℂ) • (atom ℂ ν 1 + atom ℂ ν (-1))

theorem coeff_forcing (c₃ : ℝ) (n : ℤ) :
    coeff (forcing (ν := ν) c₃) n = if n = 1 ∨ n = -1 then ((c₃ / 2 : ℝ) : ℂ) else 0 := by
  rw [forcing, coeff_smul, coeff_add, Pi.smul_apply, Pi.add_apply, coeff_atom, coeff_atom,
    smul_eq_mul]
  by_cases h1 : n = 1
  · subst h1
    simp
  · by_cases h2 : n = -1
    · subst h2
      simp
    · simp [h1, h2]

/-- **The producer for `hg`**: `supp (c₃ b) ⊆ headF N` under `N ≥ 1`. -/
theorem forcing_supp {c₃ : ℝ} (hN1 : 1 ≤ N) :
    ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0 := fun k hk => by
  rw [coeff_forcing, ite_eq_right]
  rintro (rfl | rfl)
  · exact hk (mem_headF.2 (by rw [abs_one]; exact_mod_cast hN1))
  · exact hk (mem_headF.2 (by rw [abs_neg, abs_one]; exact_mod_cast hN1))

/-- **The raw Fourier map at the Duffing data is the book's `F_n`** (book §10.1):
`F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ`. -/
theorem rawF_duffing {c₃ : ℝ} (a : X₂ ℂ ν) (n : ℤ) :
    rawF (duffing c₁ c₂) (forcing c₃) a n =
      (-(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂) * coeff a n - convCoeff a a n -
        c₃ * (if n = 1 ∨ n = -1 then 1 / 2 else 0) := by
  rw [rawF, duffing, coeff_forcing]
  split_ifs
  · push_cast
    ring
  · ring

/-- **The forcing is conjugate-symmetric** (real `c₃`): `g₋ₙ = conj gₙ`. -/
theorem coeff_forcing_conj (c₃ : ℝ) (n : ℤ) :
    coeff (forcing (ν := ν) c₃) (-n) = starRingEnd ℂ (coeff (forcing (ν := ν) c₃) n) := by
  rw [coeff_forcing, coeff_forcing, apply_ite (starRingEnd ℂ), Complex.conj_ofReal, map_zero]
  exact if_congr (by omega) rfl rfl

/-- **The forcing is even**: `g₋ₙ = gₙ`. -/
theorem coeff_forcing_neg (c₃ : ℝ) (n : ℤ) :
    coeff (forcing (ν := ν) c₃) (-n) = coeff (forcing (ν := ν) c₃) n := by
  rw [coeff_forcing, coeff_forcing]
  exact if_congr (by omega) rfl rfl

end DuffingSymbol

/-! ### B. The existence theorem -/

section Existence

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {c₁ c₂ c₃ : ℝ} {N : ℕ}

/-- **The Duffing existence theorem: a unique zero of the Fourier map in the ball** (book
Theorem 10.1.3 on `ℓ²_ν`): under `(N+1)² > c₂`, a certificate, `supp (c₃ b) ⊆ headF N`, the four
bounds and the radii inequality, the raw Fourier map
`F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ` has a unique zero in the closed ball of
radius `r₀` around the candidate. -/
theorem duffing_existsUnique (hN : c₂ < ((N : ℝ) + 1) ^ 2)
    (cert : Cert (headF N) (duffing c₁ c₂) ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ : ℝ}
    (hY₀ : ‖G (headF N) (duffing c₁ c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀)
    (hrad : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall cert.abar r₀, ∀ n : ℤ, rawF (duffing c₁ c₂) (forcing c₃) a n = 0 := by
  have hs := summable_sq_tailSymbol_duffing_headF (c₁ := c₁) hN
  have hZ1' : ‖DG (headF N) (duffing c₁ c₂) hs cert.M cert.abar -
      B0 (headF N) (duffing c₁ c₂) cert.M (betaOf (headF N) cert.abar cert.abar_supp)‖ ≤ Z₁ := by
    refine (norm_DG_sub_B0_le (headF N) (duffing c₁ c₂) hs cert.M cert.abar_supp cert.hPM
      cert.hH (norm_tailSymbol_duffing_le hN)).trans ?_
    rw [mul_one, inv_mul_eq_div]
    exact (Real.sqrt_le_sqrt hZ₁).trans_eq (Real.sqrt_sq hZ₁0)
  have hT20 : 0 ≤ T2 := (tsum_nonneg fun _ => sq_nonneg _).trans hT2
  have h2 : 2 * √(cert.U ^ 2 + T2) ≤ Z₂ := by
    refine (pow_le_pow_iff_left₀ (by positivity) hZ₂0 two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    linarith
  have hZ2' := (norm_quadComp_add_flip_le_of_bounds (headF N) (duffing c₁ c₂) hs cert.M
    cert.hPM cert.hU hT2).trans h2
  obtain ⟨a, ⟨ha, hFa⟩, hu⟩ := existsUnique_rawF (headF N) (duffing c₁ c₂) hs cert.M (forcing c₃)
    cert.abar_supp cert.hPM hg (duffing_ne_zero hN) hr₀ hY₀ cert.hZ₀ hZ1' hZ2' hrad
  exact ⟨a, ⟨ha, fun n => congrFun hFa n⟩, fun z ⟨hz, hz0⟩ => hu z ⟨hz, funext hz0⟩⟩

/-- **The enclosure at two radii**: with the hypotheses of `duffing_existsUnique` and the radii
inequality at `r₀ ≤ r₁`, the zero in the ball of radius `r₀` is the only zero in the ball of radius
`r₁`. -/
theorem duffing_enclosure (hN : c₂ < ((N : ℝ) + 1) ^ 2)
    (cert : Cert (headF N) (duffing c₁ c₂) ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ r₁ : ℝ}
    (hY₀ : ‖G (headF N) (duffing c₁ c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀) (hr : r₀ ≤ r₁)
    (hrad₀ : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hrad₁ : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₁ < 0) :
    ∃ a ∈ Metric.closedBall cert.abar r₀, (∀ n, rawF (duffing c₁ c₂) (forcing c₃) a n = 0) ∧
      ∀ z ∈ Metric.closedBall cert.abar r₁,
        (∀ n, rawF (duffing c₁ c₂) (forcing c₃) z n = 0) → z = a := by
  obtain ⟨a, ⟨ha, hFa⟩, -⟩ :=
    duffing_existsUnique hN cert hg hY₀ hZ₁ hZ₁0 hT2 hZ₂ hZ₂0 hr₀ hrad₀
  obtain ⟨b, -, hub⟩ :=
    duffing_existsUnique hN cert hg hY₀ hZ₁ hZ₁0 hT2 hZ₂ hZ₂0 (hr₀.trans_le hr) hrad₁
  have hab : a = b := hub a ⟨Metric.closedBall_subset_closedBall hr ha, hFa⟩
  exact ⟨a, ha, hFa, fun z hz hFz => (hub z ⟨hz, hFz⟩).trans hab.symm⟩

end Existence

/-! ### C. Reality -/

section Reality

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {c₁ c₂ c₃ : ℝ} {N : ℕ}

/-- **The conjugate-symmetric existence theorem** (book Prop 10.1.2 route): with the hypotheses of
`duffing_existsUnique` and `R ā = ā`, the unique zero of the Fourier map in the ball satisfies
`R ã = ã`, i.e. `conj ã₋ₙ = ãₙ` (uniqueness of the raw zero, the isometry `conjRefl` and the
equivariance `rawF_conjRefl` at the real parameters; not `R`-equivariance of `M`). -/
theorem duffing_existsUnique_real (hN : c₂ < ((N : ℝ) + 1) ^ 2)
    (cert : Cert (headF N) (duffing c₁ c₂) ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ : ℝ}
    (hY₀ : ‖G (headF N) (duffing c₁ c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀)
    (hrad : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hR : conjRefl cert.abar = cert.abar) :
    ∃ a ∈ Metric.closedBall cert.abar r₀, (∀ n, rawF (duffing c₁ c₂) (forcing c₃) a n = 0) ∧
      conjRefl a = a ∧ ∀ z ∈ Metric.closedBall cert.abar r₀,
        (∀ n, rawF (duffing c₁ c₂) (forcing c₃) z n = 0) → z = a := by
  obtain ⟨a, ⟨ha, hFa⟩, hu⟩ := duffing_existsUnique hN cert hg hY₀ hZ₁ hZ₁0 hT2 hZ₂ hZ₂0 hr₀ hrad
  refine ⟨a, ha, hFa, hu _ ⟨?_, fun n => ?_⟩, fun z hz hz0 => hu z ⟨hz, hz0⟩⟩
  · rw [← hR]
    exact isometry_conjRefl.mapsTo_closedBall _ _ ha
  · rw [rawF_conjRefl (duffing_conj c₁ c₂) (coeff_forcing_conj c₃), hFa, map_zero]

end Reality

/-! ### The undamped even subfamily -/

section Even

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic RadiiPolynomial.Fourier.IkData RadiiPolynomial.Fourier.Duffing

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {c₂ c₃ : ℝ} {N : ℕ}

/-- **The even existence theorem** (`c₁ = 0`): with the hypotheses of
`duffing_existsUnique_real` and an even candidate `refl ā = ā`, the unique zero of the raw Fourier
map in the ball is conjugate-symmetric and even, `conj ã₋ₙ = ãₙ = ã₋ₙ`. -/
theorem duffing_existsUnique_even (hN : c₂ < ((N : ℝ) + 1) ^ 2)
    (cert : Cert (headF N) (duffing 0 c₂) ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ : ℝ}
    (hY₀ : ‖G (headF N) (duffing 0 c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing 0 c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing 0 c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀)
    (hrad : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hR : conjRefl cert.abar = cert.abar) (hE : refl cert.abar = cert.abar) :
    ∃ a ∈ Metric.closedBall cert.abar r₀, (∀ n, rawF (duffing 0 c₂) (forcing c₃) a n = 0) ∧
      conjRefl a = a ∧ refl a = a ∧ ∀ z ∈ Metric.closedBall cert.abar r₀,
        (∀ n, rawF (duffing 0 c₂) (forcing c₃) z n = 0) → z = a := by
  obtain ⟨a, ha, hFa, hRa, hu⟩ :=
    duffing_existsUnique_real hN cert hg hY₀ hZ₁ hZ₁0 hT2 hZ₂ hZ₂0 hr₀ hrad hR
  refine ⟨a, ha, hFa, hRa, hu _ ?_ fun n => ?_, hu⟩
  · rw [← hE]
    exact isometry_refl.mapsTo_closedBall _ _ ha
  · rw [rawF_refl (duffing_neg c₂) (coeff_forcing_neg c₃), hFa]

end Even

open RadiiPolynomial.WeightedLp RadiiPolynomial.Fourier.IkData

section Symbols

/-! ### The shifted symbol as a real translate (`duffing_sub_ofReal`) -/

/-- The shift of a Duffing symbol by a real `l` is the Duffing symbol with `c₂ - l`. -/
theorem duffing_sub_ofReal (c₁ c₂ l : ℝ) (n : ℤ) :
    duffing c₁ c₂ n - (l : ℂ) = duffing c₁ (c₂ - l) n := by
  rw [duffing, duffing, Complex.ofReal_sub]
  ring

end Symbols

section Tail

/-! ### The tail data at a real eigenvalue

Hypothesis `hN : c₂ - l < (N + 1)²` (tail nonresonance of the shifted symbol). The tail inverse of
`μ - l` is `tailSymbol ↑(headF N) (fun n => μ n - l)`: `tailSymbol` already inverts off the head. -/

variable {c₁ c₂ l : ℝ} {N : ℕ}

/-- Tail nonresonance: `μ_n ≠ l` off the head. -/
theorem duffing_ne_ofReal (hN : c₂ - l < ((N : ℝ) + 1) ^ 2) :
    ∀ n ∉ headF N, duffing c₁ c₂ n ≠ (l : ℂ) := fun n hn =>
  sub_ne_zero.1 <| (duffing_sub_ofReal c₁ c₂ l n).trans_ne (duffing_ne_zero hN n hn)

/-- The tail inverse of the shifted symbol is bounded by `|μ_{N+1} - l|⁻¹`. -/
theorem norm_tailSymbol_duffing_sub_le (hN : c₂ - l < ((N : ℝ) + 1) ^ 2) (k : ℤ) :
    ‖tailSymbol ↑(headF N) (fun n => duffing c₁ c₂ n - (l : ℂ)) k‖ ≤
      ‖duffing c₁ (c₂ - l) ((N : ℤ) + 1)‖⁻¹ :=
  (congrArg (fun μ => ‖tailSymbol ↑(headF N) μ k‖)
    (funext (duffing_sub_ofReal c₁ c₂ l))).trans_le (norm_tailSymbol_duffing_le hN k)

/-- The tail inverse of the shifted symbol is bounded. -/
theorem bddAbove_tailSymbol_duffing_sub (hN : c₂ - l < ((N : ℝ) + 1) ^ 2) :
    BddAbove (Set.range fun k => ‖tailSymbol ↑(headF N) (fun n => duffing c₁ c₂ n - (l : ℂ)) k‖) :=
  ⟨_, Set.forall_mem_range.2 (norm_tailSymbol_duffing_sub_le hN)⟩

/-- The rational tail constant: `|μ_{N+1} - l|⁻¹ ≤ ((N + 1)² - (c₂ - l))⁻¹`, from
`|μ| ≥ |Re μ| = (N + 1)² - (c₂ - l) > 0`. -/
theorem inv_norm_duffing_succ_le (hN : c₂ - l < ((N : ℝ) + 1) ^ 2) :
    ‖duffing c₁ (c₂ - l) ((N : ℤ) + 1)‖⁻¹ ≤ (((N : ℝ) + 1) ^ 2 - (c₂ - l))⁻¹ := by
  have hsq := sq_norm_duffing c₁ (c₂ - l) ((N : ℤ) + 1)
  rw [Int.cast_add, Int.cast_natCast, Int.cast_one] at hsq
  refine inv_anti₀ (sub_pos.2 hN) ?_
  nlinarith [sub_pos.2 hN, norm_nonneg (duffing c₁ (c₂ - l) ((N : ℤ) + 1)),
    mul_nonneg (sq_nonneg c₁) (sq_nonneg ((N : ℝ) + 1))]

end Tail

section Growth

/-- For real `c₁ c₂` and `n : ℤ`, `|(n : ℝ)| ≤ ‖duffing c₁ c₂ n‖ + |c₂|`. -/
theorem abs_le_norm_duffing_add (c₁ c₂ : ℝ) (n : ℤ) :
    |(n : ℝ)| ≤ ‖duffing c₁ c₂ n‖ + |c₂| := by
  have hsq : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
    have h := Int.natAbs_le_self_sq n
    rw [Int.natCast_natAbs] at h
    exact_mod_cast h
  have hd := sq_norm_duffing c₁ c₂ n
  have h0 := norm_nonneg (duffing c₁ c₂ n)
  have hre : (n : ℝ) ^ 2 - c₂ ≤ ‖duffing c₁ c₂ n‖ := by
    nlinarith [sq_nonneg (c₁ * (n : ℝ)), sq_nonneg ((n : ℝ) ^ 2 - c₂ - ‖duffing c₁ c₂ n‖)]
  linarith [le_abs_self c₂]

/-- For real `c₁ c₂`, `n ↦ ‖duffing c₁ c₂ n‖` tends to `Filter.atTop` along `Filter.cofinite`. -/
theorem tendsto_norm_duffing (c₁ c₂ : ℝ) :
    Filter.Tendsto (fun n : ℤ => ‖duffing c₁ c₂ n‖) Filter.cofinite Filter.atTop :=
  (Filter.tendsto_atTop_add_const_right _ (-|c₂|)
    (Filter.tendsto_atTop_mono (fun n => (Real.norm_eq_abs _).trans_le
        (abs_le_norm_duffing_add c₁ c₂ n))
      (tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite))).congr
    fun _ => add_neg_cancel_right _ _

end Growth

end RadiiPolynomial.Fourier.Duffing

end
