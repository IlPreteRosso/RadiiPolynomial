import RadiiPolynomial.Applications.Fourier

/-!
# FZ semilinear tests: nonvacuity (T56, L005)

Imports the FACADE `RadiiPolynomial.Applications.Fourier` (the T52 importer check). Nonvacuity
witnesses of the semilinear consumer:

* (a) the S028b instance in the new names: `𝕜 = ℂ`, `N = 1`, `M = P_1`, `τ = 1`, `Φ = X₀²`,
  `ā = e₀` (`β = 2 e₀`, band `0`), `r = tailInv 1 ikSymbol`: every hypothesis of T33–T35 and T50
  holds jointly (the four theorems are applied), and `DG(ā) − B₀ ≠ 0` with the witness column
  `e₂ ↦ −2 D_r e₂ ≠ 0`;
* (b) the degree instance `ā = e₋₁ + e₁`, `Φ = X₀²` (`d = 2`): the hypotheses of T36/T37 hold
  jointly (both applied);
* (c) a REAL general-symbol instance: `𝕜 = ℝ`, `ν = 1` (the literal weight `vacNu1` with a
  LOCAL `Fact (1 ≤ ν)` instance), `lam k = k`, `N = 1`, `r = tailInv 1 lam`, `C = 1/2`: the
  hypotheses of T32 (tail nonvanishing, the bound) and of T33 at `K₀ = 1` hold (both applied), and
  `DG(ā) − B₀ ≠ 0` at `ā = e₀`, `Φ = X₀²` — the generalization exercised beyond `ℂ` and beyond
  the symbol `i k`;
* (d) T39 at the (a) instance, both sides positive;
* (e) `precondMap` resolves through the facade import.

The S028b vacuity rows (FS:472–:537: `Φ'hat_square`, `b_square`, `vacuity_hyps`,
`vacuity_witness`, `vacuity_ne_zero`, `dN_vacuity_hyps`) are restated here in the new names.
The carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` (local notation).
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.Semilinear

open RadiiPolynomial.Fourier RadiiPolynomial.Fourier.Semilinear

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)

/-! ### Generic computations at `Φ = X₀²` -/

section Square

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- FS:472 `Φ'hat_square`: `Φ̂′(a) = 2 a` for `Φ = X₀²`. -/
theorem vac_phiHatDeriv_square (a : 𝓔 𝕜 ν) :
    phiHatDeriv (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) 𝕜) a = (2 : 𝕜) • a := by
  simp only [phiHatDeriv, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
    Nat.reduceSub, pow_one, mul_one, map_mul, map_natCast, MvPolynomial.aeval_X]
  rw [Algebra.smul_def, map_ofNat]
  norm_num only []

/-- FS:479 `b_square`: `β = 2 a` for `τ = 1`, `Φ = X₀²`. -/
theorem vac_beta_square (a : 𝓔 𝕜 ν) :
    beta 1 (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) 𝕜) a = (2 : 𝕜) • a := by
  rw [beta, vac_phiHatDeriv_square, one_smul]

/-- The column `e_j` (`N < |j|`) of `DG(e₀) − B₀` at `τ = 1`, `Φ = X₀²`: `−2 D_r e_j`, for every
symbol, every bounded `M` and every bounded `r`. -/
theorem vac_column (N : ℕ) (M : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lam r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (j : ℤ) (hj : N < j.natAbs) :
    ((fderiv 𝕜 (precondMap N M lam r C hr 1 (MvPolynomial.X 0 ^ 2)) (lpOneAlg.single 0 1 : 𝓔 𝕜 ν) -
        modelDeriv N M lam 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1)) :
        𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lpOneAlg.single j 1) =
      (-2 : 𝕜) • (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)
        (lpOneAlg.single j 1) := by
  rw [fderiv_sub_modelDeriv, neg_apply, defect_eq, add_apply, defectHead_single,
    ite_eq_right (by omega), defectTail_single, vac_beta_square, ← lpOneAlg.one_eq_single_zero,
    smul_mul_assoc, one_mul, map_smul, lpOneAlg.headProj_single,
    ite_eq_right (fun h => by rw [mem_winZ] at h; omega), smul_zero, map_zero, zero_add, map_smul,
    neg_smul]

/-- `D_r e_j ≠ 0` when `r j ≠ 0`. -/
theorem vac_diag_single_ne_zero (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (j : ℤ) (hj : r j ≠ 0) :
    (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lpOneAlg.single j 1) ≠ 0 := by
  intro h
  have hc := congr_arg (fun x : 𝓔 𝕜 ν => lpOneAlg.toRealSeq x j) h
  simp only [lpOneAlg.toRealSeq_diagCLM, lpOneAlg.toRealSeq_single, ↓reduceIte, mul_one,
    lpOneAlg.toRealSeq_zero, Pi.zero_apply] at hc
  exact hj hc

/-- `DG(e₀) − B₀ ≠ 0` whenever some tail coordinate `|j| > N` has `r j ≠ 0` (and `2 ≠ 0` in `𝕜`). -/
theorem vac_ne_zero (N : ℕ) (M : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lam r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (j : ℤ) (hj : N < j.natAbs) (hrj : r j ≠ 0) (h2 : (2 : 𝕜) ≠ 0) :
    (fderiv 𝕜 (precondMap N M lam r C hr 1 (MvPolynomial.X 0 ^ 2)) (lpOneAlg.single 0 1 : 𝓔 𝕜 ν) -
        modelDeriv N M lam 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ≠ 0 := by
  intro h
  have hw := vac_column N M lam r C hr j hj
  rw [h, zero_apply] at hw
  exact vac_diag_single_ne_zero r C hr j hrj
    ((smul_eq_zero.mp hw.symm).resolve_left (neg_ne_zero.mpr h2))

/-- The band of `β = 2 e₀`. -/
theorem vac_beta_band :
    ∀ i : ℤ, 0 < i.natAbs →
      lpOneAlg.toRealSeq (beta 1 (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) 𝕜)
        (lpOneAlg.single 0 1 : 𝓔 𝕜 ν)) i = 0 := by
  intro i hi
  rw [vac_beta_square, lpOneAlg.toRealSeq_smul, Pi.smul_apply,
    band_single 0 0 (1 : 𝕜) (by decide) i hi, smul_zero]

end Square

/-! ### (a) the S028b instance (`𝕜 = ℂ`, `N = 1`, `M = P_1`, `τ = 1`, `Φ = X₀²`, `ā = e₀`) -/

section InstanceA

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓟₁" =>
  (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)
local notation "𝓖₁" => (precondMap 1 𝓟₁ ikSymbol (tailInv 1 ikSymbol)
  (1 / (((1 : ℕ) : ℝ) + 1)) (norm_tailInv_ikSymbol_le 1) 1 (MvPolynomial.X 0 ^ 2) :
  𝓔 ℂ ν → 𝓔 ℂ ν)
local notation "𝓑₁" => (modelDeriv 1 𝓟₁ ikSymbol 1 (MvPolynomial.X 0 ^ 2)
  (lpOneAlg.single 0 1 : 𝓔 ℂ ν) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)

/-- FS:483 `vacuity_hyps`, extended: the hypotheses of T33–T35 and T50 hold jointly at (a):
`P M = M`, `r = 0` on the head, the band `0` of `β` and two-ray monotone moduli from `K₀ = 1`. -/
theorem vac_a_hyps :
    (𝓟₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L 𝓟₁ = 𝓟₁ ∧
    (∀ k : ℤ, k.natAbs ≤ 1 → tailInv 1 ikSymbol k = 0) ∧
    (∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq
      (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν)) i = 0) ∧
    (∀ n : ℕ, max (1 + 1) 1 ≤ n →
      ‖tailInv 1 ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv 1 ikSymbol (n : ℤ)‖ ∧
        ‖tailInv 1 ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv 1 ikSymbol (-(n : ℤ))‖) :=
  ⟨lpOneAlg.headProj_comp_headProj _, tailInv_head_zero 1 ikSymbol, vac_beta_band,
    tailInv_ikSymbol_hmono 1⟩

/-- (a) T50 applies (window `N + m + 1 = 2`). -/
theorem vac_a_T50 :
    ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ =
      (winZ (1 + 0 + 1)).sup' (winZ_nonempty _)
        (fun j => headCol 1 𝓟₁ (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν)) j +
          tailCol 0 (tailInv 1 ikSymbol) (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν)) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup'_first 1 0 𝓟₁ 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1)
    (vac_a_hyps (ν := ν)).1 (vac_a_hyps (ν := ν)).2.2.1

/-- (a) T33 applies (`B = 0`, `K₀ = 1`). -/
theorem vac_a_T33 :
    ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ =
      (winZ (0 + max (1 + 1) 1)).sup' (winZ_nonempty _)
        (fun j => lpOneAlg.colRatio (defect 1 𝓟₁ (tailInv 1 ikSymbol) (1 / (((1 : ℕ) : ℝ) + 1))
          (norm_tailInv_ikSymbol_le 1) (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν))) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup' 1 0 1 𝓟₁ ikSymbol _ _ _ 1 _ _ (vac_a_hyps (ν := ν)).2.2.1
    (tailInv_ikSymbol_hmono 1)

/-- (a) T34 applies. -/
theorem vac_a_T34 :
    ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ =
      (winZ (0 + max (1 + 1) 1)).sup' (winZ_nonempty _)
        (fun j => headCol 1 𝓟₁ (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν)) j +
          tailCol 0 (tailInv 1 ikSymbol) (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν)) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup'_explicit 1 0 1 𝓟₁ ikSymbol _ _ _ 1 _ _ (vac_a_hyps (ν := ν)).2.2.1
    (vac_a_hyps (ν := ν)).1 (vac_a_hyps (ν := ν)).2.1 (tailInv_ikSymbol_hmono 1)

/-- (a) T35 applies. -/
theorem vac_a_T35 :
    ∃ j ∈ winZ (0 + max (1 + 1) 1),
      ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single j 1)‖ =
        ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ * (ν : ℝ) ^ j.natAbs :=
  fderiv_sub_modelDeriv_attained 1 0 1 𝓟₁ ikSymbol _ _ _ 1 _ _ (vac_a_hyps (ν := ν)).2.2.1
    (tailInv_ikSymbol_hmono 1)

/-- FS:499 `vacuity_witness`: the column `e₂ ↦ −2 D_r e₂`, with `D_r e₂ ≠ 0`. -/
theorem vac_a_witness :
    (fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single 2 1) =
      (-2 : ℂ) • (lpOneAlg.diagCLM (G := geomFiberZ ℂ ν) (tailInv 1 ikSymbol) (1 / (((1 : ℕ) : ℝ) + 1))
        (norm_tailInv_ikSymbol_le 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single 2 1) ∧
    (lpOneAlg.diagCLM (G := geomFiberZ ℂ ν) (tailInv 1 ikSymbol) (1 / (((1 : ℕ) : ℝ) + 1))
        (norm_tailInv_ikSymbol_le 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single 2 1) ≠ 0 := by
  have h2 : tailInv 1 ikSymbol 2 ≠ 0 := by
    intro h
    have hn := norm_tailInv_ikSymbol 1 2
    rw [h, norm_zero, ite_eq_right (by decide)] at hn
    norm_num at hn
  exact ⟨vac_column 1 _ ikSymbol _ _ _ 2 (by decide), vac_diag_single_ne_zero _ _ _ 2 h2⟩

/-- FS:527 `vacuity_ne_zero`: `DG(ā) − B₀ ≠ 0` at (a). -/
theorem vac_a_ne_zero :
    (fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ≠ 0 := by
  intro h
  have hw := (vac_a_witness (ν := ν)).1
  rw [h, zero_apply] at hw
  exact (vac_a_witness (ν := ν)).2 ((smul_eq_zero.mp hw.symm).resolve_left (by norm_num))

/-- (d) T39 at the (a) instance; both sides are positive. -/
theorem vac_d_T39 :
    0 < ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ ∧
    ‖(fderiv ℂ 𝓖₁ (lpOneAlg.single 0 1 : 𝓔 ℂ ν) - 𝓑₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ ≤
      (‖(𝓟₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ 1) :
          𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L (gammaDiag 1 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ + 1 / (((1 : ℕ) : ℝ) + 1)) *
        ‖(beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν) : 𝓔 ℂ ν)‖ ∧
    0 < (‖(𝓟₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ 1) :
          𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L (gammaDiag 1 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ + 1 / (((1 : ℕ) : ℝ) + 1)) *
        ‖(beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν) : 𝓔 ℂ ν)‖ := by
  have hβ : (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℂ ν) : 𝓔 ℂ ν) ≠ 0 := by
    intro h
    have hc := congr_arg (fun x : 𝓔 ℂ ν => lpOneAlg.toRealSeq x 0) h
    simp only [vac_beta_square, lpOneAlg.toRealSeq_smul, Pi.smul_apply, lpOneAlg.toRealSeq_single,
      smul_eq_mul, lpOneAlg.toRealSeq_zero, Pi.zero_apply] at hc
    norm_num at hc
  refine ⟨norm_pos_iff.mpr vac_a_ne_zero,
    norm_fderiv_sub_modelDeriv_le_gamma 1 𝓟₁ ikSymbol _ _ _ 1 _ _, ?_⟩
  exact mul_pos (add_pos_of_nonneg_of_pos (norm_nonneg _) (by norm_num)) (norm_pos_iff.mpr hβ)

end InstanceA

/-! ### (b) the degree instance (`ā = e₋₁ + e₁`, `Φ = X₀²`, `d = 2`) -/

section InstanceB

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓟₁" =>
  (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)

/-- FS:537 `dN_vacuity_hyps`, extended: the hypotheses of T36 and T37 hold jointly at (b). -/
theorem vac_b_hyps :
    (∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq
      ((lpOneAlg.single (-1) 1 + lpOneAlg.single 1 1) : 𝓔 ℂ ν) i = 0) ∧
    (MvPolynomial.pderiv 0 ((MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) ^ 2)).totalDegree ≤ 2 - 1 ∧
    1 ≤ (2 : ℕ) ∧ (1 : ℕ) ≤ 1 + 1 ∧
    (∀ n : ℕ, max (1 + 1) 1 ≤ n →
      ‖tailInv 1 ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv 1 ikSymbol (n : ℤ)‖ ∧
        ‖tailInv 1 ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv 1 ikSymbol (-(n : ℤ))‖) := by
  refine ⟨?_, ?_, by decide, by decide, tailInv_ikSymbol_hmono 1⟩
  · intro i hi
    rw [lpOneAlg.toRealSeq_add, Pi.add_apply, band_single 1 (-1) (1 : ℂ) (by decide) i hi,
      band_single 1 1 (1 : ℂ) (by decide) i hi, add_zero]
  · simp only [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, Nat.reduceSub, pow_one, mul_one]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [← map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 1) ℂ) 2,
      MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- (b) T36 applies, and T37 rewrites its window `(2 − 1)·1 + max 2 1` to `2·1 + 1`. -/
theorem vac_b_T36_T37 :
    ‖(fderiv ℂ (precondMap 1 (𝓟₁ : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ikSymbol (tailInv 1 ikSymbol)
          (1 / (((1 : ℕ) : ℝ) + 1)) (norm_tailInv_ikSymbol_le 1) 1 (MvPolynomial.X 0 ^ 2))
          (lpOneAlg.single (-1) 1 + lpOneAlg.single 1 1) -
        modelDeriv 1 𝓟₁ ikSymbol 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single (-1) 1 + lpOneAlg.single 1 1) :
        𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ =
      (winZ ((2 - 1) * 1 + max (1 + 1) 1)).sup' (winZ_nonempty _)
        (fun j => lpOneAlg.colRatio (defect 1 𝓟₁ (tailInv 1 ikSymbol) (1 / (((1 : ℕ) : ℝ) + 1))
          (norm_tailInv_ikSymbol_le 1) (beta 1 (MvPolynomial.X 0 ^ 2)
            (lpOneAlg.single (-1) 1 + lpOneAlg.single 1 1 : 𝓔 ℂ ν))) j) ∧
    (2 - 1) * 1 + max (1 + 1) 1 = 2 * 1 + 1 :=
  ⟨norm_fderiv_sub_modelDeriv_eq_sup'_deg 1 2 1 𝓟₁ ikSymbol _ _ _ 1 _ _ (vac_b_hyps (ν := ν)).1
      (vac_b_hyps (ν := ν)).2.1 (tailInv_ikSymbol_hmono 1),
    window_deg_eq 1 2 1 (by decide) (by decide)⟩

end InstanceB

/-! ### (c) a REAL general-symbol instance (`𝕜 = ℝ`, `ν = 1`, `lam k = k`, `N = 1`) -/

section InstanceC

/-- The literal weight `ν = 1`. -/
def vacNu1 : PosReal := ⟨1, one_pos⟩

/-- `ν = 1 ≥ 1` (a LOCAL instance below). -/
theorem vacNu1_fact : Fact (1 ≤ ((vacNu1 : PosReal) : ℝ)) := ⟨le_rfl⟩

attribute [local instance] vacNu1_fact

/-- The real symbol `lam k = k`. -/
def vacLam (k : ℤ) : ℝ := (k : ℝ)

/-- The tail inverse of `lam k = k` at `N = 1` has modulus `1_{|k| > 1} / |k|`. -/
theorem vac_norm_tailInv (k : ℤ) :
    ‖tailInv 1 vacLam k‖ = if k.natAbs ≤ 1 then 0 else (k.natAbs : ℝ)⁻¹ := by
  unfold tailInv
  by_cases hk : k.natAbs ≤ 1
  · rw [ite_eq_left (mem_winZ.mpr hk), ite_eq_left hk, norm_zero]
  · rw [ite_eq_right (fun h => hk (mem_winZ.mp h)), ite_eq_right hk, norm_inv, vacLam,
      Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

/-- The uniform bound `C = 1/2` of the tail inverse (supplied separately; T32's `hC`). -/
theorem vac_tailInv_le : ∀ k, ‖tailInv 1 vacLam k‖ ≤ 1 / 2 := by
  intro k
  rw [vac_norm_tailInv]
  split_ifs with hk
  · norm_num
  · rw [one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast (show 2 ≤ k.natAbs by omega))

/-- Tail nonvanishing of `lam k = k` (T32's `hlam`). -/
theorem vac_lam_ne_zero : ∀ k : ℤ, 1 < k.natAbs → vacLam k ≠ 0 := by
  intro k hk h
  rw [vacLam, Int.cast_eq_zero] at h
  rw [h, Int.natAbs_zero] at hk
  exact Nat.not_lt_zero 1 hk

/-- Two-ray monotone moduli from `max (1 + 1) 1` (`K₀ = 1`). -/
theorem vac_hmono : ∀ n : ℕ, max (1 + 1) 1 ≤ n →
    ‖tailInv 1 vacLam ((n : ℤ) + 1)‖ ≤ ‖tailInv 1 vacLam (n : ℤ)‖ ∧
      ‖tailInv 1 vacLam (-((n : ℤ) + 1))‖ ≤ ‖tailInv 1 vacLam (-(n : ℤ))‖ := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  simp only [vac_norm_tailInv, Int.natAbs_neg, Int.natAbs_natCast,
    show ((n : ℤ) + 1).natAbs = n + 1 by omega,
    ite_eq_right (show ¬ n ≤ 1 by omega), ite_eq_right (show ¬ n + 1 ≤ 1 by omega)]
  constructor <;> apply inv_anti₀ hn0 <;> exact_mod_cast (Nat.le_succ n)

local notation "𝓟ᵣ" => (lpOneAlg.headProj (𝕜 := ℝ) (G := geomFiberZ ℝ vacNu1) (winZ 1))

/-- (c) T32 applies: the raw identification at the tail inverse of the real symbol `k`. -/
theorem vac_c_T32 (a : 𝓔 ℝ vacNu1) :
    lpOneAlg.toRealSeq (precondMap 1 (𝓟ᵣ : 𝓔 ℝ vacNu1 →L[ℝ] 𝓔 ℝ vacNu1) vacLam (tailInv 1 vacLam) (1 / 2)
        vac_tailInv_le 1 (MvPolynomial.X 0 ^ 2) a) =
      rawPrecond 1 𝓟ᵣ (tailInv 1 vacLam) (rawMap vacLam 1 (MvPolynomial.X 0 ^ 2) a) :=
  toRealSeq_precondMap_tailInv 1 𝓟ᵣ vacLam (1 / 2) vac_tailInv_le 1 _ a vac_lam_ne_zero

/-- (c) T33 applies at `K₀ = 1` (band `0` of `β = 2 e₀`). -/
theorem vac_c_T33 :
    ‖(fderiv ℝ (precondMap 1 (𝓟ᵣ : 𝓔 ℝ vacNu1 →L[ℝ] 𝓔 ℝ vacNu1) vacLam (tailInv 1 vacLam) (1 / 2)
          vac_tailInv_le 1 (MvPolynomial.X 0 ^ 2)) (lpOneAlg.single 0 1) -
        modelDeriv 1 𝓟ᵣ vacLam 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1) :
        𝓔 ℝ vacNu1 →L[ℝ] 𝓔 ℝ vacNu1)‖ =
      (winZ (0 + max (1 + 1) 1)).sup' (winZ_nonempty _)
        (fun j => lpOneAlg.colRatio (defect 1 𝓟ᵣ (tailInv 1 vacLam) (1 / 2) vac_tailInv_le
          (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1 : 𝓔 ℝ vacNu1))) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup' 1 0 1 𝓟ᵣ vacLam _ _ _ 1 _ _ vac_beta_band vac_hmono

/-- (c) `DG(e₀) − B₀ ≠ 0` for the real general symbol (witness column `e₂`, `r₂ = 1/2`). -/
theorem vac_c_ne_zero :
    (fderiv ℝ (precondMap 1 (𝓟ᵣ : 𝓔 ℝ vacNu1 →L[ℝ] 𝓔 ℝ vacNu1) vacLam (tailInv 1 vacLam) (1 / 2)
          vac_tailInv_le 1 (MvPolynomial.X 0 ^ 2)) (lpOneAlg.single 0 1) -
        modelDeriv 1 𝓟ᵣ vacLam 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 0 1) :
        𝓔 ℝ vacNu1 →L[ℝ] 𝓔 ℝ vacNu1) ≠ 0 := by
  refine vac_ne_zero 1 _ vacLam _ _ vac_tailInv_le 2 (by decide) (fun h => ?_) two_ne_zero
  have hn := vac_norm_tailInv 2
  rw [h, norm_zero, ite_eq_right (by decide)] at hn
  norm_num at hn

end InstanceC

/-! ### (e) facade resolution -/

#check @RadiiPolynomial.Fourier.Semilinear.precondMap

end RadiiPolynomial.Tests.FZ.Semilinear

end
