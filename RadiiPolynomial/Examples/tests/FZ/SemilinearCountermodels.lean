import RadiiPolynomial.Applications.Fourier.SemilinearFirstOrder

/-!
# FZ semilinear tests: countermodels and boundaries (T57, L005)

The countermodels of the decision-bearing hypotheses of TARGET_SHEET §7, each with the other
hypotheses of its target holding, and the boundaries the semilinear consumer does NOT cross:

* `hlam` of T6; `hr0` of T12, T27 and T31; `hrlam` of T31 and `hlam` of T32 (the S028b
  modified-symbol regression, generalized); `habar`/`hdeg` of T21; `hdeg` of T22; `hd`/`hK` of
  T37; `hk` of T43;
* the band hypothesis `hβ`/`habar` of T33/T35/T36 at the NORM level (`𝕜 = ℂ`, `ν = 1`, `N = 0`,
  `M = P₀`, `r = tailInv 0 ikSymbol`, `Φ = (1/2) X₀²`, `ā = e₋₅`): `‖DG(ā) − B₀‖ ≥ 1` while every
  column ratio of the window `|j| ≤ 1` is at most `1/4`;
* the LAYER-5 BOUNDARY and `hmono` of T33 (`𝕜 = ℝ`, `ν = 1`, `N = 1`, `M = 0`,
  `lam k = k − 19/2`, `r = tailInv 1 lam`, `C = 2`, `Φ = X₀`): `‖r‖` is two-ray nonincreasing
  from `K₀ = 9` but not from `K₀ = 1` (`|r₃| > |r₂|`); `‖DG(ā) − B₀‖ = 2` (the window
  `0 + max 2 9 = 9` of T33 is correct), while the first-tail window `N + B + 1 = 2` gives `2/15`
  and the first-tail bound `1/(N + 1) = 1/2 < 2`: neither the S028b window nor its bound transfers
  to a general symbol;
* the LAYER-3 BOUNDARY: tail nonvanishing alone does not give a bounded tail inverse
  (`lam k = k⁻¹`);
* the first-order T50 `hPM` countermodel (Codex CHANGES A3 on L005 contract/v1): `ν = 1`, `N = 0`,
  `m = 1`, `τ = 1`, `Φ = (1/2) X₀²`, `ā = e₋₁ + e₀` (`β = ā`), `M a = i a₀ e₁`,
  `r = tailInv 0 ikSymbol`: `hβ` and the first-order diagonal hypotheses hold, `P₀ M ≠ M`, the
  column `j = 1` cancels, `‖DG(ā) − B₀‖ = 3/2` while the explicit separated maximum over `|j| ≤ 2`
  is `2` — at the `DG − B₀` level;
* the R6 BOUNDARY (FS:562–:591 restated over the new carrier names: `deltaAtom`, `dΨ`,
  `R6_leak`, `R6_not_multiplication`): with `δ e_k = k e_k` on atoms and `Ψ(a) = (δ a)²`, the
  directional derivative at `ā = e₋₁` on atoms is not multiplication by any fixed `c`, and it leaks
  `P₀ DΨ(ā) Q₀ e₁ = −2 e₀`: the multiplication form of T20, on which T25–T28 rest, fails once a
  derivative sits inside the nonlinearity.

The cited general-diagonal `hPM`/`hr0` regressions of T34 are the installed L002 tests
`RadiiPolynomial.Tests.FZ.TailWindow.G1'_explicit_fails` and `…G1''_explicit_fails`
(`Examples/tests/FZ/TailWindowCountermodels.lean`); T26 transports them to `DG − B₀`. The literal
weight `ν = 1` is `cmNu1` with a LOCAL `Fact (1 ≤ ν)` instance. The carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` (local notation).
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.Semilinear

open RadiiPolynomial.Fourier RadiiPolynomial.Fourier.Semilinear

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)

/-! ### Shared helpers -/

section Helpers

/-- The literal weight `ν = 1`. -/
def cmNu1 : PosReal := ⟨1, one_pos⟩

/-- `ν = 1 ≥ 1` (a LOCAL instance below). -/
theorem cmNu1_fact : Fact (1 ≤ ((cmNu1 : PosReal) : ℝ)) := ⟨le_rfl⟩

attribute [local instance] cmNu1_fact

theorem cmNu1_pow (n : ℕ) : ((cmNu1 : PosReal) : ℝ) ^ n = 1 := one_pow n

variable {𝕜 : Type*} [NormedField 𝕜]

theorem cm_norm_single (j : ℤ) (x : 𝕜) : ‖(lpOneAlg.single j x : 𝓔 𝕜 cmNu1)‖ = ‖x‖ := by
  rw [lpOneAlg.norm_single, geomFiberZ_weight, cmNu1_pow, mul_one]

theorem cm_single_ne_zero (j : ℤ) : (lpOneAlg.single j (1 : 𝕜) : 𝓔 𝕜 cmNu1) ≠ 0 := by
  intro h
  have := cm_norm_single (𝕜 := 𝕜) j 1
  rw [h, norm_zero, norm_one] at this
  exact zero_ne_one this

/-- The norm of two atoms at distinct indices is the sum of their norms (`ν = 1`). -/
theorem cm_norm_single_add_single (i j : ℤ) (hij : i ≠ j) (x y : 𝕜) :
    ‖(lpOneAlg.single i x + lpOneAlg.single j y : 𝓔 𝕜 cmNu1)‖ = ‖x‖ + ‖y‖ := by
  have h0 : ∀ k ∉ ({i, j} : Finset ℤ),
      ‖lpOneAlg.toRealSeq (lpOneAlg.single i x + lpOneAlg.single j y : 𝓔 𝕜 cmNu1) k‖ *
        ((cmNu1 : PosReal) : ℝ) ^ k.natAbs = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [lpOneAlg.toRealSeq_add, lpOneAlg.toRealSeq_single, hk.1, hk.2]
  rw [norm_eq_tsum_coeff, tsum_eq_sum h0, Finset.sum_pair hij]
  simp [lpOneAlg.toRealSeq_add, lpOneAlg.toRealSeq_single, hij, hij.symm, cmNu1_pow]

theorem cm_mem0 : (0 : ℤ) ∈ winZ 0 := mem_winZ.mpr (by decide)

theorem cm_norm_add_le (u v : 𝓔 𝕜 cmNu1) (a b : ℝ) (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) :
    ‖u + v‖ ≤ a + b :=
  (norm_add_le u v).trans (add_le_add hu hv)

end Helpers

attribute [local instance] cmNu1_fact

/-! ### Polynomial helpers -/

section Poly

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

theorem cm_beta_X (a : 𝓔 𝕜 ν) : beta 1 (MvPolynomial.X 0 : MvPolynomial (Fin 1) 𝕜) a = 1 := by
  simp [beta, phiHatDeriv]

theorem cm_phiHat_X (a : 𝓔 𝕜 ν) : phiHat (MvPolynomial.X 0 : MvPolynomial (Fin 1) 𝕜) a = a := by
  simp [phiHat]

theorem cm_phiHatDeriv_square (a : 𝓔 𝕜 ν) :
    phiHatDeriv (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) 𝕜) a = (2 : 𝕜) • a := by
  simp only [phiHatDeriv, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
    Nat.reduceSub, pow_one, mul_one, map_mul, map_natCast, MvPolynomial.aeval_X]
  rw [Algebra.smul_def, map_ofNat]
  norm_num only []

end Poly

section PolyC

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- `Φ = (1/2) X₀²`. -/
def cmPhiHalf : MvPolynomial (Fin 1) ℂ := (1 / 2 : ℂ) • MvPolynomial.X 0 ^ 2

/-- `β = τ Φ̂′(a) = a` at `τ = 1`, `Φ = (1/2) X₀²`. -/
theorem cm_beta_half (a : 𝓔 ℂ ν) : beta 1 cmPhiHalf a = a := by
  rw [beta, one_smul, phiHatDeriv, cmPhiHalf, Derivation.map_smul, map_smul, ← phiHatDeriv,
    cm_phiHatDeriv_square, smul_smul]
  norm_num

theorem cm_deg_half : (MvPolynomial.pderiv 0 cmPhiHalf).totalDegree ≤ 2 - 1 := by
  rw [cmPhiHalf, Derivation.map_smul]
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  simp only [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, Nat.reduceSub, pow_one, mul_one]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [← map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 1) ℂ) 2,
    MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

end PolyC

/-! ### T6 `hlam` -/

section T6

/-- T6 `hlam` decisive: `lam = 0`, `N = 0`, `k = 1`. -/
theorem cm_T6_hlam_fails : ¬ ∀ k : ℤ, 0 < k.natAbs → (0 : ℤ → ℝ) k ≠ 0 :=
  fun h => h 1 (by decide) rfl

theorem cm_T6 : ¬ ∀ k : ℤ, 0 < k.natAbs → tailInv 0 (0 : ℤ → ℝ) k * (0 : ℤ → ℝ) k = 1 := by
  intro h
  have h1 := h 1 (by decide)
  rw [Pi.zero_apply, mul_zero] at h1
  exact zero_ne_one h1

end T6

/-! ### T12 `hr0` -/

section T12

theorem cm_norm_one_le : ∀ k : ℤ, ‖(fun _ : ℤ => (1 : ℝ)) k‖ ≤ 1 := fun _ => by simp

theorem cm_one_hr0_fails : ¬ ∀ k : ℤ, k.natAbs ≤ 0 → (fun _ : ℤ => (1 : ℝ)) k = 0 :=
  fun h => one_ne_zero (h 0 le_rfl)

/-- T12 `hr0` decisive: `D_1 P_0 e₀ = e₀ ≠ 0`. -/
theorem cm_T12 :
    (lpOneAlg.diagCLM (G := geomFiberZ ℝ cmNu1) (fun _ : ℤ => (1 : ℝ)) 1 cm_norm_one_le :
        𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) ∘L
      (lpOneAlg.headProj (𝕜 := ℝ) (G := geomFiberZ ℝ cmNu1) (winZ 0) : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.headProj_single, ite_eq_left cm_mem0,
    lpOneAlg.diagCLM_single, mul_one, zero_apply] at h1
  exact cm_single_ne_zero 0 h1

end T12

/-! ### T27 `hr0` -/

section T27

local notation "𝓟₀" =>
  (lpOneAlg.headProj (𝕜 := ℝ) (G := geomFiberZ ℝ cmNu1) (winZ 0) : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)
local notation "𝓓₁" => (lpOneAlg.diagCLM (G := geomFiberZ ℝ cmNu1) (fun _ : ℤ => (1 : ℝ)) 1
  cm_norm_one_le : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)

/-- T27 `hr0` decisive (`N = 0`, `M = 0`, `lam = 0`, `r = 1`, `τ = 1`, `Φ = X₀`, `β = 1`): the
transport form fails, `−e₀` on the left and `0` on the right at `e₀`. -/
theorem cm_T27 :
    (fderiv ℝ (precondMap 0 0 (0 : ℤ → ℝ) (fun _ : ℤ => (1 : ℝ)) 1 cm_norm_one_le 1 (MvPolynomial.X 0))
        (0 : 𝓔 ℝ cmNu1) - modelDeriv 0 0 (0 : ℤ → ℝ) 1 (MvPolynomial.X 0) 0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) ≠
      (-1 : ℝ) • (((0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) ∘L 𝓟₀ + 𝓓₁) ∘L
        (𝓟₀ ∘L (lpOneAlg.mulLeftCLM (𝕜 := ℝ) (beta 1 (MvPolynomial.X 0) (0 : 𝓔 ℝ cmNu1)) :
            𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) ∘L (1 - 𝓟₀) +
          (1 - 𝓟₀) ∘L (lpOneAlg.mulLeftCLM (𝕜 := ℝ) (beta 1 (MvPolynomial.X 0) (0 : 𝓔 ℝ cmNu1)) :
            𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1))) := by
  intro h
  have h1 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  have hP : 𝓟₀ (lpOneAlg.single 0 1) = lpOneAlg.single 0 1 := by
    rw [lpOneAlg.headProj_single, ite_eq_left cm_mem0]
  have hQ : ((1 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) - 𝓟₀) (lpOneAlg.single 0 1) = 0 := by
    rw [sub_apply, one_apply_eq_self, hP, sub_self]
  rw [fderiv_sub_modelDeriv, neg_apply, defect_eq, add_apply, defectHead_single,
    ite_eq_left (by decide : (0 : ℤ).natAbs ≤ 0), zero_add, defectTail_single, cm_beta_X, one_mul,
    lpOneAlg.diagCLM_single, mul_one] at h1
  simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply, lpOneAlg.mulLeftCLM_apply,
    one_mul, hQ, map_zero, zero_add] at h1
  rw [smul_zero, neg_eq_zero] at h1
  exact cm_single_ne_zero 0 h1

end T27

/-! ### T31 `hr0`; T31 `hrlam` and T32 `hlam` -/

section T31

/-- T31 `hr0` decisive (`N = 0`, `M = 0`, `lam = 1`, `r = 1`, `τ = 1`, `Φ = X₀`, `a = e₀`):
`hrlam` holds, the coefficient of `G(a)` at `0` is `−1`, the raw preconditioner gives `0`. -/
theorem cm_T31_hrlam_holds :
    ∀ k : ℤ, 0 < k.natAbs → (fun _ : ℤ => (1 : ℝ)) k * (fun _ : ℤ => (1 : ℝ)) k = 1 :=
  fun _ _ => mul_one 1

theorem cm_T31_hr0 :
    lpOneAlg.toRealSeq (precondMap 0 0 (fun _ : ℤ => (1 : ℝ)) (fun _ : ℤ => (1 : ℝ)) 1 cm_norm_one_le 1
        (MvPolynomial.X 0) (lpOneAlg.single 0 1 : 𝓔 ℝ cmNu1)) ≠
      rawPrecond 0 (0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) (fun _ : ℤ => (1 : ℝ)) (rawMap (fun _ : ℤ => (1 : ℝ)) 1 (MvPolynomial.X 0)
        (lpOneAlg.single 0 1 : 𝓔 ℝ cmNu1)) := by
  intro h
  have h0 := congr_fun h 0
  simp only [precondMap, rawPrecond, cm_phiHat_X, zero_apply, zero_add, lpOneAlg.tailProj_single,
    cm_mem0, ↓reduceIte, lpOneAlg.diagCLM_single, one_smul,
    lpOneAlg.toRealSeq_sub, lpOneAlg.toRealSeq_zero, Pi.sub_apply, Pi.zero_apply,
    lpOneAlg.toRealSeq_single, mul_one] at h0
  norm_num at h0

/-- The modified symbol `lam k = k − 1` (`lam 1 = 0`). -/
def cmLamShift (k : ℤ) : ℝ := (k : ℝ) - 1

theorem cm_tailInv_shift_le : ∀ k : ℤ, ‖tailInv 0 cmLamShift k‖ ≤ 1 := by
  intro k
  unfold tailInv
  split_ifs with hk
  · simp
  · rw [norm_inv]
    rcases eq_or_ne k 1 with rfl | hk1
    · simp [cmLamShift]
    · apply inv_le_one_of_one_le₀
      have hne : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
      rw [cmLamShift, show (k : ℝ) - 1 = ((k - 1 : ℤ) : ℝ) by push_cast; ring, Real.norm_eq_abs,
        ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne

/-- T32 `hlam` fails (`lam 1 = 0`). -/
theorem cm_T32_hlam_fails : ¬ ∀ k : ℤ, 0 < k.natAbs → cmLamShift k ≠ 0 :=
  fun h => h 1 (by decide) (by simp [cmLamShift])

/-- T31 `hrlam` fails at `r = tailInv 0 lam`. -/
theorem cm_T31_hrlam_fails : ¬ ∀ k : ℤ, 0 < k.natAbs → tailInv 0 cmLamShift k * cmLamShift k = 1 := by
  intro h
  have h1 := h 1 (by decide)
  rw [show cmLamShift 1 = 0 by simp [cmLamShift], mul_zero] at h1
  exact zero_ne_one h1

/-- T31 `hrlam` / T32 `hlam` decisive (the S028b modified-symbol regression, generalized):
`N = 0`, `M = 0`, `lam k = k − 1`, `r = tailInv 0 lam` (`C = 1`, `hr0` holds), `τ = 0`, `a = e₁`:
the coefficient of `G(a)` at `1` is `1`, the raw preconditioner gives `r₁ lam₁ a₁ = 0`. -/
theorem cm_T32 :
    lpOneAlg.toRealSeq (precondMap 0 0 cmLamShift (tailInv 0 cmLamShift) 1 cm_tailInv_shift_le 0
        (MvPolynomial.X 0) (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1)) ≠
      rawPrecond 0 (0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) (tailInv 0 cmLamShift) (rawMap cmLamShift 0 (MvPolynomial.X 0)
        (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1)) := by
  intro h
  have h1 := congr_fun h 1
  have hw : (1 : ℤ) ∉ winZ 0 := fun hm => by rw [mem_winZ] at hm; exact absurd hm (by decide)
  simp only [precondMap, rawPrecond, rawMap, zero_apply, zero_add, zero_smul, sub_zero,
    lpOneAlg.tailProj_single, ite_eq_right hw, lpOneAlg.toRealSeq_zero, Pi.zero_apply,
    lpOneAlg.toRealSeq_single, ite_true, zero_mul, cmLamShift] at h1
  norm_num at h1

end T31

/-! ### The layer-3 boundary -/

section Layer3

/-- The symbol `lam k = k⁻¹`: nonvanishing on the tail, with an unbounded tail inverse. -/
def cmLamInv (k : ℤ) : ℝ := (k : ℝ)⁻¹

theorem cm_L3_nonvanishing : ∀ k : ℤ, 0 < k.natAbs → cmLamInv k ≠ 0 := by
  intro k hk
  rw [cmLamInv]
  exact inv_ne_zero (by exact_mod_cast (show k ≠ 0 by omega))

/-- LAYER-3 BOUNDARY (DOES NOT SAY): tail nonvanishing alone does not bound the tail inverse. -/
theorem cm_L3_unbounded : ¬ ∃ C : ℝ, ∀ k, ‖tailInv 0 cmLamInv k‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC ((n : ℤ) + 1)
  rw [tailInv, ite_eq_right (fun hm => by rw [mem_winZ] at hm; omega), cmLamInv, inv_inv,
    Real.norm_eq_abs] at h
  push_cast at h
  rw [abs_of_pos (by positivity)] at h
  linarith

end Layer3

/-! ### `hβ` / `habar` of T33/T35/T36 at the norm level -/

section Band

local notation "𝓟₀" =>
  (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ cmNu1) (winZ 0) : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)
local notation "𝓖b" => (precondMap 0 𝓟₀ ikSymbol (tailInv 0 ikSymbol) (1 / (((0 : ℕ) : ℝ) + 1))
  (norm_tailInv_ikSymbol_le 0) 1 cmPhiHalf : 𝓔 ℂ cmNu1 → 𝓔 ℂ cmNu1)
local notation "𝓑b" => (modelDeriv 0 𝓟₀ ikSymbol 1 cmPhiHalf (lpOneAlg.single (-5) 1 : 𝓔 ℂ cmNu1) :
  𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)
local notation "𝓓b" => (defect 0 𝓟₀ (tailInv 0 ikSymbol) (1 / (((0 : ℕ) : ℝ) + 1))
  (norm_tailInv_ikSymbol_le 0) (beta 1 cmPhiHalf (lpOneAlg.single (-5) 1 : 𝓔 ℂ cmNu1)) :
  𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)

theorem cmB_mul (j : ℤ) :
    (lpOneAlg.single (-5) 1 : 𝓔 ℂ cmNu1) * lpOneAlg.single j 1 = lpOneAlg.single (j - 5) 1 := by
  rw [lpOneAlg.single_mul_single, mul_one, show (-5 : ℤ) + j = j - 5 by ring]

/-- The columns of the defect: `D e_j = 1_{j ≠ 0} P₀ P₀ e_{j−5} + r_{j−5} e_{j−5}`. -/
theorem cmB_col (j : ℤ) :
    𝓓b (lpOneAlg.single j 1) = (if j.natAbs ≤ 0 then 0 else 𝓟₀ (𝓟₀ (lpOneAlg.single (j - 5) 1))) +
      lpOneAlg.single (j - 5) (tailInv 0 ikSymbol (j - 5) * 1) := by
  rw [defect_eq, add_apply, defectHead_single, defectTail_single, cm_beta_half, cmB_mul,
    lpOneAlg.diagCLM_single]

/-- The column `j = 5`: `D e₅ = e₀`. -/
theorem cmB_col5 : 𝓓b (lpOneAlg.single 5 1) = lpOneAlg.single 0 1 := by
  rw [cmB_col, ite_eq_right (by decide), show (5 : ℤ) - 5 = 0 by norm_num,
    tailInv_head_zero 0 ikSymbol 0 le_rfl, zero_mul, lpOneAlg.headProj_single,
    ite_eq_left cm_mem0, lpOneAlg.headProj_single, ite_eq_left cm_mem0]
  rw [lpOneAlg.single_smul 0 (0 : ℂ), zero_smul, add_zero]

/-- `‖DG(ā) − B₀‖ ≥ 1` (the column `j = 5`). -/
theorem cmB_norm_ge : 1 ≤ ‖(fderiv ℂ 𝓖b (lpOneAlg.single (-5) 1) - 𝓑b : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ := by
  rw [norm_fderiv_sub_modelDeriv]
  have h := lpOneAlg.colRatio_le_opNorm 𝓓b 5
  rwa [colRatio_geom, cmB_col5, cm_norm_single, norm_one, cmNu1_pow, div_one] at h

/-- Every column ratio of the window `|j| ≤ 1` is at most `1/4`. -/
theorem cmB_col_le (j : ℤ) (hj : j.natAbs ≤ 1) : lpOneAlg.colRatio 𝓓b j ≤ 1 / 4 := by
  have hP : 𝓟₀ (lpOneAlg.single (j - 5) 1) = 0 := by
    rw [lpOneAlg.headProj_single, ite_eq_right (fun h => by rw [mem_winZ] at h; omega)]
  rw [colRatio_geom, cmB_col, hP, map_zero, ite_self, zero_add, cm_norm_single, cmNu1_pow, div_one,
    mul_one, norm_tailInv_ikSymbol, ite_eq_right (by omega), one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast (show 4 ≤ (j - 5).natAbs by omega))

theorem cmB_sup_le (W : ℕ) (hW : W ≤ 1) :
    (winZ W).sup' (winZ_nonempty W) (fun j => lpOneAlg.colRatio 𝓓b j) ≤ 1 / 4 :=
  Finset.sup'_le _ _ fun j hj => cmB_col_le j (by rw [mem_winZ] at hj; omega)

/-- `hβ` fails (`β = e₋₅` has band `5`, not `0`); `habar` fails likewise. -/
theorem cmB_hβ_fails :
    ¬ ∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (beta 1 cmPhiHalf (lpOneAlg.single (-5) 1 : 𝓔 ℂ cmNu1)) i = 0 := by
  intro h
  have h5 := h (-5) (by decide)
  rw [cm_beta_half, lpOneAlg.toRealSeq_single, ite_eq_left rfl] at h5
  exact one_ne_zero h5

/-- The other hypotheses of T33/T35/T36 hold (`hmono` from `K₀ = 1`; `hdeg` at `d = 2`). -/
theorem cmB_other_hyps :
    (∀ n : ℕ, max (0 + 1) 1 ≤ n →
      ‖tailInv 0 ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv 0 ikSymbol (n : ℤ)‖ ∧
        ‖tailInv 0 ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv 0 ikSymbol (-(n : ℤ))‖) ∧
    (MvPolynomial.pderiv 0 cmPhiHalf).totalDegree ≤ 2 - 1 :=
  ⟨tailInv_ikSymbol_hmono 0, cm_deg_half⟩

/-- T33 `hβ` decisive at the norm level: the window formula fails. -/
theorem cmB_T33 :
    ‖(fderiv ℂ 𝓖b (lpOneAlg.single (-5) 1) - 𝓑b : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ ≠
      (winZ (0 + max (0 + 1) 1)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio 𝓓b j) := by
  intro h
  have := cmB_sup_le (0 + max (0 + 1) 1) (by decide)
  have := cmB_norm_ge
  linarith

/-- T36 `habar` decisive at the norm level (`d = 2`; `hdeg` holds): the degree window formula
fails. -/
theorem cmB_T36 :
    ‖(fderiv ℂ 𝓖b (lpOneAlg.single (-5) 1) - 𝓑b : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ ≠
      (winZ ((2 - 1) * 0 + max (0 + 1) 1)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio 𝓓b j) := by
  intro h
  have := cmB_sup_le ((2 - 1) * 0 + max (0 + 1) 1) (by decide)
  have := cmB_norm_ge
  linarith

/-- T35 `hβ` decisive: no atom of the window `|j| ≤ 1` attains the norm. -/
theorem cmB_T35 :
    ¬ ∃ j ∈ winZ (0 + max (0 + 1) 1),
      ‖(fderiv ℂ 𝓖b (lpOneAlg.single (-5) 1) - 𝓑b : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1) (lpOneAlg.single j 1)‖ =
        ‖(fderiv ℂ 𝓖b (lpOneAlg.single (-5) 1) - 𝓑b : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ *
          ((cmNu1 : PosReal) : ℝ) ^ j.natAbs := by
  rintro ⟨j, hj, h⟩
  have hc := cmB_col_le j (by rw [mem_winZ] at hj; omega)
  rw [colRatio_geom, cmNu1_pow, div_one] at hc
  rw [fderiv_sub_modelDeriv, neg_apply, norm_neg, norm_neg, cmNu1_pow, mul_one] at h
  have hn := cmB_norm_ge
  rw [norm_fderiv_sub_modelDeriv] at hn
  linarith

end Band

/-! ### The layer-5 boundary and `hmono` of T33 -/

section Layer5

/-- The symbol `lam k = k − 19/2`. -/
def cmLam5 (k : ℤ) : ℝ := (k : ℝ) - 19 / 2

theorem cmL5_half_le (k : ℤ) : 1 / 2 ≤ |cmLam5 k| := by
  rw [cmLam5]
  rcases le_or_gt k 9 with hk | hk
  · have : (k : ℝ) ≤ 9 := by exact_mod_cast hk
    exact le_abs.mpr (Or.inr (by linarith))
  · have : (10 : ℝ) ≤ k := by exact_mod_cast hk
    exact le_abs.mpr (Or.inl (by linarith))

theorem cmL5_norm (k : ℤ) (hk : 1 < k.natAbs) : ‖tailInv 1 cmLam5 k‖ = |cmLam5 k|⁻¹ := by
  rw [tailInv, ite_eq_right (fun h => by rw [mem_winZ] at h; omega), norm_inv, Real.norm_eq_abs]

theorem cmL5_head (k : ℤ) (hk : k.natAbs ≤ 1) : tailInv 1 cmLam5 k = 0 :=
  tailInv_head_zero 1 cmLam5 k hk

/-- The uniform bound `C = 2`. -/
theorem cmL5_le : ∀ k, ‖tailInv 1 cmLam5 k‖ ≤ 2 := by
  intro k
  by_cases hk : k.natAbs ≤ 1
  · rw [cmL5_head k hk, norm_zero]; norm_num
  · rw [cmL5_norm k (by omega)]
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (cmL5_half_le k)
    norm_num at h ⊢
    exact h

/-- `hmono` fails from `K₀ = 1` (`|r₃| = 2/13 > |r₂| = 2/15`). -/
theorem cmL5_hmono_fails :
    ¬ ∀ n : ℕ, max (1 + 1) 1 ≤ n →
      ‖tailInv 1 cmLam5 ((n : ℤ) + 1)‖ ≤ ‖tailInv 1 cmLam5 (n : ℤ)‖ ∧
        ‖tailInv 1 cmLam5 (-((n : ℤ) + 1))‖ ≤ ‖tailInv 1 cmLam5 (-(n : ℤ))‖ := by
  intro h
  have h2 := (h 2 (by decide)).1
  rw [cmL5_norm _ (by decide), cmL5_norm _ (by decide), cmLam5, cmLam5] at h2
  norm_num [abs_of_neg] at h2

/-- `hmono` holds from `K₀ = 9`. -/
theorem cmL5_hmono : ∀ n : ℕ, max (1 + 1) 9 ≤ n →
    ‖tailInv 1 cmLam5 ((n : ℤ) + 1)‖ ≤ ‖tailInv 1 cmLam5 (n : ℤ)‖ ∧
      ‖tailInv 1 cmLam5 (-((n : ℤ) + 1))‖ ≤ ‖tailInv 1 cmLam5 (-(n : ℤ))‖ := by
  intro n hn
  have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hne : (n : ℝ) - 19 / 2 ≠ 0 := fun h => by
    have h2 : ((2 * n : ℕ) : ℝ) = 19 := by push_cast; linarith
    have h3 : 2 * n = 19 := by exact_mod_cast h2
    omega
  rw [cmL5_norm _ (by omega), cmL5_norm _ (by omega), cmL5_norm _ (by omega),
    cmL5_norm _ (by omega), cmLam5, cmLam5, cmLam5, cmLam5]
  push_cast
  constructor
  · apply inv_anti₀ (abs_pos.mpr hne)
    rw [abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 - 19 / 2 by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · apply inv_anti₀ (abs_pos.mpr (ne_of_lt (by linarith)))
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith

/-- The first-tail bound `1/(N + 1) = 1/2` is exceeded (`|r₉| = 2`). -/
theorem cmL5_r9 : ‖tailInv 1 cmLam5 9‖ = 2 := by
  rw [cmL5_norm 9 (by decide), cmLam5]
  norm_num [abs_of_neg]

theorem cmL5_exceeds_first_tail : ¬ ∀ k, ‖tailInv 1 cmLam5 k‖ ≤ 1 / (((1 : ℕ) : ℝ) + 1) := by
  intro h
  have := h 9
  rw [cmL5_r9] at this
  norm_num at this

local notation "𝓖5" => (precondMap 1 (0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) cmLam5 (tailInv 1 cmLam5) 2 cmL5_le 1
  (MvPolynomial.X 0) : 𝓔 ℝ cmNu1 → 𝓔 ℝ cmNu1)
local notation "𝓑5" => (modelDeriv 1 (0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) cmLam5 1 (MvPolynomial.X 0)
  (0 : 𝓔 ℝ cmNu1) : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)
local notation "𝓓5" => (defect 1 (0 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1) (tailInv 1 cmLam5) 2 cmL5_le
  (beta 1 (MvPolynomial.X 0) (0 : 𝓔 ℝ cmNu1)) : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)

/-- The columns of the defect: `D e_j = r_j e_j` (`M = 0`, `β = 1`). -/
theorem cmL5_col (j : ℤ) : 𝓓5 (lpOneAlg.single j 1) = lpOneAlg.single j (tailInv 1 cmLam5 j * 1) := by
  rw [defect_eq, add_apply, defectHead_single, defectTail_single, cm_beta_X, one_mul,
    lpOneAlg.diagCLM_single]
  split_ifs <;> simp

theorem cmL5_colRatio (j : ℤ) : lpOneAlg.colRatio 𝓓5 j = ‖tailInv 1 cmLam5 j‖ := by
  rw [colRatio_geom, cmL5_col, cm_norm_single, cmNu1_pow, div_one, mul_one]

theorem cmL5_band : ∀ i : ℤ, 0 < i.natAbs →
    lpOneAlg.toRealSeq (beta 1 (MvPolynomial.X 0) (0 : 𝓔 ℝ cmNu1)) i = 0 := by
  rw [cm_beta_X]
  exact band_one

/-- `‖DG(ā) − B₀‖ = 2` (= `‖D_r‖`, attained at `k = 9`). -/
theorem cmL5_norm_eq : ‖(fderiv ℝ 𝓖5 0 - 𝓑5 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)‖ = 2 := by
  apply le_antisymm
  · refine (norm_fderiv_sub_modelDeriv_le_gamma 1 0 cmLam5 (tailInv 1 cmLam5) 2 cmL5_le 1
      (MvPolynomial.X 0) 0).trans ?_
    rw [cm_beta_X, ContinuousLinearMap.zero_comp, norm_zero, zero_add, lpOneAlg.one_eq_single_zero,
      cm_norm_single, norm_one, mul_one]
  · rw [norm_fderiv_sub_modelDeriv]
    have h := lpOneAlg.colRatio_le_opNorm 𝓓5 9
    rwa [cmL5_colRatio, cmL5_r9] at h

/-- T33 applies at `K₀ = 9` (window `0 + max 2 9 = 9`). -/
theorem cmL5_T33_K9 :
    ‖(fderiv ℝ 𝓖5 0 - 𝓑5 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)‖ =
      (winZ (0 + max (1 + 1) 9)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio 𝓓5 j) :=
  norm_fderiv_sub_modelDeriv_eq_sup' 1 0 9 0 cmLam5 _ _ _ 1 _ _ cmL5_band cmL5_hmono

/-- The first-tail window `N + B + 1 = 2` gives `2/15`. -/
theorem cmL5_first_window :
    (winZ (0 + max (1 + 1) 1)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio 𝓓5 j) = 2 / 15 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j hj => ?_
    rw [mem_winZ] at hj
    rw [cmL5_colRatio]
    by_cases h1 : j.natAbs ≤ 1
    · rw [cmL5_head j h1, norm_zero]; norm_num
    · rw [cmL5_norm j (by omega), cmLam5]
      have hj2 : j = 2 ∨ j = -2 := by omega
      rcases hj2 with rfl | rfl <;> norm_num [abs_of_neg]
  · have h := Finset.le_sup' (fun j => lpOneAlg.colRatio 𝓓5 j)
      (mem_winZ.mpr (show (2 : ℤ).natAbs ≤ 0 + max (1 + 1) 1 by decide))
    refine le_of_eq_of_le ?_ h
    rw [cmL5_colRatio, cmL5_norm 2 (by decide), cmLam5]
    norm_num [abs_of_neg]

/-- `hmono` decisive and the LAYER-5 BOUNDARY: at `K₀ = 1` (the first-order value, where
`hmono` fails) the window formula of T33 is false: `2 ≠ 2/15`. -/
theorem cmL5_T33_K1_fails :
    ‖(fderiv ℝ 𝓖5 0 - 𝓑5 : 𝓔 ℝ cmNu1 →L[ℝ] 𝓔 ℝ cmNu1)‖ ≠
      (winZ (0 + max (1 + 1) 1)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio 𝓓5 j) := by
  rw [cmL5_norm_eq, cmL5_first_window]
  norm_num

end Layer5

/-! ### T21 `habar` / `hdeg`, T22 `hdeg` -/

section Band21

/-- T21 `habar` decisive: `N = 1`, `e = 1`, `q = X₀`, `ā = e₂` (`hdeg` holds). -/
theorem cm_T21_habar :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (¬ ∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (lpOneAlg.single 2 1 : 𝓔 ℝ cmNu1) i = 0) ∧
    ¬ ∀ k : ℤ, 1 * 1 < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => (lpOneAlg.single 2 1 : 𝓔 ℝ cmNu1))
        (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) k = 0 := by
  refine ⟨(MvPolynomial.totalDegree_X _).le, fun h => ?_, fun h => ?_⟩
  · have h2 := h 2 (by decide)
    rw [lpOneAlg.toRealSeq_single, ite_eq_left rfl] at h2
    exact one_ne_zero h2
  · have h2 := h 2 (by decide)
    rw [MvPolynomial.aeval_X, lpOneAlg.toRealSeq_single, ite_eq_left rfl] at h2
    exact one_ne_zero h2

/-- T21 `hdeg` decisive: `N = 1`, `e = 0`, `q = X₀`, `ā = e₁` (`habar` holds; `hdeg` fails, as
T21 itself would otherwise kill the coefficient at `1`). -/
theorem cm_T21_hdeg :
    (∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1) i = 0) ∧
    ¬ (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 0 ∧
    ¬ ∀ k : ℤ, 0 * 1 < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1))
        (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) k = 0 := by
  have hc : ¬ ∀ k : ℤ, 0 * 1 < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1))
        (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) k = 0 := by
    intro h
    have h1 := h 1 (by decide)
    rw [MvPolynomial.aeval_X, lpOneAlg.toRealSeq_single, ite_eq_left rfl] at h1
    exact one_ne_zero h1
  refine ⟨band_single 1 1 (1 : ℝ) (by decide), fun hdeg => hc ?_, hc⟩
  exact band_aeval 1 0 _ (band_single 1 1 (1 : ℝ) (by decide)) _ hdeg

/-- T22 `hdeg` decisive: `N = 1`, `d = 1`, `Φ = X₀²`, `τ = 1`, `ā = e₁` (`β = 2 e₁`; `habar`
holds; `hdeg` fails). -/
theorem cm_T22_hdeg :
    ¬ (MvPolynomial.pderiv 0 (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℝ)).totalDegree ≤ 1 - 1 ∧
    ¬ ∀ i : ℤ, (1 - 1) * 1 < i.natAbs →
      lpOneAlg.toRealSeq (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1)) i = 0 := by
  have hc : ¬ ∀ i : ℤ, (1 - 1) * 1 < i.natAbs →
      lpOneAlg.toRealSeq (beta 1 (MvPolynomial.X 0 ^ 2) (lpOneAlg.single 1 1 : 𝓔 ℝ cmNu1)) i = 0 := by
    intro h
    have h1 := h 1 (by decide)
    rw [beta, one_smul, cm_phiHatDeriv_square, lpOneAlg.toRealSeq_smul, Pi.smul_apply,
      lpOneAlg.toRealSeq_single, ite_eq_left rfl, smul_eq_mul, mul_one] at h1
    exact two_ne_zero h1
  exact ⟨fun hdeg => hc (band_beta 1 1 1 _ _ (band_single 1 1 (1 : ℝ) (by decide)) hdeg), hc⟩

end Band21

/-! ### T37 `hd` / `hK`, T43 `hk` -/

section Arith

/-- T37 `hd` decisive: `d = 0`, `N = 1`, `K₀ = 0` (`hK` holds). -/
theorem cm_T37_hd : (0 : ℕ) ≤ 1 + 1 ∧ (0 - 1) * 1 + max (1 + 1) 0 ≠ 0 * 1 + 1 := by decide

/-- T37 `hK` decisive: `d = 1`, `N = 1`, `K₀ = 3` (`hd` holds). -/
theorem cm_T37_hK : 1 ≤ (1 : ℕ) ∧ (1 - 1) * 1 + max (1 + 1) 3 ≠ 1 * 1 + 1 := by decide

/-- T43 `hk` decisive: `ikSymbol 0 = 0`. -/
theorem cm_T43_hk : ikSymbol 0 = 0 := by
  rw [ikSymbol, Int.cast_zero, mul_zero]

end Arith

/-! ### The first-order T50 `hPM` countermodel (Codex CHANGES A3) -/

section T50

local notation "𝓟₀" =>
  (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ cmNu1) (winZ 0) : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)

/-- `M a = i a₀ e₁` (`M = L_{i e₁} P₀`). -/
def cmM50 : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1 :=
  (lpOneAlg.mulLeftCLM (𝕜 := ℂ) (lpOneAlg.single 1 Complex.I) : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1) ∘L 𝓟₀

/-- `ā = e₋₁ + e₀`. -/
def cmA50 : 𝓔 ℂ cmNu1 := lpOneAlg.single (-1) 1 + lpOneAlg.single 0 1

local notation "𝓖50" => (precondMap 0 cmM50 ikSymbol (tailInv 0 ikSymbol) (1 / (((0 : ℕ) : ℝ) + 1))
  (norm_tailInv_ikSymbol_le 0) 1 cmPhiHalf : 𝓔 ℂ cmNu1 → 𝓔 ℂ cmNu1)
local notation "𝓑50" => (modelDeriv 0 cmM50 ikSymbol 1 cmPhiHalf cmA50 : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)
local notation "𝓓50" => (defect 0 cmM50 (tailInv 0 ikSymbol) (1 / (((0 : ℕ) : ℝ) + 1))
  (norm_tailInv_ikSymbol_le 0) (beta 1 cmPhiHalf cmA50) : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)

theorem cm50_band : ∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (beta 1 cmPhiHalf cmA50) i = 0 := by
  intro i hi
  rw [cm_beta_half, cmA50, lpOneAlg.toRealSeq_add, Pi.add_apply,
    band_single 1 (-1) (1 : ℂ) (by decide) i hi, band_single 1 0 (1 : ℂ) (by decide) i hi, add_zero]

/-- `P₀ M ≠ M` (`M e₀ = i e₁` is a tail vector). -/
theorem cm50_PM_ne : 𝓟₀ ∘L cmM50 ≠ cmM50 := by
  intro h
  have h0 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  have hM : cmM50 (lpOneAlg.single 0 1) = lpOneAlg.single 1 Complex.I := by
    rw [cmM50, ContinuousLinearMap.comp_apply, lpOneAlg.headProj_single,
      ite_eq_left cm_mem0, lpOneAlg.mulLeftCLM_apply, lpOneAlg.single_mul_single,
      add_zero, mul_one]
  rw [ContinuousLinearMap.comp_apply, hM, lpOneAlg.headProj_single,
    ite_eq_right (fun hm => by rw [mem_winZ] at hm; exact absurd hm (by decide))] at h0
  have hn := congr_arg norm h0
  rw [norm_zero, cm_norm_single, Complex.norm_I] at hn
  exact zero_ne_one hn

theorem cm50_mul (j : ℤ) :
    (beta 1 cmPhiHalf cmA50) * lpOneAlg.single j 1 = lpOneAlg.single (j - 1) 1 + lpOneAlg.single j 1 := by
  rw [cm_beta_half, cmA50, add_mul, lpOneAlg.single_mul_single, lpOneAlg.single_mul_single, mul_one,
    zero_add, show (-1 : ℤ) + j = j - 1 by ring]

/-- The head columns: `M P₀ L_β Q₀ e_j = 1_{j = 1} i e₁`. -/
theorem cm50_head (j : ℤ) :
    defectHead 0 cmM50 (beta 1 cmPhiHalf cmA50) (lpOneAlg.single j 1) =
      if j = 1 then lpOneAlg.single 1 Complex.I else 0 := by
  rw [defectHead_single, cm50_mul]
  by_cases h0 : j.natAbs ≤ 0
  · rw [ite_eq_left h0, ite_eq_right (by omega)]
  · rw [ite_eq_right h0, cmM50, ContinuousLinearMap.comp_apply]
    by_cases h1 : j = 1
    · subst h1
      norm_num [lpOneAlg.headProj_single, mem_winZ, lpOneAlg.single_mul_single]
    · simp [lpOneAlg.headProj_single, mem_winZ, h1, show ¬ (j - 1).natAbs ≤ 0 by omega,
        show ¬ j.natAbs ≤ 0 by omega]

/-- The tail columns: `D_r L_β e_j = r_{j−1} e_{j−1} + r_j e_j`. -/
theorem cm50_tail (j : ℤ) :
    defectTail (tailInv 0 ikSymbol) (1 / (((0 : ℕ) : ℝ) + 1)) (norm_tailInv_ikSymbol_le 0)
        (beta 1 cmPhiHalf cmA50) (lpOneAlg.single j 1) =
      lpOneAlg.single (j - 1) (tailInv 0 ikSymbol (j - 1) * 1) +
        lpOneAlg.single j (tailInv 0 ikSymbol j * 1) := by
  rw [defectTail_single, cm50_mul, map_add, lpOneAlg.diagCLM_single, lpOneAlg.diagCLM_single]

theorem cm50_r_norm (k : ℤ) (hk : k ≠ 0) : ‖tailInv 0 ikSymbol k‖ = (k.natAbs : ℝ)⁻¹ := by
  rw [norm_tailInv_ikSymbol, ite_eq_right (by omega)]

/-- The column `j = 1` cancels: `i e₁ + r₁ e₁ = 0`. -/
theorem cm50_col1 : 𝓓50 (lpOneAlg.single 1 1) = 0 := by
  rw [defect_eq, add_apply, cm50_head, ite_eq_left rfl, cm50_tail,
    show (1 : ℤ) - 1 = 0 by norm_num, tailInv_head_zero 0 ikSymbol 0 le_rfl, zero_mul,
    lpOneAlg.single_smul 0 (0 : ℂ), zero_smul, zero_add, mul_one]
  have hr1 : tailInv 0 ikSymbol 1 = -Complex.I := by
    rw [tailInv, ite_eq_right (fun hm => by rw [mem_winZ] at hm; exact absurd hm (by decide)),
      ikSymbol, Int.cast_one, mul_one, Complex.inv_I]
  rw [hr1, lpOneAlg.single_smul 1 Complex.I, lpOneAlg.single_smul 1 (-Complex.I), neg_smul,
    add_neg_cancel]

/-- A column `j ≠ 1`: `D e_j = r_{j−1} e_{j−1} + r_j e_j`. -/
theorem cm50_col (j : ℤ) (hj : j ≠ 1) :
    𝓓50 (lpOneAlg.single j 1) =
      lpOneAlg.single (j - 1) (tailInv 0 ikSymbol (j - 1) * 1) +
        lpOneAlg.single j (tailInv 0 ikSymbol j * 1) := by
  rw [defect_eq, add_apply, cm50_head, ite_eq_right hj, zero_add, cm50_tail]

theorem cm50_colRatio (j : ℤ) (hj : j ≠ 1) :
    lpOneAlg.colRatio 𝓓50 j = ‖tailInv 0 ikSymbol (j - 1)‖ + ‖tailInv 0 ikSymbol j‖ := by
  rw [colRatio_geom, cm50_col j hj, cmNu1_pow, div_one,
    cm_norm_single_add_single _ _ (by omega), mul_one, mul_one]

theorem cm50_colRatio1 : lpOneAlg.colRatio 𝓓50 1 = 0 := by
  rw [colRatio_geom, cm50_col1, norm_zero, zero_div]

/-- `‖DG(ā) − B₀‖ = 3/2` (through the window `|j| ≤ 2` of T33; attained at `j = −1` and `j = 2`). -/
theorem cm50_norm : ‖(fderiv ℂ 𝓖50 cmA50 - 𝓑50 : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ = 3 / 2 := by
  rw [norm_fderiv_sub_modelDeriv_eq_sup' 0 1 1 cmM50 ikSymbol _ _ _ 1 cmPhiHalf cmA50 cm50_band
    (tailInv_ikSymbol_hmono 0)]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j hj => ?_
    rw [mem_winZ] at hj
    have hcases : j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [cm50_colRatio _ (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]
      norm_num
    · rw [cm50_colRatio _ (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]
      norm_num
    · rw [cm50_colRatio _ (by decide), cm50_r_norm _ (by decide),
        tailInv_head_zero 0 ikSymbol 0 le_rfl, norm_zero]
      norm_num
    · rw [cm50_colRatio1]; norm_num
    · rw [cm50_colRatio _ (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]
      norm_num
  · have h := Finset.le_sup' (fun j => lpOneAlg.colRatio 𝓓50 j)
      (mem_winZ.mpr (show (2 : ℤ).natAbs ≤ 1 + max (0 + 1) 1 by decide))
    refine le_of_eq_of_le ?_ h
    rw [cm50_colRatio _ (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]
    norm_num

/-- The explicit separated value at `j = 1`: `a₁ + s₁ = 1 + 1 = 2`. -/
theorem cm50_explicit_at1 :
    headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) 1 + tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) 1 = 2 := by
  rw [← colRatio_defectHead_eq_headCol,
    ← colRatio_defectTail 1 (tailInv 0 ikSymbol) _ (norm_tailInv_ikSymbol_le 0) _ cm50_band,
    colRatio_geom, colRatio_geom, cm50_head, ite_eq_left rfl, cm50_tail,
    show (1 : ℤ) - 1 = 0 by norm_num, tailInv_head_zero 0 ikSymbol 0 le_rfl, zero_mul,
    lpOneAlg.single_smul 0 (0 : ℂ), zero_smul, zero_add, cm_norm_single, cm_norm_single, mul_one,
    cm50_r_norm 1 (by decide), Complex.norm_I, cmNu1_pow, div_one, div_one]
  norm_num

/-- The explicit separated maximum over `|j| ≤ 2` is at least `2`. -/
theorem cm50_explicit_ge :
    2 ≤ (winZ (0 + 1 + 1)).sup' (winZ_nonempty _)
      (fun j => headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) j +
        tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) j) := by
  have h := Finset.le_sup' (fun j => headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) j +
      tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) j)
    (mem_winZ.mpr (show (1 : ℤ).natAbs ≤ 0 + 1 + 1 by decide))
  rwa [cm50_explicit_at1] at h

/-- The explicit separated columns: `a_j + s_j = 1_{j = 1} + ‖r_{j−1}‖ + ‖r_j‖`. -/
theorem cm50_explicit_col (j : ℤ) :
    headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) j + tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) j =
      (if j = 1 then 1 else 0) + (‖tailInv 0 ikSymbol (j - 1)‖ + ‖tailInv 0 ikSymbol j‖) := by
  rw [← colRatio_defectHead_eq_headCol,
    ← colRatio_defectTail 1 (tailInv 0 ikSymbol) _ (norm_tailInv_ikSymbol_le 0) _ cm50_band,
    colRatio_geom, colRatio_geom, cm50_head, cm50_tail, cm_norm_single_add_single _ _ (by omega),
    cmNu1_pow, div_one, div_one, mul_one, mul_one]
  split_ifs <;> simp [cm_norm_single, Complex.norm_I]

/-- The explicit separated maximum over `|j| ≤ 2` is exactly `2` (attained at `j = 1`). -/
theorem cm50_explicit_eq :
    (winZ (0 + 1 + 1)).sup' (winZ_nonempty _)
      (fun j => headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) j +
        tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) j) = 2 := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) cm50_explicit_ge
  rw [mem_winZ] at hj
  rw [cm50_explicit_col]
  have hcases : j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · rw [ite_eq_right (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]; norm_num
  · rw [ite_eq_right (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]; norm_num
  · rw [ite_eq_right (by decide), cm50_r_norm _ (by decide), tailInv_head_zero 0 ikSymbol 0 le_rfl,
      norm_zero]; norm_num
  · rw [ite_eq_left rfl, show (1 : ℤ) - 1 = 0 by norm_num, tailInv_head_zero 0 ikSymbol 0 le_rfl,
      norm_zero, cm50_r_norm _ (by decide)]; norm_num
  · rw [ite_eq_right (by decide), cm50_r_norm _ (by decide), cm50_r_norm _ (by decide)]; norm_num

/-- **T50 `hPM` decisive within the first-order family** (Codex CHANGES A3): `hβ`, `r = 0` on the
head, the first-tail bound and `hmono` from `K₀ = 1` hold and `P₀ M ≠ M`; the conclusion of T50
fails at the `DG − B₀` level: `‖DG(ā) − B₀‖ = 3/2 < 2 ≤ max_{|j| ≤ 2} (a_j + s_j)`. -/
theorem cm50_T50_fails :
    ‖(fderiv ℂ 𝓖50 cmA50 - 𝓑50 : 𝓔 ℂ cmNu1 →L[ℂ] 𝓔 ℂ cmNu1)‖ ≠
      (winZ (0 + 1 + 1)).sup' (winZ_nonempty _)
        (fun j => headCol 0 cmM50 (beta 1 cmPhiHalf cmA50) j +
          tailCol 1 (tailInv 0 ikSymbol) (beta 1 cmPhiHalf cmA50) j) := by
  rw [cm50_norm]
  have := cm50_explicit_ge
  intro h
  linarith

/-- The hypotheses of T50 other than `hPM` hold jointly. -/
theorem cm50_other_hyps :
    (∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (beta 1 cmPhiHalf cmA50) i = 0) ∧
    (∀ k : ℤ, k.natAbs ≤ 0 → tailInv 0 ikSymbol k = 0) ∧
    (∀ k, ‖tailInv 0 ikSymbol k‖ ≤ 1 / (((0 : ℕ) : ℝ) + 1)) ∧
    (∀ n : ℕ, max (0 + 1) 1 ≤ n →
      ‖tailInv 0 ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv 0 ikSymbol (n : ℤ)‖ ∧
        ‖tailInv 0 ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv 0 ikSymbol (-(n : ℤ))‖) :=
  ⟨cm50_band, tailInv_head_zero 0 ikSymbol, norm_tailInv_ikSymbol_le 0, tailInv_ikSymbol_hmono 0⟩

end T50

/-! ### The R6 boundary (FS:562–:591, restated over the new carrier names) -/

section R6

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The unbounded Fourier derivation, defined here only on atoms: `δ e_k = k e_k`. -/
def deltaAtom (k : ℤ) : 𝓔 ℂ ν := lpOneAlg.single k (k : ℂ)

/-- The directional derivative of `Ψ(a) = (δ a)²` at `ā = e₋₁` on the atom `e_j`. -/
def dΨ (j : ℤ) : 𝓔 ℂ ν := (2 : ℂ) • (deltaAtom (ν := ν) (-1) * deltaAtom j)

theorem dΨ_zero : dΨ (ν := ν) 0 = 0 := by
  simp only [dΨ, deltaAtom, Int.cast_zero]
  rw [lpOneAlg.single_smul 0 (0 : ℂ), zero_smul, mul_zero, smul_zero]

theorem dΨ_one : dΨ (ν := ν) 1 = lpOneAlg.single 0 (-2 : ℂ) := by
  rw [dΨ, deltaAtom, deltaAtom, lpOneAlg.single_mul_single, show (-1 : ℤ) + 1 = 0 by norm_num,
    lpOneAlg.single_smul 0 (((-1 : ℤ) : ℂ) * ((1 : ℤ) : ℂ)), lpOneAlg.single_smul 0 (-2 : ℂ),
    smul_smul]
  norm_num

/-- R6: the leak `P₀ DΨ(ā) Q₀ e₁ = −2 e₀` (`Q₀ e₁ = e₁`). -/
theorem R6_leak :
    lpOneAlg.headProj (𝕜 := ℂ) (winZ 0) (dΨ (ν := ν) 1) = lpOneAlg.single 0 (-2 : ℂ) ∧
    (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ 0) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single 1 1) =
      lpOneAlg.single 1 1 := by
  constructor
  · rw [dΨ_one, lpOneAlg.headProj_single, ite_eq_left cm_mem0]
  · rw [← lpOneAlg.tailProj_eq_one_sub, lpOneAlg.tailProj_single,
      ite_eq_right (fun hm => by rw [mem_winZ] at hm; exact absurd hm (by decide))]

/-- R6: the directional derivative on atoms is not multiplication by any fixed `c`. -/
theorem R6_not_multiplication :
    ¬ ∃ c : 𝓔 ℂ ν, ∀ j : ℤ, dΨ j = c * lpOneAlg.single j 1 := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  rw [dΨ_zero, ← lpOneAlg.one_eq_single_zero, mul_one] at h0
  have h1 := hc 1
  rw [← h0, zero_mul, dΨ_one] at h1
  have hcoef := congr_arg (fun x : 𝓔 ℂ ν => lpOneAlg.toRealSeq x 0) h1
  simp only [lpOneAlg.toRealSeq_single, ite_true, lpOneAlg.toRealSeq_zero, Pi.zero_apply] at hcoef
  norm_num at hcoef

end R6

end RadiiPolynomial.Tests.FZ.Semilinear

end
