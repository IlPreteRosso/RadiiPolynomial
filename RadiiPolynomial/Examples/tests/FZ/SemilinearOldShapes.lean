import RadiiPolynomial.Applications.Fourier.SemilinearFirstOrder

/-!
# FZ semilinear tests: old shapes (T55, L005)

Old-shape witnesses of the S028b sources FS (`FourierSemilinear.lean`, sha256 `d448cfad…`) and
FSG:164/:173/:180 (`FourierSemilinearGamma.lean`, sha256 `609f2dff…`): each
`old_<name>` states the source proposition in its source shape at `𝕜 = ℂ`, through the explicit
old → new symbol mapping below, and is proved by APPLICATION of the new API. No frozen scratch
constant is imported or revalidated.

Old → new symbol mapping (MIGRATION_TABLE.md section A):
`lamH N ↦ lamHead N ikSymbol`, `rTail N ↦ tailInv N ikSymbol`, `LamH N ↦ headDiag N ikSymbol`,
`R N ↦ diagCLM (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N)`,
`Φhat ↦ phiHat`, `Φ'hat ↦ phiHatDeriv`, `b ↦ beta`,
`G N M τ Φ ↦ precondMap N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) τ Φ`,
`B₀ N M τ Φ ↦ modelDeriv N M ikSymbol τ Φ`, `Fraw ↦ rawMap ikSymbol`,
`Araw N M ↦ rawPrecond N M (tailInv N ikSymbol)`, `HeadTailColumns.H N ↦ winZ N`,
`P_H ↦ headProj`, `1 - P_H ↦ tailProj` (the source's literal `1 - headProj (winZ N)` is kept in
the old shapes; `tailProj_eq_one_sub` holds by `rfl`), `FourierZ1Window.aCol ↦ headCol`,
`sCol ↦ tailCol`, `FourierZ1Window.defect ↦ Fourier.defect`. The carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` and the S028b operator `R N` is written `𝓡 N`
(local notations).

The last section states the RAf fallback shape of every fallback-eligible target (TARGET_SHEET
§6.F) as a byte copy of its frozen template, proved by application of the PROVED-primary face.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.Semilinear

open RadiiPolynomial.Fourier RadiiPolynomial.Fourier.Semilinear

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)

/-! ### Symbols (FS:18–:68) -/

section Symbols

/-- FS:18 `norm_fourier_symbol`. -/
theorem old_norm_fourier_symbol (k : ℤ) : ‖Complex.I * (k : ℂ)‖ = (k.natAbs : ℝ) :=
  norm_ikSymbol k

/-- FS:21 `lamH` (restated: the head symbol of `ikSymbol`). -/
theorem old_lamH (N : ℕ) (k : ℤ) :
    lamHead N ikSymbol k = if k ∈ winZ N then Complex.I * (k : ℂ) else 0 :=
  rfl

/-- FS:24 `norm_lamH_le` (the old bound `N` is `headBound N ikSymbol`). -/
theorem old_norm_lamH_le (N : ℕ) : ∀ k, ‖lamHead N ikSymbol k‖ ≤ (N : ℝ) := by
  intro k
  rw [← headBound_ikSymbol N]
  exact norm_lamHead_le N ikSymbol k

/-- FS:33 `rTail` (restated: the tail inverse of `ikSymbol`). -/
theorem old_rTail (N : ℕ) (k : ℤ) :
    tailInv N ikSymbol k = if k.natAbs ≤ N then 0 else (Complex.I * (k : ℂ))⁻¹ := by
  by_cases hk : k.natAbs ≤ N
  · rw [tailInv_head_zero N ikSymbol k hk, ite_eq_left hk]
  · rw [tailInv, ite_eq_right (fun h => hk (mem_winZ.mp h)), ite_eq_right hk]
    rfl

/-- FS:36 `rTail_head_zero`. -/
theorem old_rTail_head_zero (N : ℕ) : ∀ k : ℤ, k.natAbs ≤ N → tailInv N ikSymbol k = 0 :=
  tailInv_head_zero N ikSymbol

/-- FS:40 `norm_rTail`. -/
theorem old_norm_rTail (N : ℕ) (k : ℤ) :
    ‖tailInv N ikSymbol k‖ = if k.natAbs ≤ N then 0 else (k.natAbs : ℝ)⁻¹ :=
  norm_tailInv_ikSymbol N k

/-- FS:45 `norm_rTail_le`. -/
theorem old_norm_rTail_le (N : ℕ) : ∀ k, ‖tailInv N ikSymbol k‖ ≤ 1 / ((N : ℝ) + 1) :=
  norm_tailInv_ikSymbol_le N

/-- FS:54 `tail_symbol_ne_zero` in its `N < |k|` form. -/
theorem old_tail_symbol_ne_zero {N : ℕ} {k : ℤ} (hk : N < k.natAbs) :
    Complex.I * (k : ℂ) ≠ 0 :=
  ikSymbol_ne_zero fun h0 => by rw [h0, Int.natAbs_zero] at hk; exact Nat.not_lt_zero N hk

/-- FS:59 `rTail_hmono`. -/
theorem old_rTail_hmono (N : ℕ) : ∀ n : ℕ, max (N + 1) 1 ≤ n →
    ‖tailInv N ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv N ikSymbol (n : ℤ)‖ ∧
      ‖tailInv N ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv N ikSymbol (-(n : ℤ))‖ :=
  tailInv_ikSymbol_hmono N

end Symbols

/-! ### Operators (FS:71–:141) -/

section Operators

variable {ν : PosReal}

local notation "𝓡" N:max => (lpOneAlg.diagCLM (G := geomFiberZ ℂ _) (tailInv N ikSymbol)
  (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N))

/-- FS:74 `LamH`: the old bound `N` restated; equal to `headDiag N ikSymbol` as continuous linear
maps (the `mkContinuous` bound is not part of the map). -/
theorem old_LamH (N : ℕ) :
    (headDiag N ikSymbol : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) =
      lpOneAlg.diagCLM (G := geomFiberZ ℂ ν) (lamHead N ikSymbol) (N : ℝ) (old_norm_lamH_le N) :=
  ContinuousLinearMap.ext fun _ => rfl

/-- FS:80 `toRealSeq_LamH`. -/
theorem old_toRealSeq_LamH (N : ℕ) (a : 𝓔 ℂ ν) (k : ℤ) :
    lpOneAlg.toRealSeq (headDiag N ikSymbol a) k = lamHead N ikSymbol k * lpOneAlg.toRealSeq a k :=
  toRealSeq_headDiag N ikSymbol a k

/-- FS:84 `LamH_single`. -/
theorem old_LamH_single (N : ℕ) (k : ℤ) (x : ℂ) :
    headDiag (ν := ν) N ikSymbol (lpOneAlg.single k x) = lpOneAlg.single k (lamHead N ikSymbol k * x) :=
  headDiag_single N ikSymbol k x

/-- FS:88 `toRealSeq_R`. -/
theorem old_toRealSeq_R (N : ℕ) (a : 𝓔 ℂ ν) (k : ℤ) :
    lpOneAlg.toRealSeq ((𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) a) k = tailInv N ikSymbol k * lpOneAlg.toRealSeq a k :=
  lpOneAlg.toRealSeq_diagCLM _ _ _ a k

/-- FS:92 `R_single`. -/
theorem old_R_single (N : ℕ) (k : ℤ) (x : ℂ) :
    (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single k x) = lpOneAlg.single k (tailInv N ikSymbol k * x) :=
  lpOneAlg.diagCLM_single _ _ _ k x

/-- FS:96 `norm_R_le`. -/
theorem old_norm_R_le (N : ℕ) : ‖(𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ ≤ 1 / ((N : ℝ) + 1) :=
  lpOneAlg.norm_diagCLM_le _ _ _ (by positivity)

/-- FS:101 `P_comp_LamH`. -/
theorem old_P_comp_LamH (N : ℕ) :
    (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L headDiag N ikSymbol =
      headDiag N ikSymbol :=
  headProj_comp_headDiag N ikSymbol

/-- FS:111 `LamH_comp_P`. -/
theorem old_LamH_comp_P (N : ℕ) :
    (headDiag N ikSymbol : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) =
      headDiag N ikSymbol :=
  headDiag_comp_headProj N ikSymbol

/-- FS:121 `R_comp_P`. -/
theorem old_R_comp_P (N : ℕ) :
    (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) = 0 :=
  diagCLM_comp_headProj_of_head_zero N _ _ _ (tailInv_head_zero N ikSymbol)

/-- FS:132 `P_comp_R`. -/
theorem old_P_comp_R (N : ℕ) :
    (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) = 0 :=
  lpOneAlg.headProj_comp_diagCLM _ _ _ _ fun k hk => tailInv_head_zero N ikSymbol k (mem_winZ.mp hk)

/-- FS:170 `toRealSeq_finset_sum`. -/
theorem old_toRealSeq_finset_sum {ι : Type*} (s : Finset ι) (a : ι → 𝓔 ℂ ν) (k : ℤ) :
    lpOneAlg.toRealSeq (∑ i ∈ s, a i) k = ∑ i ∈ s, lpOneAlg.toRealSeq (a i) k :=
  toRealSeq_finset_sum s a k

/-- FS:257 `headEmbed` (restated). -/
theorem old_headEmbed (N : ℕ) (y : ℤ → ℂ) :
    (headEmbed N y : 𝓔 ℂ ν) = ∑ k ∈ winZ N, lpOneAlg.single k (y k) :=
  rfl

/-- FS:260 `Araw`: the old tail factor `y k / (I k)` restated, equal pointwise. -/
theorem old_Araw (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (y : ℤ → ℂ) (k : ℤ) :
    rawPrecond N M (tailInv N ikSymbol) y k =
      lpOneAlg.toRealSeq (M (headEmbed N y)) k +
        if k.natAbs ≤ N then 0 else y k / (Complex.I * (k : ℂ)) := by
  rw [rawPrecond]
  by_cases hk : k.natAbs ≤ N
  · rw [ite_eq_left (mem_winZ.mpr hk), ite_eq_left hk]
  · rw [ite_eq_right (fun h => hk (mem_winZ.mp h)), ite_eq_right hk, old_rTail, ite_eq_right hk,
      div_eq_mul_inv, mul_comm]

/-- FS:265 `toRealSeq_headEmbed`. -/
theorem old_toRealSeq_headEmbed (N : ℕ) (y : ℤ → ℂ) (k : ℤ) :
    lpOneAlg.toRealSeq (headEmbed (ν := ν) N y) k = if k ∈ winZ N then y k else 0 :=
  toRealSeq_headEmbed N y k

/-- FS:420 `sCol_rTail_coeff`. -/
theorem old_sCol_rTail_coeff (N m : ℕ) (c : 𝓔 ℂ ν) (j : ℤ) :
    tailCol m (tailInv N ikSymbol) c j =
      (∑ i ∈ winZ m, (if N < (j + i).natAbs then ((j + i).natAbs : ℝ)⁻¹ else 0) *
        ‖lpOneAlg.toRealSeq c i‖ * (ν : ℝ) ^ (j + i).natAbs) / (ν : ℝ) ^ j.natAbs :=
  tailCol_tailInv_ikSymbol_coeff N m c j

end Operators

/-! ### The polynomial nonlinearity and the model (FS:144–:467, FSG:164/:173/:180) -/

section Model

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓡" N:max => (lpOneAlg.diagCLM (G := geomFiberZ ℂ _) (tailInv N ikSymbol)
  (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N))
local notation "𝓖" N:max M:max => (precondMap N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1))
  (norm_tailInv_ikSymbol_le N))

/-- FS:147 `Φhat` (restated). -/
theorem old_Φhat (Φ : MvPolynomial (Fin 1) ℂ) (a : 𝓔 ℂ ν) :
    phiHat Φ a = MvPolynomial.aeval (fun _ : Fin 1 => a) Φ :=
  rfl

/-- FS:150 `Φ'hat` (restated). -/
theorem old_Φ'hat (Φ : MvPolynomial (Fin 1) ℂ) (a : 𝓔 ℂ ν) :
    phiHatDeriv Φ a = MvPolynomial.aeval (fun _ : Fin 1 => a) (MvPolynomial.pderiv 0 Φ) :=
  rfl

/-- FS:154 `hasFDerivAt_Φhat`. -/
theorem old_hasFDerivAt_Φhat (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    HasFDerivAt (phiHat Φ) (lpOneAlg.mulLeftCLM (𝕜 := ℂ) (phiHatDeriv Φ abar)) abar :=
  hasFDerivAt_phiHat Φ abar

/-- FS:180 `band_mul` (landed by L002 as `Fourier.band_mul`). -/
theorem old_band_mul (m n : ℕ) (x y : 𝓔 ℂ ν)
    (hx : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq x i = 0)
    (hy : ∀ i : ℤ, n < i.natAbs → lpOneAlg.toRealSeq y i = 0) :
    ∀ k : ℤ, m + n < k.natAbs → lpOneAlg.toRealSeq (x * y) k = 0 :=
  band_mul m n x y hx hy

/-- FS:195 `band_pow` (landed by L002 as `Fourier.band_pow`). -/
theorem old_band_pow (N : ℕ) (abar : 𝓔 ℂ ν)
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0) :
    ∀ n i, n * N < i.natAbs → lpOneAlg.toRealSeq (abar ^ n) i = 0 :=
  band_pow N abar habar

/-- FS:205 `band_aeval`. -/
theorem old_band_aeval (N e : ℕ) (abar : 𝓔 ℂ ν)
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (q : MvPolynomial (Fin 1) ℂ) (hdeg : q.totalDegree ≤ e) :
    ∀ k : ℤ, e * N < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => abar) q) k = 0 :=
  band_aeval N e abar habar q hdeg

/-- FS:228 `b` (restated). -/
theorem old_b (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    beta τ Φ abar = τ • phiHatDeriv Φ abar :=
  rfl

/-- FS:231 `G` (restated with the literal `1 - headProj`). -/
theorem old_G (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (a : 𝓔 ℂ ν) :
    precondMap N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) τ Φ a =
      M (headDiag N ikSymbol a - τ • lpOneAlg.headProj (𝕜 := ℂ) (winZ N) (phiHat Φ a)) +
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) a - τ • (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (phiHat Φ a) :=
  rfl

/-- FS:237 `B₀` (restated with the literal `1 - headProj`). -/
theorem old_B₀ (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    modelDeriv N M ikSymbol τ Φ abar =
      M ∘L (headDiag N ikSymbol - lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L
        lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) :=
  rfl

/-- FS:245 `band_b`. -/
theorem old_band_b (N d : ℕ) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν)
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1) :
    ∀ i : ℤ, (d - 1) * N < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0 :=
  band_beta N d τ Φ abar habar hdeg

/-- FS:254 `Fraw` (restated). -/
theorem old_Fraw (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (a : 𝓔 ℂ ν) (k : ℤ) :
    rawMap ikSymbol τ Φ a k =
      Complex.I * (k : ℂ) * lpOneAlg.toRealSeq a k - τ * lpOneAlg.toRealSeq (phiHat Φ a) k :=
  rfl

/-- FS:272 `headEmbed_Fraw`. -/
theorem old_headEmbed_Fraw (N : ℕ) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (a : 𝓔 ℂ ν) :
    headEmbed N (rawMap ikSymbol τ Φ a) =
      headDiag N ikSymbol a - τ • lpOneAlg.headProj (𝕜 := ℂ) (winZ N) (phiHat Φ a) :=
  headEmbed_rawMap N ikSymbol τ Φ a

/-- FS:284 `toRealSeq_G` (the first-order instance of the tail-inverse identification). -/
theorem old_toRealSeq_G (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (a : 𝓔 ℂ ν) :
    lpOneAlg.toRealSeq ((𝓖 N M) τ Φ a : 𝓔 ℂ ν) =
      rawPrecond N M (tailInv N ikSymbol) (rawMap ikSymbol τ Φ a) :=
  toRealSeq_precondMap_tailInv N M ikSymbol _ (norm_tailInv_ikSymbol_le N) τ Φ a
    fun _ hk => old_tail_symbol_ne_zero hk

/-- FS:299 `mulLeftCLM_smul` (an S028b orphan, restated). -/
theorem old_mulLeftCLM_smul (τ : ℂ) (x : 𝓔 ℂ ν) :
    lpOneAlg.mulLeftCLM (𝕜 := ℂ) (τ • x) = τ • lpOneAlg.mulLeftCLM (𝕜 := ℂ) x := by
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [lpOneAlg.mulLeftCLM_apply, smul_apply, smul_mul_assoc]

/-- FS:304 `hasFDerivAt_G` (with the literal `1 - headProj`). -/
theorem old_hasFDerivAt_G (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    HasFDerivAt ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν)
      (M ∘L (headDiag N ikSymbol - τ • (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L
        lpOneAlg.mulLeftCLM (𝕜 := ℂ) (phiHatDeriv Φ abar))) +
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) -
          τ • ((𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (phiHatDeriv Φ abar))) abar :=
  hasFDerivAt_precondMap N M ikSymbol _ _ _ τ Φ abar

/-- FS:321 `DG_sub_B0` (the literal composite). -/
theorem old_DG_sub_B0 (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar =
      -(M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L
          (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
        (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar)) :=
  fderiv_sub_modelDeriv N M ikSymbol _ _ _ τ Φ abar

/-- FS:336 `DG_sub_B0_hZ`. -/
theorem old_DG_sub_B0_hZ (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar = (-1 : ℂ) •
      ((M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) + (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)) ∘L
        (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L
            (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
          (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) ∘L
            lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar))) :=
  fderiv_sub_modelDeriv_hZ N M ikSymbol _ _ _ τ Φ abar (tailInv_head_zero N ikSymbol)

/-- FS:350 `norm_DG_sub_B0_eq` (the literal composite). -/
theorem old_norm_DG_sub_B0_eq (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ =
      ‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L
          (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
        (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar)‖ :=
  norm_fderiv_sub_modelDeriv N M ikSymbol _ _ _ τ Φ abar

/-- FS:362 `composite_eq_defect_coeff` (L002 `defect` unfolds by `rfl`). -/
theorem old_composite_eq_defect_coeff (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (c : 𝓔 ℂ ν) :
    M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) c ∘L
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
      (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) c =
        defect N M (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) c :=
  rfl

/-- FS:373 `composite_eq_defect`. -/
theorem old_composite_eq_defect (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N)) +
      (𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) =
        defect N M (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N)
          (beta τ Φ abar) :=
  old_composite_eq_defect_coeff N M (beta τ Φ abar)

/-- FS:383 `norm_DG_sub_B0_eq_sup'` (the first-order window `N + m + 1`). -/
theorem old_norm_DG_sub_B0_eq_sup' (N m : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν)
    (hPM : lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L M = M)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0) :
    ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ =
      (winZ (N + m + 1)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol m (tailInv N ikSymbol) (beta τ Φ abar) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup'_first N m M τ Φ abar hPM hb

/-- FS:398 `DG_sub_B0_attained` (the old window `N + m + 1`, by T35 with `K₀ = 1` and
`window_eq_of_le`). -/
theorem old_DG_sub_B0_attained (N m : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0) :
    ∃ j ∈ winZ (N + m + 1),
      ‖(fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar)
          (lpOneAlg.single j 1)‖ =
        ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ *
          (ν : ℝ) ^ j.natAbs := by
  rw [← window_eq_of_le N m 1 (by omega)]
  exact fderiv_sub_modelDeriv_attained N m 1 M ikSymbol _ _ (norm_tailInv_ikSymbol_le N) τ Φ abar hb
    (tailInv_ikSymbol_hmono N)

/-- FS:411 `aCol_eq_coeff` (L002 `headCol` by `rfl`). -/
theorem old_aCol_eq_coeff (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (c : 𝓔 ℂ ν) (j : ℤ) :
    headCol N M c j = if j.natAbs ≤ N then 0 else
      ‖M (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) (c * lpOneAlg.single j 1))‖ / (ν : ℝ) ^ j.natAbs :=
  rfl

/-- FS:432 `aCol_eq`. -/
theorem old_aCol_eq (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) (j : ℤ) :
    headCol N M (beta τ Φ abar) j = if j.natAbs ≤ N then 0 else
      ‖M (lpOneAlg.headProj (𝕜 := ℂ) (winZ N) (beta τ Φ abar * lpOneAlg.single j 1))‖ /
        (ν : ℝ) ^ j.natAbs :=
  old_aCol_eq_coeff N M (beta τ Φ abar) j

/-- FS:440 `sCol_rTail`. -/
theorem old_sCol_rTail (N m : ℕ) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) (j : ℤ) :
    tailCol m (tailInv N ikSymbol) (beta τ Φ abar) j =
      (∑ i ∈ winZ m, (if N < (j + i).natAbs then ((j + i).natAbs : ℝ)⁻¹ else 0) *
        ‖lpOneAlg.toRealSeq (beta τ Φ abar) i‖ * (ν : ℝ) ^ (j + i).natAbs) / (ν : ℝ) ^ j.natAbs :=
  tailCol_tailInv_ikSymbol_coeff N m (beta τ Φ abar) j

/-- FS:447 `norm_DG_sub_B0_eq_sup'_dN` (the old explicit window `N + (d - 1) N + 1`, by T34 with
T22 and `window_eq_of_le`). -/
theorem old_norm_DG_sub_B0_eq_sup'_dN (N d : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν)
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1)
    (hPM : lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L M = M) :
    ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ =
      (winZ (N + (d - 1) * N + 1)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j +
          tailCol ((d - 1) * N) (tailInv N ikSymbol) (beta τ Φ abar) j) := by
  rw [norm_fderiv_sub_modelDeriv_eq_sup'_explicit N ((d - 1) * N) 1 M ikSymbol _ _
      (norm_tailInv_ikSymbol_le N) τ Φ abar (band_beta N d τ Φ abar habar hdeg) hPM
      (tailInv_head_zero N ikSymbol) (tailInv_ikSymbol_hmono N),
    window_eq_of_le N ((d - 1) * N) 1 (by omega)]

/-- FS:459 `window_dN_eq` (from T37 at `K₀ = 1`). -/
theorem old_window_dN_eq (N d : ℕ) (hd : 1 ≤ d) : N + (d - 1) * N + 1 = d * N + 1 := by
  have h := window_deg_eq N d 1 hd (by omega)
  rw [max_eq_left (by omega)] at h
  omega

/-- FS:462 `norm_DG_sub_B0_real`. -/
theorem old_norm_DG_sub_B0_real (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    ‖(fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar).restrictScalars ℝ‖ =
      ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ :=
  norm_restrictScalars_fderiv_sub_modelDeriv N M ikSymbol _ _ _ τ Φ abar

/-- FSG:164 `norm_head_leak_le`: ONE application of L004 T13 at `c := beta τ Φ abar`. -/
theorem old_norm_head_leak_le (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ)
    (abar : 𝓔 ℂ ν) :
    ‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar) ∘L
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (winZ N))‖ ≤
      ‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L (gammaDiag N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ *
        ‖beta τ Φ abar‖ :=
  norm_head_leak_le_coeff N M (beta τ Φ abar)

/-- FSG:173 `norm_tail_leak_le`: ONE application of L004 T14 at `r := tailInv N ikSymbol`,
`C := 1/(N + 1)`. -/
theorem old_norm_tail_leak_le (N : ℕ) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    ‖(𝓡 N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L lpOneAlg.mulLeftCLM (𝕜 := ℂ) (beta τ Φ abar)‖ ≤
      ‖beta τ Φ abar‖ / ((N : ℝ) + 1) :=
  (norm_tail_leak_le_coeff (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N)
    (beta τ Φ abar)).trans_eq (by ring)

/-- FSG:180 `norm_DG_sub_B0_le_gamma` (T51). -/
theorem old_norm_DG_sub_B0_le_gamma (N : ℕ) (M : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : 𝓔 ℂ ν) :
    ‖fderiv ℂ ((𝓖 N M) τ Φ : 𝓔 ℂ ν → 𝓔 ℂ ν) abar - modelDeriv N M ikSymbol τ Φ abar‖ ≤
      (‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (winZ N) ∘L (gammaDiag N : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)‖ +
        1 / ((N : ℝ) + 1)) * ‖beta τ Φ abar‖ :=
  norm_fderiv_sub_modelDeriv_le_gamma_first N M τ Φ abar

end Model

/-! ### RAf fallback shapes (TARGET_SHEET §6.F; every fallback-eligible target is PROVED-primary) -/

section Fallback

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- RAf fallback shape of T20 (`hasFDerivAt_phiHat`), by application of the PROVED-primary face. -/
theorem fallback_hasFDerivAt_phiHat (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    HasFDerivAt (phiHat Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar :=
  RadiiPolynomial.Fourier.Semilinear.hasFDerivAt_phiHat Φ abar

/-- RAf fallback shape of T21 (`band_aeval`), by application of the PROVED-primary face. -/
theorem fallback_band_aeval (N e : ℕ) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (q : MvPolynomial (Fin 1) 𝕜) (hdeg : q.totalDegree ≤ e) :
    ∀ k : ℤ, e * N < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => abar) q) k = 0 :=
  RadiiPolynomial.Fourier.Semilinear.band_aeval N e abar habar q hdeg

/-- RAf fallback shape of T22 (`band_beta`), by application of the PROVED-primary face. -/
theorem fallback_band_beta (N d : ℕ) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1) :
    ∀ i : ℤ, (d - 1) * N < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0 :=
  RadiiPolynomial.Fourier.Semilinear.band_beta N d τ Φ abar habar hdeg

/-- RAf fallback shape of T25 (`hasFDerivAt_precondMap`), by application of the PROVED-primary face. -/
theorem fallback_hasFDerivAt_precondMap (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    HasFDerivAt (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν))
      (M ∘L ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - τ • ((lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) + (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) -
        τ • ((lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) abar :=
  RadiiPolynomial.Fourier.Semilinear.hasFDerivAt_precondMap N M lam r C hr τ Φ abar

/-- RAf fallback shape of T26 (`fderiv_sub_modelDeriv`), by application of the PROVED-primary face. -/
theorem fallback_fderiv_sub_modelDeriv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    (fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = -(defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :=
  RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv N M lam r C hr τ Φ abar

/-- RAf fallback shape of T27 (`fderiv_sub_modelDeriv_hZ`), by application of the PROVED-primary face. -/
theorem fallback_fderiv_sub_modelDeriv_hZ (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    (fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (-1 : 𝕜) •
      ((M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) + (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) ∘L
        ((lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (1 - (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) + (1 - (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) :=
  RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv_hZ N M lam r C hr τ Φ abar hr0

/-- RAf fallback shape of T28 (`norm_fderiv_sub_modelDeriv`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ = ‖(defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv N M lam r C hr τ Φ abar

/-- RAf fallback shape of T30 (`headEmbed_rawMap`), by application of the PROVED-primary face. -/
theorem fallback_headEmbed_rawMap (N : ℕ) (lam : ℤ → 𝕜) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    (headEmbed N (rawMap lam τ Φ a) : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a - τ • (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (phiHat Φ a) :=
  RadiiPolynomial.Fourier.Semilinear.headEmbed_rawMap N lam τ Φ a

/-- RAf fallback shape of T31 (`toRealSeq_precondMap`), by application of the PROVED-primary face. -/
theorem fallback_toRealSeq_precondMap (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (hrlam : ∀ k : ℤ, N < k.natAbs → r k * lam k = 1) :
    lpOneAlg.toRealSeq (precondMap N M lam r C hr τ Φ a) = rawPrecond N M r (rawMap lam τ Φ a) :=
  RadiiPolynomial.Fourier.Semilinear.toRealSeq_precondMap N M lam r C hr τ Φ a hr0 hrlam

/-- RAf fallback shape of T32 (`toRealSeq_precondMap_tailInv`), by application of the PROVED-primary face. -/
theorem fallback_toRealSeq_precondMap_tailInv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam : ℤ → 𝕜) (C : ℝ)
    (hC : ∀ k, ‖tailInv N lam k‖ ≤ C) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hlam : ∀ k : ℤ, N < k.natAbs → lam k ≠ 0) :
    lpOneAlg.toRealSeq (precondMap N M lam (tailInv N lam) C hC τ Φ a) =
      rawPrecond N M (tailInv N lam) (rawMap lam τ Φ a) :=
  RadiiPolynomial.Fourier.Semilinear.toRealSeq_precondMap_tailInv N M lam C hC τ Φ a hlam

/-- RAf fallback shape of T33 (`norm_fderiv_sub_modelDeriv_eq_sup'`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv_eq_sup' (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ (B + max (N + 1) K₀)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio (defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) j) :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup' N B K₀ M lam r C hr τ Φ abar hβ hmono

/-- RAf fallback shape of T34 (`norm_fderiv_sub_modelDeriv_eq_sup'_explicit`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv_eq_sup'_explicit (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hPM : (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ (B + max (N + 1) K₀)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol B r (beta τ Φ abar) j) :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup'_explicit N B K₀ M lam r C hr τ Φ abar hβ hPM hr0 hmono

/-- RAf fallback shape of T35 (`fderiv_sub_modelDeriv_attained`), by application of the PROVED-primary face. -/
theorem fallback_fderiv_sub_modelDeriv_attained (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ∃ j ∈ winZ (B + max (N + 1) K₀),
      ‖((fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) (lpOneAlg.single j 1)‖ =
        ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ * (ν : ℝ) ^ j.natAbs :=
  RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv_attained N B K₀ M lam r C hr τ Φ abar hβ hmono

/-- RAf fallback shape of T36 (`norm_fderiv_sub_modelDeriv_eq_sup'_deg`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv_eq_sup'_deg (N d K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ ((d - 1) * N + max (N + 1) K₀)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio (defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) j) :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup'_deg N d K₀ M lam r C hr τ Φ abar habar hdeg hmono

/-- RAf fallback shape of T38 (`norm_fderiv_sub_modelDeriv_eq_sup'_deg_explicit`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv_eq_sup'_deg_explicit (N d K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1)
    (hPM : (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ ((d - 1) * N + max (N + 1) K₀)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol ((d - 1) * N) r (beta τ Φ abar) j) :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup'_deg_explicit N d K₀ M lam r C hr τ Φ abar habar hdeg hPM hr0 hmono

/-- RAf fallback shape of T39 (`norm_fderiv_sub_modelDeriv_le_gamma`), by application of the PROVED-primary face. -/
theorem fallback_norm_fderiv_sub_modelDeriv_le_gamma (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤
      (‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ + C) * ‖(beta τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ :=
  RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_le_gamma N M lam r C hr τ Φ abar

end Fallback

end RadiiPolynomial.Tests.FZ.Semilinear

end
