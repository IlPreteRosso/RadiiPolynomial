import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Examples.tests.FZ.TailWindowTestSupport

/-!
# FZ tail-window tests: regressions (T44, L002)

The slice-25 Part G regressions
(SL25 = `tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean`,
sha256 `2c938be2…`), ported over the library API with their names kept: G2 (:1653–:1745, the
eventual window repairs a resonance), G3 (:1749–:1812, the `+1` of the window), G4 and G4′
(:1816–:1970, complex phases, `𝕜 = ℂ`), G5 (:1974–:2048, constant tail; `rConst` from
`TailWindowTestSupport`), G6 (:2052–:2089) WITHOUT its Part-F rows (`G6_lam_zero`,
`G6_bookShape_zero_symbol` stay out with Part F), and G8 (:2217, the real carrier is
`l1Chebyshev ν`). Renames as in `TailWindowCountermodels`. The carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` and `headP N` abbreviates `headProj (winZ N)`
(local notations).
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.TailWindow

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)
local notation "headP" N:max =>
  (lpOneAlg.headProj (G := geomFiberZ _ _) (RadiiPolynomial.Fourier.winZ N))

/-! ### G2 — RESONANCE: the eventual window repairs a resonance outside `N + m + 1` -/

section G2

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G2 symbol (`N = 0`): `r₀ = 0`, `r_{±1} = 1`, `r_k = 5 / (|k| − 1)` for `|k| ≥ 2`. -/
def rRes (k : ℤ) : 𝕜 := if k = 0 then 0 else if k.natAbs = 1 then 1 else 5 / ((k.natAbs : 𝕜) - 1)

theorem norm_rRes_big (k : ℤ) (hk : 2 ≤ k.natAbs) :
    ‖(rRes k : 𝕜)‖ = 5 / ((k.natAbs : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hk
  rw [rRes, ite_eq_right (by omega), ite_eq_right (by omega)]
  have e : (5 : 𝕜) / ((k.natAbs : 𝕜) - 1) = (((5 : ℝ) / ((k.natAbs : ℝ) - 1) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_div, RCLike.ofReal_sub, RCLike.ofReal_natCast, RCLike.ofReal_one,
      RCLike.ofReal_ofNat]
  rw [e, RCLike.norm_ofReal, abs_of_pos (div_pos (by norm_num) (by linarith))]

theorem norm_rRes_le (k : ℤ) : ‖(rRes k : 𝕜)‖ ≤ 5 := by
  by_cases h0 : k = 0
  · rw [rRes, ite_eq_left h0, norm_zero]; norm_num
  by_cases h1 : k.natAbs = 1
  · rw [rRes, ite_eq_right h0, ite_eq_left h1, norm_one]; norm_num
  have hk : 2 ≤ k.natAbs := by omega
  have h2 : (2 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hk
  rw [norm_rRes_big k hk]
  exact div_le_self (by norm_num) (by linarith)

theorem norm_rRes_le_one (k : ℤ) (hk : k.natAbs ≤ 1) : ‖(rRes k : 𝕜)‖ ≤ 1 := by
  by_cases h0 : k = 0
  · rw [rRes, ite_eq_left h0, norm_zero]; norm_num
  · rw [rRes, ite_eq_right h0, ite_eq_left (by omega), norm_one]

theorem rRes_head : ∀ k : ℤ, k.natAbs ≤ 0 → (rRes k : 𝕜) = 0 := by
  intro k hk; rw [rRes, ite_eq_left (by omega)]

/-- G2: `hmono` holds with `K₀ = 2` (tail-to-tail comparisons from `n = 2`). -/
theorem G2_hmono : ∀ n : ℕ, max (0 + 1) 2 ≤ n →
    ‖(rRes ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rRes (n : ℤ) : 𝕜)‖ ∧
    ‖(rRes (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rRes (-(n : ℤ)) : 𝕜)‖ := by
  intro n hn
  have hn2 : 2 ≤ n := by simpa using hn
  have hr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have key : ‖(rRes ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rRes (n : ℤ) : 𝕜)‖ := by
    rw [norm_rRes_big _ (by omega), norm_rRes_big _ (by omega),
      show ((n : ℤ) + 1).natAbs = n + 1 by omega, Int.natAbs_natCast]
    push_cast
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  refine ⟨key, ?_⟩
  rw [norm_rRes_big _ (by omega), norm_rRes_big _ (by omega),
    show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, show (-(n : ℤ)).natAbs = n by omega]
  push_cast
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- G2 window: `W = m + max (N + 1) K₀ = 0 + max 1 2 = 2`. -/
theorem G2_window : 0 + max (0 + 1) 2 = 2 := rfl

/-- G2 defect: `N = 0`, `M = 0`, `b = 1` (`m = 0`), `r = rRes`. -/
abbrev DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν := defect 0 0 rRes 5 norm_rRes_le 1

theorem colRatio_DRes (j : ℤ) : colRatio (DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j = ‖(rRes j : 𝕜)‖ := by
  rw [DRes, defect_M_zero, colRatio_Tl_one]

/-- G2: `‖D‖ = 5`, obtained through the window theorem D2 with `K₀ = 2`. -/
theorem G2_norm : ‖(DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ = 5 := by
  rw [DRes, opNorm_defect_eq_sup' 0 0 2 0 rRes 5 norm_rRes_le 1 band_one G2_hmono]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j _ => by
      rw [← DRes, colRatio_DRes]; exact norm_rRes_le j
  · refine Finset.le_sup'_of_le _ (b := 2) (mem_winZ.mpr (by decide)) ?_
    rw [← DRes, colRatio_DRes, norm_rRes_big 2 (by decide)]
    norm_num

/-- G2: the norm is attained at `|j| = 2`. -/
theorem G2_attained :
    colRatio (DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) 2 = 5 ∧ colRatio (DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (-2) = 5 := by
  rw [colRatio_DRes, colRatio_DRes, norm_rRes_big _ (by decide), norm_rRes_big _ (by decide)]
  norm_num

/-- G2: the maximum over the small window `|j| ≤ N + m + 1 = 1` is `1`. -/
theorem G2_small_window :
    (winZ 1).sup' (winZ_nonempty 1) (fun j => colRatio (DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j) = 1 := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j hj => by
      rw [colRatio_DRes]; exact norm_rRes_le_one j (mem_winZ.mp hj)
  · refine Finset.le_sup'_of_le _ (b := 1) (mem_winZ.mpr (by decide)) ?_
    rw [colRatio_DRes, rRes, ite_eq_right (by decide), ite_eq_left (by decide), norm_one]

/-- G2: the small window misses the resonance. -/
theorem G2_small_lt :
    (winZ 1).sup' (winZ_nonempty 1) (fun j => colRatio (DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j)
      < ‖(DRes : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ := by
  rw [G2_small_window, G2_norm]; norm_num

end G2

/-! ### G3 — `m = 0`: first tail input `±(N + 1)`; `b = 0` gives `0` -/

section G3

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

theorem band_smul_one (c : 𝕜) :
    ∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (c • (1 : 𝓔 𝕜 ν)) i = 0 := by
  intro i hi
  rw [lpOneAlg.toRealSeq_smul, Pi.smul_apply, band_one i hi, smul_zero]

theorem colRatio_G3 (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝕜) (j : ℤ) :
    colRatio (defect N 0 r C hr (c • (1 : 𝓔 𝕜 ν))) j = ‖c‖ * ‖r j‖ := by
  rw [defect_M_zero, colRatio_Tl_smul_one]

/-- G3 (`m = 0`, `b = c • 1`, `M = 0`, moduli monotone from `N + 1`):
`‖D‖ = ‖c‖ max (‖r_{N+1}‖, ‖r_{−(N+1)}‖)` — the maximum sits at the first tail inputs.
(Holds for every `c`, and for non-strictly monotone moduli; strictness is not needed.) -/
theorem G3_norm (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝕜)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, N + 1 ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N 0 r C hr (c • (1 : 𝓔 𝕜 ν))‖
      = ‖c‖ * max ‖r ((N : ℤ) + 1)‖ ‖r (-((N : ℤ) + 1))‖ := by
  rw [opNorm_defect_eq_sup'_first N 0 0 r C hr _ (band_smul_one c) hmono]
  simp only [colRatio_G3]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j hj => ?_
    rw [mem_winZ] at hj
    by_cases hjN : j.natAbs ≤ N
    · rw [hr0 j hjN, norm_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (le_max_left _ _))
    · rcases (show j = (N : ℤ) + 1 ∨ j = -((N : ℤ) + 1) by omega) with h | h
      · rw [h]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      · rw [h]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  · rw [mul_max_of_nonneg _ _ (norm_nonneg c)]
    exact max_le (Finset.le_sup' (fun j => ‖c‖ * ‖r j‖) (mem_winZ.mpr (by omega)))
      (Finset.le_sup' (fun j => ‖c‖ * ‖r j‖) (mem_winZ.mpr (by omega)))

/-- G3: the `+1` is needed for `m = 0`: the head-only window `|j| ≤ N + m = N` misses the
maximum whenever `c ≠ 0` and `r_{N+1} ≠ 0`. -/
theorem G3_plus_one_needed (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝕜)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (hc : c ≠ 0) (hrN : r ((N : ℤ) + 1) ≠ 0) :
    (winZ (N + 0)).sup' (winZ_nonempty _)
        (fun j => colRatio (defect N 0 r C hr (c • (1 : 𝓔 𝕜 ν))) j)
      < ‖defect N 0 r C hr (c • (1 : 𝓔 𝕜 ν))‖ := by
  have hwin : (winZ (N + 0)).sup' (winZ_nonempty _)
      (fun j => colRatio (defect N 0 r C hr (c • (1 : 𝓔 𝕜 ν))) j) = 0 := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j hj => ?_
      rw [colRatio_G3, hr0 j (by rw [mem_winZ] at hj; omega), norm_zero, mul_zero]
    · exact (colRatio_nonneg _ 0).trans (Finset.le_sup' _ (mem_winZ.mpr (by simp)))
  rw [hwin]
  refine lt_of_lt_of_le ?_ (colRatio_le_opNorm _ ((N : ℤ) + 1))
  rw [colRatio_G3]
  exact mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hrN)

/-- G3: `b = 0` gives `D = 0` (empty shell, value `0`), for every `M` and `r`. -/
theorem G3_zero (N : ℕ) (M : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) :
    ‖defect N M r C hr (0 : 𝓔 𝕜 ν)‖ = 0 := by
  have h : defect N M r C hr (0 : 𝓔 𝕜 ν) = 0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [defect, lpOneAlg.mulLeftCLM_apply]
  rw [h, norm_zero]

end G3

/-! ### G4 — PHASES: complex phases pass through `M` before absolute values (`𝕜 = ℂ`) -/

section G4

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G4 column family (`N = 1`): `k ↦ e₀` for `|k| ≤ 1`, `0` otherwise. -/
def colsG4 (k : ℤ) : 𝓔 ℂ ν := if k.natAbs ≤ 1 then lpOneAlg.single 0 1 else 0

theorem colsG4_bound (k : ℤ) :
    ‖(colsG4 k : 𝓔 ℂ ν)‖ ≤ 1 *
      ‖lpAlgRingData.ofReal (E := geomFiberZ ℂ ν) k (1 : ℂ)‖ := by
  rw [geomFiberZ_weight, one_mul]
  unfold colsG4
  split_ifs
  · rw [lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul, Int.natAbs_zero, pow_zero]
    exact one_le_pow₀ (Fact.out : (1 : ℝ) ≤ ν)
  · rw [norm_zero]; exact (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).le

/-- G4: `M` = the lift of the columns `k ↦ e₀` (`|k| ≤ 1`), `0` otherwise. -/
def MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν := lpOneAlg.liftCLM colsG4 1 colsG4_bound

theorem MG4_single (j : ℤ) (x : ℂ) :
    (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single j x)
      = if j.natAbs ≤ 1 then lpOneAlg.single 0 x else 0 := by
  rw [MG4, lpOneAlg.liftCLM_single, colsG4]
  split_ifs
  · rw [← lpOneAlg.single_smul]
  · rw [smul_zero]

/-- G4: `P M = M`. -/
theorem G4_PM : headP 1 ∘L (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) = MG4 := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, MG4_single]
  split_ifs
  · rw [lpOneAlg.headProj_single, ite_eq_left (mem_winZ.mpr (by decide))]
  · rw [map_zero]

/-- G4: `M P = M` (so `M = P M P`). -/
theorem G4_MP : (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ∘L headP 1 = MG4 := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.headProj_single]
  split_ifs with h
  · rfl
  · rw [map_zero, MG4_single, ite_eq_right fun h' => h (mem_winZ.mpr h')]

/-- G4 multiplier: `b₋₁ = 1`, `b₋₂ = i`, `b₋₃ = −1`. -/
def bG4 : 𝓔 ℂ ν :=
  lpOneAlg.single (-1) 1 + lpOneAlg.single (-2) Complex.I + lpOneAlg.single (-3) (-1)

theorem bG4_mul_e2 :
    (bG4 : 𝓔 ℂ ν) * lpOneAlg.single 2 1
      = lpOneAlg.single 1 1 + lpOneAlg.single 0 Complex.I + lpOneAlg.single (-1) (-1) := by
  rw [bG4, add_mul, add_mul, lpOneAlg.single_mul_single, lpOneAlg.single_mul_single,
    lpOneAlg.single_mul_single, mul_one, mul_one, mul_one]
  norm_num

/-- G4: the exact head column at `j = 2` is `1 / ν²` (phases cancel inside `M`). -/
theorem G4_Hd : colRatio (defectHead 1 (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) bG4) 2 = 1 / (ν : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ∈ winZ 1 := mem_winZ.mpr (by decide)
  have h0 : (0 : ℤ) ∈ winZ 1 := mem_winZ.mpr (by decide)
  have hm1 : (-1 : ℤ) ∈ winZ 1 := mem_winZ.mpr (by decide)
  have hM : (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)
      ((lpOneAlg.headProj (winZ 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ((bG4 : 𝓔 ℂ ν) * lpOneAlg.single 2 1))
      = lpOneAlg.single 0 Complex.I := by
    rw [bG4_mul_e2]
    simp only [map_add, lpOneAlg.headProj_single, ite_eq_left h1, ite_eq_left h0, ite_eq_left hm1,
        MG4_single,
      ite_eq_left (mem_winZ.mp h1), ite_eq_left (mem_winZ.mp h0), ite_eq_left (mem_winZ.mp hm1)]
    rw [← single_add', ← single_add', show (1 : ℂ) + Complex.I + -1 = Complex.I by ring]
  rw [colRatio_defectHead_eq 1 _ _ 2 (by decide), hM, lpOneAlg.norm_single, geomFiberZ_weight,
      Complex.norm_I]
  simp

theorem winZ_one : winZ 1 = {-1, 0, 1} := by
  ext j; simp only [mem_winZ, Finset.mem_insert, Finset.mem_singleton]; omega

/-- G4: the absolute-value (phase-blind) sum is `3 / ν²`. -/
theorem G4_abs_sum :
    (∑ k ∈ winZ 1, ‖(MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single k 1)‖
        * ‖lpOneAlg.toRealSeq (bG4 : 𝓔 ℂ ν) (k - 2)‖) / (ν : ℝ) ^ 2 = 3 / (ν : ℝ) ^ 2 := by
  congr 1
  rw [winZ_one, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [MG4_single, bG4, lpOneAlg.toRealSeq_add, Pi.add_apply, lpOneAlg.toRealSeq_single]
  norm_num [lpOneAlg.norm_single, geomFiberZ_weight]

/-- G4: phases pass through `M` before absolute values: `1/ν² < 3/ν²`. -/
theorem G4_phase_gap :
    colRatio (defectHead 1 (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) bG4) 2
      < (∑ k ∈ winZ 1, ‖(MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single k 1)‖
          * ‖lpOneAlg.toRealSeq (bG4 : 𝓔 ℂ ν) (k - 2)‖) / (ν : ℝ) ^ 2 := by
  rw [G4_Hd, G4_abs_sum]
  exact div_lt_div_of_pos_right (by norm_num) (pow_pos ν.2 2)

end G4

/-! ### G4′ — a GENUINE complex phase (`𝕜 = ℂ`)

Same `M` as G4 (`MG4`, `N = 1`, `M = P M P`) and `b₋₁ = 3`, `b₋₂ = 4i` (`b₋₃ = 0`). Then
`M P (b e₂) = (3 + 4i) e₀`, so `colRatio defectHead 2 = |3 + 4i| / ν² = 5/ν²`, while the
phase-blind sum is
`(3 + 4)/ν² = 7/ν²`. With REAL coefficients of moduli 3 and 4 the combined modulus is 1 or 7,
never 5 (`G4'_real_moduli`): this gap needs a genuinely complex phase. -/

section G4'

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G4′ multiplier: `b₋₁ = 3`, `b₋₂ = 4i`. -/
def bG4' : 𝓔 ℂ ν := lpOneAlg.single (-1) 3 + lpOneAlg.single (-2) (4 * Complex.I)

theorem bG4'_mul_e2 :
    (bG4' : 𝓔 ℂ ν) * lpOneAlg.single 2 1
      = lpOneAlg.single 1 3 + lpOneAlg.single 0 (4 * Complex.I) := by
  rw [bG4', add_mul, lpOneAlg.single_mul_single, lpOneAlg.single_mul_single, mul_one, mul_one]
  norm_num

/-- `|3 + 4i| = 5`. -/
theorem norm_three_add_four_I : ‖(3 : ℂ) + 4 * Complex.I‖ = 5 := by
  have h := Complex.norm_add_mul_I 3 4
  push_cast at h
  rw [h, show ((3 : ℝ) ^ 2 + 4 ^ 2) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- G4′: the exact head column at `j = 2` is `5 / ν²`. -/
theorem G4'_Hd : colRatio (defectHead 1 (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) bG4') 2 = 5 / (ν : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ∈ winZ 1 := mem_winZ.mpr (by decide)
  have h0 : (0 : ℤ) ∈ winZ 1 := mem_winZ.mpr (by decide)
  have hM : (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν)
      ((lpOneAlg.headProj (winZ 1) : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) ((bG4' : 𝓔 ℂ ν) * lpOneAlg.single 2 1))
      = lpOneAlg.single 0 (3 + 4 * Complex.I) := by
    rw [bG4'_mul_e2]
    simp only [map_add, lpOneAlg.headProj_single, ite_eq_left h1, ite_eq_left h0, MG4_single,
      ite_eq_left (mem_winZ.mp h1), ite_eq_left (mem_winZ.mp h0)]
    rw [← single_add']
  rw [colRatio_defectHead_eq 1 _ _ 2 (by decide), hM, lpOneAlg.norm_single, geomFiberZ_weight,
      norm_three_add_four_I]
  simp

/-- G4′: the absolute-value (phase-blind) sum is `7 / ν²`. -/
theorem G4'_abs_sum :
    (∑ k ∈ winZ 1, ‖(MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single k 1)‖
        * ‖lpOneAlg.toRealSeq (bG4' : 𝓔 ℂ ν) (k - 2)‖) / (ν : ℝ) ^ 2 = 7 / (ν : ℝ) ^ 2 := by
  congr 1
  rw [winZ_one, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [MG4_single, bG4', lpOneAlg.toRealSeq_add, Pi.add_apply, lpOneAlg.toRealSeq_single]
  norm_num [lpOneAlg.norm_single, geomFiberZ_weight]

/-- G4′: phases pass through `M` before absolute values: `5/ν² < 7/ν²`. -/
theorem G4'_phase_gap :
    colRatio (defectHead 1 (MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) bG4') 2
      < (∑ k ∈ winZ 1, ‖(MG4 : 𝓔 ℂ ν →L[ℂ] 𝓔 ℂ ν) (lpOneAlg.single k 1)‖
          * ‖lpOneAlg.toRealSeq (bG4' : 𝓔 ℂ ν) (k - 2)‖) / (ν : ℝ) ^ 2 := by
  rw [G4'_Hd, G4'_abs_sum]
  exact div_lt_div_of_pos_right (by norm_num) (pow_pos ν.2 2)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- G4′: a real cancellation cannot produce the value `5`: real numbers of moduli `3` and `4`
add up to modulus `1` or `7`. -/
theorem G4'_real_moduli (x y : ℝ) (hx : |x| = 3) (hy : |y| = 4) : |x + y| ≠ 5 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 3)).mp hx with rfl | rfl <;>
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 4)).mp hy with rfl | rfl <;> norm_num [abs_of_neg]

end G4'

/-! ### G5 — CONSTANT TAIL: the finite maximum holds, no decay; unequal rays -/

section G5

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

-- `rConst`, `norm_rConst_le`, `rConst_head`, `rConst_tail`: `TailWindowTestSupport` (T42).

/-- G5: `hmono` holds for every `K₀`. -/
theorem G5_hmono (N K₀ : ℕ) : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
    ‖(rConst N ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rConst N (n : ℤ) : 𝕜)‖ ∧
    ‖(rConst N (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rConst N (-(n : ℤ)) : 𝕜)‖ := by
  intro n hn
  have hN : N + 1 ≤ n := (le_max_left _ _).trans hn
  rw [rConst_tail N _ (by omega), rConst_tail N _ (by omega), rConst_tail N _ (by omega),
    rConst_tail N _ (by omega)]
  exact ⟨le_rfl, le_rfl⟩

/-- G5: far right columns are CONSTANT in `j` (no decay): `Σ_i ‖b_i‖ ν^i`. -/
theorem G5_far_pos (N m K₀ : ℕ) (b : 𝓔 𝕜 ν)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ)
    (hj : ((m + max (N + 1) K₀ : ℕ) : ℤ) ≤ j) :
    colRatio (defectTail (rConst N) 1 (norm_rConst_le N) b) j
      = ∑ i ∈ winZ m, ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ i := by
  have h1 := le_max_left (N + 1) K₀
  rw [colRatio_defectTail_far_pos m _ 1 _ b hb j (by omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_winZ] at hi
  rw [rConst_tail N _ (by omega), norm_one, one_mul]

/-- G5: far left columns are constant: `Σ_i ‖b_i‖ ν^{−i}`. -/
theorem G5_far_neg (N m K₀ : ℕ) (b : 𝓔 𝕜 ν)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ)
    (hj : j ≤ -((m + max (N + 1) K₀ : ℕ) : ℤ)) :
    colRatio (defectTail (rConst N) 1 (norm_rConst_le N) b) j
      = ∑ i ∈ winZ m, ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ (-i) := by
  have h1 := le_max_left (N + 1) K₀
  rw [colRatio_defectTail_far_neg m _ 1 _ b hb j (by omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_winZ] at hi
  rw [rConst_tail N _ (by omega), norm_one, one_mul]

/-- G5: unequal rays for `b = e₁`: right value `ν`. -/
theorem G5_ray_right (N K₀ : ℕ) (j : ℤ) (hj : ((1 + max (N + 1) K₀ : ℕ) : ℤ) ≤ j) :
    colRatio (defectTail (rConst N) 1 (norm_rConst_le N) (lpOneAlg.single 1 1 : 𝓔 𝕜 ν)) j = ν := by
  rw [G5_far_pos N 1 K₀ _ (band_single 1 1 1 (by decide)) j hj,
    Finset.sum_eq_single (1 : ℤ)]
  · rw [lpOneAlg.toRealSeq_single, ite_eq_left rfl, norm_one, one_mul, zpow_one]
  · intro i _ hi; rw [lpOneAlg.toRealSeq_single, ite_eq_right hi, norm_zero, zero_mul]
  · intro h; exact absurd (mem_winZ.mpr (by decide)) h

/-- G5: unequal rays for `b = e₁`: left value `ν⁻¹`. -/
theorem G5_ray_left (N K₀ : ℕ) (j : ℤ) (hj : j ≤ -((1 + max (N + 1) K₀ : ℕ) : ℤ)) :
    colRatio (defectTail (rConst N) 1 (norm_rConst_le N) (lpOneAlg.single 1 1 : 𝓔 𝕜 ν)) j
      = (ν : ℝ)⁻¹ := by
  rw [G5_far_neg N 1 K₀ _ (band_single 1 1 1 (by decide)) j hj,
    Finset.sum_eq_single (1 : ℤ)]
  · rw [lpOneAlg.toRealSeq_single, ite_eq_left rfl, norm_one, one_mul, zpow_neg, zpow_one]
  · intro i _ hi; rw [lpOneAlg.toRealSeq_single, ite_eq_right hi, norm_zero, zero_mul]
  · intro h; exact absurd (mem_winZ.mpr (by decide)) h

omit [Fact (1 ≤ (ν : ℝ))] in
/-- G5: the two ray values differ when `1 < ν`. -/
theorem G5_rays_ne (h : 1 < (ν : ℝ)) : (ν : ℝ)⁻¹ < (ν : ℝ) :=
  (inv_lt_one_of_one_lt₀ h).trans h

end G5

/-! ### G6 — ZERO SYMBOLS: only tail nonvanishing is assumed -/

section G6

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem diagCLM_zero (C : ℝ) (hr : ∀ k, ‖(0 : ℤ → 𝕜) k‖ ≤ C) :
    (diagCLM (0 : ℤ → 𝕜) C hr : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) = 0 := by
  refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [lpOneAlg.toRealSeq_diagCLM, Pi.zero_apply, zero_mul, zero_apply, lpOneAlg.toRealSeq_zero]
  rfl

theorem norm_zero_sym_le : ∀ k : ℤ, ‖(0 : ℤ → 𝕜) k‖ ≤ 0 := fun k => by simp

/-- G6: `r = 0` is allowed; then `D = defectHead` and the theorem gives the composed-leakage window
`|j| ≤ N + m + 1`, for every bounded `M` (v2: `hPM` dropped). Note (adversary N3, not proved
here): for `r = 0` the tighter window `|j| ≤ N + m` already suffices (`colRatio_defectHead_far`). -/
theorem G6_r_zero (N m : ℕ) (M : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (b : 𝓔 𝕜 ν)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) :
    ‖defectHead N M b‖
      = (winZ (N + m + 1)).sup' (winZ_nonempty _) (fun j => colRatio (defectHead N M b) j) := by
  have hD : defect N M (0 : ℤ → 𝕜) 0 norm_zero_sym_le b = defectHead N M b := by
    rw [defect_eq, defectTail, diagCLM_zero, ContinuousLinearMap.zero_comp, add_zero]
  have h := opNorm_defect_eq_sup'_first N m M (0 : ℤ → 𝕜) 0 norm_zero_sym_le b hb
    (fun n _ => by simp)
  rwa [hD] at h

-- `G6_lam_zero` and `G6_bookShape_zero_symbol` (slice :2078, :2081) stay out with Part F.

end G6

/-! ### G8 — REAL REGRESSION -/

section G8

/-- G8: the real bilateral carrier IS `l1Chebyshev ν` (definitional; slice `example` :2217). -/
theorem G8_real_regression (ν : PosReal) : lpOneAlg ℤ (geomFiberZ ℝ ν) = l1Chebyshev ν := rfl

end G8

end RadiiPolynomial.Tests.FZ.TailWindow
