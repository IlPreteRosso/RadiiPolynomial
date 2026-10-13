import RadiiPolynomial.Examples.tests.FZ.TailWindowTestSupport

/-!
# FZ tail-window tests: decisive countermodels (T43, L002)

The slice-25 Part G countermodels
(SL25 = `tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean`,
sha256 `2c938be2…`), ported over the library API with their names kept: G1 (:1274–:1369), G1′
(:1379–:1506), G1″ (:1515–:1649), G7 (:2104–:2210), G9 (:2229–:2374; the `Fact (1 ≤ ν)` instance on
the literal weight `nu1` is LOCAL) and G10 (:2383–:2468). Renames of record (MIGRATION_TABLE.md):
`Hd ↦ defectHead`, `Tl ↦ defectTail`, `aCol ↦ headCol`, `sCol ↦ tailCol`, `headP N ↦
headProj (winZ N)`, `colRatio ↦ lpOneAlg.colRatio` (read through `colRatio_geom`),
`colRatio_Hd_* ↦ colRatio_defectHead_*`, `colRatio_Tl_eq_sCol ↦ colRatio_defectTail`,
`norm_single' ↦ lpOneAlg.norm_single + geomFiberZ_weight`, `opNorm_le_iff_cols` (L001 form).

New in L002 (TARGET_SHEET §7): the joint-form countermodels for `hZQ` (`ZQ_*`) and `hPZ`
(`ZP_*`, `negZP_*`) of T37/T38, the nonvacuity witnesses of T33 and T37, and the `hx`-drop
countermodel of T12 with the boundary witness of the summed radius. The carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` and `headP N` abbreviates the head projection
`headProj (winZ N)` (local notations).
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.TailWindow

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)
local notation "headP" N:max =>
  (lpOneAlg.headProj (G := geomFiberZ _ _) (RadiiPolynomial.Fourier.winZ N))

/-! ### G1 — RANGE: `M = M P` without `P M = M` breaks the column identity C4

(Column level only: on this data the norm formula holds, `‖D‖ = ν + 1`. The norm-level failure
of the aggregate B1/K2 without `P M = M` is G1′ below.) -/

section G1

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G1 column family: `0 ↦ −e₁`, every other column `0`. -/
def colsG1 (j : ℤ) : 𝓔 𝕜 ν := if j = 0 then -(lpOneAlg.single 1 1) else 0

theorem colsG1_bound (j : ℤ) :
    ‖(colsG1 j : 𝓔 𝕜 ν)‖ ≤ (ν : ℝ) *
      FiberTrivialization.weight (E := geomFiberZ 𝕜 ν) j := by
  rw [geomFiberZ_weight]
  unfold colsG1
  split_ifs with h
  · subst h; rw [norm_neg, lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul]; simp
  · rw [norm_zero]; exact mul_nonneg ν.2.le (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).le

/-- G1: `M` = the lift of the columns `0 ↦ −e₁` (other columns `0`). -/
def MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν := lpOneAlg.liftCLM colsG1 (ν : ℝ) colsG1_bound

theorem MG1_single (j : ℤ) : (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lpOneAlg.single j 1) = colsG1 j := by
  rw [MG1, lpOneAlg.liftCLM_single, one_smul]

/-- G1 multiplier `b = e₋₁ + e₀` (band `m = 1`). -/
def bG1 : 𝓔 𝕜 ν := lpOneAlg.single (-1) 1 + lpOneAlg.single 0 1

/-- G1 tail symbol `r_k = 1_{k ≠ 0}` (vanishes on the head `N = 0`). -/
def rG1 (k : ℤ) : 𝕜 := if k = 0 then 0 else 1

theorem norm_rG1_le (k : ℤ) : ‖(rG1 k : 𝕜)‖ ≤ 1 := by
  unfold rG1; split_ifs <;> simp

theorem rG1_head : ∀ k : ℤ, k.natAbs ≤ 0 → (rG1 k : 𝕜) = 0 := by
  intro k hk; rw [rG1, ite_eq_left (by omega)]

/-- G1: `M P = M` holds. -/
theorem G1_MP : (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ∘L headP 0 = MG1 := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.headProj_single]
  split_ifs with h
  · rfl
  · rw [map_zero, MG1_single, colsG1, ite_eq_right (by rw [mem_winZ] at h; omega)]

/-- G1: `P M = M` fails. -/
theorem G1_PM_ne : headP 0 ∘L (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ≠ MG1 := by
  intro h
  have h1 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  rw [ContinuousLinearMap.comp_apply, MG1_single, colsG1, ite_eq_left rfl, map_neg,
      lpOneAlg.headProj_single,
    ite_eq_right (by rw [mem_winZ]; omega), neg_zero] at h1
  exact single_ne_zero' (𝕜 := 𝕜) (ν := ν) 1 (neg_eq_zero.mp h1.symm)

theorem bG1_mul_e1 :
    (bG1 : 𝓔 𝕜 ν) * lpOneAlg.single 1 1 = lpOneAlg.single 0 1 + lpOneAlg.single 1 1 := by
  rw [bG1, add_mul, lpOneAlg.single_mul_single, lpOneAlg.single_mul_single, mul_one]
  norm_num

theorem G1_Hd_e1 :
    defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1 (lpOneAlg.single 1 1) = -(lpOneAlg.single 1 1) := by
  rw [defectHead_single, ite_eq_right (by omega), bG1_mul_e1, map_add, lpOneAlg.headProj_single,
      lpOneAlg.headProj_single,
    ite_eq_left (mem_winZ.mpr (by omega)), ite_eq_right (by rw [mem_winZ]; omega), add_zero,
    MG1_single, colsG1, ite_eq_left rfl]

theorem G1_Tl_e1 :
    defectTail rG1 1 norm_rG1_le (bG1 : 𝓔 𝕜 ν) (lpOneAlg.single 1 1) = lpOneAlg.single 1 1 := by
  rw [defectTail_single, bG1_mul_e1, map_add, lpOneAlg.diagCLM_single, lpOneAlg.diagCLM_single,
      rG1, rG1, ite_eq_left rfl,
    ite_eq_right (by omega), zero_mul, one_mul, single_zero', zero_add]

/-- G1: the defect column at `e₁` cancels, `D e₁ = 0`. -/
theorem G1_defect_e1 :
    defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1 1 norm_rG1_le bG1 (lpOneAlg.single 1 1) = 0 := by
  rw [defect_eq, add_apply, G1_Hd_e1, G1_Tl_e1, neg_add_cancel]

/-- G1: while the head and tail column norms add up to `2ν`. -/
theorem G1_sum :
    ‖defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1 (lpOneAlg.single 1 1)‖
      + ‖defectTail rG1 1 norm_rG1_le (bG1 : 𝓔 𝕜 ν) (lpOneAlg.single 1 1)‖ = 2 * (ν : ℝ) := by
  rw [G1_Hd_e1, G1_Tl_e1, norm_neg, lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul]
  simp; ring

/-- G1: the column identity C4 fails without `P M = M` (the other C4 hypotheses hold:
`r = 0` on the head, and `b` is banded with `m = 1`). -/
theorem G1_C4_fails :
    colRatio (defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1 1 norm_rG1_le bG1) 1
      ≠ colRatio (defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1) 1
        + colRatio (defectTail rG1 1 norm_rG1_le (bG1 : 𝓔 𝕜 ν)) 1 := by
  have hν : (0 : ℝ) < ν := ν.2
  simp only [colRatio_geom]
  rw [G1_defect_e1, norm_zero, zero_div, ← add_div, G1_sum]
  simp only [Int.natAbs_one, pow_one]
  rw [mul_div_assoc, div_self hν.ne', mul_one]
  norm_num

theorem G1_band : ∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (bG1 : 𝓔 𝕜 ν) i = 0 := by
  intro i hi
  rw [bG1, lpOneAlg.toRealSeq_add, Pi.add_apply, lpOneAlg.toRealSeq_single,
      lpOneAlg.toRealSeq_single,
    ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

end G1

/-! ### G1′ — RANGE at the NORM level: without `P M = M` the aggregate B1/K2 fails

Same `M` as G1 (`MG1`: `M e₀ = −e₁`, so `M P = M` but `P M ≠ M`) and `b = e₋₁ + e₀`, but the tail
symbol `r = 1_{k = 1}` (`N = 0`; `r = 0` on the head; band `m = 1`; `hmono` from `K₀ = 1`). The
only nonzero column of `D` is `D e₂ = e₁` (at `j = 1`: `defectHead e₁ = −e₁`,
    `defectTail e₁ = e₁`), so
`‖D‖ = ν⁻¹`, while `a₁ = s₁ = 1`: `2 ≤ ⨆ j (a_j + s_j)`. The colRatio-form window theorem still
applies to the same data (`G1'_window`). -/

section G1'

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G1′ tail symbol `r_k = 1_{k = 1}`. -/
def rG1' (k : ℤ) : 𝕜 := if k = 1 then 1 else 0

theorem norm_rG1'_le (k : ℤ) : ‖(rG1' k : 𝕜)‖ ≤ 1 := by
  unfold rG1'; split_ifs <;> simp

theorem rG1'_head : ∀ k : ℤ, k.natAbs ≤ 0 → (rG1' k : 𝕜) = 0 := by
  intro k hk; rw [rG1', ite_eq_right (by omega)]

/-- G1′: `hmono` from `K₀ = 1` (at `n = 1`: `‖r 2‖ = 0 ≤ 1 = ‖r 1‖` and
`‖r (−2)‖ = 0 ≤ 0 = ‖r (−1)‖`; beyond, both sides vanish). -/
theorem G1'_hmono : ∀ n : ℕ, max (0 + 1) 1 ≤ n →
    ‖(rG1' ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rG1' (n : ℤ) : 𝕜)‖ ∧
    ‖(rG1' (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rG1' (-(n : ℤ)) : 𝕜)‖ := by
  intro n hn
  have hn1 : 1 ≤ n := by simpa using hn
  refine ⟨?_, ?_⟩
  · rw [rG1', ite_eq_right (by omega), norm_zero]; exact norm_nonneg _
  · rw [rG1', ite_eq_right (by omega), norm_zero]; exact norm_nonneg _

theorem bG1_mul_single (j : ℤ) :
    (bG1 : 𝓔 𝕜 ν) * lpOneAlg.single j 1 = lpOneAlg.single (j - 1) 1 + lpOneAlg.single j 1 := by
  rw [bG1, add_mul, lpOneAlg.single_mul_single, lpOneAlg.single_mul_single, mul_one, zero_add,
    show (-1 : ℤ) + j = j - 1 by ring]

/-- G1′: the columns of `D`: `D e₂ = e₁`, every other column is `0`. -/
theorem G1'_defect_single (j : ℤ) :
    defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1 (lpOneAlg.single j 1)
      = if j = 2 then lpOneAlg.single 1 1 else 0 := by
  rw [defect_eq, add_apply, defectHead_single, defectTail_single, bG1_mul_single]
  simp only [map_add, lpOneAlg.diagCLM_single, mul_one]
  by_cases h0 : j = 0
  · subst h0
    simp [rG1', single_zero']
  · by_cases h1 : j = 1
    · subst h1
      simp [rG1', single_zero', lpOneAlg.headProj_single, mem_winZ, MG1_single, colsG1]
    · by_cases h2 : j = 2
      · subst h2
        simp [rG1', single_zero', lpOneAlg.headProj_single, mem_winZ]
      · have ha : ¬ j.natAbs ≤ 0 := by omega
        have hb : ¬ (j - 1).natAbs ≤ 0 := by omega
        have hc : ¬ j - 1 = 1 := by omega
        simp [rG1', single_zero', lpOneAlg.headProj_single, mem_winZ, ha, hb, hc, h1, h2]

/-- G1′: `‖D‖ = ν⁻¹` (the single nonzero column `D e₂ = e₁` has ratio `ν / ν²`). -/
theorem G1'_norm :
    ‖defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1‖ = (ν : ℝ)⁻¹ := by
  have hν : (0 : ℝ) < ν := ν.2
  have e : (ν : ℝ) ^ (1 : ℤ).natAbs = (ν : ℝ)⁻¹ * (ν : ℝ) ^ (2 : ℤ).natAbs := by
    norm_num; field_simp
  apply le_antisymm
  · refine (lpOneAlg.opNorm_le_iff_cols _ (inv_nonneg.mpr hν.le)).mpr fun j => ?_
    rw [geomFiberZ_weight, G1'_defect_single]
    split_ifs with h
    · subst h
      rw [lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul, e]
    · rw [norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hν.le) (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).le
  · have h := colRatio_le_opNorm
      (defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1) 2
    rwa [colRatio_geom, G1'_defect_single, ite_eq_left rfl, lpOneAlg.norm_single,
        geomFiberZ_weight, norm_one, one_mul, e,
      mul_div_assoc, div_self (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).ne', mul_one] at h

/-- G1′: at `j = 1` the head and tail columns are `a₁ = 1` and `s₁ = 1`. -/
theorem G1'_colsum_one :
    colRatio (defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1) 1
      + colRatio (defectTail rG1' 1 norm_rG1'_le (bG1 : 𝓔 𝕜 ν)) 1 = 2 := by
  have e0 : (rG1' 0 : 𝕜) = 0 := by rw [rG1', ite_eq_right (by decide)]
  have e1 : (rG1' 1 : 𝕜) = 1 := by rw [rG1', ite_eq_left rfl]
  simp only [colRatio_geom]
  rw [G1_Hd_e1, defectTail_single, bG1_mul_e1, map_add, lpOneAlg.diagCLM_single,
      lpOneAlg.diagCLM_single, e0, e1,
    zero_mul, one_mul, single_zero', zero_add, norm_neg, lpOneAlg.norm_single, geomFiberZ_weight,
    norm_one, one_mul,
    div_self (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).ne']
  norm_num

/-- G1′: `2 ≤ ⨆ j (a_j + s_j)`. -/
theorem G1'_iSup_ge :
    (2 : ℝ) ≤ ⨆ j : ℤ, (colRatio (defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1) j
      + colRatio (defectTail rG1' 1 norm_rG1'_le (bG1 : 𝓔 𝕜 ν)) j) := by
  have hb : BddAbove (Set.range fun j : ℤ =>
      colRatio (defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1) j
        + colRatio (defectTail rG1' 1 norm_rG1'_le (bG1 : 𝓔 𝕜 ν)) j) := by
    refine ⟨‖defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1‖
      + ‖defectTail rG1' 1 norm_rG1'_le (bG1 : 𝓔 𝕜 ν)‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact add_le_add (colRatio_le_opNorm _ j) (colRatio_le_opNorm _ j)
  rw [← G1'_colsum_one (𝕜 := 𝕜) (ν := ν)]
  exact le_ciSup hb 1

/-- **G1′: the aggregate formula B1/K2 FAILS at the norm level without `P M = M`**
(`M P = M`, `r = 0` on the head, band `m = 1` and `hmono` from `K₀ = 1` all hold):
`‖D‖ = ν⁻¹ ≤ 1 < 2 ≤ ⨆ j (a_j + s_j)`. -/
theorem G1'_B1_fails :
    ‖defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1‖
      < ⨆ j : ℤ, (colRatio (defectHead 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1) j
          + colRatio (defectTail rG1' 1 norm_rG1'_le (bG1 : 𝓔 𝕜 ν)) j) := by
  have h1 : (ν : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Fact.out : (1 : ℝ) ≤ ν)
  rw [G1'_norm]
  linarith [G1'_iSup_ge (𝕜 := 𝕜) (ν := ν)]

/-- G1′: the conclusion of `opNorm_defect_eq_sup'_explicit` is false for this data (all its
hypotheses except `P M = M` hold). -/
theorem G1'_explicit_fails :
    ‖defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1‖
      < (winZ (1 + max (0 + 1) 1)).sup' (winZ_nonempty _)
          (fun j => headCol 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1 j
            + tailCol 1 rG1' (bG1 : 𝓔 𝕜 ν) j) := by
  have h1 : (ν : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Fact.out : (1 : ℝ) ≤ ν)
  have h2 : headCol 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1 1 + tailCol 1 rG1' (bG1 : 𝓔 𝕜 ν) 1 = 2 := by
    rw [← colRatio_defectHead_eq_headCol, ← colRatio_defectTail 1 rG1' 1 norm_rG1'_le _ G1_band,
      G1'_colsum_one]
  have h3 := Finset.le_sup'
    (fun j => headCol 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1 j + tailCol 1 rG1' (bG1 : 𝓔 𝕜 ν) j)
    (mem_winZ.mpr (show (1 : ℤ).natAbs ≤ 1 + max (0 + 1) 1 by decide))
  simp only [h2] at h3
  rw [G1'_norm]
  linarith

/-- G1′: the colRatio-form window theorem (v2, no `P M = M`) applies to the same data. -/
theorem G1'_window :
    ‖defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1‖
      = (winZ (1 + max (0 + 1) 1)).sup' (winZ_nonempty _)
          (fun j => colRatio (defect 0 (MG1 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1' 1 norm_rG1'_le bG1) j) :=
  opNorm_defect_eq_sup' (𝕜 := 𝕜) (ν := ν) 0 1 1 MG1 rG1' 1 norm_rG1'_le bG1 G1_band G1'_hmono

end G1'

/-! ### G1″ — HEAD-VANISHING at the NORM level: without `r = 0` on the head the split fails

`N = 0`, `M = −P₀` (the operator whose only nonzero column is `0 ↦ −e₀`; `P M = M` and
`M P = M`), `b = e₋₁` (band `m = 1`), `r = 1_{k = 0}` (so `hr0` FAILS; `hmono` holds for every
`K₀`). Then `D = 0`: at `j = 1`, `defectHead e₁ = M P e₀ = −e₀` cancels
`defectTail e₁ = r₀ e₀ = e₀`; every other
column vanishes. But `a₁ = s₁ = 1/ν`, so `a₁ + s₁ = 2/ν`. -/

section G1''

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G1″ head block `M = −P₀`. -/
def MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν := -headP 0

/-- G1″: `M = −P₀` is the operator with the single nonzero column `0 ↦ −e₀`. -/
theorem MG1''_single (j : ℤ) :
    (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (lpOneAlg.single j 1)
      = if j = 0 then -(lpOneAlg.single 0 1) else 0 := by
  rw [MG1'', neg_apply, lpOneAlg.headProj_single]
  by_cases h : j = 0
  · subst h; rw [ite_eq_left (mem_winZ.mpr (by decide)), ite_eq_left rfl]
  · rw [ite_eq_right (by rw [mem_winZ]; omega), ite_eq_right h, neg_zero]

theorem G1''_PM : headP 0 ∘L (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) = MG1'' := by
  rw [MG1'', ContinuousLinearMap.comp_neg, lpOneAlg.headProj_comp_headProj]

theorem G1''_MP : (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ∘L headP 0 = MG1'' := by
  rw [MG1'', ContinuousLinearMap.neg_comp, lpOneAlg.headProj_comp_headProj]

/-- G1″ multiplier `b = e₋₁` (band `m = 1`). -/
def bG1'' : 𝓔 𝕜 ν := lpOneAlg.single (-1) 1

omit [Fact (1 ≤ (ν : ℝ))] in
theorem G1''_band : ∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (bG1'' : 𝓔 𝕜 ν) i = 0 :=
  band_single 1 (-1) 1 (by decide)

theorem bG1''_mul (j : ℤ) :
    (bG1'' : 𝓔 𝕜 ν) * lpOneAlg.single j 1 = lpOneAlg.single (j - 1) 1 := by
  rw [bG1'', lpOneAlg.single_mul_single, mul_one, show (-1 : ℤ) + j = j - 1 by ring]

/-- G1″ symbol `r_k = 1_{k = 0}`: NOT zero on the head. -/
def rG1'' (k : ℤ) : 𝕜 := if k = 0 then 1 else 0

theorem norm_rG1''_le (k : ℤ) : ‖(rG1'' k : 𝕜)‖ ≤ 1 := by
  unfold rG1''; split_ifs <;> simp

/-- G1″: head-vanishing FAILS. -/
theorem G1''_hr0_fails : ¬ ∀ k : ℤ, k.natAbs ≤ 0 → (rG1'' k : 𝕜) = 0 := by
  intro h
  have := h 0 (by decide)
  rw [rG1'', ite_eq_left rfl] at this
  exact one_ne_zero this

/-- G1″: `hmono` holds for every `K₀` (both sides vanish for `n ≥ 1`). -/
theorem G1''_hmono (K₀ : ℕ) : ∀ n : ℕ, max (0 + 1) K₀ ≤ n →
    ‖(rG1'' ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rG1'' (n : ℤ) : 𝕜)‖ ∧
    ‖(rG1'' (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rG1'' (-(n : ℤ)) : 𝕜)‖ := by
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  refine ⟨?_, ?_⟩
  · rw [rG1'', ite_eq_right (by omega), norm_zero]; exact norm_nonneg _
  · rw [rG1'', ite_eq_right (by omega), norm_zero]; exact norm_nonneg _

/-- G1″: `D = 0`. -/
theorem G1''_defect_zero :
    defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le bG1'' = 0 := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [defect_eq, add_apply, zero_apply, defectHead_single, defectTail_single, bG1''_mul,
      lpOneAlg.diagCLM_single, mul_one]
  by_cases h0 : j = 0
  · subst h0
    rw [ite_eq_left (by decide), zero_add, rG1'', ite_eq_right (by decide), single_zero']
  · rw [ite_eq_right (by omega), lpOneAlg.headProj_single]
    by_cases h1 : j = 1
    · subst h1
      rw [show (1 : ℤ) - 1 = 0 by norm_num, ite_eq_left (mem_winZ.mpr (by decide)), MG1''_single,
          ite_eq_left rfl, rG1'',
        ite_eq_left rfl, neg_add_cancel]
    · rw [ite_eq_right (by rw [mem_winZ]; omega), map_zero, zero_add, rG1'',
        ite_eq_right (by omega), single_zero']

/-- G1″: at `j = 1`, `a₁ + s₁ = 2/ν`. -/
theorem G1''_colsum_one :
    colRatio (defectHead 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'') 1
      + colRatio (defectTail rG1'' 1 norm_rG1''_le (bG1'' : 𝓔 𝕜 ν)) 1 = 2 / (ν : ℝ) := by
  have e0 : (rG1'' 0 : 𝕜) = 1 := by rw [rG1'', ite_eq_left rfl]
  simp only [colRatio_geom]
  rw [defectHead_single, ite_eq_right (by decide), defectTail_single, bG1''_mul,
      show (1 : ℤ) - 1 = 0 by norm_num,
    lpOneAlg.headProj_single, ite_eq_left (mem_winZ.mpr (by decide)), MG1''_single, ite_eq_left rfl,
    lpOneAlg.diagCLM_single, e0, mul_one,
    norm_neg, lpOneAlg.norm_single, geomFiberZ_weight, norm_one, one_mul, ← add_div]
  norm_num

/-- **G1″: the aggregate formula B1/K2 FAILS at the norm level without `r = 0` on the head**
(`P M = M`, `M P = M`, band `m = 1` and `hmono` hold): `‖D‖ = 0 < 2/ν ≤ ⨆ j (a_j + s_j)`. -/
theorem G1''_B1_fails :
    ‖defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le bG1''‖
      < ⨆ j : ℤ, (colRatio (defectHead 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'') j
          + colRatio (defectTail rG1'' 1 norm_rG1''_le (bG1'' : 𝓔 𝕜 ν)) j) := by
  have hb : BddAbove (Set.range fun j : ℤ =>
      colRatio (defectHead 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'') j
        + colRatio (defectTail rG1'' 1 norm_rG1''_le (bG1'' : 𝓔 𝕜 ν)) j) := by
    refine ⟨‖defectHead 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1''‖
      + ‖defectTail rG1'' 1 norm_rG1''_le (bG1'' : 𝓔 𝕜 ν)‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact add_le_add (colRatio_le_opNorm _ j) (colRatio_le_opNorm _ j)
  rw [G1''_defect_zero, norm_zero]
  refine lt_of_lt_of_le ?_ (le_ciSup hb 1)
  rw [G1''_colsum_one]
  exact div_pos two_pos ν.2

/-- G1″: the conclusion of `opNorm_defect_eq_sup'_explicit` is false for this data (all its
hypotheses except `r = 0` on the head hold). -/
theorem G1''_explicit_fails :
    ‖defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le bG1''‖
      < (winZ (1 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => headCol 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'' j
            + tailCol 1 rG1'' (bG1'' : 𝓔 𝕜 ν) j) := by
  have h2 : headCol 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'' 1 + tailCol 1 rG1'' (bG1'' : 𝓔 𝕜 ν) 1
      = 2 / (ν : ℝ) := by
    rw [← colRatio_defectHead_eq_headCol, ← colRatio_defectTail 1 rG1'' 1 norm_rG1''_le _ G1''_band,
      G1''_colsum_one]
  have h3 := Finset.le_sup'
    (fun j => headCol 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'' j + tailCol 1 rG1'' (bG1'' : 𝓔 𝕜 ν) j)
    (mem_winZ.mpr (show (1 : ℤ).natAbs ≤ 1 + max (0 + 1) 0 by decide))
  simp only [h2] at h3
  rw [G1''_defect_zero, norm_zero]
  exact lt_of_lt_of_le (div_pos two_pos ν.2) h3

/-- G1″: the column identity C4 fails at `j = 1`. -/
theorem G1''_C4_fails :
    colRatio (defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le bG1'') 1
      ≠ colRatio (defectHead 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) bG1'') 1
        + colRatio (defectTail rG1'' 1 norm_rG1''_le (bG1'' : 𝓔 𝕜 ν)) 1 := by
  rw [G1''_defect_zero, colRatio_zero, G1''_colsum_one]
  exact (div_pos two_pos ν.2).ne

/-- G1″: the colRatio-form window theorem (v2, no `hr0`) applies to the same data. -/
theorem G1''_window :
    ‖defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le bG1''‖
      = (winZ (1 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => colRatio (defect 0 (MG1'' : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) rG1'' 1 norm_rG1''_le
            bG1'') j) :=
  opNorm_defect_eq_sup' (𝕜 := 𝕜) (ν := ν) 0 1 0 MG1'' rG1'' 1 norm_rG1''_le bG1'' G1''_band
    (G1''_hmono 0)

end G1''

/-! ### G7 — the DECLARED BAND decides the window radius: a multiplier outside band `m` breaks
`winZ (N + m + 1)`

(v2 wording, finding C3: G7 is a mis-declared-band test with a ONE-ATOM multiplier; the same `b`
satisfies band `m + 1` and the window theorem applies at `N + m + 2` (`G7_true_band`).
Infinite support is tested by G9.)

`b = e_{−(m+1)}` violates the band `m`; with the one-sided symbol
`r_k = 1_{k > 0, |k| > N} / k`, the column `j` of `D = R L_b` is `r_{j−m−1} ν^{|j−m−1|} / ν^{|j|}`,
which vanishes for `j ≤ N + m + 1` and is positive at `j = N + m + 2`, just outside the window
`|j| ≤ N + m + 1`. (The other sign of the shift puts the maximiser at `j = N − m`, INSIDE the
window, so it is not a test.) -/

section G7

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G7 one-sided symbol. -/
def rOne (N : ℕ) (k : ℤ) : 𝕜 := if 0 < k ∧ N < k.natAbs then (k : 𝕜)⁻¹ else 0

theorem norm_rOne_le (N : ℕ) (k : ℤ) : ‖(rOne N k : 𝕜)‖ ≤ 1 := by
  unfold rOne
  split_ifs with h
  · rw [norm_inv, ← RCLike.ofReal_intCast, RCLike.norm_ofReal]
    have : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs (show k ≠ 0 by omega)
    exact inv_le_one_of_one_le₀ this
  · simp

theorem rOne_head (N : ℕ) : ∀ k : ℤ, k.natAbs ≤ N → (rOne N k : 𝕜) = 0 := by
  intro k hk; rw [rOne, ite_eq_right (by omega)]

theorem norm_rOne_tail (N : ℕ) (n : ℕ) (hn : N < n) :
    ‖(rOne N (n : ℤ) : 𝕜)‖ = ((n : ℝ))⁻¹ := by
  rw [rOne, ite_eq_left ⟨by omega, by omega⟩, norm_inv, ← RCLike.ofReal_intCast, RCLike.norm_ofReal,
    Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]

/-- G7: `hmono` holds from `N + 1` (the left ray is identically `0`). -/
theorem G7_hmono (N : ℕ) : ∀ n : ℕ, N + 1 ≤ n →
    ‖(rOne N ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rOne N (n : ℤ) : 𝕜)‖ ∧
    ‖(rOne N (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rOne N (-(n : ℤ)) : 𝕜)‖ := by
  intro n hn
  refine ⟨?_, ?_⟩
  · rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, norm_rOne_tail N _ (by omega),
      norm_rOne_tail N _ (by omega)]
    have h1 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    push_cast
    exact inv_anti₀ h1 (by linarith)
  · rw [rOne, rOne, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- G7 multiplier `b = e_{−(m+1)}`: outside the band `m`. -/
def bG7 (m : ℕ) : 𝓔 𝕜 ν := lpOneAlg.single (-((m : ℤ) + 1)) 1

omit [Fact (1 ≤ (ν : ℝ))] in
/-- G7: the band hypothesis FAILS for `bG7 m` at band `m`. -/
theorem G7_band_fails (m : ℕ) :
    ¬ ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (bG7 m : 𝓔 𝕜 ν) i = 0 := by
  intro h
  have := h (-((m : ℤ) + 1)) (by omega)
  rw [bG7, lpOneAlg.toRealSeq_single, ite_eq_left rfl] at this
  exact one_ne_zero this

/-- G7 defect (`M = 0`). -/
abbrev DG7 (N m : ℕ) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν := defect N 0 (rOne N) 1 (norm_rOne_le N) (bG7 m)

theorem colRatio_DG7 (N m : ℕ) (j : ℤ) :
    colRatio (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j
      = ‖(rOne N (j - ((m : ℤ) + 1)) : 𝕜)‖ * (ν : ℝ) ^ (j - ((m : ℤ) + 1)).natAbs
          / (ν : ℝ) ^ j.natAbs := by
  rw [DG7, defect_M_zero, colRatio_geom, defectTail_single, bG7, lpOneAlg.single_mul_single,
      mul_one,
    lpOneAlg.diagCLM_single, mul_one, lpOneAlg.norm_single, geomFiberZ_weight,
    show -((m : ℤ) + 1) + j = j - ((m : ℤ) + 1) by ring]

/-- G7: every column inside the window `|j| ≤ N + m + 1` is zero. -/
theorem G7_window_zero (N m : ℕ) :
    (winZ (N + m + 1)).sup' (winZ_nonempty _)
      (fun j => colRatio (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j) = 0 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j hj => ?_
    rw [mem_winZ] at hj
    rw [colRatio_DG7, rOne, ite_eq_right (by omega), norm_zero, zero_mul, zero_div]
  · exact (colRatio_nonneg _ 0).trans (Finset.le_sup' _ (mem_winZ.mpr (by simp)))

/-- G7: the column `j = N + m + 2` (outside the window) is positive. -/
theorem G7_outside_pos (N m : ℕ) :
    0 < colRatio (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ((N : ℤ) + m + 2) := by
  rw [colRatio_DG7, show (N : ℤ) + m + 2 - ((m : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) by push_cast; ring,
    norm_rOne_tail N (N + 1) (by omega)]
  have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  exact div_pos (mul_pos (inv_pos.mpr this) (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _))
    (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _)

/-- **G7: the declared band is decisive for the window radius.** All other window hypotheses
hold (`P M = M` with `M = 0`,
`r = 0` on the head, `hmono` from `N + 1`), the band fails, and the window maximum over
`|j| ≤ N + m + 1` is strictly below the operator norm. -/
theorem G7_gap (N m : ℕ) :
    (winZ (N + m + 1)).sup' (winZ_nonempty _)
        (fun j => colRatio (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j)
      < ‖(DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ := by
  rw [G7_window_zero]
  exact (G7_outside_pos N m).trans_le (colRatio_le_opNorm (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) _)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- G7: `bG7 m` DOES satisfy the band `m + 1` (one atom at `−(m + 1)`). -/
theorem G7_band_succ (m : ℕ) :
    ∀ i : ℤ, m + 1 < i.natAbs → lpOneAlg.toRealSeq (bG7 m : 𝓔 𝕜 ν) i = 0 :=
  band_single (m + 1) _ 1 (by omega)

/-- **G7 with the TRUE band** (fix round 1, F5): `bG7 m` satisfies the band `m + 1`, and the
window theorem applies with window `N + m + 2`. So G7 is a MIS-DECLARED-band test (the declared
band `m` decides the window radius), not an infinite-support test (that is G9). -/
theorem G7_true_band (N m : ℕ) :
    (∀ i : ℤ, m + 1 < i.natAbs → lpOneAlg.toRealSeq (bG7 m : 𝓔 𝕜 ν) i = 0) ∧
      ‖(DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖
        = (winZ (N + m + 2)).sup' (winZ_nonempty _)
            (fun j => colRatio (DG7 N m : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j) := by
  refine ⟨G7_band_succ m, ?_⟩
  have h := opNorm_defect_eq_sup'_first (𝕜 := 𝕜) (ν := ν) N (m + 1) 0 (rOne N) 1
    (norm_rOne_le N) (bG7 m) (G7_band_succ m) (G7_hmono N)
  rwa [show N + (m + 1) + 1 = N + m + 2 by ring] at h

end G7

/-! ### G9 — INFINITE SUPPORT (consensus K9 (7)): no finite window attains the norm

`ν = 1` (the literal `nu1`), `N = 0`, `M = 0`, `r = 1_{k ≠ 0}` (`rConst 0`), and the
infinite-support multiplier `b_i = 2^{−|i|}` (in `ℓ¹`: `Σ_i 2^{−|i|} = 3`). Every hypothesis of
the window theorem holds EXCEPT the band, which fails for every `m`. The columns are
`colRatio D j = 3 − 2^{−|j|} < 3 = ‖D‖`: the norm is attained by no column and by no finite
window, so the band hypothesis cannot be replaced by "`b ∈ ℓ¹`". -/

section G9

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

/-- The literal weight `ν = 1`. -/
def nu1 : PosReal := ⟨1, one_pos⟩

/-- `ν = 1 ≥ 1` (a LOCAL instance: no global instance on a literal weight). -/
theorem fact_one_le_nu1 : Fact (1 ≤ ((nu1 : PosReal) : ℝ)) := ⟨le_rfl⟩

attribute [local instance] fact_one_le_nu1

theorem nu1_weight (k : ℤ) : ((nu1 : PosReal) : ℝ) ^ k.natAbs = 1 := one_pow _

/-- `geo i = 2^{−|i|}`. -/
def geo (i : ℤ) : ℝ := (2 : ℝ)⁻¹ ^ i.natAbs

theorem geo_pos (i : ℤ) : 0 < geo i := pow_pos (by norm_num) _

theorem geo_neg (i : ℤ) : geo (-i) = geo i := by rw [geo, geo, Int.natAbs_neg]

/-- `Σ_{i ∈ ℤ} 2^{−|i|} = 2 + 1 = 3`. -/
theorem hasSum_geo : HasSum geo 3 := by
  have hg := hasSum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h1 : HasSum (fun n : ℕ => geo n) 2 := by
    have e : (fun n : ℕ => geo n) = fun n : ℕ => (2 : ℝ)⁻¹ ^ n := by
      funext n; rw [geo, show ((n : ℤ)).natAbs = n by omega]
    rw [show (1 - (2 : ℝ)⁻¹)⁻¹ = 2 by norm_num] at hg
    rw [e]; exact hg
  have h2 : HasSum (fun n : ℕ => geo (-((n : ℤ) + 1))) 1 := by
    have e : (fun n : ℕ => geo (-((n : ℤ) + 1))) = fun n : ℕ => (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n := by
      funext n; rw [geo, show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ']
    have h := hg.mul_left (2 : ℝ)⁻¹
    rw [show (2 : ℝ)⁻¹ * (1 - (2 : ℝ)⁻¹)⁻¹ = 1 by norm_num] at h
    rw [e]; exact h
  have h := h1.of_nat_of_neg_add_one h2
  norm_num at h
  exact h

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The fibre values of `b` (`b_k = 2^{−|k|}`). -/
def bG9Fun (k : ℤ) : geomFiberZ 𝕜 nu1 k :=
  FiberTrivialization.equiv (E := geomFiberZ 𝕜 nu1) k
    ((geo k : ℝ) : 𝕜)

theorem norm_bG9Fun (k : ℤ) : ‖(bG9Fun k : WeightedScalar 𝕜 _ k)‖ = geo k := by
  rw [bG9Fun, FiberTrivialization.norm_equiv_apply, geomFiberZ_weight, nu1_weight, mul_one,
    RCLike.norm_ofReal, abs_of_pos (geo_pos k)]

theorem bG9Fun_mem : Memℓp (bG9Fun (𝕜 := 𝕜)) 1 := by
  refine memℓp_gen (hasSum_geo.summable.congr fun k => ?_)
  rw [ENNReal.toReal_one, Real.rpow_one, norm_bG9Fun]

/-- G9 multiplier `b = Σ_i 2^{−|i|} e_i`: infinite support, in `ℓ¹_1`. -/
def bG9 : 𝓔 𝕜 nu1 := ⟨⟨bG9Fun, bG9Fun_mem⟩⟩

theorem toRealSeq_bG9 (k : ℤ) : lpOneAlg.toRealSeq (bG9 : 𝓔 𝕜 nu1) k = ((geo k : ℝ) : 𝕜) :=
  FiberTrivialization.equiv_symm_apply_equiv k _

/-- G9: `rConst 0` is the brief's symbol `r_k = if k = 0 then 0 else 1`. -/
theorem G9_r_eq (k : ℤ) : (rConst 0 k : 𝕜) = if k = 0 then 0 else 1 := by
  rw [rConst]
  by_cases hk : k = 0
  · rw [ite_eq_left (by omega), ite_eq_left hk]
  · rw [ite_eq_right (by omega), ite_eq_right hk]

/-- G9: the band fails for EVERY `m` (`b_{m+1} = 2^{−(m+1)} ≠ 0`). -/
theorem G9_band_fails (m : ℕ) :
    ¬ ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (bG9 : 𝓔 𝕜 nu1) i = 0 := by
  intro h
  have := h ((m : ℤ) + 1) (by omega)
  rw [toRealSeq_bG9, RCLike.ofReal_eq_zero] at this
  exact (geo_pos _).ne' this

/-- G9: the other hypotheses of the window theorem hold (`r = 0` on the head, `hmono` for every
`K₀`, `P M = M` for `M = 0`). -/
theorem G9_other_hyps (K₀ : ℕ) :
    (∀ k : ℤ, k.natAbs ≤ 0 → (rConst 0 k : 𝕜) = 0) ∧
    (∀ n : ℕ, max (0 + 1) K₀ ≤ n →
      ‖(rConst 0 ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rConst 0 (n : ℤ) : 𝕜)‖ ∧
      ‖(rConst 0 (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rConst 0 (-(n : ℤ)) : 𝕜)‖) ∧
    headP 0 ∘L (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) = 0 :=
  ⟨rConst_head 0, fun n hn => by
    have hN : 0 + 1 ≤ n := (le_max_left _ _).trans hn
    rw [rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega),
      rConst_tail 0 _ (by omega)]
    exact ⟨le_rfl, le_rfl⟩, headP_comp_zero 0⟩

/-- G9 defect: `N = 0`, `M = 0`, `r = 1_{k ≠ 0}`, `b = bG9`, `ν = 1`. -/
abbrev D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1 := defect 0 0 (rConst 0) 1 (norm_rConst_le 0) bG9

/-- G9: the exact columns `colRatio D j = 3 − 2^{−|j|}` (the omitted term is `k = 0`). -/
theorem colRatio_D9 (j : ℤ) : colRatio (D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j = 3 - geo j := by
  have hs : HasSum (fun k : ℤ => geo (k - j)) 3 := by
    have h := (Equiv.subRight j).hasSum_iff (f := geo) (a := 3)
    rw [show (geo ∘ ⇑(Equiv.subRight j)) = fun k : ℤ => geo (k - j) from
      funext fun k => by simp only [Function.comp_apply, Equiv.subRight_apply]] at h
    exact h.mpr hasSum_geo
  have hz : HasSum (fun k : ℤ => if k = 0 then geo (0 - j) else 0) (geo (0 - j)) :=
    hasSum_ite_eq 0 _
  have ht : HasSum (fun k : ℤ =>
      ‖lpOneAlg.toRealSeq
        (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 nu1) (rConst 0 : ℤ → 𝕜) 1 (norm_rConst_le 0)
          ((bG9 : 𝓔 𝕜 nu1) * lpOneAlg.single j 1)) k‖
        * ((nu1 : PosReal) : ℝ) ^ k.natAbs) (3 - geo j) := by
    rw [show geo j = geo (0 - j) by rw [zero_sub, geo_neg]]
    refine (hs.sub hz).congr_fun fun k => ?_
    rw [lpOneAlg.toRealSeq_diagCLM, toRealSeq_mul_single, toRealSeq_bG9, nu1_weight, mul_one,
        norm_mul,
      RCLike.norm_ofReal, abs_of_pos (geo_pos _)]
    by_cases hk : k = 0
    · subst hk
      rw [rConst_head 0 0 (by decide), norm_zero, zero_mul, ite_eq_left rfl, sub_self]
    · rw [rConst_tail 0 k (by omega), norm_one, one_mul, ite_eq_right hk, sub_zero]
  rw [D9, defect_M_zero, colRatio_geom, defectTail_single, nu1_weight, div_one, norm_eq_tsum_coeff,
    ht.tsum_eq]

/-- **G9 (i): `‖D‖ = 3`** (= `⨆ j colRatio D j`, a supremum approached as `|j| → ∞`). -/
theorem G9_norm : ‖(D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)‖ = 3 := by
  rw [opNorm_eq_iSup_cols]
  simp only [colRatio_D9]
  have hbdd : BddAbove (Set.range fun j : ℤ => 3 - geo j) :=
    ⟨3, by rintro _ ⟨j, rfl⟩; linarith [geo_pos j]⟩
  apply le_antisymm
  · exact ciSup_le fun j => by linarith [geo_pos j]
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hc) (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hg : geo (n : ℤ) = (2 : ℝ)⁻¹ ^ n := by rw [geo, show ((n : ℤ)).natAbs = n by omega]
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd (n : ℤ))
    rw [hg]; linarith

/-- **G9 (ii): every column is strictly below the norm** — the norm is attained at no column. -/
theorem G9_col_lt (j : ℤ) :
    colRatio (D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j < ‖(D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)‖ := by
  rw [colRatio_D9, G9_norm]; linarith [geo_pos j]

/-- G9: attainment (D3) fails at every atom. -/
theorem G9_not_attained (j : ℤ) :
    ‖(D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (lpOneAlg.single j 1)‖
      ≠ ‖(D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)‖ * ((nu1 : PosReal) : ℝ) ^ j.natAbs := by
  intro h
  have h1 := G9_col_lt (𝕜 := 𝕜) j
  rw [colRatio_geom, h, nu1_weight, mul_one, div_one] at h1
  exact lt_irrefl _ h1

/-- **G9: no finite window gives the norm**: for every `W`, the window maximum is strictly
below `‖D‖`. -/
theorem G9_no_window (W : ℕ) :
    (winZ W).sup' (winZ_nonempty W) (fun j => colRatio (D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j)
      < ‖(D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)‖ := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (winZ_nonempty W)
    (fun j => colRatio (D9 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j)
  rw [hj]
  exact G9_col_lt j

end G9

/-! ### G10 — `hmono` IS decisive: a bounded, strictly INCREASING tail modulus

`N = 0`, `b = 1` (`m = 0`), `M = 0`, `r₀ = 0` and `r_k = 1 − 1/|k|` for `k ≠ 0`. The band,
`P M = M`,
`r = 0` on the head and boundedness hold; `hmono` FAILS for every `K₀` (the moduli strictly
increase on both rays). The columns are `colRatio D j = ‖r_j‖ < 1 = ‖D‖`: the supremum is not
attained, and no finite window gives the norm. -/

section G10

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- G10 symbol: `r₀ = 0`, `r_k = 1 − 1/|k|`. -/
def rInc (k : ℤ) : 𝕜 := if k = 0 then 0 else 1 - 1 / (k.natAbs : 𝕜)

theorem norm_rInc (k : ℤ) (hk : k ≠ 0) : ‖(rInc k : 𝕜)‖ = 1 - 1 / (k.natAbs : ℝ) := by
  have h1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast (show 1 ≤ k.natAbs by omega)
  have e : (1 : 𝕜) - 1 / (k.natAbs : 𝕜) = (((1 : ℝ) - 1 / (k.natAbs : ℝ) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sub, RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_natCast]
  rw [rInc, ite_eq_right hk, e, RCLike.norm_ofReal,
    abs_of_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ h1 (by linarith)))]

theorem norm_rInc_lt_one (k : ℤ) : ‖(rInc k : 𝕜)‖ < 1 := by
  by_cases hk : k = 0
  · rw [rInc, ite_eq_left hk, norm_zero]; norm_num
  · have h1 : (0 : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast (show 0 < k.natAbs by omega)
    rw [norm_rInc k hk]
    have := one_div_pos.mpr h1
    linarith

theorem norm_rInc_le (k : ℤ) : ‖(rInc k : 𝕜)‖ ≤ 1 := (norm_rInc_lt_one k).le

theorem rInc_head : ∀ k : ℤ, k.natAbs ≤ 0 → (rInc k : 𝕜) = 0 := by
  intro k hk; rw [rInc, ite_eq_left (by omega)]

/-- G10: `hmono` FAILS for every `K₀`: at `n = max 1 K₀`, `‖r (n+1)‖ = 1 − 1/(n+1) > 1 − 1/n`. -/
theorem G10_hmono_fails (K₀ : ℕ) : ¬ ∀ n : ℕ, max (0 + 1) K₀ ≤ n →
    ‖(rInc ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rInc (n : ℤ) : 𝕜)‖ ∧
    ‖(rInc (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rInc (-(n : ℤ)) : 𝕜)‖ := by
  intro h
  set n := max (0 + 1) K₀ with hn
  have hn1 : 1 ≤ n := le_max_left _ _
  have h1 := (h n le_rfl).1
  rw [norm_rInc _ (by omega), norm_rInc _ (by omega),
    show ((n : ℤ) + 1).natAbs = n + 1 by omega, Int.natAbs_natCast] at h1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : 1 / ((n + 1 : ℕ) : ℝ) < 1 / (n : ℝ) :=
    one_div_lt_one_div_of_lt hpos (by push_cast; linarith)
  linarith

/-- G10 defect: `N = 0`, `M = 0`, `b = 1`, `r = rInc`. -/
abbrev DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν := defect 0 0 rInc 1 norm_rInc_le 1

theorem colRatio_DInc (j : ℤ) : colRatio (DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j = ‖(rInc j : 𝕜)‖ := by
  rw [DInc, defect_M_zero, colRatio_Tl_one]

/-- G10: the other hypotheses of the window theorem hold (band `m = 0`, `r = 0` on the head,
`P M = M` for `M = 0`). -/
theorem G10_other_hyps :
    (∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (1 : 𝓔 𝕜 ν) i = 0) ∧
    (∀ k : ℤ, k.natAbs ≤ 0 → (rInc k : 𝕜) = 0) ∧
    headP 0 ∘L (0 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) = 0 :=
  ⟨band_one, rInc_head, headP_comp_zero 0⟩

/-- **G10: `‖D‖ = 1`** (a supremum approached as `|j| → ∞`). -/
theorem G10_norm : ‖(DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ = 1 := by
  rw [opNorm_eq_iSup_cols]
  simp only [colRatio_DInc]
  have hbdd : BddAbove (Set.range fun j : ℤ => ‖(rInc j : 𝕜)‖) :=
    ⟨1, by rintro _ ⟨j, rfl⟩; exact norm_rInc_le j⟩
  apply le_antisymm
  · exact ciSup_le fun j => norm_rInc_le j
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd ((n : ℤ) + 1))
    rw [norm_rInc _ (by omega), show ((n : ℤ) + 1).natAbs = n + 1 by omega]
    push_cast
    linarith

/-- **G10: every column is strictly below the norm** — the supremum is not attained. -/
theorem G10_col_lt (j : ℤ) :
    colRatio (DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j < ‖(DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ := by
  rw [colRatio_DInc, G10_norm]; exact norm_rInc_lt_one j

/-- G10: no finite window gives the norm. -/
theorem G10_no_window (W : ℕ) :
    (winZ W).sup' (winZ_nonempty W) (fun j => colRatio (DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j)
      < ‖(DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)‖ := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (winZ_nonempty W)
    (fun j => colRatio (DInc : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j)
  rw [hj]
  exact G10_col_lt j

end G10

/-! ### Joint form, hypothesis `hZQ` of T37/T38 is decisive (new in L002, TARGET_SHEET §7)

`ν = 1`, `N = m = K₀ = 0` (window `W = 1`), `M = 0`, `r = 0`, `C = 0`, `b = 0` (so `D = 0`), and
`Z` the lift of the column family `j ↦ (if j = 2 then e₀ else 0)`. Then `P Z = Z`, every other
hypothesis of T37/T38 holds, `Z Q ≠ 0`, and `‖Z ∓ D‖ ≥ 1` against the window maximum `0`. -/

section JointHZQ

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

attribute [local instance] fact_one_le_nu1

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The zero symbol is bounded by `0`. -/
theorem zeroSym_le : ∀ k : ℤ, ‖(0 : ℤ → 𝕜) k‖ ≤ 0 := fun k => by simp

/-- hZQ-drop column family: `2 ↦ e₀`, every other column `0`. -/
def colsZQ (j : ℤ) : 𝓔 𝕜 nu1 := if j = 2 then lpOneAlg.single 0 1 else 0

theorem colsZQ_bound (j : ℤ) :
    ‖(colsZQ j : 𝓔 𝕜 nu1)‖ ≤ 1 * FiberTrivialization.weight (E := geomFiberZ 𝕜 nu1) j := by
  rw [geomFiberZ_weight, nu1_weight, one_mul]
  unfold colsZQ
  split_ifs
  · rw [lpOneAlg.norm_single, geomFiberZ_weight, nu1_weight, norm_one, one_mul]
  · rw [norm_zero]; exact zero_le_one

/-- hZQ-drop head block: the lift of `colsZQ`. -/
def ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1 := lpOneAlg.liftCLM colsZQ 1 colsZQ_bound

theorem ZQ_single (j : ℤ) : (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (lpOneAlg.single j 1) = colsZQ j := by
  rw [ZQ, lpOneAlg.liftCLM_single, one_smul]

/-- hZQ-drop: the retained premise `P Z = Z` holds. -/
theorem ZQ_hPZ : (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L ZQ = ZQ := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, ZQ_single, colsZQ]
  split_ifs
  · rw [lpOneAlg.headProj_single, ite_eq_left (mem_winZ.mpr (by decide))]
  · rw [map_zero]

/-- hZQ-drop: the dropped premise `Z Q = 0` fails (`Z Q e₂ = e₀`). -/
theorem ZQ_hZQ_fails :
    (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (lpOneAlg.tailProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ≠ 0 := by
  intro h
  have h2 := DFunLike.congr_fun h (lpOneAlg.single 2 1)
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.tailProj_single,
    ite_eq_right (by rw [mem_winZ]; omega), ZQ_single, colsZQ, ite_eq_left rfl, zero_apply] at h2
  exact single_ne_zero' (𝕜 := 𝕜) (ν := nu1) 0 h2

/-- hZQ-drop: the other premises of T37/T38 hold (band `m = 0` of `b = 0`, `P M = M` for
`M = 0`, `r = 0` on the head, `hmono` from `K₀ = 0`). -/
theorem ZQ_other_hyps :
    (∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (0 : 𝓔 𝕜 nu1) i = 0) ∧
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) = 0 ∧
    (∀ k : ℤ, k.natAbs ≤ 0 → (0 : ℤ → 𝕜) k = 0) ∧
    (∀ n : ℕ, max (0 + 1) 0 ≤ n →
      ‖(0 : ℤ → 𝕜) ((n : ℤ) + 1)‖ ≤ ‖(0 : ℤ → 𝕜) (n : ℤ)‖ ∧
      ‖(0 : ℤ → 𝕜) (-((n : ℤ) + 1))‖ ≤ ‖(0 : ℤ → 𝕜) (-(n : ℤ))‖) :=
  ⟨fun i _ => by rw [lpOneAlg.toRealSeq_zero]; rfl, ContinuousLinearMap.comp_zero _,
    fun _ _ => rfl, fun _ _ => by simp⟩

/-- hZQ-drop: the defect vanishes (`b = 0`). -/
theorem ZQ_defect_eq_zero :
    defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp [defect, lpOneAlg.mulLeftCLM_apply]

/-- hZQ-drop: every summand of the window function vanishes on `|j| ≤ 1`. -/
theorem ZQ_window_zero :
    (winZ (0 + max (0 + 1) 0)).sup' (winZ_nonempty _)
      (fun j => colRatio (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
        + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : 𝓔 𝕜 nu1)) j
        + colRatio (defectTail (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)) j) = 0 := by
  have hz : ∀ j ∈ winZ (0 + max (0 + 1) 0),
      colRatio (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
        + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : 𝓔 𝕜 nu1)) j
        + colRatio (defectTail (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)) j = 0 := by
    intro j hj
    rw [mem_winZ] at hj
    rw [colRatio_geom, ZQ_single, colsZQ, ite_eq_right (by omega), norm_zero, zero_div, zero_add,
      Hd_zero, colRatio_zero, zero_add, colRatio_geom, defectTail_single, zero_mul, map_zero,
      norm_zero, zero_div]
  exact le_antisymm (Finset.sup'_le _ _ fun j hj => (hz j hj).le)
    (Finset.le_sup'_of_le _ (mem_winZ.mpr (by decide)) (hz 0 (mem_winZ.mpr (by decide))).ge)

/-- hZQ-drop: `‖Z‖ ≥ 1` (the column `Z e₂ = e₀`). -/
theorem ZQ_norm_ge : (1 : ℝ) ≤ ‖(ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)‖ := by
  have h := colRatio_le_opNorm (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) 2
  rwa [colRatio_geom, ZQ_single, colsZQ, ite_eq_left rfl, lpOneAlg.norm_single, geomFiberZ_weight,
    nu1_weight, norm_one, one_mul, nu1_weight, div_one] at h

/-- **hZQ-drop, T38 form: the conclusion fails** (`‖Z − D‖ ≥ 1 > 0` = the window maximum), with
`P Z = Z` and all other premises of T38 holding (`ZQ_hPZ`, `ZQ_other_hyps`). -/
theorem ZQ_sub_fails :
    ‖(ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
        - defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)‖
      ≠ (winZ (0 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => colRatio (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
            + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : 𝓔 𝕜 nu1)) j
            + colRatio (defectTail (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)) j) := by
  rw [ZQ_window_zero, ZQ_defect_eq_zero, sub_zero]
  exact (zero_lt_one.trans_le ZQ_norm_ge).ne'

/-- **hZQ-drop, T37 form: the conclusion fails** (`‖Z + D‖ ≥ 1 > 0`). -/
theorem ZQ_add_fails :
    ‖(ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
        + defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)‖
      ≠ (winZ (0 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => colRatio (ZQ : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
            + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (0 : 𝓔 𝕜 nu1)) j
            + colRatio (defectTail (0 : ℤ → 𝕜) 0 zeroSym_le (0 : 𝓔 𝕜 nu1)) j) := by
  rw [ZQ_window_zero, ZQ_defect_eq_zero, add_zero]
  exact (zero_lt_one.trans_le ZQ_norm_ge).ne'

end JointHZQ

/-! ### Joint form, hypothesis `hPZ` of T37/T38 is decisive (new in L002, TARGET_SHEET §7)

`ν = 1`, `N = 0`, `m = 1`, `K₀ = 0` (window `W = 2`), `M = 0`, `r = 1_{k ≠ 0}` (`rConst 0`,
`C = 1`), `b = e₁`, and `Z` the lift of `j ↦ (if j = 0 then e₁ else 0)`. Then `Z Q = 0` and every
other premise holds, `P Z ≠ Z`, `(Z − D) e₀ = e₁ − r₁ e₁ = 0` and every other column ratio of
`Z − D` is at most `1`, so `‖Z − D‖ ≤ 1`, against `colRatio Z 0 + colRatio (R L_b) 0 = 2` inside
the window; dually for `Z + D` with `−Z`. -/

section JointHPZ

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

attribute [local instance] fact_one_le_nu1

variable {𝕜 : Type*} [RCLike 𝕜]

/-- hPZ-drop column family: `0 ↦ e₁`, every other column `0`. -/
def colsZP (j : ℤ) : 𝓔 𝕜 nu1 := if j = 0 then lpOneAlg.single 1 1 else 0

theorem colsZP_bound (j : ℤ) :
    ‖(colsZP j : 𝓔 𝕜 nu1)‖ ≤ 1 * FiberTrivialization.weight (E := geomFiberZ 𝕜 nu1) j := by
  rw [geomFiberZ_weight, nu1_weight, one_mul]
  unfold colsZP
  split_ifs
  · rw [lpOneAlg.norm_single, geomFiberZ_weight, nu1_weight, norm_one, one_mul]
  · rw [norm_zero]; exact zero_le_one

/-- hPZ-drop head block: the lift of `colsZP`. -/
def ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1 := lpOneAlg.liftCLM colsZP 1 colsZP_bound

theorem ZP_single (j : ℤ) : (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (lpOneAlg.single j 1) = colsZP j := by
  rw [ZP, lpOneAlg.liftCLM_single, one_smul]

/-- hPZ-drop: the retained premise `Z Q = 0` holds. -/
theorem ZP_hZQ :
    (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (lpOneAlg.tailProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) = 0 := by
  refine lpOneAlg.continuousLinearMap_ext fun j => ?_
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.tailProj_single, zero_apply]
  split_ifs with h
  · rw [map_zero]
  · rw [ZP_single, colsZP, ite_eq_right (by rw [mem_winZ] at h; omega)]

/-- hPZ-drop: the dropped premise `P Z = Z` fails (`P Z e₀ = P e₁ = 0 ≠ e₁`). -/
theorem ZP_hPZ_fails :
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L ZP ≠ ZP := by
  intro h
  have h0 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  rw [ContinuousLinearMap.comp_apply, ZP_single, colsZP, ite_eq_left rfl, lpOneAlg.headProj_single,
    ite_eq_right (by rw [mem_winZ]; omega)] at h0
  exact single_ne_zero' (𝕜 := 𝕜) (ν := nu1) 1 h0.symm

/-- hPZ-drop: the other premises of T37/T38 hold (band `m = 1` of `b = e₁`, `P M = M` for
`M = 0`, `r = 0` on the head, `hmono` from `K₀ = 0`). -/
theorem ZP_other_hyps :
    (∀ i : ℤ, 1 < i.natAbs → lpOneAlg.toRealSeq (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1) i = 0) ∧
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) = 0 ∧
    (∀ k : ℤ, k.natAbs ≤ 0 → (rConst 0 k : 𝕜) = 0) ∧
    (∀ n : ℕ, max (0 + 1) 0 ≤ n →
      ‖(rConst 0 ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rConst 0 (n : ℤ) : 𝕜)‖ ∧
      ‖(rConst 0 (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rConst 0 (-(n : ℤ)) : 𝕜)‖) :=
  ⟨band_single 1 1 1 (by decide), ContinuousLinearMap.comp_zero _, rConst_head 0, fun n hn => by
    have hN : 0 + 1 ≤ n := (le_max_left _ _).trans hn
    rw [rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega),
      rConst_tail 0 _ (by omega)]
    exact ⟨le_rfl, le_rfl⟩⟩

/-- hPZ-drop: the defect columns `D e_j = r_{j+1} e_{j+1}` (`M = 0`, `b = e₁`). -/
theorem ZP_defect_single (j : ℤ) :
    defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (rConst 0) 1 (norm_rConst_le 0)
        (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1) (lpOneAlg.single j 1)
      = lpOneAlg.single (1 + j) (rConst 0 (1 + j) : 𝕜) := by
  rw [defect_M_zero, defectTail_single, lpOneAlg.single_mul_single, mul_one,
      lpOneAlg.diagCLM_single,
    mul_one]

/-- hPZ-drop: every column of `Z − D` has ratio at most `1`, so `‖Z − D‖ ≤ 1`. -/
theorem ZP_sub_norm_le :
    ‖(ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
        - defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (rConst 0) 1 (norm_rConst_le 0)
          (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)‖ ≤ 1 := by
  refine lpOneAlg.opNorm_le_of_cols _ zero_le_one fun j => ?_
  rw [geomFiberZ_weight, nu1_weight, one_mul, sub_apply, ZP_single, ZP_defect_single, colsZP]
  split_ifs with h
  · subst h
    rw [add_zero, rConst_tail 0 1 (by decide), sub_self, norm_zero]; exact zero_le_one
  · rw [zero_sub, norm_neg, lpOneAlg.norm_single, geomFiberZ_weight, nu1_weight, mul_one]
    exact norm_rConst_le 0 _

/-- hPZ-drop: the window function at `j = 0` is `1 + 0 + 1 = 2`. -/
theorem ZP_window_at_zero :
    colRatio (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) 0
      + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) 0
      + colRatio (defectTail (rConst 0) 1 (norm_rConst_le 0) (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) 0
      = 2 := by
  rw [Hd_zero, colRatio_zero, add_zero, colRatio_geom, ZP_single, colsZP, ite_eq_left rfl,
    colRatio_geom, defectTail_single, lpOneAlg.single_mul_single, mul_one, lpOneAlg.diagCLM_single,
    mul_one, add_zero, rConst_tail 0 1 (by decide), lpOneAlg.norm_single, geomFiberZ_weight,
    nu1_weight, norm_one, one_mul, nu1_weight, div_one]
  norm_num

/-- hPZ-drop: the window maximum (`W = 2`) is at least `2`. -/
theorem ZP_window_ge :
    (2 : ℝ) ≤ (winZ (1 + max (0 + 1) 0)).sup' (winZ_nonempty _)
      (fun j => colRatio (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
        + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j
        + colRatio (defectTail (rConst 0) 1 (norm_rConst_le 0)
            (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j) :=
  Finset.le_sup'_of_le _ (mem_winZ.mpr (by decide)) ZP_window_at_zero.ge

/-- **hPZ-drop, T38 form: the conclusion fails** (`‖Z − D‖ ≤ 1 < 2 ≤` the window maximum), with
`Z Q = 0` and all other premises of T38 holding (`ZP_hZQ`, `ZP_other_hyps`). -/
theorem ZP_sub_fails :
    ‖(ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
        - defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (rConst 0) 1 (norm_rConst_le 0)
          (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)‖
      ≠ (winZ (1 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => colRatio (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
            + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
                (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j
            + colRatio (defectTail (rConst 0) 1 (norm_rConst_le 0)
                (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j) := by
  intro h
  have h1 := ZP_sub_norm_le (𝕜 := 𝕜)
  have h2 := ZP_window_ge (𝕜 := 𝕜)
  rw [h] at h1
  linarith

/-- hPZ-drop, T37 form: `−Z` satisfies `(−Z) Q = 0`. -/
theorem negZP_hZQ :
    (-ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (lpOneAlg.tailProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) = 0 := by
  rw [ContinuousLinearMap.neg_comp, ZP_hZQ, neg_zero]

/-- hPZ-drop, T37 form: `P (−Z) ≠ −Z`. -/
theorem negZP_hPZ_fails :
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) ∘L (-ZP) ≠ -ZP := by
  rw [ContinuousLinearMap.comp_neg]
  exact fun h => ZP_hPZ_fails (neg_injective h)

/-- **hPZ-drop, T37 form: the conclusion fails** for `−Z + D = −(Z − D)`. -/
theorem negZP_add_fails :
    ‖(-ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
        + defect 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) (rConst 0) 1 (norm_rConst_le 0)
          (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)‖
      ≠ (winZ (1 + max (0 + 1) 0)).sup' (winZ_nonempty _)
          (fun j => colRatio (-ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
            + colRatio (defectHead 0 (0 : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1)
                (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j
            + colRatio (defectTail (rConst 0) 1 (norm_rConst_le 0)
                (lpOneAlg.single 1 1 : 𝓔 𝕜 nu1)) j) := by
  have hcol : ∀ j, colRatio (-ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j
      = colRatio (ZP : 𝓔 𝕜 nu1 →L[𝕜] 𝓔 𝕜 nu1) j := fun j => by
    rw [colRatio_geom, colRatio_geom, neg_apply, norm_neg]
  simp only [hcol]
  rw [neg_add_eq_sub, norm_sub_rev]
  exact ZP_sub_fails

end JointHPZ

/-! ### Nonvacuity witnesses for T33 and T37 (new in L002, TARGET_SHEET §6 T43)

`N = m = K₀ = 0`, `M = P₀` (`P M = M`), `r = 1_{k ≠ 0}` (`rConst 0`, `C = 1`), `b = 1`; for T37
also `Z = P₀` (`P Z = Z`, `Z Q = 0`). All premises hold and `M`, `r`, `b`, `Z` are nonzero. -/

section NonVacuity

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

theorem nv_hmono (K₀ : ℕ) : ∀ n : ℕ, max (0 + 1) K₀ ≤ n →
    ‖(rConst 0 ((n : ℤ) + 1) : 𝕜)‖ ≤ ‖(rConst 0 (n : ℤ) : 𝕜)‖ ∧
    ‖(rConst 0 (-((n : ℤ) + 1)) : 𝕜)‖ ≤ ‖(rConst 0 (-(n : ℤ)) : 𝕜)‖ := fun n hn => by
  have hN : 0 + 1 ≤ n := (le_max_left _ _).trans hn
  rw [rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega), rConst_tail 0 _ (by omega),
    rConst_tail 0 _ (by omega)]
  exact ⟨le_rfl, le_rfl⟩

omit [Fact (1 ≤ (ν : ℝ))] in
theorem nv_P_ne_zero : (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ≠ 0 := by
  intro h
  have h0 := DFunLike.congr_fun h (lpOneAlg.single 0 1)
  rw [lpOneAlg.headProj_single, ite_eq_left (mem_winZ.mpr (by decide)), zero_apply] at h0
  exact single_ne_zero' (𝕜 := 𝕜) (ν := ν) 0 h0

theorem nv_r_ne_zero : (rConst 0 : ℤ → 𝕜) ≠ 0 := fun h => by
  have h1 := congr_fun h 1
  rw [rConst_tail 0 1 (by decide), Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem nv_one_ne_zero : (1 : 𝓔 𝕜 ν) ≠ 0 := by
  rw [lpOneAlg.one_eq_single_zero (𝕜 := 𝕜)]
  exact single_ne_zero' 0

/-- **T33 nonvacuity**: `M ≠ 0`, `r ≠ 0`, `b ≠ 0`, every premise of T33 holds, and T33 applies. -/
theorem T33_nonvacuity :
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ≠ 0 ∧ (rConst 0 : ℤ → 𝕜) ≠ 0 ∧
      (1 : 𝓔 𝕜 ν) ≠ 0 ∧
      ‖defect 0 (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (rConst 0) 1 (norm_rConst_le 0)
          (1 : 𝓔 𝕜 ν)‖
        = (winZ (0 + max (0 + 1) 0)).sup' (winZ_nonempty _)
            (fun j => headCol 0 (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (1 : 𝓔 𝕜 ν) j
              + tailCol 0 (rConst 0 : ℤ → 𝕜) (1 : 𝓔 𝕜 ν) j) :=
  ⟨nv_P_ne_zero, nv_r_ne_zero, nv_one_ne_zero,
    opNorm_defect_eq_sup'_explicit (𝕜 := 𝕜) (ν := ν) 0 0 0 _ (rConst 0) 1 (norm_rConst_le 0) 1
      band_one (lpOneAlg.headProj_comp_headProj _) (rConst_head 0) (nv_hmono 0)⟩

/-- **T37 nonvacuity**: additionally `Z = P₀ ≠ 0` with `P Z = Z` and `Z Q = 0`; T37 applies. -/
theorem T37_nonvacuity :
    (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ≠ 0 ∧
      ‖(lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)
          + defect 0 (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) (rConst 0) 1
            (norm_rConst_le 0) (1 : 𝓔 𝕜 ν)‖
        = (winZ (0 + max (0 + 1) 0)).sup' (winZ_nonempty _)
            (fun j => colRatio (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) j
              + colRatio (defectHead 0 (lpOneAlg.headProj (winZ 0) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν)
                  (1 : 𝓔 𝕜 ν)) j
              + colRatio (defectTail (rConst 0) 1 (norm_rConst_le 0) (1 : 𝓔 𝕜 ν)) j) :=
  ⟨nv_P_ne_zero, opNorm_joint_defect_eq_sup' (𝕜 := 𝕜) (ν := ν) 0 0 0 _ _ (rConst 0) 1
    (norm_rConst_le 0) 1 (lpOneAlg.headProj_comp_headProj _) (lpOneAlg.headProj_comp_tailProj _)
    band_one (lpOneAlg.headProj_comp_headProj _) (rConst_head 0) (nv_hmono 0)⟩

end NonVacuity

/-! ### T12 (`band_mul`): the band premise `hx` is decisive; the summed radius is sharp
(new in L002, TARGET_SHEET §7, Codex A2) -/

section BandMul

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

attribute [local instance] fact_one_le_nu1

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **hx-drop countermodel of T12** (`ν = 1`, `x = e_{m+1}`, `y = 1`, `n = 0`): the retained
premise `hy` holds, `hx` fails, and the conclusion fails at `k = m + 1`: `m + n < |k|` while the
coefficient of `x * y` at `k` is `1 ≠ 0`. -/
theorem T12_hx_drop (m : ℕ) :
    (∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (1 : 𝓔 𝕜 nu1) i = 0) ∧
      ¬ (∀ i : ℤ, m < i.natAbs →
        lpOneAlg.toRealSeq (lpOneAlg.single ((m : ℤ) + 1) 1 : 𝓔 𝕜 nu1) i = 0) ∧
      m + 0 < ((m : ℤ) + 1).natAbs ∧
      lpOneAlg.toRealSeq ((lpOneAlg.single ((m : ℤ) + 1) 1 : 𝓔 𝕜 nu1) * 1) ((m : ℤ) + 1) ≠ 0 := by
  refine ⟨band_one, fun h => ?_, by omega, ?_⟩
  · have h1 := h ((m : ℤ) + 1) (by omega)
    rw [lpOneAlg.toRealSeq_single, ite_eq_left rfl] at h1
    exact one_ne_zero h1
  · rw [mul_one, lpOneAlg.toRealSeq_single, ite_eq_left rfl]
    exact one_ne_zero

/-- **Boundary witness of T12** (`ν = 1`): `x = e_m` and `y = e_n` satisfy both band premises
and the coefficient of `x * y` at `k = m + n` (`|k| = m + n`) is `1`: the radius `m + n` cannot
be lowered. -/
theorem T12_boundary (m n : ℕ) :
    (∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (lpOneAlg.single (m : ℤ) 1 : 𝓔 𝕜 nu1) i = 0) ∧
      (∀ i : ℤ, n < i.natAbs → lpOneAlg.toRealSeq (lpOneAlg.single (n : ℤ) 1 : 𝓔 𝕜 nu1) i = 0) ∧
      ((m : ℤ) + n).natAbs = m + n ∧
      lpOneAlg.toRealSeq ((lpOneAlg.single (m : ℤ) 1 : 𝓔 𝕜 nu1) * lpOneAlg.single (n : ℤ) 1)
        ((m : ℤ) + n) = 1 := by
  refine ⟨band_single m m 1 (by simp), band_single n n 1 (by simp), by omega, ?_⟩
  rw [lpOneAlg.single_mul_single, mul_one, lpOneAlg.toRealSeq_single, ite_eq_left rfl]

end BandMul

end RadiiPolynomial.Tests.FZ.TailWindow
