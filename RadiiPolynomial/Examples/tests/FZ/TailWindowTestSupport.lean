import RadiiPolynomial.Analysis.SequenceSpace.Fourier.TailWindow

/-!
# FZ tail-window tests: shared support (T42, L002)

Test-only helpers shared by `TailWindowCountermodels` and `TailWindowRegressions`, ported from
the slice-25 Part G helpers (`tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean`,
sha256 `2c938be2…`, lines 1209–1267 and 1979–1990) and restated over the library names
(`Hd ↦ defectHead`, `Tl ↦ defectTail`, `headP N ↦ headProj (winZ N)`, `colRatio ↦
lpOneAlg.colRatio` read through `colRatio_geom`). The slice names are kept. The carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)` is written `𝓔 𝕜 ν` (local notation).
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.TailWindow

local notation "𝓔" k:max n:max => lpOneAlg ℤ (geomFiberZ k n)

section GHelpers

open RadiiPolynomial.Fourier RadiiPolynomial.lpOneAlg

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal}

theorem single_zero' (j : ℤ) : (lpOneAlg.single j (0 : 𝕜) : 𝓔 𝕜 ν) = 0 := by
  rw [lpOneAlg.single_smul, zero_smul]

theorem single_add' (j : ℤ) (x y : 𝕜) :
    (lpOneAlg.single j (x + y) : 𝓔 𝕜 ν) = lpOneAlg.single j x + lpOneAlg.single j y := by
  rw [lpOneAlg.single_smul, lpOneAlg.single_smul j x, lpOneAlg.single_smul j y, add_smul]

theorem single_ne_zero' (j : ℤ) : (lpOneAlg.single j (1 : 𝕜) : 𝓔 𝕜 ν) ≠ 0 := by
  intro h
  have := lpOneAlg.norm_single (E := geomFiberZ 𝕜 ν) j (1 : 𝕜)
  rw [geomFiberZ_weight, h, norm_zero, norm_one, one_mul] at this
  exact (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).ne this

theorem colRatio_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (j : ℤ) :
    colRatio (0 : 𝓔 𝕜 ν →L[𝕜] F) j = 0 := by
  rw [colRatio_geom, zero_apply, norm_zero, zero_div]

variable [Fact (1 ≤ (ν : ℝ))]

theorem Hd_zero (N : ℕ) (b : 𝓔 𝕜 ν) : defectHead N (0 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) b = 0 :=
  ContinuousLinearMap.zero_comp _

theorem defect_M_zero (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔 𝕜 ν) :
    defect N 0 r C hr b = defectTail r C hr b := by
  rw [defect_eq, Hd_zero, zero_add]

theorem headP_comp_zero (N : ℕ) :
    (lpOneAlg.headProj (winZ N) : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) ∘L (0 : 𝓔 𝕜 ν →L[𝕜] 𝓔 𝕜 ν) = 0 :=
  ContinuousLinearMap.comp_zero _

/-- The tail column of `b = c • 1`: `colRatio (R L_{c•1}) j = ‖c‖ ‖r_j‖`. -/
theorem colRatio_Tl_smul_one (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝕜) (j : ℤ) :
    colRatio (defectTail r C hr (c • (1 : 𝓔 𝕜 ν))) j = ‖c‖ * ‖r j‖ := by
  rw [colRatio_geom, defectTail_single, smul_mul_assoc, one_mul, map_smul, lpOneAlg.diagCLM_single,
    norm_smul, lpOneAlg.norm_single, geomFiberZ_weight, mul_one, mul_div_assoc,
    mul_div_cancel_right₀ _ (pow_pos (show (0 : ℝ) < (ν : ℝ) from ν.2) _).ne']

theorem colRatio_Tl_one (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (j : ℤ) :
    colRatio (defectTail r C hr (1 : 𝓔 𝕜 ν)) j = ‖r j‖ := by
  have h := colRatio_Tl_smul_one (ν := ν) r C hr 1 j
  rwa [one_smul, norm_one, one_mul] at h

end GHelpers

/-! ### The constant tail symbol (slice G5; shared by G5 and G9) -/

section RConst

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The constant tail symbol `r_k = 1_{|k| > N}`. -/
def rConst (N : ℕ) (k : ℤ) : 𝕜 := if k.natAbs ≤ N then 0 else 1

theorem norm_rConst_le (N : ℕ) (k : ℤ) : ‖(rConst N k : 𝕜)‖ ≤ 1 := by
  unfold rConst; split_ifs <;> simp

theorem rConst_head (N : ℕ) : ∀ k : ℤ, k.natAbs ≤ N → (rConst N k : 𝕜) = 0 := by
  intro k hk; rw [rConst, ite_eq_left hk]

theorem rConst_tail (N : ℕ) (k : ℤ) (hk : N < k.natAbs) : (rConst N k : 𝕜) = 1 := by
  rw [rConst, ite_eq_right (show ¬k.natAbs ≤ N by omega)]

end RConst

end RadiiPolynomial.Tests.FZ.TailWindow
