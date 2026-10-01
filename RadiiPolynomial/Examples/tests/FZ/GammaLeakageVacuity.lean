import RadiiPolynomial.Analysis.SequenceSpace.Fourier

/-!
# FZ Γ-leakage tests: nonvacuity witnesses (T20, L004)

Imports the PATCHED Fourier facade (the T17 importer check). The witnesses:

* (a) `norm_gammaInvDiag_leak_le` at `𝕜 = ℝ`, `ν = 1`, `N = 0`, `c = e₁`: the chain `Γ⁺ P₀ L_c Q₀`
  maps `e₋₁` to `e₀` (`chain_single_neg_one`), so the operator is nonzero and the bound is not vacuous;
* (b) `gammaDiag_comp_gammaInvDiag` and `gammaDiag_entry_eq_rees` at `𝕜 = ℝ` and at `𝕜 = ℂ` (the
  real-scalar requirement instantiated at both fields of record), the head hypothesis satisfiable;
* (c) `norm_head_leak_le_coeff` and `norm_defect_le_gamma` at `𝕜 = ℂ` with `M = 1`, `r = 0`, `C = 0`
  and `c = e₁`, whose head leakage is nonzero;
* (d) `norm_tail_leak_le_coeff` at `r = 1`, `C = 1` (`‖r k‖ ≤ 1` satisfiable) with a nonzero operator;
* (e) `gammaW_inv_le` at `ν = 2`, `N = 0`, `k = 1` (hypothesis satisfiable; both sides positive);
* (f) `RadiiPolynomial.Fourier.gammaDiag` resolves through the facade import.

The `Fact (1 ≤ ν)` instance on the literal weight `nu1` is LOCAL.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.GammaLeakage

section Vacuity

open RadiiPolynomial.Fourier

/-- The literal weight `ν = 1`. -/
def nu1 : PosReal := ⟨1, one_pos⟩

/-- `ν = 1 ≥ 1` (a LOCAL instance: no global instance on a literal weight). -/
theorem fact_one_le_nu1 : Fact (1 ≤ ((nu1 : PosReal) : ℝ)) := ⟨le_rfl⟩

attribute [local instance] fact_one_le_nu1

theorem nu1_coe : ((nu1 : PosReal) : ℝ) = 1 := rfl

/-! ### (a) the leakage chain is nonzero -/

section ChainReal

/-- The T12 chain `Γ⁺ P₀ L_c Q₀` at `𝕜 = ℝ`, `ν = 1`, `N = 0`, `c = e₁` (local notation). -/
local notation "chainR" =>
  ((gammaInvDiag 0 : lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1)) ∘L
    (lpOneAlg.headProj (𝕜 := ℝ) (G := geomFiberZ ℝ nu1) (winZ 0)) ∘L
    (lpOneAlg.mulLeftCLM (𝕜 := ℝ) (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℝ nu1))) ∘L
    (lpOneAlg.tailProj (𝕜 := ℝ) (G := geomFiberZ ℝ nu1) (winZ 0)) :
    lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1))

/-- (a) The chain maps `e₋₁` to a vector with coefficient `1` at `0`. -/
theorem chain_single_neg_one :
    lpOneAlg.toRealSeq (chainR (lpOneAlg.single (-1) 1)) 0 = 1 := by
  have hm : (-1 : ℤ) ∉ winZ 0 := by rw [mem_winZ]; decide
  have h0 : (0 : ℤ) ∈ winZ 0 := mem_winZ.mpr le_rfl
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    lpOneAlg.tailProj_single, ite_eq_right hm, lpOneAlg.mulLeftCLM_apply, toRealSeq_gammaInvDiag,
    lpOneAlg.toRealSeq_headProj, ite_eq_left h0, ite_eq_left h0, toRealSeq_mul_single,
    lpOneAlg.toRealSeq_single, ite_eq_left (by norm_num), gammaScalar, Rees.Laurent.gammaW, nu1_coe]
  norm_num

/-- (a) The T12 chain is a nonzero operator. -/
theorem chainR_ne_zero : chainR ≠ 0 := by
  intro h
  have := chain_single_neg_one
  rw [h, zero_apply, lpOneAlg.toRealSeq_zero] at this
  exact zero_ne_one this

/-- (a) The T12 bound on the nonzero chain. -/
theorem chainR_norm_le : ‖chainR‖ ≤ ‖(lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℝ nu1))‖ :=
  norm_gammaInvDiag_leak_le 0 _

end ChainReal

/-! ### (b) `Γ Γ⁺ = P` and the Rees head entries at `𝕜 = ℝ` and `𝕜 = ℂ` -/

section BothFields

/-- (b) `gammaDiag_comp_gammaInvDiag` at `𝕜 = ℝ`. -/
theorem gammaDiag_comp_real (N : ℕ) :
    (gammaDiag N : lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1)) ∘L gammaInvDiag N =
      lpOneAlg.headProj (𝕜 := ℝ) (G := geomFiberZ ℝ nu1) (winZ N) :=
  gammaDiag_comp_gammaInvDiag N

/-- (b) `gammaDiag_comp_gammaInvDiag` at `𝕜 = ℂ`. -/
theorem gammaDiag_comp_complex (N : ℕ) :
    (gammaDiag N : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1)) ∘L gammaInvDiag N =
      lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ nu1) (winZ N) :=
  gammaDiag_comp_gammaInvDiag N

/-- (b) `gammaDiag_entry_eq_rees` at `𝕜 = ℝ`, `N = 0`, `k = 0 ∈ winZ 0` (head hypothesis satisfiable). -/
theorem gammaDiag_entry_real :
    lpOneAlg.toRealSeq ((gammaDiag 0 : lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1))
      (lpOneAlg.single 0 1)) 0 =
      algebraMap ℝ ℝ (Polynomial.eval (1 / ((nu1 : PosReal) : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN 0 0)) :=
  gammaDiag_entry_eq_rees 0 0 (mem_winZ.mpr le_rfl)

/-- (b) `gammaDiag_entry_eq_rees` at `𝕜 = ℂ`, `N = 0`, `k = 0 ∈ winZ 0`. -/
theorem gammaDiag_entry_complex :
    lpOneAlg.toRealSeq ((gammaDiag 0 : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1))
      (lpOneAlg.single 0 1)) 0 =
      algebraMap ℝ ℂ (Polynomial.eval (1 / ((nu1 : PosReal) : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN 0 0)) :=
  gammaDiag_entry_eq_rees 0 0 (mem_winZ.mpr le_rfl)

end BothFields

/-! ### (c) the head leakage and the defect majorant at `𝕜 = ℂ` with a nonzero head leakage -/

section HeadComplex

/-- The head leakage `1 ∘ P₀ L_c Q₀` at `𝕜 = ℂ`, `ν = 1`, `c = e₁` (local notation). -/
local notation "leakC" =>
  ((1 : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1)) ∘L
    (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ nu1) (winZ 0)) ∘L
    (lpOneAlg.mulLeftCLM (𝕜 := ℂ) (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1))) ∘L
    (lpOneAlg.tailProj (𝕜 := ℂ) (G := geomFiberZ ℂ nu1) (winZ 0)) :
    lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1))

/-- (c) The head leakage maps `e₋₁` to a vector with coefficient `1` at `0`. -/
theorem leakC_single_neg_one :
    lpOneAlg.toRealSeq (leakC (lpOneAlg.single (-1) 1)) 0 = 1 := by
  have hm : (-1 : ℤ) ∉ winZ 0 := by rw [mem_winZ]; decide
  have h0 : (0 : ℤ) ∈ winZ 0 := mem_winZ.mpr le_rfl
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    lpOneAlg.tailProj_single, ite_eq_right hm, lpOneAlg.mulLeftCLM_apply, one_apply_eq_self,
    lpOneAlg.toRealSeq_headProj, ite_eq_left h0, toRealSeq_mul_single, lpOneAlg.toRealSeq_single,
    ite_eq_left (by norm_num)]

/-- (c) The head leakage is nonzero. -/
theorem leakC_ne_zero : leakC ≠ 0 := by
  intro h
  have := leakC_single_neg_one
  rw [h, zero_apply, lpOneAlg.toRealSeq_zero] at this
  exact zero_ne_one this

/-- (c) `norm_head_leak_le_coeff` at `𝕜 = ℂ`, `M = 1`, `c = e₁` (nonzero head leakage). -/
theorem head_leak_complex :
    ‖leakC‖ ≤ ‖(1 : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1)) ∘L
        (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ nu1) (winZ 0)) ∘L gammaDiag 0‖ *
      ‖(lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1))‖ :=
  norm_head_leak_le_coeff 0 1 _

/-- `‖(0 : ℤ → ℂ) k‖ ≤ 0`. -/
theorem zero_symbol_le (k : ℤ) : ‖(0 : ℤ → ℂ) k‖ ≤ 0 := by simp

/-- (c) The defect with `M = 1`, `r = 0`, `C = 0`, `c = e₁` is the (nonzero) head leakage. -/
theorem defect_complex_eq :
    defect 0 1 (0 : ℤ → ℂ) 0 zero_symbol_le (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1)) =
      leakC + defectTail (0 : ℤ → ℂ) 0 zero_symbol_le (lpOneAlg.single 1 1) :=
  defect_eq 0 1 0 0 zero_symbol_le _

/-- (c) `norm_defect_le_gamma` at `𝕜 = ℂ`, `M = 1`, `r = 0`, `C = 0`, `c = e₁`. -/
theorem defect_complex_le :
    ‖defect 0 1 (0 : ℤ → ℂ) 0 zero_symbol_le (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1))‖ ≤
      (‖(1 : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1)) ∘L
        (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ nu1) (winZ 0)) ∘L gammaDiag 0‖ + 0) *
      ‖(lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1))‖ :=
  norm_defect_le_gamma 0 1 0 0 zero_symbol_le _

/-- (c) The defect itself is nonzero on this data (its tail term vanishes: `r = 0`). -/
theorem defect_complex_ne_zero :
    defect 0 1 (0 : ℤ → ℂ) 0 zero_symbol_le (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1)) ≠ 0 := by
  intro h
  have := leakC_single_neg_one
  have ht : defectTail (0 : ℤ → ℂ) 0 zero_symbol_le
      (lpOneAlg.single 1 1 : lpOneAlg ℤ (geomFiberZ ℂ nu1)) (lpOneAlg.single (-1) 1) = 0 := by
    refine lpOneAlg.ext_toRealSeq (funext fun k => ?_)
    rw [defectTail_single, lpOneAlg.toRealSeq_diagCLM, lpOneAlg.toRealSeq_zero, Pi.zero_apply, zero_mul]
  have hd := congr_arg (fun T : lpOneAlg ℤ (geomFiberZ ℂ nu1) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ nu1) =>
    lpOneAlg.toRealSeq (T (lpOneAlg.single (-1) 1)) 0) h
  simp only [defect_complex_eq, add_apply, ht, add_zero, zero_apply,
    lpOneAlg.toRealSeq_zero, Pi.zero_apply] at hd
  rw [this] at hd
  exact one_ne_zero hd

end HeadComplex

/-! ### (d) the tail estimate with a nonzero operator -/

section TailReal

/-- `‖(1 : ℤ → ℝ) k‖ ≤ 1`. -/
theorem one_symbol_le (k : ℤ) : ‖(1 : ℤ → ℝ) k‖ ≤ 1 := by simp

/-- (d) `norm_tail_leak_le_coeff` at `𝕜 = ℝ`, `r = 1`, `C = 1`, `c = e₀`. -/
theorem tail_leak_real :
    ‖(lpOneAlg.diagCLM (G := geomFiberZ ℝ nu1) (1 : ℤ → ℝ) 1 one_symbol_le :
        lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1)) ∘L
      lpOneAlg.mulLeftCLM (𝕜 := ℝ) (lpOneAlg.single 0 1 : lpOneAlg ℤ (geomFiberZ ℝ nu1))‖ ≤
      1 * ‖(lpOneAlg.single 0 1 : lpOneAlg ℤ (geomFiberZ ℝ nu1))‖ :=
  norm_tail_leak_le_coeff 1 1 one_symbol_le _

/-- (d) The operator `D₁ L_{e₀}` is nonzero: it maps `e₀` to a vector with coefficient `1` at `0`. -/
theorem tail_op_ne_zero :
    ((lpOneAlg.diagCLM (G := geomFiberZ ℝ nu1) (1 : ℤ → ℝ) 1 one_symbol_le :
        lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1)) ∘L
      lpOneAlg.mulLeftCLM (𝕜 := ℝ) (lpOneAlg.single 0 1 : lpOneAlg ℤ (geomFiberZ ℝ nu1))) ≠ 0 := by
  intro h
  have hd := congr_arg (fun T : lpOneAlg ℤ (geomFiberZ ℝ nu1) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu1) =>
    lpOneAlg.toRealSeq (T (lpOneAlg.single 0 1)) 0) h
  simp only [ContinuousLinearMap.comp_apply, lpOneAlg.mulLeftCLM_apply, lpOneAlg.toRealSeq_diagCLM,
    toRealSeq_mul_single, zero_apply, lpOneAlg.toRealSeq_zero, Pi.zero_apply, Pi.one_apply, one_mul,
    lpOneAlg.toRealSeq_single, sub_zero, ite_true] at hd
  exact one_ne_zero hd

end TailReal

/-! ### (e) the gamma inverse bound at `ν = 2` -/

/-- (e) `gammaW_inv_le` at `ν = 2`, `N = 0`, `k = 1`. -/
theorem gammaW_inv_le_two : (Rees.Laurent.gammaW 2 0 1)⁻¹ ≤ (2 : ℝ) ^ (2 * (0 + 1)) :=
  Rees.Laurent.gammaW_inv_le (by norm_num) 0 1

/-- (e) Both sides are positive. -/
theorem gammaW_inv_le_two_pos :
    0 < (Rees.Laurent.gammaW 2 0 1)⁻¹ ∧ 0 < (2 : ℝ) ^ (2 * (0 + 1)) :=
  ⟨inv_pos.mpr (Rees.Laurent.gammaW_pos (by norm_num) 0 1), by norm_num⟩

/-! ### (f) resolution through the facade import -/

#check @RadiiPolynomial.Fourier.gammaDiag

end Vacuity

end RadiiPolynomial.Tests.FZ.GammaLeakage
