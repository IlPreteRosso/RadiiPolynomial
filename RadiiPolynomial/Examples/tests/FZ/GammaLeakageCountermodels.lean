import RadiiPolynomial.Analysis.SequenceSpace.Fourier.GammaLeakage

/-!
# FZ Γ-leakage tests: decisive countermodels and redundancy proofs (T21, L004)

This file contains exactly the following faces of TARGET_SHEET §7 (no exhaustiveness claim beyond
them):

* `gammaW_inv_le`: the hypothesis `1 ≤ ν` is DECISIVE — at `ν = 1/2`, `N = 0`, `k = 1` the
  conclusion fails (`countermodel_gammaW_inv_le`);
* `norm_gammaScalar` has no positivity hypothesis: the identity holds at `ν = 0` and at `ν = -1`
  (`norm_gammaScalar_at_zero`, `norm_gammaScalar_at_neg_one`; redundancy of the source's `ν > 0`);
* `gammaScalar_ne_zero`: the hypothesis `0 < ν` is DECISIVE — at `ν = 0`, `N = 0`, `k = 0` the Γ
  scalar is `0` (`countermodel_gammaScalar_ne_zero`);
* `norm_gamma_head_le` and `norm_gamma_inv_head_le`: the instance `Fact (1 ≤ ν)` is DECISIVE, stated
  on the unconditional real propositions at `ν = 1/2` (`countermodel_norm_gamma_head_le`,
  `countermodel_norm_gamma_inv_head_le`);
* `gammaDiag_entry_eq_rees`: the head membership `k ∈ winZ N` is DECISIVE — at `𝕜 = ℝ`, `ν = 2`,
  `N = 0`, `k = 1` the entry is `0` while the evaluated monomial is `1`
  (`countermodel_gammaDiag_entry_eq_rees`);
* `norm_tail_leak_le_coeff`: the conclusion needs no `0 ≤ C` (`redundancy_tail_nonneg_C`).

The `Fact (1 ≤ ν)` instance on the literal weight `nu2` is LOCAL.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.GammaLeakage

section Countermodels

open RadiiPolynomial.Fourier

/-! ### `gammaW_inv_le`: `1 ≤ ν` decisive -/

/-- At `ν = 1/2`, `N = 0`, `k = 1`: `γ₀(1) = ν²/ν² = 1`, so `γ₀(1)⁻¹ = 1 > ν² = 1/4`. -/
theorem countermodel_gammaW_inv_le :
    ¬ ((Rees.Laurent.gammaW (1 / 2) 0 1)⁻¹ ≤ (1 / 2 : ℝ) ^ (2 * (0 + 1))) := by
  rw [Rees.Laurent.gammaW]
  norm_num

/-! ### `norm_gammaScalar`: no positivity hypothesis (redundancy of `ν > 0`) -/

/-- The identity at `ν = 0` (`γ = 0⁰ / 0² = 0` in Lean). -/
theorem norm_gammaScalar_at_zero :
    ‖(gammaScalar 0 0 0 : ℝ)‖ = Rees.Laurent.gammaW 0 0 0 :=
  norm_gammaScalar 0 0 0

/-- The identity at `ν = -1` (`γ₀(1) = (-1)² / (-1)² = 1 ≥ 0`: even exponents). -/
theorem norm_gammaScalar_at_neg_one :
    ‖(gammaScalar (-1) 0 1 : ℂ)‖ = 1 := by
  rw [norm_gammaScalar, Rees.Laurent.gammaW]
  norm_num

/-! ### `gammaScalar_ne_zero`: `0 < ν` decisive -/

/-- At `ν = 0`, `N = 0`, `k = 0`: `γ₀(0) = 0⁰ / 0² = 1 / 0 = 0`. -/
theorem countermodel_gammaScalar_ne_zero : (gammaScalar 0 0 0 : ℝ) = 0 := by
  rw [gammaScalar, Rees.Laurent.gammaW]
  norm_num

/-! ### `norm_gamma_head_le`, `norm_gamma_inv_head_le`: `Fact (1 ≤ ν)` decisive -/

/-- At `ν = 1/2`, `N = 0`, `k = 0 ∈ W₀`: `γ₀(0) = ν⁰ / ν² = 4 > 1`. -/
theorem countermodel_norm_gamma_head_le :
    ¬ (‖(if (0 : ℤ) ∈ winZ 0 then (gammaScalar (1 / 2) 0 0 : ℝ) else 0)‖ ≤ 1) := by
  rw [ite_eq_left (mem_winZ.mpr (le_refl 0) : (0 : ℤ) ∈ winZ 0), norm_gammaScalar, Rees.Laurent.gammaW]
  norm_num

/-- At `ν = 1/2`, `N = 1`, `k = 1 ∈ W₁`: `γ₁(1)⁻¹ = (ν² / ν⁴)⁻¹ = ν² = 1/4 > ν⁴ = 1/16`. -/
theorem countermodel_norm_gamma_inv_head_le :
    ¬ (‖(if (1 : ℤ) ∈ winZ 1 then (gammaScalar (1 / 2) 1 1 : ℝ)⁻¹ else 0)‖ ≤
      (1 / 2 : ℝ) ^ (2 * (1 + 1))) := by
  rw [ite_eq_left (mem_winZ.mpr (le_refl 1) : (1 : ℤ) ∈ winZ 1), norm_inv, norm_gammaScalar, Rees.Laurent.gammaW]
  norm_num

/-! ### `gammaDiag_entry_eq_rees`: head membership decisive -/

section EntryTail

/-- The literal weight `ν = 2`. -/
def nu2 : PosReal := ⟨2, by norm_num⟩

/-- `ν = 2 ≥ 1` (a LOCAL instance: no global instance on a literal weight). -/
theorem fact_one_le_nu2 : Fact (1 ≤ ((nu2 : PosReal) : ℝ)) := ⟨show (1 : ℝ) ≤ 2 by norm_num⟩

attribute [local instance] fact_one_le_nu2

/-- At `𝕜 = ℝ`, `ν = 2`, `N = 0`, `k = 1 ∉ W₀`: the entry of `Γ` at `e₁` is `0`, while
`eval_{1/2} (X ^ aN 0 1) = eval_{1/2} (X⁰) = 1`. -/
theorem countermodel_gammaDiag_entry_eq_rees :
    lpOneAlg.toRealSeq ((gammaDiag 0 : lpOneAlg ℤ (geomFiberZ ℝ nu2) →L[ℝ] lpOneAlg ℤ (geomFiberZ ℝ nu2))
      (lpOneAlg.single 1 1)) 1 ≠
      algebraMap ℝ ℝ (Polynomial.eval (1 / ((nu2 : PosReal) : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN 0 1)) := by
  have h1 : (1 : ℤ) ∉ winZ 0 := by rw [mem_winZ]; decide
  rw [toRealSeq_gammaDiag, ite_eq_right h1, zero_mul, Rees.Laurent.aN]
  norm_num

end EntryTail

/-! ### `norm_tail_leak_le_coeff`: no `0 ≤ C` needed (redundancy) -/

/-- `‖r 0‖ ≤ C` gives `0 ≤ C` on the nonempty index `ℤ`. -/
theorem redundancy_tail_nonneg_C {𝕜 : Type*} [NormedField 𝕜] (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) : 0 ≤ C :=
  (norm_nonneg _).trans (hr 0)

end Countermodels

end RadiiPolynomial.Tests.FZ.GammaLeakage
