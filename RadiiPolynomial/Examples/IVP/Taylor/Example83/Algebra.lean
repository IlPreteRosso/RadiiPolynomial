import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Certification.IVP.Taylor
import RadiiPolynomial.Algebra.Polynomial
import RadiiPolynomial.Examples.IVP.Taylor.Example83.Numbers

/-!
# Example 8.3 — Algebraic Infrastructure

Lorenz IVP (Section 8.3):
  ẋ₁ = σ(x₂ - x₁),  ẋ₂ = ρx₁ - x₂ - x₁x₃,  ẋ₃ = -βx₃ + x₁x₂
with σ=10, ρ=28, β=8/3, x₀=(1,0,0), N=30, L=3, ν=3/20.

Uses `StdIVPData` to auto-derive all standard IVP constructions and
`ivp_hDF_block_nat` for single-shot DF verification.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace Example83

/-! ## 1. Parameters -/

abbrev N : ℕ := 30
abbrev L : ℕ := 3
/-- Scoped: `L` is a reducible abbreviation of the numeral, so a global instance would also
serve every `NeZero 3` query outside this example. -/
scoped instance : NeZero L := ⟨by decide⟩
abbrev ν_q : ℚ := 3 / 20
def ν_val : PosReal := ⟨3/20, by norm_num⟩

lemma ν_val_eq_q : (ν_val : ℝ) = ((ν_q : ℚ) : ℝ) := by
  show ν_val.1 = _; simp [ν_val, ν_q]

/-! ## 2. StdIVPData Bundle -/

/-- ā component data from Numbers.lean. -/
def abar_Q : Fin L → Array ℚ
  | 0 => abar_0
  | 1 => abar_1
  | 2 => abar_2

def data : IVP.StdIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := abar_Q
  ν_q := ν_q
  hν := ν_val_eq_q
  habar_size := fun l => by fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]

/-! ## 3. Lorenz vector field f -/

abbrev σ_q : ℚ := 10
abbrev ρ_q_val : ℚ := 28
abbrev β_q : ℚ := 8 / 3

def x₀ : Fin L → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

open MvPolyBridge (CompPoly) in
def f_cpoly : Fin L → CompPoly L
  | 0 => .smul σ_q (.X 1 - .X 0)
  | 1 => .smul ρ_q_val (.X 0) - .X 1 - .X 0 * .X 2
  | 2 => -(.smul β_q (.X 2)) + .X 0 * .X 1

def f (a : Fin L → l1Weighted ν_val) (l : Fin L) : l1Weighted ν_val :=
  (f_cpoly l).evalBanach a



/-- The sequence-space operator `F`, generated from the vector field `f` via
the IVP Taylor recurrence `IVP.ivpCoeffs`:
  `F(a)_l(0) = a_l(0) − x₀(l)`,
  `F(a)_l(n+1) = (n+1)·a_l(n+1) − f(a)_l(n)`.
Codomain is the raw coefficient sequence `SystemCoeff L = Fin L → ℕ → ℝ`. -/
def F (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs f x₀ a l n

/-! ## 4. Fréchet derivative Df -/

/-- The derivative map fed to the `Z₁` face: componentwise, the Fréchet derivative of `f` at
`ā`, so the identification hypothesis of `Z₁_le_of_compPoly` holds by `rfl`. -/
def Df (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val :=
  fun l => fderiv ℝ (fun a => f a l) data.abar h


/-! ## 5. DF Correctness (Jacobian via `ivp_hDF_block_nat`) -/

/-- DF verification: single `native_decide` using `ivp_DF_of_Dφ_nat`. -/
private lemma hDF_nat :
    ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff data.abar_Q k)
          j m (row : ℕ) (col : ℕ) := by
  native_decide

/-- `data.composedApprox = fderiv(G)` on finite modes (modes `0 ≤ n ≤ N`).
The `CompPoly` adapter derives the symbolic specification, differentiability, and
coefficient bridge; `hDF_nat` is the remaining equation-specific matrix check. -/
lemma composedApprox_eq_fderiv_G_fin (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) ((fderiv ℝ (data.G f x₀) data.abar) h) l n :=
  data.composedApprox_eq_fderiv_G_fin_of_compPoly f_cpoly x₀ hDF_nat h l n hn

/-! ## 7. ℚ Bridges and Support Bounds -/

def x₀_q : Fin L → ℚ | 0 => 1 | 1 => 0 | 2 => 0

private lemma abar_toSeq_zero (l : Fin L) (k : ℕ) (hk : N < k) :
    l1Weighted.toSeq (data.abar l) k = 0 := by
  rw [data.abar_toSeq_eq, data.abar_Q_getD_eq_zero l k hk, Rat.cast_zero]


/-! ## 8. Norm bounds for ā components -/

lemma abar_norm_0_le : ‖data.abar 0‖ ≤ (20 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 0 n hn)]
  -- `finsum_bound` requires a literal range endpoint, so unfold `N` first.
  simp only [N]
  show _ ≤ ((20 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 0) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 0 k) (hν := ν_val_eq_q))

lemma abar_norm_1_le : ‖data.abar 1‖ ≤ (26 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 1 n hn)]
  simp only [N]
  show _ ≤ ((26 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 1) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 1 k) (hν := ν_val_eq_q))

lemma abar_norm_2_le : ‖data.abar 2‖ ≤ (11 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 2 n hn)]
  simp only [N]
  show _ ≤ ((11 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 2) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 2 k) (hν := ν_val_eq_q))

end Example83
