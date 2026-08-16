import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.CompPoly
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.source.MvPolyBridge.CompPoly
import RadiiPolynomial.examples.Example83.Numbers

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
instance : NeZero L := ⟨by decide⟩
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

def σ_val : ℝ := (σ_q : ℚ)
def ρ_val : ℝ := (ρ_q_val : ℚ)
def β_val : ℝ := (β_q : ℚ)

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

def f_spec (j : Fin L) : MvPolynomial (Fin L) ℚ :=
  (f_cpoly j).toMvPoly

lemma f_eq_spec (a : XL1 ν_val L) (l : Fin L) :
    f a l = MvPolyBridge.evalInBanach (f_spec l) a :=
  MvPolyBridge.compPoly_evalBanach_eq_evalInBanach _ _

/-- The sequence-space operator `F`, generated from the vector field `f` via
the IVP Taylor recurrence `IVP.ivpCoeffs`:
  `F(a)_l(0) = a_l(0) − x₀(l)`,
  `F(a)_l(n+1) = (n+1)·a_l(n+1) − f(a)_l(n)`.
Codomain is the raw coefficient sequence `SystemCoeff L = Fin L → ℕ → ℝ`
(see `project_ivp_codomain_design`). -/
def F (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs f x₀ a l n

/-! ## 4. Fréchet derivative Df -/

def Df (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | 0 => σ_val • (h 1 - h 0)
  | 1 => ρ_val • h 0 - h 1 - (data.abar 0 * h 2 + h 0 * data.abar 2)
  | 2 => -(β_val • h 2) + (data.abar 0 * h 1 + h 0 * data.abar 1)

lemma differentiable_f_component (l : Fin L) :
    Differentiable ℝ (fun a : XL1 ν_val L => f a l) := by
  exact MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l)

private abbrev proj_L (l : Fin L) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν_val) l

lemma fderiv_f_0 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => f a 0) a =
    σ_val • (proj_L 1 - proj_L 0) := by
  show fderiv ℝ (fun a : XL1 ν_val L => σ_val • (a 1 - a 0)) a = _
  auto_poly_fderiv

lemma fderiv_f_1 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => f a 1) a =
    ρ_val • proj_L 0 - proj_L 1 -
      ((l1Weighted.leftMul (a 0)).comp (proj_L 2) +
       (l1Weighted.leftMul (a 2)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => ρ_val • a 0 - a 1 - a 0 * a 2) a = _
  auto_poly_fderiv

lemma fderiv_f_2 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => f a 2) a =
    -(β_val • proj_L 2) +
      ((l1Weighted.leftMul (a 0)).comp (proj_L 1) +
       (l1Weighted.leftMul (a 1)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => -(β_val • a 2) + a 0 * a 1) a = _
  auto_poly_fderiv

lemma Df_eq_fderiv (h : XL1 ν_val L) (l : Fin L) :
    Df h l = (fderiv ℝ (fun a => f a l) data.abar) h := by
  fin_cases l <;>
    simp only [Df, show (⟨0, by decide⟩ : Fin L) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin L) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin L) = 2 from rfl,
      fderiv_f_0, fderiv_f_1, fderiv_f_2, proj_L,
      sub_apply, add_apply,
      neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      l1Weighted.leftMul_apply, mul_comm (data.abar _) (h _)]

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

/-! ## 6. Fderiv infrastructure (via StdIVPData) -/

lemma fderiv_G_lorenz_tail (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν_val) ((fderiv ℝ (data.G f x₀) data.abar h)) l n =
      toCoeff (ν := ν_val) h l n -
        toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Df h l)) l n :=
  data.fderiv_G_tail f x₀ differentiable_f_component
    Df Df_eq_fderiv h l n hn

/-! ## 7. ℚ Bridges and Support Bounds -/

def x₀_q : Fin L → ℚ | 0 => 1 | 1 => 0 | 2 => 0

def F_Q (l : Fin L) (n : ℕ) : ℚ :=
  IVP.ivpCoeffsQ f_cpoly data.abar_Q x₀_q l n

lemma f_bridge (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (f data.abar l) n =
      ((f_cpoly l).evalCoeff abar_Q n : ℝ) := by
  exact (f_cpoly l).toSeq_evalBanach data.abar abar_Q data.abar_toSeq_eq n

lemma F_bridge (l : Fin L) (n : ℕ) :
    F data.abar l n = (F_Q l n : ℝ) := by
  have hx₀ : ∀ j, x₀ j = (x₀_q j : ℝ) := by
    intro j
    fin_cases j <;> norm_num [x₀, x₀_q]
  change IVP.ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ data.abar l n =
    (IVP.ivpCoeffsQ f_cpoly data.abar_Q x₀_q l n : ℝ)
  exact data.ivpCoeffs_abar_eq_cast_of_compPoly f_cpoly x₀ x₀_q hx₀ l n

private lemma abar_toSeq_zero (l : Fin L) (k : ℕ) (hk : N < k) :
    l1Weighted.toSeq (data.abar l) k = 0 := by
  rw [data.abar_toSeq_eq]; show ((abar_Q l).getD k 0 : ℝ) = 0
  have hsz : (abar_Q l).size = N + 1 := by
    fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]
  have : ¬(k < (abar_Q l).size) := by omega
  simp [Array.getD, this]

lemma f_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N < n) :
    l1Weighted.toSeq (f data.abar l) n = 0 := by
  have ha' : ∀ i : Fin L, ∀ k, N < k → l1Weighted.toSeq (data.abar i) k = 0 :=
    fun i k hk => abar_toSeq_zero i k hk
  have h02 : l1Weighted.toSeq (data.abar 0 * data.abar 2) n = 0 := by
    rw [l1Weighted.toSeq_mul]; exact CauchyProduct.zero_of_support (ha' 0) (ha' 2) n hn
  have h01 : l1Weighted.toSeq (data.abar 0 * data.abar 1) n = 0 := by
    rw [l1Weighted.toSeq_mul]; exact CauchyProduct.zero_of_support (ha' 0) (ha' 1) n hn
  fin_cases l
  · show σ_val * (l1Weighted.toSeq (data.abar 1) n - l1Weighted.toSeq (data.abar 0) n) = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega)]; ring
  · show ρ_val * l1Weighted.toSeq (data.abar 0) n - l1Weighted.toSeq (data.abar 1) n -
        l1Weighted.toSeq (data.abar 0 * data.abar 2) n = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega), h02]; ring
  · show -(β_val * l1Weighted.toSeq (data.abar 2) n) +
        l1Weighted.toSeq (data.abar 0 * data.abar 1) n = 0
    rw [ha' 2 n (by omega), h01]; ring

lemma F_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    IVP.ivpCoeffs f x₀ data.abar l n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar l) (m + 1) -
    l1Weighted.toSeq (f data.abar l) m = 0
  rw [abar_toSeq_zero l (m + 1) (by omega), f_abar_support l m (by omega)]; ring

lemma F_abar_mem (l : Fin L) :
    l1Weighted.Mem ν_val (F data.abar l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (2 * N + 1)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [F, F_abar_support l n (by omega)]

/-! ## 8. Norm bounds for ā components -/

lemma abar_norm_0_le : ‖data.abar 0‖ ≤ (20 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 0 n hn)]
  -- `finsum_bound` now requires a literal range endpoint, so unfold `N` first.
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
