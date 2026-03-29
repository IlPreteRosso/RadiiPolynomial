import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.MvPolyBridge.Basic
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

/-- Simp set for evaluating CLM applications on Pi-type Banach algebras. -/
macro "clm_apply" : tactic =>
  `(tactic| simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply])

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

/-! ## 3. Lorenz Nonlinearity φ -/

def σ_val : ℝ := 10
def ρ_val : ℝ := 28
def β_val : ℝ := 8 / 3

def x₀ : Fin L → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

def φ_lorenz (a : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | 0 => σ_val • (a 1 - a 0)
  | 1 => ρ_val • a 0 - a 1 - a 0 * a 2
  | 2 => -(β_val • a 2) + a 0 * a 1

open MvPolynomial (C X pderiv) in
def φ_lorenz_spec : Fin L → MvPolynomial (Fin L) ℚ
  | 0 => C 10 * (X 1 - X 0)
  | 1 => C 28 * X 0 - X 1 - X 0 * X 2
  | 2 => -(C (8 / 3)) * X 2 + X 0 * X 1

lemma φ_lorenz_eq_spec (a : XL1 ν_val L) (l : Fin L) :
    φ_lorenz a l = MvPolyBridge.evalInBanach (φ_lorenz_spec l) a := by
  fin_cases l <;>
    simp only [φ_lorenz, φ_lorenz_spec, MvPolyBridge.evalInBanach, σ_val, ρ_val, β_val,
      map_mul, map_sub, map_add, map_neg, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, neg_mul, smul_mul_assoc, one_mul, smul_sub,
      l1Weighted.ratSmul_eq] <;>
    push_cast <;> ring

@[simp] lemma toSeq_φ_lorenz_0 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 0) n =
      σ_val * (l1Weighted.toSeq (a 1) n - l1Weighted.toSeq (a 0) n) := rfl

@[simp] lemma toSeq_φ_lorenz_1 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 1) n =
      ρ_val * l1Weighted.toSeq (a 0) n - l1Weighted.toSeq (a 1) n -
        l1Weighted.toSeq (a 0 * a 2) n := rfl

@[simp] lemma toSeq_φ_lorenz_2 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 2) n =
      -(β_val * l1Weighted.toSeq (a 2) n) + l1Weighted.toSeq (a 0 * a 1) n := rfl

noncomputable def F_lorenz (a : XL1 ν_val L) : Fin L → l1Omega ν_val := fun l =>
  l1Omega.mk (fun n =>
    match n with
    | 0 => l1Weighted.toSeq (a l) 0 - x₀ l
    | n + 1 => ((n : ℝ) + 1) * l1Weighted.toSeq (a l) (n + 1) -
        l1Weighted.toSeq (φ_lorenz a l) n)
    (l1Omega.mem_deriv_shift_sub (a l) (φ_lorenz a l) _)

def F_coeffs (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs φ_lorenz x₀ a l n

/-! ## 4. Fréchet Derivative of φ -/

def Dφ_lorenz (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | 0 => σ_val • (h 1 - h 0)
  | 1 => ρ_val • h 0 - h 1 - (data.abar 0 * h 2 + h 0 * data.abar 2)
  | 2 => -(β_val • h 2) + (data.abar 0 * h 1 + h 0 * data.abar 1)

lemma differentiable_φ_lorenz_component (l : Fin L) :
    Differentiable ℝ (fun a : XL1 ν_val L => φ_lorenz a l) := by
  fin_cases l <;> simp only [φ_lorenz] <;> fun_prop

private abbrev proj_L (l : Fin L) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν_val) l

lemma fderiv_φ_lorenz_0 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 0) a =
    σ_val • (proj_L 1 - proj_L 0) := by
  show fderiv ℝ (fun a : XL1 ν_val L => σ_val • (a 1 - a 0)) a = _
  auto_poly_fderiv

lemma fderiv_φ_lorenz_1 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 1) a =
    ρ_val • proj_L 0 - proj_L 1 -
      ((l1Weighted.leftMul (a 0)).comp (proj_L 2) +
       (l1Weighted.leftMul (a 2)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => ρ_val • a 0 - a 1 - a 0 * a 2) a = _
  auto_poly_fderiv

lemma fderiv_φ_lorenz_2 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 2) a =
    -(β_val • proj_L 2) +
      ((l1Weighted.leftMul (a 0)).comp (proj_L 1) +
       (l1Weighted.leftMul (a 1)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => -(β_val • a 2) + a 0 * a 1) a = _
  auto_poly_fderiv

lemma Dφ_lorenz_eq_fderiv (h : XL1 ν_val L) (l : Fin L) :
    Dφ_lorenz h l = (fderiv ℝ (fun a => φ_lorenz a l) data.abar) h := by
  fin_cases l <;>
    simp only [Dφ_lorenz, show (⟨0, by decide⟩ : Fin L) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin L) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin L) = 2 from rfl,
      fderiv_φ_lorenz_0, fderiv_φ_lorenz_1, fderiv_φ_lorenz_2, proj_L,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      l1Weighted.leftMul_apply, mul_comm (data.abar _) (h _)]

/-! ## 5. DF Correctness (Jacobian via `ivp_hDF_block_nat`) -/

/-- ℚ mirror of pderiv coefficients at ābar. -/
private def Dφ_pderiv_Q (j m : Fin L) (k : ℕ) : ℚ :=
  match j, m with
  | 0, 0 => if k = 0 then -10 else 0
  | 0, 1 => if k = 0 then 10 else 0
  | 0, 2 => 0
  | 1, 0 => (if k = 0 then 28 else 0) - (abar_Q 2).getD k 0
  | 1, 1 => if k = 0 then -1 else 0
  | 1, 2 => -((abar_Q 0).getD k 0)
  | 2, 0 => (abar_Q 1).getD k 0
  | 2, 1 => (abar_Q 0).getD k 0
  | 2, 2 => if k = 0 then -(8 / 3 : ℚ) else 0

/-- Bridge: Dφ_pderiv_Q matches analytical pderiv evaluation at ā. -/
private lemma Dφ_pderiv_bridge (j m : Fin L) (k : ℕ) :
    l1Weighted.toSeq (MvPolyBridge.evalInBanach
      (MvPolynomial.pderiv (↑m) (φ_lorenz_spec j)) data.abar) k =
      (Dφ_pderiv_Q j m k : ℝ) := by
  rw [MvPolyBridge.toSeq_evalInBanach _ _ abar_Q (fun i n => data.abar_toSeq_eq i n)]
  norm_cast
  fin_cases j <;> fin_cases m <;>
    simp (config := { decide := true }) [φ_lorenz_spec, Dφ_pderiv_Q,
      MvPolynomial.pderiv_X, Pi.single_apply, neg_mul] <;>
    split_ifs <;> simp_all

/-- DF verification: single `native_decide` using `ivp_DF_of_Dφ_nat`. -/
private lemma hDF_nat :
    ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat Dφ_pderiv_Q j m (row : ℕ) (col : ℕ) := by
  native_decide

/-- **DF correctness via generic `ivp_hDF_block_nat`.** -/
lemma fderiv_F_coeffs_eq (h : XL1 ν_val L) (j : Fin L) (k : Fin (N + 1)) :
    (fderiv ℝ (fun a => IVP.ivpCoeffs φ_lorenz x₀ a j ↑k) data.abar) h =
      ∑ m : Fin L, (data.approxDeriv.finBlock j m).mulVec
        (fun p => toCoeff (ν := ν_val) h m ↑p) k :=
  IVP.ivp_hDF_block_nat data.approxDeriv φ_lorenz φ_lorenz_spec x₀ data.abar abar_Q
    φ_lorenz_eq_spec differentiable_φ_lorenz_component data.abar_toSeq_eq
    Dφ_pderiv_Q Dφ_pderiv_bridge
    DF_col (fun _ _ _ _ => rfl) hDF_nat h j k

/-- composedApprox = fderiv(G) on finite modes. -/
lemma composedApprox_eq_fderiv_G_fin (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) ((fderiv ℝ (data.G φ_lorenz x₀) data.abar) h) l n :=
  data.composedApprox_eq_fderiv_G_fin φ_lorenz φ_lorenz_spec x₀
    φ_lorenz_eq_spec differentiable_φ_lorenz_component
    Dφ_pderiv_Q Dφ_pderiv_bridge hDF_nat h l n hn

/-! ## 6. Fderiv infrastructure (via StdIVPData) -/

lemma fderiv_G_lorenz_tail (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν_val) ((fderiv ℝ (data.G φ_lorenz x₀) data.abar h)) l n =
      toCoeff (ν := ν_val) h l n -
        toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Dφ_lorenz h l)) l n :=
  data.fderiv_G_tail φ_lorenz x₀ differentiable_φ_lorenz_component
    Dφ_lorenz Dφ_lorenz_eq_fderiv h l n hn

/-! ## 7. ℚ Bridges and Support Bounds -/

abbrev σ_q : ℚ := 10
abbrev ρ_q_val : ℚ := 28
abbrev β_q : ℚ := 8 / 3
def x₀_q : Fin L → ℚ | 0 => 1 | 1 => 0 | 2 => 0

def φ_lorenz_Q (l : Fin L) (n : ℕ) : ℚ :=
  match l with
  | 0 => σ_q * ((abar_Q 1).getD n 0 - (abar_Q 0).getD n 0)
  | 1 => ρ_q_val * (abar_Q 0).getD n 0 - (abar_Q 1).getD n 0 -
      CauchyProduct (fun k => (abar_Q 0).getD k 0) (fun k => (abar_Q 2).getD k 0) n
  | 2 => -(β_q * (abar_Q 2).getD n 0) +
      CauchyProduct (fun k => (abar_Q 0).getD k 0) (fun k => (abar_Q 1).getD k 0) n

def F_coeffs_Q (l : Fin L) (n : ℕ) : ℚ :=
  match n with
  | 0 => (abar_Q l).getD 0 0 - x₀_q l
  | n + 1 => ((n : ℚ) + 1) * (abar_Q l).getD (n + 1) 0 - φ_lorenz_Q l n

lemma φ_lorenz_bridge (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz data.abar l) n = (φ_lorenz_Q l n : ℝ) := by
  rw [φ_lorenz_eq_spec]
  rw [MvPolyBridge.toSeq_evalInBanach _ _ abar_Q (fun i n => data.abar_toSeq_eq i n)]
  norm_cast
  fin_cases l <;> simp [φ_lorenz_spec, φ_lorenz_Q, σ_q, ρ_q_val, β_q, neg_mul]

lemma F_coeffs_bridge (l : Fin L) (n : ℕ) :
    F_coeffs data.abar l n = (F_coeffs_Q l n : ℝ) := by
  simp only [F_coeffs]
  cases n with
  | zero =>
    show l1Weighted.toSeq (data.abar l) 0 - x₀ l = _
    rw [data.abar_toSeq_eq]; simp [F_coeffs_Q, x₀_q, x₀, data]
    fin_cases l <;> push_cast <;> ring
  | succ m =>
    show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar l) (m + 1) -
      l1Weighted.toSeq (φ_lorenz data.abar l) m = _
    rw [data.abar_toSeq_eq, φ_lorenz_bridge l m]
    simp only [F_coeffs_Q, data]; push_cast; ring

private lemma abar_toSeq_zero (l : Fin L) (k : ℕ) (hk : N < k) :
    l1Weighted.toSeq (data.abar l) k = 0 := by
  rw [data.abar_toSeq_eq]; show ((abar_Q l).getD k 0 : ℝ) = 0
  have hsz : (abar_Q l).size = N + 1 := by
    fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]
  have : ¬(k < (abar_Q l).size) := by omega
  simp [Array.getD, this]

lemma φ_lorenz_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N < n) :
    l1Weighted.toSeq (φ_lorenz data.abar l) n = 0 := by
  have ha' : ∀ i : Fin L, ∀ k, N < k → l1Weighted.toSeq (data.abar i) k = 0 :=
    fun i k hk => abar_toSeq_zero i k hk
  have h02 : l1Weighted.toSeq (data.abar 0 * data.abar 2) n = 0 :=
    CauchyProduct.zero_of_support (ha' 0) (ha' 2) n hn
  have h01 : l1Weighted.toSeq (data.abar 0 * data.abar 1) n = 0 :=
    CauchyProduct.zero_of_support (ha' 0) (ha' 1) n hn
  fin_cases l
  · show σ_val * (l1Weighted.toSeq (data.abar 1) n - l1Weighted.toSeq (data.abar 0) n) = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega)]; ring
  · show ρ_val * l1Weighted.toSeq (data.abar 0) n - l1Weighted.toSeq (data.abar 1) n -
        l1Weighted.toSeq (data.abar 0 * data.abar 2) n = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega), h02]; ring
  · show -(β_val * l1Weighted.toSeq (data.abar 2) n) +
        l1Weighted.toSeq (data.abar 0 * data.abar 1) n = 0
    rw [ha' 2 n (by omega), h01]; ring

lemma F_coeffs_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    IVP.ivpCoeffs φ_lorenz x₀ data.abar l n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar l) (m + 1) -
    l1Weighted.toSeq (φ_lorenz data.abar l) m = 0
  rw [abar_toSeq_zero l (m + 1) (by omega), φ_lorenz_abar_support l m (by omega)]; ring

lemma F_coeffs_abar_mem (l : Fin L) :
    lpWeighted.Mem ν_val 1 (F_coeffs data.abar l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (2 * N + 1)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [F_coeffs, F_coeffs_abar_support l n (by omega)]

/-! ## 8. Norm bounds for ā components -/

lemma abar_norm_0_le : ‖data.abar 0‖ ≤ (20 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 0 n hn)]
  show _ ≤ ((20 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 0) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 0 k) (hν := ν_val_eq_q))

lemma abar_norm_1_le : ‖data.abar 1‖ ≤ (26 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 1 n hn)]
  show _ ≤ ((26 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 1) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 1 k) (hν := ν_val_eq_q))

lemma abar_norm_2_le : ‖data.abar 2‖ ≤ (11 : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => abar_toSeq_zero 2 n hn)]
  show _ ≤ ((11 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 2) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := data.abar_toSeq_eq 2 k) (hν := ν_val_eq_q))

end Example83
