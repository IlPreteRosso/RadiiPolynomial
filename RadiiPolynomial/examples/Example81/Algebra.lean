import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.examples.Example81.Numbers

/-!
# Example 8.1 — Algebraic Infrastructure

Scalar IVP: x' = x(x-1), x(0) = 1/2, with N = 10, ν = 1.

Uses `StdIVPData` to auto-derive all standard IVP constructions (approxInverse,
approxDeriv, tailCancel, abar, G, differentiable_G, composedApprox, Z₀, etc.).

Only equation-specific code remains: φ, Dφ, fderiv proofs, ℚ bridges.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace Example81

/-! ## 1. Parameters -/

abbrev N : ℕ := 10
abbrev L : ℕ := 1
instance : NeZero L := ⟨by decide⟩
abbrev ν_q : ℚ := 1
def ν_val : PosReal := ⟨1, by norm_num⟩

lemma ν_val_eq_q : (ν_val : ℝ) = ((ν_q : ℚ) : ℝ) := by
  show ν_val.1 = _; simp [ν_val, ν_q]

/-! ## 2. StdIVPData Bundle -/

def data : IVP.StdIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := fun _ => abar_0
  ν_q := ν_q
  hν := ν_val_eq_q
  habar_size := fun _ => by simp [abar_0]

/-! ## 3. Nonlinearity φ -/

/-- Initial condition x₀ = 1/2. -/
def x₀ : Fin L → ℝ | _ => 1 / 2

def x₀_q : Fin L → ℚ | _ => 1 / 2

/-- Nonlinearity φ(a)₀ = a₀² - a₀ (sequence-level Cauchy product minus identity). -/
def φ_scalar (a : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | _ => a 0 * a 0 - a 0

open MvPolynomial (C X pderiv) in
/-- φ as MvPolynomial for automatic differentiation. -/
def φ_scalar_spec : Fin L → MvPolynomial (Fin L) ℚ
  | _ => X 0 * X 0 - X 0

lemma φ_scalar_eq_spec (a : XL1 ν_val L) (l : Fin L) :
    φ_scalar a l = MvPolyBridge.evalInBanach (φ_scalar_spec l) a := by
  fin_cases l
  simp only [φ_scalar, φ_scalar_spec, MvPolyBridge.evalInBanach,
    map_mul, map_sub, MvPolynomial.aeval_X]

@[simp] lemma toSeq_φ_scalar (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_scalar a 0) n =
      l1Weighted.toSeq (a 0 * a 0) n - l1Weighted.toSeq (a 0) n := rfl

/-! ## 4. Fréchet Derivative of φ -/

lemma differentiable_φ_scalar_component (l : Fin L) :
    Differentiable ℝ (fun a : XL1 ν_val L => φ_scalar a l) := by
  fin_cases l; simp only [φ_scalar]; fun_prop

private abbrev proj_L (l : Fin L) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν_val) l

/-- Fréchet derivative of φ_scalar: Dφ(a)(h) = 2·a₀·h₀ - h₀. -/
lemma fderiv_φ_scalar (a : XL1 ν_val L) :
    fderiv ℝ (fun a : XL1 ν_val L => a 0 * a 0 - a 0) a =
    (l1Weighted.leftMul (a 0)).comp (proj_L 0) +
    (l1Weighted.leftMul (a 0)).comp (proj_L 0) - proj_L 0 := by
  auto_poly_fderiv

/-- Dφ at ābar: Dφ(h)₀ = 2·ā₀·h₀ - h₀ = (2ā₀ - 1)·h₀. -/
def Dφ_scalar (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | _ => 2 • (data.abar 0 * h 0) - h 0

lemma Dφ_scalar_eq_fderiv (h : XL1 ν_val L) (l : Fin L) :
    Dφ_scalar h l = (fderiv ℝ (fun a => φ_scalar a l) data.abar) h := by
  fin_cases l
  show 2 • (data.abar 0 * h 0) - h 0 =
    (fderiv ℝ (fun a : XL1 ν_val L => a 0 * a 0 - a 0) data.abar) h
  rw [fderiv_φ_scalar]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply]
  rw [show (2 : ℕ) • (data.abar 0 * h 0) = data.abar 0 * h 0 + data.abar 0 * h 0
    from two_nsmul _]


/-! ## 5. DF Correctness (Jacobian matches numerical data) -/

/-- ℚ mirror of pderiv coefficient at ābar:
    ∂φ₀/∂a₀ = 2·X₀ - 1, evaluated at ā gives (2a_k - δ_{k,0}). -/
private def Dφ_pderiv_Q (k : ℕ) : ℚ :=
  2 * abar_0.getD k 0 - (if k = 0 then 1 else 0)

/-- Bridge: Dφ_pderiv_Q matches analytical pderiv evaluation at ā. -/
private lemma Dφ_pderiv_bridge (j m : Fin L) (k : ℕ) :
    l1Weighted.toSeq (MvPolyBridge.evalInBanach
      (MvPolynomial.pderiv (↑m) (φ_scalar_spec j)) data.abar) k =
      (Dφ_pderiv_Q k : ℝ) := by
  fin_cases j; fin_cases m
  rw [MvPolyBridge.toSeq_evalInBanach _ _ (fun _ => abar_0)
    (fun l n => data.abar_toSeq_eq l n)]
  norm_cast
  simp [φ_scalar_spec, Dφ_pderiv_Q, MvPolynomial.pderiv_X]
  ring

/-- DF verification: single `native_decide` using bounded `Fin`-argument form. -/
private lemma hDF_nat :
    ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat (fun (_ _ : Fin L) => Dφ_pderiv_Q) j m (row : ℕ) (col : ℕ) := by
  native_decide

/-- **DF correctness via generic `ivp_hDF_block_nat`.** -/
lemma fderiv_F_coeffs_eq (h : XL1 ν_val L) (j : Fin L) (k : Fin (N + 1)) :
    (fderiv ℝ (fun a => IVP.ivpCoeffs φ_scalar x₀ a j ↑k) data.abar) h =
      ∑ m : Fin L, (data.approxDeriv.finBlock j m).mulVec
        (fun p => toCoeff (ν := ν_val) h m ↑p) k :=
  IVP.ivp_hDF_block_nat data.approxDeriv φ_scalar φ_scalar_spec x₀ data.abar (fun _ => abar_0)
    φ_scalar_eq_spec differentiable_φ_scalar_component data.abar_toSeq_eq
    (fun _ _ => Dφ_pderiv_Q) Dφ_pderiv_bridge
    DF_col (fun _ _ _ _ => rfl) hDF_nat h j k

/-- composedApprox = fderiv(G) on finite modes. -/
lemma composedApprox_eq_fderiv_G_fin (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) ((fderiv ℝ (data.G φ_scalar x₀) data.abar) h) l n :=
  data.composedApprox_eq_fderiv_G_fin φ_scalar φ_scalar_spec x₀
    φ_scalar_eq_spec differentiable_φ_scalar_component
    (fun _ _ => Dφ_pderiv_Q) Dφ_pderiv_bridge hDF_nat h l n hn

/-! ## 6. ℚ Bridges -/

/-- ℚ mirror of φ_scalar(ābar) coefficients. -/
def φ_scalar_Q (n : ℕ) : ℚ :=
  CauchyProduct (fun k => abar_0.getD k 0) (fun k => abar_0.getD k 0) n -
    abar_0.getD n 0

lemma φ_scalar_bridge (n : ℕ) :
    l1Weighted.toSeq (φ_scalar data.abar 0) n = (φ_scalar_Q n : ℝ) := by
  rw [φ_scalar_eq_spec]
  rw [MvPolyBridge.toSeq_evalInBanach _ _ (fun _ => abar_0)
    (fun l n => data.abar_toSeq_eq l n)]
  norm_cast
  simp [φ_scalar_spec, φ_scalar_Q]

/-- ℚ mirror of F_coeffs(ābar). -/
def F_coeffs_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => abar_0.getD 0 0 - x₀_q 0
  | n + 1 => ((n : ℚ) + 1) * abar_0.getD (n + 1) 0 - φ_scalar_Q n

def F_coeffs (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs φ_scalar x₀ a l n

lemma F_coeffs_bridge (l : Fin L) (n : ℕ) :
    F_coeffs data.abar l n = (F_coeffs_Q n : ℝ) := by
  fin_cases l
  simp only [F_coeffs]
  cases n with
  | zero =>
    show l1Weighted.toSeq (data.abar 0) 0 - x₀ 0 = _
    rw [data.abar_toSeq_eq]; simp [F_coeffs_Q, x₀_q, x₀, data]
  | succ m =>
    show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar 0) (m + 1) -
      l1Weighted.toSeq (φ_scalar data.abar 0) m = _
    rw [data.abar_toSeq_eq, φ_scalar_bridge m]
    simp only [F_coeffs_Q, data]; push_cast; ring

private lemma abar_toSeq_zero (k : ℕ) (hk : N < k) :
    l1Weighted.toSeq (data.abar 0) k = 0 := by
  rw [data.abar_toSeq_eq]; show ((abar_0.getD k 0 : ℚ) : ℝ) = 0
  have hsz : abar_0.size = N + 1 := by decide
  have : ¬(k < abar_0.size) := by omega
  simp [Array.getD, this]

lemma φ_scalar_abar_support (n : ℕ) (hn : 2 * N < n) :
    l1Weighted.toSeq (φ_scalar data.abar 0) n = 0 := by
  have ha : ∀ k, N < k → l1Weighted.toSeq (data.abar 0) k = 0 :=
    fun k hk => abar_toSeq_zero k hk
  simp only [toSeq_φ_scalar]
  have h00 : l1Weighted.toSeq (data.abar 0 * data.abar 0) n = 0 :=
    CauchyProduct.zero_of_support ha ha n hn
  rw [h00, ha n (by omega)]; ring

lemma F_coeffs_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    IVP.ivpCoeffs φ_scalar x₀ data.abar l n = 0 := by
  fin_cases l
  cases n with
  | zero => omega
  | succ m =>
    show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar 0) (m + 1) -
      l1Weighted.toSeq (φ_scalar data.abar 0) m = 0
    have ha : l1Weighted.toSeq (data.abar 0) (m + 1) = 0 :=
      abar_toSeq_zero (m + 1) (by omega)
    have hphi : l1Weighted.toSeq (φ_scalar data.abar 0) m = 0 :=
      φ_scalar_abar_support m (by omega)
    rw [ha, hphi]; ring

lemma F_coeffs_abar_mem (l : Fin L) :
    lpWeighted.Mem ν_val 1 (F_coeffs data.abar l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (2 * N + 1)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [F_coeffs, F_coeffs_abar_support l n (by omega)]

/-! ## 7. Norm bounds for ā components -/

/-- ℚ array for `2•ā₀ - 1` (precomputed literal for fast `native_decide`). -/
def two_abar_sub_one_Q : Array ℚ :=
  #[0, -1/2, 0, 1/24, 0, -1/240, 0, 17/40320, 0, -31/725760, 0]

/-- Bridge: `toSeq(2•ā₀ - 1) k = (two_abar_sub_one_Q.getD k 0 : ℝ)`. -/
lemma two_abar_sub_one_toSeq (k : ℕ) :
    l1Weighted.toSeq (2 • data.abar 0 - (1 : l1Weighted ν_val)) k =
      (two_abar_sub_one_Q.getD k 0 : ℝ) := by
  rw [show (1 : l1Weighted ν_val) = l1Weighted.one ν_val from rfl]
  rw [l1Weighted.toSeq_nsmul_sub_one 2 (data.abar 0) k, data.abar_toSeq_eq 0 k]
  -- data.abar_Q 0 = abar_0 by definition
  change (2 : ℝ) * ((abar_0.getD k 0 : ℚ) : ℝ) - _ = _
  have hℚ : ∀ i : Fin (N + 1),
      (2 : ℚ) * abar_0.getD (i : ℕ) 0 - (if (i : ℕ) = 0 then 1 else 0) =
      two_abar_sub_one_Q.getD (i : ℕ) 0 := by native_decide
  by_cases hk : k < N + 1
  · have := hℚ ⟨k, hk⟩
    convert congrArg ((↑) : ℚ → ℝ) this using 1
    · push_cast; split_ifs <;> simp
  · have hsz1 : abar_0.size = N + 1 := by decide
    have hsz2 : two_abar_sub_one_Q.size = N + 1 := by decide
    have hk1 : ¬(k < abar_0.size) := by omega
    have hk2 : ¬(k < two_abar_sub_one_Q.size) := by omega
    simp [Array.getD, hk1, hk2]; cases k with | zero => omega | succ => simp

lemma two_abar_sub_one_support (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (2 • data.abar 0 - (1 : l1Weighted ν_val)) n = 0 := by
  rw [two_abar_sub_one_toSeq]
  simp [Array.getD, show ¬(n < two_abar_sub_one_Q.size) from by
    simp [two_abar_sub_one_Q, N] at hn ⊢; omega]

/-! ## 8. Fderiv infrastructure (via StdIVPData) -/

lemma fderiv_G_scalar_tail (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν_val) ((fderiv ℝ (data.G φ_scalar x₀) data.abar h)) l n =
      toCoeff (ν := ν_val) h l n -
        toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Dφ_scalar h l)) l n :=
  data.fderiv_G_tail φ_scalar x₀ differentiable_φ_scalar_component
    Dφ_scalar Dφ_scalar_eq_fderiv h l n hn

end Example81
