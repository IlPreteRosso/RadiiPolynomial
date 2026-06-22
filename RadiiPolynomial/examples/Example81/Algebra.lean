import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv
import RadiiPolynomial.source.IVP.Theorem
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.source.MvPolyBridge.CompPoly
import RadiiPolynomial.examples.Example81.Numbers

/-!
# Example 8.1 — Algebraic Infrastructure

Scalar IVP: x' = x(x-1), x(0) = 1/2, with N = 10, ν = 1.

Uses `StdIVPData` to auto-derive all standard IVP constructions (approxInverse,
approxDeriv, tailCancel, abar, G, differentiable_G, composedApprox, Z₀, etc.).

Only equation-specific code remains: f, Df, fderiv proofs, ℚ bridges.
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

/-! ## 3. Vector field f -/

/-- Initial condition x₀ = 1/2. -/
def x₀ : Fin L → ℝ | _ => 1 / 2

def x₀_q : Fin L → ℚ | _ => 1 / 2

open MvPolyBridge (CompPoly) in
def f_cpoly : Fin L → CompPoly L
  | _ => .X 0 * .X 0 - .X 0

def f (a : Fin L → l1Weighted ν_val) (l : Fin L) : l1Weighted ν_val :=
  (f_cpoly l).evalBanach a

def f_spec (j : Fin L) : MvPolynomial (Fin L) ℚ :=
  (f_cpoly j).toMvPoly

lemma f_eq_spec (a : XL1 ν_val L) (l : Fin L) :
    f a l = MvPolyBridge.evalInBanach (f_spec l) a :=
  MvPolyBridge.compPoly_evalBanach_eq_evalInBanach _ _

/-! ## 4. Fréchet derivative Df -/

lemma differentiable_f_component (l : Fin L) :
    Differentiable ℝ (fun a : XL1 ν_val L => f a l) := by
  exact MvPolyBridge.differentiable_evalBanach_l1Weighted (f_cpoly l)

private abbrev proj_L (l : Fin L) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν_val) l

/-- Fréchet derivative of f: Df(a)(h) = 2·a₀·h₀ - h₀. -/
lemma fderiv_f (a : XL1 ν_val L) :
    fderiv ℝ (fun a : XL1 ν_val L => a 0 * a 0 - a 0) a =
    (l1Weighted.leftMul (a 0)).comp (proj_L 0) +
    (l1Weighted.leftMul (a 0)).comp (proj_L 0) - proj_L 0 := by
  auto_poly_fderiv

/-- Df at ābar: Df(h)₀ = 2·ā₀·h₀ - h₀ = (2ā₀ - 1)·h₀. -/
def Df (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | _ => 2 • (data.abar 0 * h 0) - h 0

lemma Df_eq_fderiv (h : XL1 ν_val L) (l : Fin L) :
    Df h l = (fderiv ℝ (fun a => f a l) data.abar) h := by
  fin_cases l
  show 2 • (data.abar 0 * h 0) - h 0 =
    (fderiv ℝ (fun a : XL1 ν_val L => a 0 * a 0 - a 0) data.abar) h
  rw [fderiv_f]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply]
  rw [show (2 : ℕ) • (data.abar 0 * h 0) = data.abar 0 * h 0 + data.abar 0 * h 0
    from two_nsmul _]


/-! ## 5. DF Correctness (Jacobian matches numerical data) -/

private def Df_pderiv_Q (j m : Fin L) (k : ℕ) : ℚ :=
  ((f_cpoly j).pderiv m).evalCoeff (fun _ => abar_0) k

private lemma Df_pderiv_bridge (j m : Fin L) (k : ℕ) :
    l1Weighted.toSeq (MvPolyBridge.evalInBanach
      (MvPolynomial.pderiv (↑m) (f_spec j)) data.abar) k =
      (Df_pderiv_Q j m k : ℝ) :=
  MvPolyBridge.compPoly_Dφ_bridge f_cpoly f_spec
    (fun _ => rfl)
    (fun _ => abar_0) data.abar data.abar_toSeq_eq j m k

private lemma hDF_nat :
    ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat Df_pderiv_Q j m (row : ℕ) (col : ℕ) := by
  native_decide

/-- `data.composedApprox = fderiv(G)` on finite modes (modes `0 ≤ n ≤ N`).
Live wrapper around `IVP.ivp_hDF_block_nat`: the StdIVPData abstraction packages
the per-example `Df_pderiv_Q`/`Df_pderiv_bridge`/`hDF_nat` triple together with
the symbolic-vs-numerical Jacobian agreement into the toCoeff/G-side framing
that the Z₁ bound consumes. -/
lemma composedApprox_eq_fderiv_G_fin (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν_val) (data.composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) ((fderiv ℝ (data.G f x₀) data.abar) h) l n :=
  data.composedApprox_eq_fderiv_G_fin f f_spec x₀
    f_eq_spec differentiable_f_component
    Df_pderiv_Q Df_pderiv_bridge hDF_nat h l n hn

/-! ## 6. ℚ Bridges -/

/-- Coefficient bridge: real `toSeq (f ā) n` equals the ℚ-arithmetic
`(f_cpoly 0).evalCoeff (·, abar_0) n`, cast to ℝ. Routes through
`MvPolynomial.aeval` (via `f_eq_spec` + `toSeq_evalInBanach`) and then
through `CompPoly.evalCoeff_eq_mvPolyCoeffQ` — the universal-property bridge
that lets us *generate* the ℚ mirror from `f_cpoly` instead of writing
it by hand. -/
lemma f_bridge (n : ℕ) :
    l1Weighted.toSeq (f data.abar 0) n =
      ((f_cpoly 0).evalCoeff (fun _ => abar_0) n : ℝ) := by
  rw [f_eq_spec,
    MvPolyBridge.toSeq_evalInBanach _ _ (fun _ => abar_0)
      (fun l n => data.abar_toSeq_eq l n)]
  exact_mod_cast
    (MvPolyBridge.CompPoly.evalCoeff_eq_mvPolyCoeffQ _ (fun _ => abar_0) n).symm

/-- ℚ mirror of `F(ābar)` — the IVP Taylor recurrence run in exact ℚ
arithmetic. The nonlinear term is `(f_cpoly 0).evalCoeff` rather than a
hand-written closed form, so the same definition works for any polynomial
nonlinearity. -/
def F_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => abar_0.getD 0 0 - x₀_q 0
  | n + 1 => ((n : ℚ) + 1) * abar_0.getD (n + 1) 0 -
      (f_cpoly 0).evalCoeff (fun _ => abar_0) n

/-- The sequence-space operator `F`, generated from the vector field `f`
via the IVP Taylor recurrence `IVP.ivpCoeffs`:
  `F(a)_l(0) = a_l(0) − x₀(l)`,
  `F(a)_l(n+1) = (n+1)·a_l(n+1) − f(a)_l(n)`.
Codomain is the raw coefficient sequence `SystemCoeff L = Fin L → ℕ → ℝ`
(see `project_ivp_codomain_design`). -/
def F (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs f x₀ a l n

lemma F_bridge (l : Fin L) (n : ℕ) :
    F data.abar l n = (F_Q n : ℝ) := by
  fin_cases l
  simp only [F]
  cases n with
  | zero =>
    show l1Weighted.toSeq (data.abar 0) 0 - x₀ 0 = _
    rw [data.abar_toSeq_eq]; simp [F_Q, x₀_q, x₀, data]
  | succ m =>
    show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar 0) (m + 1) -
      l1Weighted.toSeq (f data.abar 0) m = _
    rw [data.abar_toSeq_eq, f_bridge m]
    simp only [F_Q, data]; push_cast; ring

private lemma abar_toSeq_zero (k : ℕ) (hk : N < k) :
    l1Weighted.toSeq (data.abar 0) k = 0 := by
  rw [data.abar_toSeq_eq]; show ((abar_0.getD k 0 : ℚ) : ℝ) = 0
  have hsz : abar_0.size = N + 1 := by decide
  have : ¬(k < abar_0.size) := by omega
  simp [Array.getD, this]

lemma f_abar_support (n : ℕ) (hn : 2 * N < n) :
    l1Weighted.toSeq (f data.abar 0) n = 0 := by
  have ha : ∀ k, N < k → l1Weighted.toSeq (data.abar 0) k = 0 :=
    fun k hk => abar_toSeq_zero k hk
  have h00 : l1Weighted.toSeq (data.abar 0 * data.abar 0) n = 0 := by
    rw [l1Weighted.toSeq_mul]; exact CauchyProduct.zero_of_support ha ha n hn
  show l1Weighted.toSeq (data.abar 0 * data.abar 0) n - l1Weighted.toSeq (data.abar 0) n = 0
  rw [h00, ha n (by omega)]; ring

lemma F_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    IVP.ivpCoeffs f x₀ data.abar l n = 0 := by
  fin_cases l
  cases n with
  | zero => omega
  | succ m =>
    show ((m : ℝ) + 1) * l1Weighted.toSeq (data.abar 0) (m + 1) -
      l1Weighted.toSeq (f data.abar 0) m = 0
    have ha : l1Weighted.toSeq (data.abar 0) (m + 1) = 0 :=
      abar_toSeq_zero (m + 1) (by omega)
    have hphi : l1Weighted.toSeq (f data.abar 0) m = 0 :=
      f_abar_support m (by omega)
    rw [ha, hphi]; ring

lemma F_abar_mem (l : Fin L) :
    l1Weighted.Mem ν_val (F data.abar l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (2 * N + 1)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [F, F_abar_support l n (by omega)]

/-! ## 7. Norm bounds for ā components -/

/-- ℚ array for `2•ā₀ - 1` (precomputed literal for fast `native_decide`). -/
def two_abar_sub_one_Q : Array ℚ :=
  #[0, -1/2, 0, 1/24, 0, -1/240, 0, 17/40320, 0, -31/725760, 0]

/-- Bridge: `toSeq(2•ā₀ - 1) k = (two_abar_sub_one_Q.getD k 0 : ℝ)`. -/
lemma two_abar_sub_one_toSeq (k : ℕ) :
    l1Weighted.toSeq (2 • data.abar 0 - (1 : l1Weighted ν_val)) k =
      (two_abar_sub_one_Q.getD k 0 : ℝ) := by
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
    toCoeff (ν := ν_val) ((fderiv ℝ (data.G f x₀) data.abar h)) l n =
      toCoeff (ν := ν_val) h l n -
        toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Df h l)) l n :=
  data.fderiv_G_tail f x₀ differentiable_f_component
    Df Df_eq_fderiv h l n hn

end Example81
