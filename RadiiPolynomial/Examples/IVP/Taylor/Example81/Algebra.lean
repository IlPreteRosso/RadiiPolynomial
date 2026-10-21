import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Certification.IVP.Taylor
import RadiiPolynomial.Algebra.Polynomial
import RadiiPolynomial.Examples.IVP.Taylor.Example81.Numbers

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
/-- Scoped: `L` is a reducible abbreviation of the numeral, so a global instance would also
serve every `NeZero 1` query outside this example. -/
scoped instance : NeZero L := ⟨by decide⟩
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



/-! ## 4. Fréchet derivative Df -/






/-! ## 5. DF Correctness (Jacobian matches numerical data) -/



/-! ## 6. ℚ Bridges -/

/-- ℚ mirror of `F(ābar)` — the IVP Taylor recurrence run in exact ℚ
arithmetic. The nonlinear term is `(f_cpoly 0).evalCoeff` rather than a
hand-written closed form, so the same definition works for any polynomial
nonlinearity. -/
def F_Q (n : ℕ) : ℚ :=
  IVP.ivpCoeffsQ f_cpoly data.abar_Q x₀_q 0 n

/-- The sequence-space operator `F`, generated from the vector field `f`
via the IVP Taylor recurrence `IVP.ivpCoeffs`:
  `F(a)_l(0) = a_l(0) − x₀(l)`,
  `F(a)_l(n+1) = (n+1)·a_l(n+1) − f(a)_l(n)`.
Codomain is the raw coefficient sequence `SystemCoeff L = Fin L → ℕ → ℝ`. -/
def F (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => IVP.ivpCoeffs f x₀ a l n

lemma F_bridge (l : Fin L) (n : ℕ) :
    F data.abar l n = (F_Q n : ℝ) := by
  have hl : l = 0 := Subsingleton.elim l 0
  subst l
  have hx₀ : ∀ j, x₀ j = (x₀_q j : ℝ) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    norm_num [x₀, x₀_q]
  change IVP.ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ data.abar 0 n =
    (IVP.ivpCoeffsQ f_cpoly data.abar_Q x₀_q 0 n : ℝ)
  exact data.ivpCoeffs_abar_eq_cast_of_compPoly f_cpoly x₀ x₀_q hx₀ 0 n


/-- The support index of `F(ā)` read off the syntax: `supportM f_cpoly N = 2N + 1`. -/
private lemma supportM_eq : IVP.supportM f_cpoly N = 2 * N + 1 := by decide


lemma F_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    IVP.ivpCoeffs f x₀ data.abar l n = 0 :=
  data.ivpCoeffs_abar_eq_zero_of_compPoly f_cpoly x₀ l n (supportM_eq ▸ hn)


/-! ## 7. Norm bounds for ā components -/




end Example81
