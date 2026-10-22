import RadiiPolynomial.Examples.PowerSeries.Example77.Algebra
import RadiiPolynomial.Certification
import RadiiPolynomial.Tactic.FinMatrixBound
import RadiiPolynomial.Certification.PowerSeries.PolynomialZero

/-!
# Example 7.7 — Certificate

Computer-assisted proof for `x² - λ = 0` at `λ₀ = 1/3`.

`main_theorem` goes through `data : PolyZeroData` (the member `P = X·X` of the
polynomial-zero family) and `PolyZeroData.existsUnique`; `data_checks` checks every
bound in `ℚ` with one `decide +kernel`. `data` refers to `ā₀ ā₁ ā₂`, `lam0`, `ν_q` and `r₀`
by name and writes the `A` columns and the four bounds as literals.

All parameter defs are ℚ. Lean auto-coerces ℚ → ℝ wherever ℝ is expected.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial Example77

noncomputable section

namespace Example77.Cert

/-! ## Numerical input (λ₀ = 1/3) -/

def ā₀ : ℚ := 5774/10000
def ā₁ : ℚ := 8660/10000
def ā₂ : ℚ := -6495/10000
def lam0 : ℚ := 1/3
def ν_q : ℚ := 1/4
def r₀ : ℚ := 996/10000

/-! ## Derived definitions -/

noncomputable def ν_val : PosReal := ⟨ν_q, by unfold ν_q; norm_num⟩


noncomputable def sol : ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := by unfold ā₀; norm_num






/-! ## ℚ data for evaluators -/



open RadiiPolynomial in
/-! ## Main Theorem

The equation is the member `P = X·X` of the polynomial-zero family, with the centre
`ā₀ ā₁ ā₂` and radius `r₀` above; the `A` columns and bounds are written as literals in
`data`, and one `decide +kernel` checks every bound in `ℚ`. -/

/-- The certificate data (`λ₀ = 1/3`) as a `PolyZeroData`. -/
def data : PolyZeroData where
  P := .mul (.X 0) (.X 0)
  N := 2
  νq := ν_q
  aQ := #[ā₀, ā₁, ā₂]
  cQ := #[lam0, 1]
  Acols := ![#[8660/10000, -12990/10000, 29240/10000], #[0, 8660/10000, -12990/10000],
    #[0, 0, 8660/10000]]
  r₀ := r₀
  Y₀ := 9/500
  Z₀ := 2/1000
  Z₁ := 46/100
  Z₂ := 28/10

/-- The single certificate obligation. -/
theorem data_checks : data.Checks := by decide +kernel

theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀,
      F lam0 xTilde = 0 :=
  data.existsUnique rfl _ _
    (fun n => by
      rw [ApproxSolution.toL1_toSeq]
      rcases n with _ | _ | _ | n <;> simp [ApproxSolution.toSeq, sol, data,
      PolyZeroData.a, Array.getD_eq_getD_getElem?])
    (fun n => by rcases n with _ | _ | n <;> simp [c, paramSeq, data, PolyZeroData.cq,
      Array.getD_eq_getD_getElem?])
    data_checks

end Example77.Cert
