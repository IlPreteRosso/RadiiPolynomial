import RadiiPolynomial.Applications.IVP.Chebyshev.Polynomial
import RadiiPolynomial.Certification.Rational.Matrix

/-!
# Chebyshev certification adapter: ℚ layer

`radiusF`, `MY`, `Y₀Q`, `SnormQ` — the computable ℚ quantities of the residual and of the
symmetrized candidate. The module imports the Chebyshev discretization through its narrow owner
`Applications/IVP/Chebyshev/Polynomial` and the exact-rational layer `Rational/Matrix` (the
shared `blockActionQ`).
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

/-! ### ℚ layer (ν-free; the definitions of this section are computable)

The formulas take arbitrary rational data. The readings of `Y₀Q` and `SnormQ` as exact norms
hold at the stored data of a bundle `d : StdChebIVPData ν L N` (`ν_q = d.ν_q`, `p` the cast of
`p_q`): for `Y₀Q` inside the proof of `StdChebIVPData.Y₀_le_of_Q`, for `SnormQ` as
`StdChebIVPData.norm_symmetrize_abar_eq`. `Y₀Q` uses the shared `blockActionQ` with tail
multiplier `(2n)⁻¹`; its soundness proof invokes `SystemBlockDiagData.action_eq_blockActionQ`
directly. The family residual, support window and weighted norm sum are defined here. -/

section QLayer

variable {L : ℕ}

/-- Laurent support radius of the nonlinearity on the stored arrays. -/
def radiusF (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) : ℕ :=
  Finset.univ.sup fun l => (f l).laurentRadius (fun i => (arrs i).size)

/-- Support index of the residual `F(ā)` (and of `G(ā)`). -/
def MY (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (N : ℕ) : ℕ :=
  max N (radiusF f arrs + 1)

/-- Exact ℚ value of `‖G(ā)_l‖`. -/
def Y₀Q (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) (l : Fin L) : ℚ :=
  ∑ n : Fin (MY f abar_Q N + 1),
    |blockActionQ (N := N) (fun l j k => A_col l j k.val)
      (fun _ n => (2 * (n : ℚ))⁻¹) (compPolyIvpCoeffsQ f abar_Q p_q) l n| * ν_q ^ (n : ℕ)

/-- Exact ℚ value of `‖S(ā_i)‖` (bilateral, support `|k| ≤ N`). -/
def SnormQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (i : Fin L) : ℚ :=
  (∑ n : Fin (N + 1), |(abar_Q i).getD n 0| * ν_q ^ (n : ℕ)) +
    ∑ n : Fin N, |(abar_Q i).getD ((n : ℕ) + 1) 0| * ν_q ^ ((n : ℕ) + 1)

end QLayer

end ChebyshevIVP
