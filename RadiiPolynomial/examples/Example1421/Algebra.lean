import RadiiPolynomial.source.Chebyshev.StandardChebyshevIVP
import RadiiPolynomial.source.Chebyshev.ChebyshevBlockDiag
import RadiiPolynomial.source.LeanCertEval
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.examples.Example1421.Numbers

/-!
# Example 14.2.1 — Chebyshev IVP: u' = u(u-1)

Scalar IVP with Chebyshev basis: u̇ = u(u-1), u(-1) = p ∈ (-1,1).
Same ODE as Example 8.1 (Taylor), now verified on [-1,1] with Chebyshev expansion.

Uses `StdChebIVPData` to auto-derive all standard Chebyshev IVP constructions.
Only equation-specific code remains: φ (= a²-a as bilateral convolution).
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace Example1421

/-! ## 1. Parameters -/

-- TODO: Set N, ν from numerical solver output
-- abbrev N : ℕ := 20
-- abbrev L : ℕ := 1
-- instance : NeZero L := ⟨by decide⟩
-- abbrev ν_q : ℚ := 11/10  -- ν = 1.1
-- def ν_val : PosReal := ⟨1.1, by norm_num⟩

/-! ## 2. StdChebIVPData Bundle -/

-- TODO: Populate from Julia export
-- def data : ChebyshevIVP.StdChebIVPData ν_val L N where
--   A_col := A_col      -- from Numbers.lean
--   DF_col := DF_col     -- from Numbers.lean
--   abar_Q := fun _ => abar_0  -- from Numbers.lean
--   ν_q := ν_q
--   hν := by show ν_val.1 = _; simp [ν_val, ν_q]
--   habar_size := fun _ => by simp [abar_0]

/-! ## 3. Nonlinearity φ(a) = a² - a (bilateral convolution) -/

-- The polynomial: φ(u) = u² - u = u·u - u
-- In Chebyshev MvPolynomial form: X(0) * X(0) - X(0)
-- def phi_spec : Fin 1 → MvPolynomial (Fin 1) ℚ :=
--   fun _ => MvPolynomial.X 0 * MvPolynomial.X 0 - MvPolynomial.X 0

/-! ## 4. Bounds and Certificate -/

-- TODO: Y₀, Z₀, Z₁, Z₂ bounds from numerical verification
-- The certificate proof follows the same pattern as Example81.Certificate

end Example1421

end
