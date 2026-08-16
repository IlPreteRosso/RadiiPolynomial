import Mathlib.Data.Rat.Defs

/-!
# Example 14.2.1 — Numerical Data

Numerical certificates from Julia solver for the Chebyshev IVP: u' = u(u-1).

TODO: Populate with Julia export output:
- `abar_0`: approximate solution coefficients (ℚ array)
- `A_col`: approximate inverse matrix columns
- `DF_col`: Jacobian matrix columns
- Bound values: Y₀, Z₀, Z₁, Z₂, r₀
-/

namespace Example1421

-- TODO: Julia export fills these
-- def abar_0 : Array ℚ := #[...]
-- def A_col : Fin 1 → Fin 1 → ℕ → Array ℚ := ...
-- def DF_col : Fin 1 → Fin 1 → ℕ → Array ℚ := ...

end Example1421
