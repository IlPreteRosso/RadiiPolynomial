import Mathlib.Data.Rat.Defs

/-!
# Example 8.1 — Numerical Data

Exact ℚ data for the scalar IVP x' = x(x-1), x(0) = 1/2 with N = 10, ν = 1.

All data is exact (no floating-point rounding):
- Taylor coefficients: exact solution of the truncated system F^(N)(ā) = 0
- Approximate inverse: exact inverse of DF^(N)(ā) in ℚ
- Approximate derivative: exact Jacobian DF^(N)(ā) in ℚ
- Defect = 0 (exact inverse → Z₀ = 0)
-/

namespace Example81

/-! ## Approximate solution ābar -/

/-- Taylor coefficients of x(t) = 1/(1+e^t) truncated to order 10.
Even-indexed coefficients (except a₀) are zero by symmetry. -/
def abar_0 : Array ℚ :=
  #[1/2, -1/4, 0, 1/48, 0, -1/480, 0, 17/80640, 0, -31/1451520, 0]

/-! ## Approximate inverse A^(N) = [DF^(N)(ā)]^{-1}

Lower triangular 11×11 matrix, stored column-by-column.
Each `A_col 0 0 k` is column `k` of the single (l=0, j=0) block. -/

private def A_col_0 : Array ℚ :=
  #[1, 0, -1/4, 0, 1/24, 0, -17/2880, 0, 31/40320, 0, -691/7257600]

private def A_col_1 : Array ℚ :=
  #[0, 1, 0, -1/6, 0, 1/40, 0, -17/5040, 0, 31/72576, 0]

private def A_col_2 : Array ℚ :=
  #[0, 0, 1/2, 0, -1/16, 0, 5/576, 0, -13/11520, 0, 169/1209600]

private def A_col_3 : Array ℚ :=
  #[0, 0, 0, 1/3, 0, -1/30, 0, 11/2520, 0, -5/9072, 0]

private def A_col_4 : Array ℚ :=
  #[0, 0, 0, 0, 1/4, 0, -1/48, 0, 1/384, 0, -37/115200]

private def A_col_5 : Array ℚ :=
  #[0, 0, 0, 0, 0, 1/5, 0, -1/70, 0, 13/7560, 0]

private def A_col_6 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 1/6, 0, -1/96, 0, 7/5760]

private def A_col_7 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 1/7, 0, -1/126, 0]

private def A_col_8 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1/8, 0, -1/160]

private def A_col_9 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1/9, 0]

private def A_col_10 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/10]

/-- Column accessor for A^(N). For L=1, the block indices (l,j) are always (0,0). -/
def A_col (_ _ : Fin 1) (k : ℕ) : Array ℚ :=
  match k with
  | 0 => A_col_0 | 1 => A_col_1 | 2 => A_col_2 | 3 => A_col_3
  | 4 => A_col_4 | 5 => A_col_5 | 6 => A_col_6 | 7 => A_col_7
  | 8 => A_col_8 | 9 => A_col_9 | 10 => A_col_10 | _ => #[]

/-! ## Approximate derivative DF^(N)(ā)

Lower triangular 11×11 Jacobian matrix, stored column-by-column. -/

private def DF_col_0 : Array ℚ :=
  #[1, 0, 1/2, 0, -1/24, 0, 1/240, 0, -17/40320, 0, 31/725760]

private def DF_col_1 : Array ℚ :=
  #[0, 1, 0, 1/2, 0, -1/24, 0, 1/240, 0, -17/40320, 0]

private def DF_col_2 : Array ℚ :=
  #[0, 0, 2, 0, 1/2, 0, -1/24, 0, 1/240, 0, -17/40320]

private def DF_col_3 : Array ℚ :=
  #[0, 0, 0, 3, 0, 1/2, 0, -1/24, 0, 1/240, 0]

private def DF_col_4 : Array ℚ :=
  #[0, 0, 0, 0, 4, 0, 1/2, 0, -1/24, 0, 1/240]

private def DF_col_5 : Array ℚ :=
  #[0, 0, 0, 0, 0, 5, 0, 1/2, 0, -1/24, 0]

private def DF_col_6 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 6, 0, 1/2, 0, -1/24]

private def DF_col_7 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 7, 0, 1/2, 0]

private def DF_col_8 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 1/2]

private def DF_col_9 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0]

private def DF_col_10 : Array ℚ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10]

/-- Column accessor for DF^(N)(ā). -/
def DF_col (_ _ : Fin 1) (k : ℕ) : Array ℚ :=
  match k with
  | 0 => DF_col_0 | 1 => DF_col_1 | 2 => DF_col_2 | 3 => DF_col_3
  | 4 => DF_col_4 | 5 => DF_col_5 | 6 => DF_col_6 | 7 => DF_col_7
  | 8 => DF_col_8 | 9 => DF_col_9 | 10 => DF_col_10 | _ => #[]

/-! ## Numerical bounds (all exact ℚ) -/

/-- Y₀ bound: ‖A·F(ā)‖_{ℓ¹_ν} (tail residual). -/
def Y₀_bound : ℚ := 3 / 1000000

/-- Z₀ bound: ‖I - A·A†‖ = 0 (exact inverse). -/
def Z₀_bound : ℚ := 0

/-- Z₁ bound: ν/(N+1) · K where K = ‖2ā-1‖_{ℓ¹_ν}. -/
def Z₁_bound : ℚ := 396482 / 7983360

/-- Z₂ bound: 2·ν·(blockNorm + tailBound). -/
def Z₂_bound : ℚ := 110916221 / 39916800

/-- Radius of the existence ball. -/
def r_minus : ℚ := 1 / 10

end Example81
