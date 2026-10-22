import RadiiPolynomial.Applications.IVP.Chebyshev
import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Numbers

/-!
# Example 14.2.1 — Chebyshev IVP: u' = u(u-1)

Scalar IVP with Chebyshev basis: u̇ = u(u-1), u(-1) = 1/2.
Same ODE as Example 8.1 (Taylor) — the book's own twin pair — now verified on
[-1,1] with Chebyshev expansion at ν = 2, N = 40.

## One polynomial, every interpretation

The example supplies the syntax `f_cpoly = X² − X` and nothing structural. The
coefficient nonlinearity is the library's `ChebyshevIVP.banachField f_cpoly`: the
book's convolution (Eq. 14.10) is bilateral with the SYMMETRIC extension
`ã_{-k} = ã_k` of the one-sided storage, so each input is first symmetrized
(`l1Chebyshev.symmetrize`, `S(h)_k = h_{|k|}`, `‖S‖ ≤ 2`) and then multiplied in the
bilateral algebra: `φ(a) = S(a)·S(a) − S(a)`. Reading only non-negative modes is what
keeps the Z₁ bound finite (the composed approximation is the identity on negative
modes, so unsymmetrized derivative couplings would leak unpreconditioned); zeros of
`G` have vanishing negative modes, where φ agrees with the book's Eq. 14.11.

## The derivative

The certificate uses the family's derivative `compPolyDerivative`; for `f_cpoly` its value in
the direction `h` is `2·S(aₗ)·S(hₗ) − S(hₗ)`, a closed form not stated in this file.
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter RadiiPolynomial ChebyshevIVP MvPolyBridge

noncomputable section

namespace Example1421

/-! ## 1. Parameters -/

abbrev N : ℕ := 40
abbrev L : ℕ := 1
/-- Scoped: `L` is a reducible abbreviation of the numeral, so a global instance would also
serve every `NeZero 1` query outside this example. -/
scoped instance : NeZero L := ⟨by decide⟩
abbrev ν_q : ℚ := 2
def ν_val : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1 : ℝ) ≤ (ν_val : ℝ)) := ⟨by rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num⟩

lemma ν_val_eq_q : (ν_val : ℝ) = ((ν_q : ℚ) : ℝ) := by
  rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num

/-- The weight is at least `2`: the hypothesis of the contractive (`_of_two_le_`) solution
faces, which this example meets with equality. -/
lemma two_le_ν_val : (2 : ℝ) ≤ (ν_val : ℝ) := by
  rw [show ((ν_val : ℝ)) = 2 from rfl]

/-- Initial value u(-1) = 1/2. -/
def p₀ : Fin L → ℝ := fun _ => 1/2

/-! ## 2. The polynomial system and its explicit derivative -/

/-- One polynomial supplies the function, coefficient, and rational certificate interpretations. -/
def f_cpoly (l : Fin L) : CompPoly L := .X l * .X l - .X l





/-! ## 3. Data bundle -/

/-- The bundled numerical data for the standard Chebyshev IVP pipeline. -/
def data : ChebyshevIVP.StdChebIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := fun _ => abar_0
  ν_q := ν_q
  hν := ν_val_eq_q
  habar_size := fun _ => by decide +kernel

/-! ## 4. Audit witnesses

The three theorems below are not consumed by the certificate: `Certificate.lean` checks
the stored Jacobian through its own exact-ℚ folds (`Z₀_finBlockNorm_le`, the `Z₁` column
computation). They are independent `native_decide` witnesses that the stored matrix
`DF_col` is the one the polynomial generates. -/




end Example1421
