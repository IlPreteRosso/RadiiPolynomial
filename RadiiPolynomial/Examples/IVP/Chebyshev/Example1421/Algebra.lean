import RadiiPolynomial.Applications.IVP.Chebyshev
import RadiiPolynomial.Tactic.MakeCompPoly
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

## The explicit derivative

`Dphi a h l = 2·S(aₗ)·S(hₗ) − S(hₗ)` is the example's own algebra: the Z₁ column
computation of `Certificate.lean` unfolds it by `show`. `Dphi_eq_derivative` /
`compPolyDerivative_apply_eq_Dphi` identify it with the adapter's symbolic derivative
of `f_cpoly`; differentiability of the preconditioned map (`G_diff`) comes from the
adapter, not from this formula.
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter RadiiPolynomial ChebyshevIVP MvPolyBridge

noncomputable section

namespace Example1421

/-! ## 1. Parameters -/

abbrev N : ℕ := 40
abbrev L : ℕ := 1
instance : NeZero L := ⟨by decide⟩
abbrev ν_q : ℚ := 2
def ν_val : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1 : ℝ) ≤ (ν_val : ℝ)) := ⟨by rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num⟩
instance : Fact ((1 : ℝ) < (ν_val : ℝ)) := ⟨by rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num⟩

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

/-- The literal syntax is what `compPolyOf%` reifies the nonlinearity's own lambda to:
the certificate-level witness that the elaborator and the hand-written AST agree. -/
theorem f_cpoly_reified :
    f_cpoly 0 = compPolyOf% (fun u : Fin L → ℝ => u 0 * u 0 - u 0) := rfl

/-- The Dφ direction map used in the Z-bounds: `Dφ(a)(h)ₗ = 2·S(aₗ)·S(hₗ) − S(hₗ)`. -/
def Dphi (a h : XCheb ν_val L) (l : Fin L) : l1Chebyshev ν_val :=
  (2 : ℝ) • (l1Chebyshev.symmetrize_CLM (a l) * l1Chebyshev.symmetrize_CLM (h l))
    - l1Chebyshev.symmetrize_CLM (h l)

/-- The direction map is the adapter's derivative applied to the direction. -/
lemma Dphi_eq_derivative (a h : XCheb ν_val L) (l : Fin L) :
    Dphi a h l = CompPoly.Chebyshev.derivative (f_cpoly l) a h := by
  rw [CompPoly.Chebyshev.derivative_apply, Fin.sum_univ_one]
  have hl : l = 0 := Subsingleton.elim _ _
  subst hl
  symm
  change CompPoly.Chebyshev.eval ((f_cpoly 0).pderiv 0) a * l1Chebyshev.symmetrize_CLM (h 0) =
    (2 : ℝ) • (l1Chebyshev.symmetrize_CLM (a 0) * l1Chebyshev.symmetrize_CLM (h 0))
      - l1Chebyshev.symmetrize_CLM (h 0)
  simp only [CompPoly.Chebyshev.eval, f_cpoly, CompPoly.pderiv_sub_op,
    CompPoly.pderiv_mul_op, CompPoly.pderiv.eq_2, ite_true]
  change ((algebraMap ℝ _ ((1 : ℚ) : ℝ) * l1Chebyshev.symmetrize_CLM (a 0) +
    l1Chebyshev.symmetrize_CLM (a 0) * algebraMap ℝ _ ((1 : ℚ) : ℝ) -
    algebraMap ℝ _ ((1 : ℚ) : ℝ)) * l1Chebyshev.symmetrize_CLM (h 0)) = _
  simp [two_smul, sub_mul, add_mul]

/-- The adapter's system derivative, read componentwise, is the explicit direction map. -/
lemma compPolyDerivative_apply_eq_Dphi (a h : XCheb ν_val L) (l : Fin L) :
    compPolyDerivative f_cpoly a h l = Dphi a h l :=
  (Dphi_eq_derivative a h l).symm

/-! ## 3. Data bundle -/

/-- The bundled numerical data for the standard Chebyshev IVP pipeline. -/
def data : ChebyshevIVP.StdChebIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := fun _ => abar_0
  ν_q := ν_q
  hν := ν_val_eq_q
  habar_size := fun _ => by native_decide

/-- Differentiability of the preconditioned map, from the syntax
(consumed by `Examples/Transport/TwinTransport.lean`). -/
lemma G_diff : Differentiable ℝ (data.G (banachField f_cpoly) p₀) :=
  data.differentiable_G_of_compPoly f_cpoly p₀

/-! ## 4. Audit witnesses

The three theorems below are not consumed by the certificate: `Certificate.lean` checks
the stored Jacobian through its own exact-ℚ folds (`Z₀_finBlockNorm_le`, the `Z₁` column
computation). They are independent `native_decide` witnesses that the stored matrix
`DF_col` is the one the polynomial generates, and the audit files under
`tmp/proposal_experiments_2026_09_06/checks/cheb_comppoly_promotion_2026_09_12/`
(`promoted_axioms.lean`) print their axioms. -/

/-- Audit witness: every stored finite Jacobian column is generated by the shared
polynomial (one `native_decide` over the 41 × 41 block). -/
theorem computed_DF_columns : ∀ l m : Fin L, ∀ k : Fin (N + 1),
    Array.ofFn (fun n : Fin (N + 1) =>
      compPolyDFQ f_cpoly (fun _ => abar_0) l m n k) = DF_col l m k := by
  native_decide

/-- Audit witness, entrywise form of `computed_DF_columns`. -/
theorem computed_DF_entries (l m : Fin L) (n k : Fin (N + 1)) :
    compPolyDFQ f_cpoly data.abar_Q l m n k = (data.DF_col l m k).getD n 0 := by
  have h := congrArg (fun a : Array ℚ => a.getD n 0) (computed_DF_columns l m k)
  simpa [Array.getD, n.isLt, data] using h

/-- Audit witness: the checked finite entries are the derivatives of the raw coefficient
equations (`computed_DF_entries` composed with the adapter's
`rawDerivative_single_eq_cast_of_compPoly`). -/
theorem rawDerivative_single_eq_dataDF (l m : Fin L) (n k : Fin (N + 1)) :
    FAseq ((Pi.single m (l1Chebyshev.single (ν := ν_val) (↑(k : ℕ) : ℤ) 1) :
      XCheb ν_val L) l) n +
      FCseq (compPolyDerivative f_cpoly data.abar
        (Pi.single m (l1Chebyshev.single (↑(k : ℕ) : ℤ) 1)) l) n =
      ((data.DF_col l m k).getD n 0 : ℝ) := by
  rw [data.rawDerivative_single_eq_cast_of_compPoly, computed_DF_entries]

end Example1421
