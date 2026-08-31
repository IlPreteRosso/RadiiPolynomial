import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Algebra

/-!
# Example 14.2.1 — instantiating the library Λ-decomposition

The generic decomposition `G a = constG + TA a + TC (φ a)` — its rows, CLMs,
norm constants, and `fderiv_G` — lives in the library
(`Applications/IVP/Chebyshev/Lambda.lean`, promoted from this example
2026-08-25). This file keeps only the equation-specific residue:

- `DPhiCLM` — the derivative of the logistic nonlinearity
  `φ(a)ₗ = S(aₗ)² − S(aₗ)` as a CLM, `DΦ(a)h = (2·S(aₗ)·— − id) ∘ S ∘ projₗ`;
- `hasFDerivAt_Phi` — assembled from the componentwise `hasFDerivAt_phi`;
- the instantiations `G_diff` / `fderiv_G` consumed by `Certificate.lean`.
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap RadiiPolynomial ChebyshevIVP

noncomputable section

namespace Example1421

/-- The derivative of `Φ` at `a` as a CLM. -/
def DPhiCLM (a : XCheb ν_val L) : XCheb ν_val L →L[ℝ] XCheb ν_val L :=
  ContinuousLinearMap.pi fun l =>
    ((2 : ℝ) • l1Chebyshev.leftMul (S (a l)) - ContinuousLinearMap.id ℝ _).comp (SP l)

lemma DPhiCLM_apply (a h : XCheb ν_val L) : DPhiCLM a h = fun l => Dphi a h l := by
  funext l
  show ((2 : ℝ) • l1Chebyshev.leftMul (S (a l))
      - ContinuousLinearMap.id ℝ (l1Chebyshev ν_val)) (S (h l)) = Dphi a h l
  rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply]
  show (2 : ℝ) • (l1Chebyshev.leftMul (S (a l)) (S (h l))) - S (h l) = _
  rw [leftMul_apply']
  rfl

lemma hasFDerivAt_Phi (a : XCheb ν_val L) :
    HasFDerivAt (fun x : XCheb ν_val L => (fun l => phi x l)) (DPhiCLM a) a := by
  rw [hasFDerivAt_pi']
  intro l
  rw [show (ContinuousLinearMap.proj l).comp (DPhiCLM a)
      = ((2 : ℝ) • l1Chebyshev.leftMul (S (a l))
        - ContinuousLinearMap.id ℝ _).comp (SP l) from ContinuousLinearMap.proj_pi _ _]
  exact hasFDerivAt_phi a l

/-- Differentiability obligation of `StdChebIVPData.existsUnique`. -/
lemma G_diff : Differentiable ℝ (data.G phi p₀) :=
  data.differentiable_G phi p₀ DPhiCLM hasFDerivAt_Phi

/-- **The derivative of G**: `DG(a) = TA + TC ∘ DΦ(a)`. -/
lemma fderiv_G (a : XCheb ν_val L) :
    fderiv ℝ (data.G phi p₀) a = data.TA + data.TC.comp (DPhiCLM a) :=
  data.fderiv_G phi p₀ DPhiCLM hasFDerivAt_Phi a

end Example1421
