import Mathlib.Analysis.Calculus.MeanValue
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Calculus
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Coefficients
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# MvPolynomial Evaluation in Weighted l1

Bridges between `MvPolynomial (Fin L) ℚ` (symbolic polynomial specification)
and `l1Weighted ν` (Banach algebra with `cauchyProduct` multiplication).

## Architecture

`MvPolynomial` is noncomputable in Mathlib, so it lives in the PROOF world only.
For `native_decide`, the caller supplies computable ℚ data outside this file (for example
the `Dφ_Q` table of `ivp_hDF_block_nat`, or `CompPoly.evalCoeff`); no computable mirror is
declared here. The MvPolynomial bridge automates:

1. **ℚ↔ℝ bridge**: `toSeq(aeval a p) n = (mvPolyCoeff p coeffs n : ℝ)`
   — reduces to `cauchyProduct.map_cauchyProduct (Rat.castHom ℝ)` + ring hom properties
2. **Derivative**: `aeval · p` has the derivative of the generic `MvPolynomial.hasFDerivAt_aeval`
3. **Fderiv via pderiv**: `fderiv(aeval · p)(a) = Σᵢ leftMul(aeval a (pderiv i p)) ∘ proj i`
4. **DF verification**: Jacobian entries = coefficients of `pderiv m (φ_spec j)` evaluated at `a`
5. **Z₂ bound**: derivative-difference bounds from explicit pointwise Lipschitz sums.

The caller connects its computable ℚ data to these coefficients by an agreement hypothesis
(for example `hDφ_Q` of `ivp_hDF_block_nat`).

## Key Insight

The value of MvPolynomial is NOT computation — it's PROOF automation.
By stating φ as `MvPolynomial (Fin L) ℚ`, we get:
- `fderiv_aeval` and differentiability from the generic
  `MvPolynomial.hasFDerivAt_aeval`;
- `pderiv`-based DF verification (consumed by `ivp_hDF_block_nat`);
- derivative-difference norm bounds from explicit pointwise Lipschitz data.
-/

open MvPolynomial (C X aeval pderiv)
open RadiiPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-! ## Rational evaluation in the weighted algebra -/

variable {ν : PosReal}

-- The `Algebra ℚ` instance `instAlgebraRat` is in Analysis/SequenceSpace/Geometric/Basic.lean

/-! ## Coefficient bridge: `toSeq_aeval_eq_mvPolyCoeff`

Connects evaluation in `l1Weighted ν` to rational sequence semantics:

```
toSeq(aeval a p) n = (mvPolyCoeff p coeffs n : ℝ)
```

-/

/-- `toSeq` of `algebraMap ℚ (l1Weighted ν) r` at mode n:
mode 0 = (r : ℝ), mode n+1 = 0. -/
private lemma toSeq_algebraMap_rat (r : ℚ) (n : ℕ) :
    l1Weighted.toSeq (algebraMap ℚ (l1Weighted ν) r) n =
      if n = 0 then (r : ℝ) else 0 := by
  -- algebraMap ℚ _ r = algebraMap ℝ _ ((r : ℚ) : ℝ) = ((r : ℚ) : ℝ) • 1
  change l1Weighted.toSeq ((algebraMap ℝ (l1Weighted ν) ((r : ℚ) : ℝ))) n = _
  rw [l1Weighted.algebraMap_apply, l1Weighted.smul_toSeq, l1Weighted.one_toSeq_eq]
  cases n with
  | zero => simp
  | succ n => simp

-- toSeq_mul is public in Analysis/SequenceSpace/Geometric/Basic.lean as l1Weighted.toSeq_mul

/-- Coefficient extraction commutes with `MvPolynomial` evaluation. -/
theorem toSeq_aeval_eq_mvPolyCoeff (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) (coeffs : Fin L → ℕ → ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = (coeffs i n : ℝ)) :
    ∀ n, l1Weighted.toSeq (MvPolynomial.aeval a p) n = (mvPolyCoeff p coeffs n : ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro n
    simp only [MvPolynomial.aeval_C]
    rw [toSeq_algebraMap_rat, mvPolyCoeff_C]
    split <;> simp
  | add p q ihp ihq =>
    intro n
    simp only [map_add] at ihp ihq ⊢
    have hadd : l1Weighted.toSeq ((aeval a p : l1Weighted ν) + aeval a q) n =
        l1Weighted.toSeq (aeval a p) n + l1Weighted.toSeq (aeval a q) n := rfl
    rw [hadd, ihp, ihq]
    simp only [mvPolyCoeff_add, Rat.cast_add]
  | mul_X p i ih =>
    intro n
    simp only [map_mul, MvPolynomial.aeval_X] at ih ⊢
    rw [l1Weighted.toSeq_mul]
    rw [show l1Weighted.toSeq (aeval a p) = fun k =>
        (mvPolyCoeff p coeffs k : ℝ) from funext ih,
      show l1Weighted.toSeq (a i) = fun k => (coeffs i k : ℝ) from funext (ha i)]
    trans ((cauchyProduct (mvPolyCoeff p coeffs) (coeffs i) n : ℚ) : ℝ)
    · exact cauchyProduct.map_cauchyProduct (Rat.castHom ℝ) _ _ _
    · rw [mvPolyCoeff_mul, mvPolyCoeff_X_fun]

/-! ## Fréchet derivative via pderiv

The Fréchet derivative of `fun a => aeval a p` (a polynomial on a Banach algebra) at `a` equals
`Σᵢ leftMul(aeval a (pderiv i p)) ∘ proj i`.

This formalizes the book's equation (8.27): `Dφ_j(a)b = Σ_{j'} D_{a_{j'}} φ_j(a) · b_{j'}`. -/

open ContinuousLinearMap (proj)

/-- Fréchet derivative of `fun a => aeval a p` at `a`: the pderiv sum formula.

For a polynomial `p : MvPolynomial (Fin L) ℚ` evaluated in the Banach algebra `l1Weighted ν`:
```
fderiv ℝ (fun x => aeval x p) a =
  Σᵢ (leftMul (aeval a (pderiv i p))).comp (proj i)
```

The induction lives once, at the `MvPolynomial` layer (`MvPolynomial.hasFDerivAt_aeval`). -/
theorem fderiv_aeval (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) :
    fderiv ℝ (fun x => MvPolynomial.aeval x p) a =
      ∑ i : Fin L, (l1Weighted.leftMul (MvPolynomial.aeval a (MvPolynomial.pderiv i p))).comp
        (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i) := by
  rw [(MvPolynomial.hasFDerivAt_aeval (𝕜 := ℝ) p a).fderiv]
  ext1 h
  simp

/-- Fréchet derivative difference of `fun a => aeval a p` at two points factors through
pderiv evaluation differences:
```
(fderiv (fun x => aeval x p) c - fderiv (fun x => aeval x p) a) h =
  Σᵢ (aeval c (pderiv i p) - aeval a (pderiv i p)) * h i
```
The statement assumes nothing on the degree. For degree ≤ 2 polynomials, each `pderiv i p`
is degree ≤ 1 (affine), so the difference is bilinear in `(c - a)` and `h`. -/
theorem fderiv_diff_aeval (p : MvPolynomial (Fin L) ℚ)
    (c a : Fin L → l1Weighted ν) (h : Fin L → l1Weighted ν) :
    (fderiv ℝ (fun x => MvPolynomial.aeval x p) c -
      fderiv ℝ (fun x => MvPolynomial.aeval x p) a) h =
      ∑ i : Fin L,
        (MvPolynomial.aeval c (MvPolynomial.pderiv i p) -
          MvPolynomial.aeval a (MvPolynomial.pderiv i p)) * h i := by
  rw [fderiv_aeval p c, fderiv_aeval p a]
  simp only [sub_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply, ← Finset.sum_sub_distrib]
  congr 1; ext i; rw [← sub_mul]

/-- Coefficient extraction of `fderiv (fun x => aeval x p)` as Toeplitz sum over pderiv evaluations.
Combines `fderiv_aeval` → CLM extraction → `toSeq` distribution →
`cauchyProduct.eq_sum_fin` into one reusable step (book eq. 8.27, coefficient form). -/
theorem toSeq_fderiv_aeval
    (p : MvPolynomial (Fin L) ℚ) (a h : Fin L → l1Weighted ν)
    {N : ℕ} {n : ℕ} (hn : n ≤ N) :
    l1Weighted.toSeq ((fderiv ℝ (fun x => MvPolynomial.aeval x p) a) h) n =
      ∑ m : Fin L, ∑ q : Fin (N + 1),
        (if (q : ℕ) ≤ n then
          l1Weighted.toSeq (MvPolynomial.aeval a (MvPolynomial.pderiv (↑m) p)) (n - (q : ℕ))
        else 0) * l1Weighted.toSeq (h m) (q : ℕ) := by
  rw [fderiv_aeval]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply,
    l1Weighted.toSeq_finset_sum, l1Weighted.toSeq_mul]
  simp_rw [cauchyProduct.eq_sum_fin _ _ hn]

/-! ## Derivative norm and pointwise difference bounds -/



/-- Generic Z₂ bilinear bound for polynomial evaluation: if the partial derivatives satisfy
`∑ i, ‖aeval c (pderiv i p) - aeval a (pderiv i p)‖ ≤ C * ‖c - a‖` at the two
points `c` and `a`, then `‖(Df(c) - Df(a)) h‖ ≤ C * ‖c - a‖ * ‖h‖`. The hypothesis is needed
only at `(c, a)`; a global Lipschitz bound gives it as the instance `hLip c a`.
The syntactic Taylor face `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_sub_le` is a corollary. -/
theorem norm_fderiv_diff_aeval_bilinear
    (p : MvPolynomial (Fin L) ℚ)
    (c a h : Fin L → l1Weighted ν)
    {C : ℝ}
    (hLip : ∑ i : Fin L, ‖MvPolynomial.aeval c (MvPolynomial.pderiv i p) -
        MvPolynomial.aeval a (MvPolynomial.pderiv i p)‖ ≤ C * ‖c - a‖) :
    ‖(fderiv ℝ (fun x => MvPolynomial.aeval x p) c -
      fderiv ℝ (fun x => MvPolynomial.aeval x p) a) h‖ ≤
      C * ‖c - a‖ * ‖h‖ := by
  rw [fderiv_diff_aeval]
  exact (RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le _ _).trans (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))


end MvPolyBridge
