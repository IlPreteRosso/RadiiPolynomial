import Mathlib.Analysis.Calculus.MeanValue
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Algebra.Convolution.CauchyProductReal
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Calculus
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Coefficients
import RadiiPolynomial.Analysis.Calculus.Pi

/-!
# MvPolynomial Evaluation in Weighted l1

Bridges between `MvPolynomial (Fin L) ℚ` (symbolic polynomial specification)
and `l1Weighted ν` (Banach algebra with CauchyProduct multiplication).

## Architecture

`MvPolynomial` is noncomputable in Mathlib, so it lives in the PROOF world only.
For `native_decide`, the caller supplies computable ℚ data outside this file (for example
the `Dφ_Q` table of `ivp_hDF_block_nat`, or `CompPoly.evalCoeff`); no computable mirror is
declared here. The MvPolynomial bridge automates:

1. **ℚ↔ℝ bridge**: `toSeq(aeval a p) n = (mvPolyCoeff p coeffs n : ℝ)`
   — reduces to `CauchyProduct.ratCast` + ring hom properties
2. **Differentiability**: `aeval · p` is differentiable (polynomial on Banach algebra)
3. **Fderiv via pderiv**: `fderiv(aeval · p)(a) = Σᵢ leftMul(aeval a (pderiv i p)) ∘ proj i`
4. **DF verification**: Jacobian entries = coefficients of `pderiv m (φ_spec j)` evaluated at `a`
5. **Z₂ bound**: when every `pderiv j (pderiv i p)` is a constant (hypothesis `hD₂`; true for
   degree ≤ 2) → bilinear bound

The caller connects its computable ℚ data to these coefficients by an agreement hypothesis
(for example `hDφ_Q` of `ivp_hDF_block_nat`).

## Key Insight

The value of MvPolynomial is NOT computation — it's PROOF automation.
By stating φ as `MvPolynomial (Fin L) ℚ`, we get:
- `differentiable_evalInBanach`, `fderiv_evalInBanach` (from the generic
  `MvPolynomial.hasFDerivAt_aeval`);
- `pderiv`-based DF verification (consumed by `ivp_hDF_block_nat`);
- the constant-second-pderiv Z₂ bound.
-/

open MvPolynomial (C X aeval pderiv)
open RadiiPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-! ## 1. ℝ Evaluation via aeval into Banach Algebra -/

variable {ν : PosReal}

-- Algebra ℚ instance and ratSmul_eq are in Analysis/SequenceSpace/Geometric/Basic.lean

/-- Evaluate MvPolynomial in the Banach algebra `l1Weighted ν` via `aeval`.
Multiplication = CauchyProduct (from `instNormedCommRing`). -/
def evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) : l1Weighted ν :=
  aeval a p

/-! ## 2. Master Bridge: `toSeq_evalInBanach_of_coeffs`

Connects evaluation in `l1Weighted ν` to rational sequence semantics:

```
toSeq(evalInBanach p a) n = (mvPolyCoeff p coeffs n : ℝ)
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
theorem toSeq_evalInBanach_of_coeffs (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) (coeffs : Fin L → ℕ → ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = (coeffs i n : ℝ)) :
    ∀ n, l1Weighted.toSeq (evalInBanach p a) n = (mvPolyCoeff p coeffs n : ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro n
    simp only [evalInBanach, MvPolynomial.aeval_C]
    rw [toSeq_algebraMap_rat, mvPolyCoeff_C]
    split <;> simp
  | add p q ihp ihq =>
    intro n
    simp only [evalInBanach, map_add] at ihp ihq ⊢
    have hadd : l1Weighted.toSeq ((aeval a p : l1Weighted ν) + aeval a q) n =
        l1Weighted.toSeq (aeval a p) n + l1Weighted.toSeq (aeval a q) n := rfl
    rw [hadd, ihp, ihq]
    simp only [mvPolyCoeff_add, Rat.cast_add]
  | mul_X p i ih =>
    intro n
    simp only [evalInBanach, map_mul, MvPolynomial.aeval_X] at ih ⊢
    rw [l1Weighted.toSeq_mul]
    rw [show l1Weighted.toSeq (aeval a p) = fun k =>
        (mvPolyCoeff p coeffs k : ℝ) from funext ih,
      show l1Weighted.toSeq (a i) = fun k => (coeffs i k : ℝ) from funext (ha i)]
    rw [CauchyProduct.ratCast, mvPolyCoeff_mul, mvPolyCoeff_X_fun]

/-! ## 3. evalInBanach simp API

Pointwise lemmas for `evalInBanach` on compound MvPolynomials.
The `@[simp]` lemmas normalize `evalInBanach (C r) a`, `evalInBanach (p + q) a`, etc. -/

@[simp] lemma evalInBanach_C (r : ℚ) (a : Fin L → l1Weighted ν) :
    evalInBanach (MvPolynomial.C r) a = algebraMap ℚ (l1Weighted ν) r := by
  simp [evalInBanach]

/-- ‖evalInBanach(C r, a)‖ = |r| — norm of a constant polynomial evaluation. -/
@[simp] lemma norm_evalInBanach_C (r : ℚ) (a : Fin L → l1Weighted ν) :
    ‖evalInBanach (MvPolynomial.C r) a‖ = ‖(r : ℝ)‖ := by
  rw [evalInBanach_C]
  show ‖algebraMap ℝ (l1Weighted ν) (r : ℝ)‖ = ‖(r : ℝ)‖
  exact l1Weighted.norm_algebraMap _

@[simp] lemma evalInBanach_X (i : Fin L) (a : Fin L → l1Weighted ν) :
    evalInBanach (MvPolynomial.X i) a = a i := by
  simp [evalInBanach]

@[simp] lemma evalInBanach_add (p q : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) :
    evalInBanach (p + q) a = evalInBanach p a + evalInBanach q a := by
  simp [evalInBanach]

@[simp] lemma evalInBanach_mul (p q : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) :
    evalInBanach (p * q) a = evalInBanach p a * evalInBanach q a := by
  simp [evalInBanach]

@[simp] lemma evalInBanach_neg (p : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) :
    evalInBanach (-p) a = -evalInBanach p a := by
  simp [evalInBanach]

@[simp] lemma evalInBanach_sub (p q : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) :
    evalInBanach (p - q) a = evalInBanach p a - evalInBanach q a := by
  simp [evalInBanach]

/-- `pderiv j (X i)` evaluated in Banach algebra = Kronecker delta. -/
@[simp] lemma evalInBanach_pderiv_X (j i : Fin L) (a : Fin L → l1Weighted ν) :
    evalInBanach (MvPolynomial.pderiv j (MvPolynomial.X i)) a =
      if j = i then 1 else 0 := by
  simp only [evalInBanach, MvPolynomial.pderiv_X, Pi.single_apply,
    apply_ite (aeval a), map_one, map_zero, eq_comm]

/-! ## 4. Differentiability and Fréchet Derivative via pderiv

`evalInBanach p` is differentiable (polynomial on Banach algebra), and its Fréchet derivative
at `a` equals `Σᵢ leftMul(evalInBanach (pderiv i p) a) ∘ proj i`.

This formalizes the book's equation (8.27): `Dφ_j(a)b = Σ_{j'} D_{a_{j'}} φ_j(a) · b_{j'}`. -/

open ContinuousLinearMap (proj)

/-- `evalInBanach p` has Fréchet derivative `MvPolynomial.polynomialDerivative p a` at `a`,
the continuous linear map `h ↦ ∑ i, evalInBanach (pderiv i p) a * h i`. This is
`MvPolynomial.hasFDerivAt_aeval` in the normed commutative algebra `l1Weighted ν`. -/
theorem hasFDerivAt_evalInBanach (p : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) :
    HasFDerivAt (fun x => evalInBanach p x)
      (MvPolynomial.polynomialDerivative (𝕜 := ℝ) p a) a :=
  MvPolynomial.hasFDerivAt_aeval p a

/-- `evalInBanach p` is differentiable at every point (from `hasFDerivAt_evalInBanach`). -/
theorem differentiable_evalInBanach (p : MvPolynomial (Fin L) ℚ) :
    Differentiable ℝ (fun x : Fin L → l1Weighted ν => evalInBanach p x) :=
  fun a => (hasFDerivAt_evalInBanach p a).differentiableAt

/-- Fréchet derivative of `evalInBanach p` at `a`: the pderiv sum formula.

For a polynomial `p : MvPolynomial (Fin L) ℚ` evaluated in the Banach algebra `l1Weighted ν`:
```
fderiv ℝ (fun x => evalInBanach p x) a =
  Σᵢ (leftMul (evalInBanach (pderiv i p) a)).comp (proj i)
```

The induction lives once, at the `MvPolynomial` layer (`MvPolynomial.hasFDerivAt_aeval`). -/
theorem fderiv_evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) :
    fderiv ℝ (fun x => evalInBanach p x) a =
      ∑ i : Fin L, (l1Weighted.leftMul (evalInBanach (MvPolynomial.pderiv i p) a)).comp
        (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i) := by
  rw [(hasFDerivAt_evalInBanach p a).fderiv]
  ext1 h
  simp [evalInBanach]

/-- Fréchet derivative difference of `evalInBanach p` at two points factors through
pderiv evaluation differences:
```
(fderiv(evalInBanach p)(c) - fderiv(evalInBanach p)(a)) h =
  Σᵢ (evalInBanach(pderiv i p)(c) - evalInBanach(pderiv i p)(a)) * h i
```
The statement assumes nothing on the degree. For degree ≤ 2 polynomials, each `pderiv i p`
is degree ≤ 1 (affine), so the difference is bilinear in `(c - a)` and `h`. -/
theorem fderiv_diff_evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (c a : Fin L → l1Weighted ν) (h : Fin L → l1Weighted ν) :
    (fderiv ℝ (fun x => evalInBanach p x) c -
      fderiv ℝ (fun x => evalInBanach p x) a) h =
      ∑ i : Fin L,
        (evalInBanach (MvPolynomial.pderiv i p) c -
          evalInBanach (MvPolynomial.pderiv i p) a) * h i := by
  rw [fderiv_evalInBanach p c, fderiv_evalInBanach p a]
  simp only [sub_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply, ← Finset.sum_sub_distrib]
  congr 1; ext i; rw [← sub_mul]

/-- Coefficient extraction of `fderiv(evalInBanach p)` as Toeplitz sum over pderiv evaluations.
Combines `fderiv_evalInBanach` → CLM extraction → `toSeq` distribution →
`CauchyProduct.eq_sum_fin` into one reusable step (book eq. 8.27, coefficient form). -/
theorem toSeq_fderiv_evalInBanach
    (p : MvPolynomial (Fin L) ℚ) (a h : Fin L → l1Weighted ν)
    {N : ℕ} {n : ℕ} (hn : n ≤ N) :
    l1Weighted.toSeq ((fderiv ℝ (fun x => evalInBanach p x) a) h) n =
      ∑ m : Fin L, ∑ q : Fin (N + 1),
        (if (q : ℕ) ≤ n then
          l1Weighted.toSeq (evalInBanach (MvPolynomial.pderiv (↑m) p) a) (n - (q : ℕ))
        else 0) * l1Weighted.toSeq (h m) (q : ℕ) := by
  rw [fderiv_evalInBanach]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply,
    l1Weighted.toSeq_finset_sum, l1Weighted.toSeq_mul]
  simp_rw [CauchyProduct.eq_sum_fin _ _ hn]

/-! ## 5. System Z₂ Norm Bound for Degree ≤ 2 Polynomials

For a system `φ_spec : Fin L → MvPolynomial (Fin L) ℚ` of degree ≤ 2,
the fderiv difference `(Df(c) - Df(a)) h` at each component j equals
`Σᵢ (evalInBanach(∂ᵢφⱼ)(c) - evalInBanach(∂ᵢφⱼ)(a)) * hᵢ`.

Since each `∂ᵢφⱼ` has degree ≤ 1, the difference `evalInBanach(∂ᵢφⱼ)(c) - evalInBanach(∂ᵢφⱼ)(a)`
is controlled by `‖c - a‖` (it's a linear function of `c - a`).

We accept a bound `C` as a parameter with a verification hypothesis, matching the
existing API style where certificates provide numerical bounds. -/

/-! ## 5b. Generic Z₂ bilinear bound for polynomial systems

For degree ≤ 2 polynomials, the fderiv difference is bilinear: each `pderiv i p`
is degree ≤ 1, so its evaluation is Lipschitz with computable constant.
The chain: MVT → fderiv norm → pderiv norms → constant second pderivs. -/

/-- ‖∑_i f_i * h_i‖ ≤ (∑_i ‖f_i‖) * ‖h‖ for pi-type h; the consumer-compatibility face of
`RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le`. -/
theorem norm_sum_mul_pi_le
    (f h : Fin L → l1Weighted ν) :
    ‖∑ i : Fin L, f i * h i‖ ≤ (∑ i : Fin L, ‖f i‖) * ‖h‖ :=
  NormHelpers.norm_sum_mul_pi_le f h

/-- MVT: ‖eval(q, c) - eval(q, a)‖ ≤ C * ‖c - a‖ when ‖fderiv(eval q)‖ ≤ C everywhere. -/
theorem norm_evalInBanach_sub_le
    (q : MvPolynomial (Fin L) ℚ)
    (c a : Fin L → l1Weighted ν)
    {C : ℝ}
    (hfderiv_bound : ∀ x : Fin L → l1Weighted ν,
      ‖fderiv ℝ (fun y => evalInBanach q y) x‖ ≤ C) :
    ‖evalInBanach q c - evalInBanach q a‖ ≤ C * ‖c - a‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => differentiable_evalInBanach q x)
    (fun x _ => hfderiv_bound x)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)

/-- ‖fderiv(eval q)(a)‖ ≤ ∑_j ‖eval(∂_j q, a)‖. -/
theorem norm_fderiv_evalInBanach_le
    (q : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) :
    ‖fderiv ℝ (fun y => evalInBanach q y) a‖ ≤
      ∑ j : Fin L, ‖evalInBanach (MvPolynomial.pderiv j q) a‖ := by
  rw [fderiv_evalInBanach]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply]
  exact norm_sum_mul_pi_le _ _

/-- Generic Z₂ bilinear bound for polynomial evaluation: if the partial derivatives satisfy
`∑ i, ‖evalInBanach (pderiv i p) c - evalInBanach (pderiv i p) a‖ ≤ C * ‖c - a‖` at the two
points `c` and `a`, then `‖(Df(c) - Df(a)) h‖ ≤ C * ‖c - a‖ * ‖h‖`. The hypothesis is needed
only at `(c, a)`; a global Lipschitz bound gives it as the instance `hLip c a`.
The syntactic Taylor face `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_sub_le` and the semantic
face `norm_fderiv_diff_evalInBanach_of_const_second_pderiv` are its corollaries. -/
theorem norm_fderiv_diff_evalInBanach_bilinear
    (p : MvPolynomial (Fin L) ℚ)
    (c a h : Fin L → l1Weighted ν)
    {C : ℝ}
    (hLip : ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv i p) c -
        evalInBanach (MvPolynomial.pderiv i p) a‖ ≤ C * ‖c - a‖) :
    ‖(fderiv ℝ (fun x => evalInBanach p x) c -
      fderiv ℝ (fun x => evalInBanach p x) a) h‖ ≤
      C * ‖c - a‖ * ‖h‖ := by
  rw [fderiv_diff_evalInBanach]
  exact (norm_sum_mul_pi_le _ _).trans (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))

/-- Combined Z₂ bilinear bound for polynomial evaluation with constant second pderivs.

For degree ≤ 2 polynomials, each `pderiv j (pderiv i p) = C c_{i,j}` is constant.
The caller provides a ℚ coefficient table `D₂` and verifies:
1. `hD₂ : pderiv j (pderiv i p) = C (D₂ i j)` (e.g. by `pderiv_simp`)
2. `∑_{i,j} |D₂ i j| ≤ C` (e.g. by `norm_num`)

The proof does not use the degree: constancy of the second pderivs is the hypothesis `hD₂`
(for total degree ≤ 2 it exists by `MvPolynomial.pderiv_pderiv_eq_C_of_totalDegree_le_two`,
which this proof does not invoke). -/
theorem norm_fderiv_diff_evalInBanach_of_const_second_pderiv
    (p : MvPolynomial (Fin L) ℚ)
    (c a h : Fin L → l1Weighted ν)
    -- ℚ coefficient table for second pderivs
    (D₂ : Fin L → Fin L → ℚ)
    -- Verification: D₂ matches actual second pderiv constant coefficients
    (hD₂ : ∀ (i j : Fin L),
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) = MvPolynomial.C (D₂ i j))
    -- Computable bound
    {C : ℝ}
    (hC_bound : (∑ i : Fin L, ∑ j : Fin L, |(D₂ i j : ℝ)|) ≤ C) :
    ‖(fderiv ℝ (fun x => evalInBanach p x) c -
      fderiv ℝ (fun x => evalInBanach p x) a) h‖ ≤ C * ‖c - a‖ * ‖h‖ := by
  refine norm_fderiv_diff_evalInBanach_bilinear _ c a h ?_
  refine (Finset.sum_le_sum fun i _ => norm_evalInBanach_sub_le _ c a (C := ∑ j, |(D₂ i j : ℝ)|)
    fun z => (norm_fderiv_evalInBanach_le _ z).trans (Finset.sum_le_sum fun j _ => by
      rw [hD₂ i j, norm_evalInBanach_C, Real.norm_eq_abs])).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hC_bound (norm_nonneg _)

/-- For inactive components (all `D₂ l i j = 0`), the fderiv difference is zero. -/
theorem fderiv_diff_zero_of_D₂_zero
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (c a : Fin L → l1Weighted ν)
    (D₂ : Fin L → Fin L → Fin L → ℚ)
    (hD₂ : ∀ (l i j : Fin L),
      MvPolynomial.pderiv j (MvPolynomial.pderiv i (φ_spec l)) = MvPolynomial.C (D₂ l i j))
    (l : Fin L) (hl : ∀ i j, D₂ l i j = 0)
    (h : Fin L → l1Weighted ν) :
    (fderiv ℝ (fun x => evalInBanach (φ_spec l) x) c -
      fderiv ℝ (fun x => evalInBanach (φ_spec l) x) a) h = 0 := by
  have hle := norm_fderiv_diff_evalInBanach_of_const_second_pderiv (φ_spec l) c a h
    (D₂ := D₂ l) (fun i j => hD₂ l i j)
    (show (∑ i : Fin L, ∑ j : Fin L, |(D₂ l i j : ℝ)|) ≤ 0 by
      simp [hl])
  exact norm_le_zero_iff.mp (by linarith)

end MvPolyBridge
