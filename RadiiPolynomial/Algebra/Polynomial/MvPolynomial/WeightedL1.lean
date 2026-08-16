import Mathlib.Analysis.Calculus.MeanValue
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Core
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Coefficients
import RadiiPolynomial.Analysis.Calculus.Pi

/-!
# MvPolynomial Evaluation in Weighted l1

Bridges between `MvPolynomial (Fin L) ℚ` (symbolic polynomial specification)
and `l1Weighted ν` (Banach algebra with CauchyProduct multiplication).

## Architecture

`MvPolynomial` is noncomputable in Mathlib, so it lives in the PROOF world only.
For `native_decide`, the user provides a computable ℚ mirror (`φ_Q : Fin L → ℕ → ℚ`)
as in the existing pipeline. The MvPolynomial bridge automates:

1. **ℚ↔ℝ bridge**: `toSeq(aeval a p) n = (mvPolyCoeffQ p arrs n : ℝ)`
   — reduces to `ratCast_CauchyProduct` + ring hom properties
2. **Differentiability**: `aeval · p` is differentiable (polynomial on Banach algebra)
3. **Fderiv via pderiv**: `fderiv(aeval · p)(a) = Σᵢ leftMul(aeval a (pderiv i p)) ∘ proj i`
4. **DF verification**: Jacobian entries = `mvPolyCoeffQ(pderiv m (φ_spec j))`
5. **Z₂ bound**: for degree ≤ 2, `pderiv i (pderiv j p)` is constant → bilinear bound

The computable ℚ evaluator (`φ_Q`) matches `mvPolyCoeffQ` by a simple
agreement lemma. The user proves this once per equation (~5 lines).

## Key Insight

The value of MvPolynomial is NOT computation — it's PROOF automation.
By stating φ as `MvPolynomial (Fin L) ℚ`, we get:
- `differentiable_aeval` (replaces ~60 lines of manual differentiability proofs)
- `fderiv_aeval` (replaces ~100 lines of fderiv computation)
- `pderiv`-based DF verification (~200 lines collapsed into `ivp_hDF_block_nat`)
- degree-based Z₂ bound (replaces ~60 lines of bilinear bound proofs)
-/

open MvPolynomial (C X aeval pderiv)
open RadiiPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-! ## 1. ℝ Evaluation via aeval into Banach Algebra -/

variable {ν : PosReal}

-- Algebra ℚ instance and ratSmul_eq are in LpOneBanachAlgebra.lean

/-- Evaluate MvPolynomial in the Banach algebra `l1Weighted ν` via `aeval`.
Multiplication = CauchyProduct (from `instNormedCommRing`). -/
def evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) : l1Weighted ν :=
  aeval a p

/-! ## 2. Master Bridge: `toSeq_evalInBanach`

Connects evaluation in `l1Weighted ν` to rational sequence semantics:

```
toSeq(evalInBanach p a) n = (mvPolyCoeff p coeffs n : ℝ)
```

The array theorem is a compatibility wrapper around this sequence-level statement. -/

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

-- toSeq_mul is now public in LpOneBanachAlgebra.lean as l1Weighted.toSeq_mul

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

/-- Array adapter for `toSeq_evalInBanach_of_coeffs`. -/
theorem toSeq_evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) (arrs : Fin L → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ)) :
    ∀ n, l1Weighted.toSeq (evalInBanach p a) n = (mvPolyCoeffQ p arrs n : ℝ) := by
  simpa only [mvPolyCoeffQ] using
    toSeq_evalInBanach_of_coeffs p a (fun i n => (arrs i).getD n 0) ha

/-! ## 3. evalInBanach simp API

Pointwise and function-level lemmas for `evalInBanach` on compound MvPolynomials.
The pointwise `@[simp]` lemmas normalize `evalInBanach (C r) a`, `evalInBanach (p + q) a`, etc.
The `_fun` lemmas rewrite the lambda `fun x => evalInBanach (·) x` to expose the
algebraic structure, enabling `rw` with `fderiv_add`, `HasFDerivAt.mul`, etc. -/

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

/-- Function-level: `fun x => evalInBanach (C r) x` = constant. -/
lemma evalInBanach_C_fun (r : ℚ) :
    (fun x : Fin L → l1Weighted ν => evalInBanach (MvPolynomial.C r) x) =
      fun _ => algebraMap ℚ (l1Weighted ν) r :=
  funext fun x => evalInBanach_C r x

/-- Function-level: `fun x => evalInBanach (p + q) x` = sum of evaluations. -/
lemma evalInBanach_add_fun (p q : MvPolynomial (Fin L) ℚ) :
    (fun x : Fin L → l1Weighted ν => evalInBanach (p + q) x) =
      fun x => evalInBanach p x + evalInBanach q x :=
  funext fun x => evalInBanach_add p q x

/-- Function-level: `fun x => evalInBanach (p * X i) x` = product with coordinate. -/
lemma evalInBanach_mul_X_fun (p : MvPolynomial (Fin L) ℚ) (i : Fin L) :
    (fun x : Fin L → l1Weighted ν => evalInBanach (p * MvPolynomial.X i) x) =
      fun x => evalInBanach p x * x i :=
  funext fun x => by simp [evalInBanach]

/-! ## 4. Differentiability and Fréchet Derivative via pderiv

`evalInBanach p` is differentiable (polynomial on Banach algebra), and its Fréchet derivative
at `a` equals `Σᵢ leftMul(evalInBanach (pderiv i p) a) ∘ proj i`.

This formalizes the book's equation (8.27): `Dφ_j(a)b = Σ_{j'} D_{a_{j'}} φ_j(a) · b_{j'}`. -/

open ContinuousLinearMap (proj)

/-- `evalInBanach p` is differentiable: polynomial expressions on Banach algebras
are smooth (constant, sum, product of differentiable functions). -/
theorem differentiable_evalInBanach (p : MvPolynomial (Fin L) ℚ) :
    Differentiable ℝ (fun x : Fin L → l1Weighted ν => evalInBanach p x) := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [evalInBanach_C_fun]; exact differentiable_const _
  | add p q ihp ihq => rw [evalInBanach_add_fun]; exact ihp.add ihq
  | mul_X p i ih => rw [evalInBanach_mul_X_fun]; exact ih.mul (differentiable_pi_apply i)

/-- Fréchet derivative of `evalInBanach p` at `a`: the pderiv sum formula.

For a polynomial `p : MvPolynomial (Fin L) ℚ` evaluated in the Banach algebra `l1Weighted ν`:
```
fderiv ℝ (fun x => evalInBanach p x) a =
  Σᵢ (leftMul (evalInBanach (pderiv i p) a)).comp (proj i)
```

Proof by `MvPolynomial.induction_on`:
- `C r`: constant → fderiv = 0, all pderivs = 0
- `p + q`: linearity of fderiv and pderiv
- `p * X i`: product rule + IH + `pderiv_mul` + commutativity of `l1Weighted` -/
theorem fderiv_evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) :
    fderiv ℝ (fun x => evalInBanach p x) a =
      ∑ i : Fin L, (l1Weighted.leftMul (evalInBanach (MvPolynomial.pderiv i p) a)).comp
        (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [evalInBanach_C_fun, (hasFDerivAt_const (algebraMap ℚ (l1Weighted ν) r) a).fderiv]
    symm; apply Finset.sum_eq_zero; intro i _
    simp only [MvPolynomial.pderiv_C, evalInBanach, map_zero]
    ext h; simp
  | add p q ihp ihq =>
    have hfd : fderiv ℝ (fun x => evalInBanach p x + evalInBanach q x) a =
        fderiv ℝ (fun x => evalInBanach p x) a +
          fderiv ℝ (fun x => evalInBanach q x) a :=
      ((differentiable_evalInBanach p a).hasFDerivAt.add
        (differentiable_evalInBanach q a).hasFDerivAt).fderiv
    rw [evalInBanach_add_fun, hfd, ihp, ihq, ← Finset.sum_add_distrib]
    congr 1; funext i
    simp only [← ContinuousLinearMap.add_comp]
    congr 1; ext1 h; simp
  | mul_X p i ih =>
    rw [evalInBanach_mul_X_fun]
    -- Product rule via HasFDerivAt
    have hfi : HasFDerivAt (fun x : Fin L → l1Weighted ν => x i)
        (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i) a :=
      (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i).hasFDerivAt
    have hfd : fderiv ℝ (fun x => evalInBanach p x * x i) a =
        evalInBanach p a • (proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) i) +
          (a i) • fderiv ℝ (fun x => evalInBanach p x) a :=
      ((differentiable_evalInBanach p a).hasFDerivAt.mul hfi).fderiv
    rw [hfd, ih]
    -- Apply to h and work at l1Weighted level
    ext1 h
    simp only [add_apply, sum_apply,
      ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply,
      smul_eq_mul, Finset.smul_sum]
    -- Expand pderiv on RHS using pderiv_mul + evalInBanach API
    conv_rhs => arg 2; ext j; rw [MvPolynomial.pderiv_mul]
    simp only [evalInBanach_add, evalInBanach_mul, evalInBanach_X, evalInBanach_pderiv_X]
    -- Split RHS sum and collapse the Kronecker delta part
    conv_rhs => arg 2; ext j; rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hcollapse : ∑ j : Fin L,
        (evalInBanach p a * if j = i then (1 : l1Weighted ν) else 0) * h j =
        evalInBanach p a * h i := by
      rw [show (∑ j : Fin L, (evalInBanach p a * if j = i then (1 : l1Weighted ν) else 0) * h j) =
        ∑ j : Fin L, if j = i then evalInBanach p a * h i else 0 from
        Finset.sum_congr rfl fun j _ => by split_ifs with hji <;> simp [hji]]
      simp
    rw [hcollapse, add_comm]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring

/-- Fréchet derivative difference of `evalInBanach p` at two points factors through
pderiv evaluation differences:
```
(fderiv(evalInBanach p)(c) - fderiv(evalInBanach p)(a)) h =
  Σᵢ (evalInBanach(pderiv i p)(c) - evalInBanach(pderiv i p)(a)) * h i
```
For degree ≤ 2 polynomials, each `pderiv i p` is degree ≤ 1 (affine),
so the difference is bilinear in `(c - a)` and `h`. -/
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

We accept a bound `C_Z₂` as a parameter with a verification hypothesis, matching the
existing API style where certificates provide numerical bounds. -/

/-! ## 5b. Generic Z₂ bilinear bound for polynomial systems

For degree ≤ 2 polynomials, the fderiv difference is bilinear: each `pderiv i p`
is degree ≤ 1, so its evaluation is Lipschitz with computable constant.
The chain: MVT → fderiv norm → pderiv norms → constant second pderivs. -/

/-- ‖∑_i f_i * h_i‖ ≤ (∑_i ‖f_i‖) * ‖h‖ for pi-type h.
Combines triangle inequality, submultiplicativity, and ‖h_i‖ ≤ ‖h‖. -/
theorem norm_sum_mul_pi_le
    (f h : Fin L → l1Weighted ν) :
    ‖∑ i : Fin L, f i * h i‖ ≤ (∑ i : Fin L, ‖f i‖) * ‖h‖ := by
  refine ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => norm_mul_le _ _)).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _)

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

/-- Generic Z₂ bilinear bound for polynomial evaluation from total pderiv Lipschitz. -/
theorem norm_fderiv_diff_evalInBanach_bilinear
    (p : MvPolynomial (Fin L) ℚ)
    (c a h : Fin L → l1Weighted ν)
    {C : ℝ}
    (hLip : ∀ x y : Fin L → l1Weighted ν,
      ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv i p) x -
        evalInBanach (MvPolynomial.pderiv i p) y‖ ≤ C * ‖x - y‖) :
    ‖(fderiv ℝ (fun x => evalInBanach p x) c -
      fderiv ℝ (fun x => evalInBanach p x) a) h‖ ≤
      C * ‖c - a‖ * ‖h‖ := by
  rw [fderiv_diff_evalInBanach]
  exact (norm_sum_mul_pi_le _ _).trans
    (mul_le_mul_of_nonneg_right (hLip c a) (norm_nonneg _))

/-- Combined Z₂ bilinear bound for polynomial evaluation with constant second pderivs.

For degree ≤ 2 polynomials, each `pderiv j (pderiv i p) = C c_{i,j}` is constant.
The caller provides a ℚ coefficient table `D₂` and verifies:
1. `D₂ i j = coeff 0 (pderiv j (pderiv i p))` (by `native_decide`)
2. `∑_{i,j} |D₂ i j| ≤ C` (by `native_decide` or `norm_num`)

The internal proof uses `pderiv_pderiv_eq_C_of_totalDegree_le_two` structure. -/
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
  apply norm_fderiv_diff_evalInBanach_bilinear _ _ _ _ (fun x y => ?_)
  calc ∑ i : Fin L, ‖evalInBanach (MvPolynomial.pderiv i p) x -
          evalInBanach (MvPolynomial.pderiv i p) y‖
      ≤ ∑ i : Fin L, (∑ j : Fin L, |(D₂ i j : ℝ)|) * ‖x - y‖ :=
        Finset.sum_le_sum fun i _ => norm_evalInBanach_sub_le _ _ _
          (fun z => (norm_fderiv_evalInBanach_le _ z).trans
            (Finset.sum_le_sum fun j _ => by
              rw [hD₂ i j, norm_evalInBanach_C, Real.norm_eq_abs]))
    _ = (∑ i : Fin L, ∑ j : Fin L, |(D₂ i j : ℝ)|) * ‖x - y‖ := by
        rw [← Finset.sum_mul]
    _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_right hC_bound (norm_nonneg _)

/-- System-level Z₂ bilinear bound for polynomial systems with constant second pderivs.

Given `D₂ l i j = coeff of ∂ⱼ∂ᵢ(φ_spec l)` for the whole system, derives:
- Per-component bilinear bound `‖(Df_l c - Df_l ā) h‖ ≤ C * ‖c-ā‖ * ‖h‖`
- `hzero`: inactive components (where all `D₂ l i j = 0`) have zero fderiv difference

The caller provides:
- `D₂` and `hD₂` (verified by `pderiv_simp`)
- `C` and `hC` (the maximum row sum, verified by `norm_num`) -/
theorem norm_fderiv_diff_system_of_const_second_pderiv
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (c a : Fin L → l1Weighted ν)
    -- System-level second pderiv coefficient table
    (D₂ : Fin L → Fin L → Fin L → ℚ)
    (hD₂ : ∀ (l i j : Fin L),
      MvPolynomial.pderiv j (MvPolynomial.pderiv i (φ_spec l)) = MvPolynomial.C (D₂ l i j))
    -- Per-component bilinear bound
    {C : ℝ}
    (hC : ∀ l : Fin L, (∑ i : Fin L, ∑ j : Fin L, |(D₂ l i j : ℝ)|) ≤ C)
    -- Per-component bound
    (h : Fin L → l1Weighted ν) (l : Fin L) :
    ‖(fderiv ℝ (fun x => evalInBanach (φ_spec l) x) c -
      fderiv ℝ (fun x => evalInBanach (φ_spec l) x) a) h‖ ≤ C * ‖c - a‖ * ‖h‖ :=
  norm_fderiv_diff_evalInBanach_of_const_second_pderiv _ _ _ _
    (D₂ := D₂ l) (fun i j => hD₂ l i j) ((hC l).trans (le_refl _))

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
