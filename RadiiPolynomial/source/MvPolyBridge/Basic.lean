import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RadiiPolynomial.source.lpSpace.CauchyProduct
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv

/-!
# MvPolynomial Bridge: Symbolic Specification ↔ Banach Algebra Evaluation

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
- `pderiv`-based DF verification (replaces ~200 lines of `fderiv_F_coeffs_eq`)
- degree-based Z₂ bound (replaces ~60 lines of bilinear bound proofs)
-/

open MvPolynomial (C X aeval pderiv)
open RadiiPolynomial

/-! ## 0. Degree-drop lemma for pderiv

The (N+1)th iterated partial derivative of a degree ≤ N polynomial is zero. -/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Each partial derivative drops the total degree by at least 1.
    Proof: decompose p into monomials; `pderiv_monomial` shifts exponents down;
    bound the sum via `totalDegree_finset_sum` + `totalDegree_monomial_le`. -/
theorem totalDegree_pderiv_le [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h : coeff s p * ↑(s i) = 0
  · simp [h]
  · refine (totalDegree_monomial _ h).le.trans ?_
    have hi : 1 ≤ s i := by
      rcases Nat.eq_zero_or_pos (s i) with h' | h'
      · exfalso; simp [h'] at h
      · exact h'
    have hle : Finsupp.single i 1 ≤ s :=
      fun j => by
        simp only [Finsupp.single_apply]
        split_ifs with hij
        · subst hij; exact hi
        · exact Nat.zero_le _
    -- (s - single i 1).sum id + 1 = s.sum id, and s.sum id ≤ totalDegree p
    have hsum : (s - Finsupp.single i 1).sum (fun _ => id) + 1 =
        s.sum (fun _ => id) := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp [Finsupp.sum_single_index]
    -- Split: (s - single).sum id ≤ s.sum id - 1 ≤ totalDegree p - 1
    have h1 : (s - Finsupp.single i 1).sum (fun _ => id) ≤
        s.sum (fun _ => id) - 1 := by omega
    show (s - Finsupp.single i 1).sum (fun _ => id) ≤ p.totalDegree - 1
    exact h1.trans (Nat.sub_le_sub_right (le_totalDegree hs) 1)

/-- Specialization: second pderiv of degree ≤ 2 polynomial has totalDegree = 0. -/
theorem totalDegree_pderiv_pderiv_eq_zero [DecidableEq σ] (i j : σ) (p : MvPolynomial σ R)
    (hp : p.totalDegree ≤ 2) :
    (pderiv i (pderiv j p)).totalDegree = 0 := by
  have h1 := totalDegree_pderiv_le j p
  have h2 := totalDegree_pderiv_le i (pderiv j p)
  omega

/-- Second pderiv of degree ≤ 2 polynomial is a constant. -/
theorem pderiv_pderiv_eq_C_of_totalDegree_le_two [DecidableEq σ] (i j : σ)
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 2) :
    ∃ c : R, pderiv i (pderiv j p) = C c := by
  have h := totalDegree_pderiv_pderiv_eq_zero i j p hp
  exact ⟨coeff 0 (pderiv i (pderiv j p)),
    (totalDegree_eq_zero_iff_eq_C).mp h⟩

/-- Simp-friendly ≤ version of `totalDegree_C`. -/
lemma totalDegree_C_le (a : R) : (C a : MvPolynomial σ R).totalDegree ≤ 0 :=
  le_of_eq (totalDegree_C a)

/-- Simp-friendly ≤ version of `totalDegree_X`. -/
lemma totalDegree_X_le [Nontrivial R] (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 :=
  le_of_eq (totalDegree_X i)

/-- `totalDegree` of sum bounded by sum of degrees (avoids `max` for `linarith`). -/
lemma totalDegree_add_le (p q : MvPolynomial σ R) :
    (p + q).totalDegree ≤ p.totalDegree + q.totalDegree :=
  (totalDegree_add _ _).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

lemma totalDegree_sub_le {R : Type*} [CommRing R] (p q : MvPolynomial σ R) :
    (p - q).totalDegree ≤ p.totalDegree + q.totalDegree :=
  (totalDegree_sub _ _).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

lemma totalDegree_neg_le {R : Type*} [CommRing R] (p : MvPolynomial σ R) :
    (-p).totalDegree ≤ p.totalDegree :=
  le_of_eq (totalDegree_neg _)

end MvPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-! ## 1. Noncomputable ℚ Evaluation via PowerSeries

Used in bridge proofs only (not `native_decide`). -/

/-- Convert ℚ array to PowerSeries ℚ (formal power series with CauchyProduct mul). -/
def arrayToPowerSeries (arr : Array ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => arr.getD n 0

/-- Evaluate MvPolynomial in PowerSeries ℚ. -/
def mvPolyToPowerSeries (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → PowerSeries ℚ) : PowerSeries ℚ :=
  MvPolynomial.eval₂ PowerSeries.C seqs p

/-- The n-th ℚ coefficient of the polynomial evaluation.
Noncomputable; used in bridge proofs connecting the user's computable `φ_Q`
to the ℝ evaluation `aeval`. -/
def mvPolyCoeffQ (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) : ℚ :=
  (PowerSeries.coeff (R := ℚ) n) (mvPolyToPowerSeries p (fun i => arrayToPowerSeries (arrs i)))

/-! ## 2. ℝ Evaluation via aeval into Banach Algebra -/

variable {ν : PosReal}

-- Algebra ℚ instance and ratSmul_eq are in LpOneBanachAlgebra.lean

/-- Evaluate MvPolynomial in the Banach algebra `l1Weighted ν` via `aeval`.
Multiplication = CauchyProduct (from `instNormedCommRing`). -/
def evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) : l1Weighted ν :=
  aeval a p

/-! ## 3. Master Bridge: `toSeq_evalInBanach`

Connects the ℝ evaluation in `l1Weighted ν` to the ℚ evaluation in `PowerSeries ℚ`:

```
toSeq(evalInBanach p a) n = (mvPolyCoeffQ p arrs n : ℝ)
```

Proof by `MvPolynomial.induction_on`:
- `hC r`: algebraMap chain ℚ → ℝ → l1Weighted matches PowerSeries.C
- `hAdd`: map_add on both sides + IH
- `hMul_X p i`: mul = CauchyProduct ↔ PowerSeries.coeff_mul + CauchyProduct.ratCast + IH -/

/-- `toSeq` of `algebraMap ℚ (l1Weighted ν) r` at mode n:
mode 0 = (r : ℝ), mode n+1 = 0. -/
private lemma toSeq_algebraMap_rat (r : ℚ) (n : ℕ) :
    l1Weighted.toSeq (algebraMap ℚ (l1Weighted ν) r) n =
      if n = 0 then (r : ℝ) else 0 := by
  -- algebraMap ℚ _ r = algebraMap ℝ _ ((r : ℚ) : ℝ) = ((r : ℚ) : ℝ) • 1
  change lpWeighted.toSeq ((algebraMap ℝ (l1Weighted ν) ((r : ℚ) : ℝ))) n = _
  rw [l1Weighted.algebraMap_apply, lpWeighted.smul_toSeq,
    show (1 : l1Weighted ν) = l1Weighted.one ν from rfl, l1Weighted.one_toSeq]
  cases n with
  | zero => simp [CauchyProduct.one]
  | succ n => simp [CauchyProduct.one]

/-- `PowerSeries.coeff n (PowerSeries.C r)` = Kronecker delta at 0. -/
private lemma coeff_C_eq (r : ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.C (R := ℚ) r) =
      if n = 0 then r else 0 := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_C]
  | succ n => simp [PowerSeries.coeff_succ_C]

-- toSeq_mul is now public in LpOneBanachAlgebra.lean as l1Weighted.toSeq_mul

/-- Master bridge: coefficient extraction commutes with MvPolynomial evaluation.

For any polynomial `p : MvPolynomial (Fin L) ℚ` and sequences `a` with
`toSeq(a i) n = (arrs i).getD n 0`, the n-th coefficient of `evalInBanach p a`
equals the ℚ → ℝ cast of the corresponding PowerSeries coefficient. -/
theorem toSeq_evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) (arrs : Fin L → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ)) :
    ∀ n, l1Weighted.toSeq (evalInBanach p a) n = (mvPolyCoeffQ p arrs n : ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro n
    simp only [evalInBanach, MvPolynomial.aeval_C]
    simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_C]
    rw [toSeq_algebraMap_rat, coeff_C_eq]
    split <;> simp
  | add p q ihp ihq =>
    intro n
    simp only [evalInBanach, map_add] at ihp ihq ⊢
    have hadd : l1Weighted.toSeq ((aeval a p : l1Weighted ν) + aeval a q) n =
        l1Weighted.toSeq (aeval a p) n + l1Weighted.toSeq (aeval a q) n := rfl
    rw [hadd, ihp, ihq]
    simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_add, map_add,
      Rat.cast_add]
  | mul_X p i ih =>
    intro n
    simp only [evalInBanach, map_mul, MvPolynomial.aeval_X] at ih ⊢
    rw [l1Weighted.toSeq_mul]
    -- Use IH to rewrite toSeq(aeval a p) and toSeq(a i) pointwise
    rw [show l1Weighted.toSeq (aeval a p) = fun k =>
        (mvPolyCoeffQ p arrs k : ℝ) from funext ih,
      show l1Weighted.toSeq (a i) = fun k => ((arrs i).getD k 0 : ℝ) from
        funext (ha i)]
    -- CauchyProduct of ℝ-cast ℚ seqs = ℝ-cast of CauchyProduct of ℚ seqs
    rw [CauchyProduct.ratCast]; congr 1
    -- Both sides unfold to the same antidiagonal sum
    simp only [mvPolyCoeffQ, mvPolyToPowerSeries, arrayToPowerSeries,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      CauchyProduct.apply, PowerSeries.coeff_mul, PowerSeries.coeff_mk]

/-! ## 3b. mvPolyCoeffQ simp API

Simp lemmas that reduce `mvPolyCoeffQ` of compound MvPolynomials to arithmetic
on the coefficient arrays. Used in bridge lemmas (φ_lorenz_bridge, Dφ_jacobian bridge). -/

@[simp] lemma mvPolyCoeffQ_C (r : ℚ) (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.C r) arrs n = if n = 0 then r else 0 := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_C, coeff_C_eq]

@[simp] lemma mvPolyCoeffQ_zero (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ 0 arrs n = 0 := by
  rw [show (0 : MvPolynomial (Fin L) ℚ) = MvPolynomial.C 0 from by simp, mvPolyCoeffQ_C]; simp

@[simp] lemma mvPolyCoeffQ_X (i : Fin L) (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.X i) arrs n = (arrs i).getD n 0 := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, arrayToPowerSeries,
    MvPolynomial.eval₂_X, PowerSeries.coeff_mk]

@[simp] lemma mvPolyCoeffQ_add (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p + q) arrs n = mvPolyCoeffQ p arrs n + mvPolyCoeffQ q arrs n := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_add, map_add]

@[simp] lemma mvPolyCoeffQ_neg (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (-p) arrs n = -mvPolyCoeffQ p arrs n := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_neg, map_neg]

@[simp] lemma mvPolyCoeffQ_sub (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p - q) arrs n = mvPolyCoeffQ p arrs n - mvPolyCoeffQ q arrs n := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_sub, map_sub]

@[simp] lemma mvPolyCoeffQ_mul (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p * q) arrs n =
      CauchyProduct (mvPolyCoeffQ p arrs) (mvPolyCoeffQ q arrs) n := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_mul,
    CauchyProduct.apply, PowerSeries.coeff_mul]

@[simp] lemma mvPolyCoeffQ_one (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ 1 arrs n = if n = 0 then 1 else 0 := by
  rw [show (1 : MvPolynomial (Fin L) ℚ) = MvPolynomial.C 1 from by simp, mvPolyCoeffQ_C]

-- Function-level versions: enable simp under binders (e.g. inside CauchyProduct args)
@[simp] lemma mvPolyCoeffQ_X_fun (i : Fin L) (arrs : Fin L → Array ℚ) :
    mvPolyCoeffQ (MvPolynomial.X i) arrs = fun n => (arrs i).getD n 0 :=
  funext (mvPolyCoeffQ_X i arrs)

@[simp] lemma mvPolyCoeffQ_C_fun (r : ℚ) (arrs : Fin L → Array ℚ) :
    mvPolyCoeffQ (MvPolynomial.C r) arrs = fun n => if n = 0 then r else 0 :=
  funext (mvPolyCoeffQ_C r arrs)

@[simp] lemma mvPolyCoeffQ_C_mul (r : ℚ) (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.C r * p) arrs n = r * mvPolyCoeffQ p arrs n := by
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  rw [show PowerSeries.C (R := ℚ) r = algebraMap ℚ _ r from rfl,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

/-! ## 4. evalInBanach simp API

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

/-! ## 5. Differentiability and Fréchet Derivative via pderiv

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
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
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
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
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
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, l1Weighted.leftMul_apply,
    l1Weighted.toSeq_finset_sum, l1Weighted.toSeq_mul]
  simp_rw [CauchyProduct.eq_sum_fin _ _ hn]

/-! ## 6. System Z₂ Norm Bound for Degree ≤ 2 Polynomials

For a system `φ_spec : Fin L → MvPolynomial (Fin L) ℚ` of degree ≤ 2,
the fderiv difference `(Df(c) - Df(a)) h` at each component j equals
`Σᵢ (evalInBanach(∂ᵢφⱼ)(c) - evalInBanach(∂ᵢφⱼ)(a)) * hᵢ`.

Since each `∂ᵢφⱼ` has degree ≤ 1, the difference `evalInBanach(∂ᵢφⱼ)(c) - evalInBanach(∂ᵢφⱼ)(a)`
is controlled by `‖c - a‖` (it's a linear function of `c - a`).

We accept a bound `C_Z₂` as a parameter with a verification hypothesis, matching the
existing API style where certificates provide numerical bounds. -/

/-! ## Generic Z₂ bilinear bound for polynomial systems

For degree ≤ 2 polynomials, the fderiv difference is bilinear: each `pderiv i p`
is degree ≤ 1, so its evaluation is Lipschitz with computable constant.
The chain: MVT → fderiv norm → pderiv norms → constant second pderivs. -/

/-- ‖∑_i f_i * h_i‖ ≤ (∑_i ‖f_i‖) * ‖h‖ for pi-type h.
Combines triangle inequality, submultiplicativity, and ‖h_i‖ ≤ ‖h‖. -/
private theorem norm_sum_mul_pi_le
    (f h : Fin L → l1Weighted ν) :
    ‖∑ i : Fin L, f i * h i‖ ≤ (∑ i : Fin L, ‖f i‖) * ‖h‖ :=
  calc ‖∑ i : Fin L, f i * h i‖
      ≤ ∑ i : Fin L, ‖f i‖ * ‖h i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_mul_le _ _)
    _ ≤ (∑ i : Fin L, ‖f i‖) * ‖h‖ := by
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
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
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
