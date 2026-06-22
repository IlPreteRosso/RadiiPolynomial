import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Computable Polynomial AST

`MvPolynomial` evaluation and `pderiv` are noncomputable in Mathlib, blocking `native_decide`.
`CompPoly L` is a computable syntax tree mirroring `MvPolynomial (Fin L) ℚ`, with three
evaluation targets:

- `evalCoeff` (computable, into `ℚ` arrays) — for `native_decide`
- `evalAlg` (noncomputable, into any `ℚ`-algebra) — defines the Banach algebra map
- `toMvPoly` (noncomputable, into `MvPolynomial`) — connects to Mathlib's `pderiv`

## Usage

```lean
def f_cpoly : Fin L → CompPoly L := fun _ => .X 0 * .X 0 - .X 0

def f (a) l      := (f_cpoly l).evalBanach a                    -- Banach algebra
def f_spec (j)   := (f_cpoly j).toMvPoly                        -- MvPolynomial bridge
def Df_Q (j m) k := ((f_cpoly j).pderiv m).evalCoeff arrs k     -- computable Jacobian
```
-/

open scoped BigOperators
open RadiiPolynomial MvPolyBridge

/-! ### Mathlib-ready: smoothness of multivariate polynomials

The single-variable analogue `Polynomial.contDiff_aeval` is in
`Mathlib/Analysis/Calculus/ContDiff/Polynomial.lean`. The lemma below extends it to
multivariate polynomials and is suitable for upstreaming. The proof inducts via
`MvPolynomial.induction_on` (3 cases: `C`, `add`, `mul_X`); each case dispatches to
the corresponding `ContDiff` closure lemma. -/

namespace MvPolynomial

@[simp] theorem C_natCast_eq {σ R : Type*} [CommSemiring R] (n : ℕ) :
    MvPolynomial.C (n : R) = (n : MvPolynomial σ R) :=
  map_natCast MvPolynomial.C n

@[simp] theorem C_ofNat_eq {σ R : Type*} [CommSemiring R] (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.C (OfNat.ofNat n : R) = (OfNat.ofNat n : MvPolynomial σ R) :=
  map_ofNat MvPolynomial.C n

@[simp] theorem C_intCast_eq {σ R : Type*} [CommRing R] (z : ℤ) :
    MvPolynomial.C (z : R) = (z : MvPolynomial σ R) :=
  map_intCast MvPolynomial.C z

/-- Multivariate polynomials, viewed as functions on `σ → 𝕜`, are `C^n` for any `n`.
Multivariate analogue of `Polynomial.contDiff_aeval`. -/
lemma contDiff_aeval {σ R 𝕜 : Type*} [Fintype σ] [CommSemiring R]
    [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
    (p : MvPolynomial σ R) (n : WithTop ℕ∞) :
    ContDiff 𝕜 n (fun x : σ → 𝕜 => aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [aeval_C]
      exact contDiff_const
  | add p q ihp ihq =>
      simp only [map_add]
      exact ihp.add ihq
  | mul_X p i ih =>
      simp only [map_mul, aeval_X]
      exact ih.mul
        ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i).contDiff)

end MvPolynomial

namespace MvPolyBridge

variable {L : ℕ}

-- CauchyProduct is in a noncomputable section; this computable duplicate enables native_decide.
def cauchyProdQ (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2

lemma cauchyProdQ_eq_CauchyProduct (f g : ℕ → ℚ) (n : ℕ) :
    cauchyProdQ f g n = CauchyProduct f g n := rfl

inductive CompPoly (L : ℕ) where
  | C : ℚ → CompPoly L
  | X : Fin L → CompPoly L
  | add : CompPoly L → CompPoly L → CompPoly L
  | sub : CompPoly L → CompPoly L → CompPoly L
  | mul : CompPoly L → CompPoly L → CompPoly L
  | neg : CompPoly L → CompPoly L
  | smul : ℚ → CompPoly L → CompPoly L
  deriving DecidableEq

namespace CompPoly

instance : Add (CompPoly L) := ⟨.add⟩
instance : Sub (CompPoly L) := ⟨.sub⟩
instance : Mul (CompPoly L) := ⟨.mul⟩
instance : Neg (CompPoly L) := ⟨.neg⟩

def evalCoeff : CompPoly L → (Fin L → Array ℚ) → ℕ → ℚ
  | .C r, _, n => if n = 0 then r else 0
  | .X i, arrs, n => (arrs i).getD n 0
  | .add p q, arrs, n => evalCoeff p arrs n + evalCoeff q arrs n
  | .sub p q, arrs, n => evalCoeff p arrs n - evalCoeff q arrs n
  | .mul p q, arrs, n => cauchyProdQ (evalCoeff p arrs) (evalCoeff q arrs) n
  | .neg p, arrs, n => -(evalCoeff p arrs n)
  | .smul r p, arrs, n => r * evalCoeff p arrs n

def pderiv (m : Fin L) : CompPoly L → CompPoly L
  | .C _ => .C 0
  | .X i => if m = i then .C 1 else .C 0
  | .add p q => .add (pderiv m p) (pderiv m q)
  | .sub p q => .sub (pderiv m p) (pderiv m q)
  | .mul p q => .add (.mul (pderiv m p) q) (.mul p (pderiv m q))
  | .neg p => .neg (pderiv m p)
  | .smul r p => .smul r (pderiv m p)

noncomputable def toMvPoly : CompPoly L → MvPolynomial (Fin L) ℚ
  | .C r => MvPolynomial.C r
  | .X i => MvPolynomial.X i
  | .add p q => p.toMvPoly + q.toMvPoly
  | .sub p q => p.toMvPoly - q.toMvPoly
  | .mul p q => p.toMvPoly * q.toMvPoly
  | .neg p => -p.toMvPoly
  | .smul r p => MvPolynomial.C r * p.toMvPoly

attribute [simp] pderiv.eq_1 pderiv.eq_2 pderiv.eq_3 pderiv.eq_4
  pderiv.eq_5 pderiv.eq_6 pderiv.eq_7
  toMvPoly.eq_1 toMvPoly.eq_2 toMvPoly.eq_3 toMvPoly.eq_4
  toMvPoly.eq_5 toMvPoly.eq_6 toMvPoly.eq_7

@[simp] theorem pderiv_add_op (m : Fin L) (p q : CompPoly L) :
    pderiv m (p + q) = pderiv m p + pderiv m q := rfl

@[simp] theorem pderiv_sub_op (m : Fin L) (p q : CompPoly L) :
    pderiv m (p - q) = pderiv m p - pderiv m q := rfl

@[simp] theorem pderiv_mul_op (m : Fin L) (p q : CompPoly L) :
    pderiv m (p * q) = pderiv m p * q + p * pderiv m q := rfl

@[simp] theorem pderiv_neg_op (m : Fin L) (p : CompPoly L) :
    pderiv m (-p) = -pderiv m p := rfl

@[simp] theorem toMvPoly_add_op (p q : CompPoly L) :
    (p + q).toMvPoly = p.toMvPoly + q.toMvPoly := rfl

@[simp] theorem toMvPoly_sub_op (p q : CompPoly L) :
    (p - q).toMvPoly = p.toMvPoly - q.toMvPoly := rfl

@[simp] theorem toMvPoly_mul_op (p q : CompPoly L) :
    (p * q).toMvPoly = p.toMvPoly * q.toMvPoly := rfl

@[simp] theorem toMvPoly_neg_op (p : CompPoly L) :
    (-p).toMvPoly = -p.toMvPoly := rfl

theorem evalCoeff_eq_mvPolyCoeffQ (p : CompPoly L) (arrs : Fin L → Array ℚ) (n : ℕ) :
    p.evalCoeff arrs n = mvPolyCoeffQ p.toMvPoly arrs n := by
  induction p generalizing n with
  | C r => simp [evalCoeff, toMvPoly]
  | X i => simp [evalCoeff, toMvPoly]
  | add p q ihp ihq =>
      simp only [evalCoeff, toMvPoly, mvPolyCoeffQ_add]
      rw [ihp, ihq]
  | sub p q ihp ihq =>
      simp only [evalCoeff, toMvPoly, mvPolyCoeffQ_sub]
      rw [ihp, ihq]
  | neg p ih =>
      simp only [evalCoeff, toMvPoly, mvPolyCoeffQ_neg]
      rw [ih]
  | mul p q ihp ihq =>
      simp only [evalCoeff, toMvPoly, mvPolyCoeffQ_mul,
        cauchyProdQ, CauchyProduct.apply]
      exact Finset.sum_congr rfl fun kl _ => by rw [ihp, ihq]
  | smul r p ih =>
      simp only [evalCoeff, toMvPoly, mvPolyCoeffQ_C_mul]
      rw [ih]

theorem pderiv_toMvPoly (m : Fin L) (p : CompPoly L) :
    (p.pderiv m).toMvPoly = MvPolynomial.pderiv m p.toMvPoly := by
  induction p with
  | C r => simp [CompPoly.pderiv, toMvPoly]
  | X i =>
      simp only [CompPoly.pderiv, toMvPoly]
      split_ifs with h
      · subst h; simp [toMvPoly]
      · simp [toMvPoly, MvPolynomial.pderiv_X_of_ne (Ne.symm h)]
  | add p q ihp ihq =>
      simp only [CompPoly.pderiv, toMvPoly, map_add, ihp, ihq]
  | sub p q ihp ihq =>
      simp only [CompPoly.pderiv, toMvPoly, map_sub, ihp, ihq]
  | mul p q ihp ihq =>
      simp only [CompPoly.pderiv, toMvPoly, MvPolynomial.pderiv_mul, ihp, ihq]
  | neg p ih =>
      simp only [CompPoly.pderiv, toMvPoly, map_neg, ih]
  | smul r p ih =>
      simp only [CompPoly.pderiv, toMvPoly, MvPolynomial.pderiv_C_mul, ih]

/-- Iterated computable partial derivatives commute with the `MvPolynomial` bridge. -/
theorem pderiv_pderiv_toMvPoly (i j : Fin L) (p : CompPoly L) :
    ((p.pderiv i).pderiv j).toMvPoly =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p.toMvPoly) := by
  rw [← pderiv_toMvPoly i p, ← pderiv_toMvPoly j (p.pderiv i)]

noncomputable def evalAlg {R : Type*} [CommRing R] [Algebra ℚ R]
    (p : CompPoly L) (a : Fin L → R) : R :=
  match p with
  | .C r => algebraMap ℚ R r
  | .X i => a i
  | .add p q => p.evalAlg a + q.evalAlg a
  | .sub p q => p.evalAlg a - q.evalAlg a
  | .mul p q => p.evalAlg a * q.evalAlg a
  | .neg p => -(p.evalAlg a)
  | .smul r p => algebraMap ℚ R r * p.evalAlg a

theorem evalAlg_eq_aeval {R : Type*} [CommRing R] [Algebra ℚ R]
    (p : CompPoly L) (a : Fin L → R) :
    p.evalAlg a = MvPolynomial.aeval a p.toMvPoly := by
  induction p with
  | C r => simp [evalAlg, toMvPoly]
  | X i => simp [evalAlg, toMvPoly]
  | add p q ihp ihq => simp only [evalAlg, toMvPoly, map_add]; rw [ihp, ihq]
  | sub p q ihp ihq => simp only [evalAlg, toMvPoly, map_sub]; rw [ihp, ihq]
  | mul p q ihp ihq => simp only [evalAlg, toMvPoly, map_mul]; rw [ihp, ihq]
  | neg p ih => simp only [evalAlg, toMvPoly, map_neg]; rw [ih]
  | smul r p ih => simp only [evalAlg, toMvPoly, map_mul, MvPolynomial.aeval_C]; rw [ih]

noncomputable def evalBanach {R : Type*} [CommRing R] [Algebra ℝ R]
    (p : CompPoly L) (a : Fin L → R) : R :=
  match p with
  | .C r => algebraMap ℝ R ((r : ℚ) : ℝ)
  | .X i => a i
  | .add p q => p.evalBanach a + q.evalBanach a
  | .sub p q => p.evalBanach a - q.evalBanach a
  | .mul p q => p.evalBanach a * q.evalBanach a
  | .neg p => -(p.evalBanach a)
  | .smul r p => ((r : ℚ) : ℝ) • p.evalBanach a

theorem evalBanach_eq_evalAlg {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℚ R] [IsScalarTower ℚ ℝ R]
    (p : CompPoly L) (a : Fin L → R) :
    p.evalBanach a = p.evalAlg a := by
  induction p with
  | C r =>
      simp only [evalBanach, evalAlg]
      exact (IsScalarTower.algebraMap_apply ℚ ℝ R r).symm
  | X i => rfl
  | add p q ihp ihq => simp only [evalBanach, evalAlg]; rw [ihp, ihq]
  | sub p q ihp ihq => simp only [evalBanach, evalAlg]; rw [ihp, ihq]
  | mul p q ihp ihq => simp only [evalBanach, evalAlg]; rw [ihp, ihq]
  | neg p ih => simp only [evalBanach, evalAlg]; rw [ih]
  | smul r p ih =>
      simp only [evalBanach, evalAlg, ih]
      rw [Algebra.smul_def]
      congr 1
      exact (IsScalarTower.algebraMap_apply ℚ ℝ R r).symm

end CompPoly

open CompPoly in
theorem compPoly_evalAlg_eq_evalInBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) :
    p.evalAlg a = evalInBanach p.toMvPoly a :=
  p.evalAlg_eq_aeval a

open CompPoly in
theorem compPoly_evalBanach_eq_evalInBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) :
    p.evalBanach a = evalInBanach p.toMvPoly a :=
  (p.evalBanach_eq_evalAlg a).trans (p.evalAlg_eq_aeval a)

/-- The pointwise interpretation of a `CompPoly` is `C^∞` — the polynomial-function
view on `ℝ^L` is smooth.

The proof factors through `MvPolynomial.contDiff_aeval`: bridge `evalBanach` to `aeval`
(via `evalBanach_eq_evalAlg` + `evalAlg_eq_aeval`), then invoke smoothness of multivariate
polynomial functions. The induction lives at the `MvPolynomial` layer (3 constructors)
rather than the `CompPoly` layer (7 constructors).

Used in the f-F bridge: `ContDiff` on `ℝ^L` plus compactness of any closed ball gives a
Lipschitz constant via `ContDiffOn.exists_lipschitzOnWith`, feeding directly into
Picard-Lindelöf for the function-space uniqueness lift. -/
theorem contDiff_evalBanach {L : ℕ} (p : CompPoly L) :
    ContDiff ℝ ⊤ (fun x : Fin L → ℝ => p.evalBanach x) := by
  have h : (fun x : Fin L → ℝ => p.evalBanach x) =
           (fun x => MvPolynomial.aeval x p.toMvPoly) :=
    funext fun x => (p.evalBanach_eq_evalAlg x).trans (p.evalAlg_eq_aeval x)
  rw [h]
  exact MvPolynomial.contDiff_aeval p.toMvPoly ⊤

/-- Differentiability follows from smoothness; kept as a named lemma for ergonomic use. -/
theorem differentiable_evalBanach {L : ℕ} (p : CompPoly L) :
    Differentiable ℝ (fun x : Fin L → ℝ => p.evalBanach x) :=
  (contDiff_evalBanach p).differentiable (by decide)

/-- Banach-algebra interpretation of a computable polynomial is differentiable on `l1Weighted`.

This is the computable-AST wrapper around `differentiable_evalInBanach`; the analytic
work stays at the `MvPolynomial` bridge layer. -/
theorem differentiable_evalBanach_l1Weighted {ν : PosReal} {L : ℕ} (p : CompPoly L) :
    Differentiable ℝ (fun x : Fin L → l1Weighted ν => p.evalBanach x) := by
  have h :
      (fun x : Fin L → l1Weighted ν => p.evalBanach x) =
        fun x => evalInBanach p.toMvPoly x :=
    funext fun x => compPoly_evalBanach_eq_evalInBanach p x
  rw [h]
  exact differentiable_evalInBanach p.toMvPoly

/-- **Mertens-recursive evaluation bridge** — the analytic counterpart to `evalBanach_eq_evalAlg`.

For a polynomial `p : CompPoly L` and a sequence `a : Fin L → l1Weighted ν`, the analytic
evaluation of `p.evalBanach a` at a point `t` (with `|t| ≤ ν`) factors through pointwise
evaluation: it equals `p` applied to the function values `i ↦ eval (a i) t`.

The proof factors through Mathlib's `MvPolynomial.comp_aeval_apply`: bridge `evalBanach`
to `aeval` (via `evalBanach_eq_evalAlg` + `evalAlg_eq_aeval`), then exploit that
`evalAlgHomQ t ht : l1Weighted ν →ₐ[ℚ] ℝ` is an algebra homomorphism — so applying it
to `aeval a φ` equals `aeval (evalAlgHomQ t ht ∘ a) φ`, which is exactly evaluation at the
function values.

Mertens' theorem is what makes `evalAlgHom` a ring hom in the first place; this is where
the analytic content sits. The induction is "compiled away" by `comp_aeval_apply`.

Combined with `hasDerivAt_eval`, this is the algebraic engine of the f-F bridge:
if `F(a) = 0` (sequence-space), then `t ↦ eval (a · , t)` solves the ODE `ẋ = f(x)`. -/
theorem eval_evalBanach {ν : PosReal} {L : ℕ}
    (p : CompPoly L) (a : Fin L → l1Weighted ν) {t : ℝ} (ht : |t| ≤ ν) :
    l1Weighted.eval (p.evalBanach a) t =
      p.evalBanach (fun i => l1Weighted.eval (a i) t) := by
  rw [p.evalBanach_eq_evalAlg, p.evalAlg_eq_aeval]
  rw [show l1Weighted.eval (MvPolynomial.aeval a p.toMvPoly) t =
        l1Weighted.evalAlgHomQ t ht (MvPolynomial.aeval a p.toMvPoly) from rfl]
  rw [MvPolynomial.comp_aeval_apply]
  rw [← p.evalAlg_eq_aeval, ← p.evalBanach_eq_evalAlg]
  rfl

theorem compPoly_Dφ_bridge {ν : PosReal} {L : ℕ}
    (φ_comp : Fin L → CompPoly L)
    (φ_spec : Fin L → MvPolynomial (Fin L) ℚ)
    (hφ : ∀ j, (φ_comp j).toMvPoly = φ_spec j)
    (arrs : Fin L → Array ℚ)
    (ā : Fin L → l1Weighted ν)
    (ha : ∀ i n, l1Weighted.toSeq (ā i) n = ((arrs i).getD n 0 : ℝ))
    (j m : Fin L) (k : ℕ) :
    l1Weighted.toSeq (evalInBanach
      (MvPolynomial.pderiv m (φ_spec j)) ā) k =
      (((φ_comp j).pderiv m).evalCoeff arrs k : ℝ) := by
  rw [← hφ, ← CompPoly.pderiv_toMvPoly,
    toSeq_evalInBanach _ ā arrs ha k]
  exact_mod_cast (CompPoly.evalCoeff_eq_mvPolyCoeffQ _ arrs k).symm

end MvPolyBridge
