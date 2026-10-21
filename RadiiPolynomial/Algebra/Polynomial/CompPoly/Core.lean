import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Coefficients
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Computable Polynomial AST

`MvPolynomial` evaluation and `pderiv` are noncomputable in Mathlib, blocking `native_decide`.
`CompPoly L` is a computable syntax tree mirroring `MvPolynomial (Fin L) ℚ`, with six
evaluation targets:

- `evalCoeffSeq` (computable, on rational coefficient sequences)
- `evalCoeff` (computable array adapter) — for `native_decide`
- `evalQ` (computable, at a rational point) — exact arithmetic for `decide`
- `evalAlg` (noncomputable, into any `ℚ`-algebra)
- `evalBanach` (noncomputable, into any `ℝ`-algebra) — the public semantic evaluator
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

namespace MvPolyBridge

variable {L : ℕ}

inductive CompPoly (L : ℕ) where
  | C : ℚ → CompPoly L
  | X : Fin L → CompPoly L
  | add : CompPoly L → CompPoly L → CompPoly L
  | sub : CompPoly L → CompPoly L → CompPoly L
  | mul : CompPoly L → CompPoly L → CompPoly L
  | neg : CompPoly L → CompPoly L
  | smul : ℚ → CompPoly L → CompPoly L

namespace CompPoly

instance : Add (CompPoly L) := ⟨.add⟩
instance : Sub (CompPoly L) := ⟨.sub⟩
instance : Mul (CompPoly L) := ⟨.mul⟩
instance : Neg (CompPoly L) := ⟨.neg⟩

/-- Evaluate a computable polynomial in rational Taylor coefficient sequences. -/
def evalCoeffSeq : CompPoly L → (Fin L → ℕ → ℚ) → ℕ → ℚ
  | .C r, _, n => if n = 0 then r else 0
  | .X i, seqs, n => seqs i n
  | .add p q, seqs, n => evalCoeffSeq p seqs n + evalCoeffSeq q seqs n
  | .sub p q, seqs, n => evalCoeffSeq p seqs n - evalCoeffSeq q seqs n
  | .mul p q, seqs, n => cauchyProduct (evalCoeffSeq p seqs) (evalCoeffSeq q seqs) n
  | .neg p, seqs, n => -(evalCoeffSeq p seqs n)
  | .smul r p, seqs, n => r * evalCoeffSeq p seqs n

/-- Array adapter for `evalCoeffSeq`; arrays are read as zero-padded sequences. -/
def evalCoeff (p : CompPoly L) (arrs : Fin L → Array ℚ) : ℕ → ℚ :=
  p.evalCoeffSeq fun i n => (arrs i).getD n 0

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

theorem evalCoeffSeq_eq_mvPolyCoeff (p : CompPoly L) (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    p.evalCoeffSeq seqs n = mvPolyCoeff p.toMvPoly seqs n := by
  induction p generalizing n with
  | C r => simp [evalCoeffSeq, toMvPoly]
  | X i => simp [evalCoeffSeq, toMvPoly]
  | add p q ihp ihq =>
      simp only [evalCoeffSeq, toMvPoly, mvPolyCoeff_add]
      rw [ihp, ihq]
  | sub p q ihp ihq =>
      simp only [evalCoeffSeq, toMvPoly, mvPolyCoeff_sub]
      rw [ihp, ihq]
  | neg p ih =>
      simp only [evalCoeffSeq, toMvPoly, mvPolyCoeff_neg]
      rw [ih]
  | mul p q ihp ihq =>
      simp only [evalCoeffSeq, toMvPoly, mvPolyCoeff_mul, cauchyProduct.apply]
      exact Finset.sum_congr rfl fun kl _ => by rw [ihp, ihq]
  | smul r p ih =>
      simp only [evalCoeffSeq, toMvPoly, mvPolyCoeff_C_mul]
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

/-! ### Rational evaluation and the `ℚ → R` embedding

`evalQ` evaluates at a rational point in exact arithmetic; `ratMap R` embeds `ℚ` into a real
algebra `R` through `ℝ`; `evalBanach_ratMap` identifies the two at rational points, and
`evalBanach_eq_aeval_map` identifies `evalBanach` with `aeval` of the `ℝ`-mapped polynomial. -/

/-- Computable evaluation at a rational point. -/
def evalQ {L : ℕ} : CompPoly L → (Fin L → ℚ) → ℚ
  | .C r, _ => r
  | .X i, x => x i
  | .add p q, x => evalQ p x + evalQ q x
  | .sub p q, x => evalQ p x - evalQ q x
  | .mul p q, x => evalQ p x * evalQ q x
  | .neg p, x => -evalQ p x
  | .smul r p, x => r * evalQ p x

/-- The rational embedding `ℚ → ℝ → R` into a real algebra `R` (a real algebra carries no
`Algebra ℚ R` instance in general). -/
noncomputable def ratMap (R : Type*) [CommRing R] [Algebra ℝ R] : ℚ →+* R :=
  (algebraMap ℝ R).comp (Rat.castHom ℝ)

theorem ratMap_apply (R : Type*) [CommRing R] [Algebra ℝ R] (q : ℚ) :
    ratMap R q = algebraMap ℝ R (q : ℝ) := rfl

/-- `evalBanach` at a rational point of `R^L` is the embedded `evalQ`. -/
theorem evalBanach_ratMap {R : Type*} [CommRing R] [Algebra ℝ R] {L : ℕ} (p : CompPoly L)
    (c : Fin L → ℚ) : p.evalBanach (fun i => ratMap R (c i)) = ratMap R (evalQ p c) := by
  induction p with
  | C r => rfl
  | X i => rfl
  | add p q ihp ihq => simp only [CompPoly.evalBanach, evalQ, map_add, ihp, ihq]
  | sub p q ihp ihq => simp only [CompPoly.evalBanach, evalQ, map_sub, ihp, ihq]
  | mul p q ihp ihq => simp only [CompPoly.evalBanach, evalQ, map_mul, ihp, ihq]
  | neg p ih => simp only [CompPoly.evalBanach, evalQ, map_neg, ih]
  | smul r p ih =>
    simp only [CompPoly.evalBanach, evalQ, map_mul, ih, Algebra.smul_def]
    rfl


/-- The norm of an embedded rational in a normed real algebra whose unit has norm one. -/
theorem norm_ratMap (R : Type*) [NormedCommRing R] [NormedAlgebra ℝ R] [NormOneClass R]
    (q : ℚ) : ‖ratMap R q‖ = |(q : ℝ)| := by
  rw [ratMap_apply, norm_algebraMap', Real.norm_eq_abs]

/-- `evalBanach` in a real algebra `R` is `aeval` of the `ℝ`-mapped `MvPolynomial`: the bridge to
Mathlib's polynomial calculus through the canonical `Algebra ℝ R` only (no `Algebra ℚ R`). -/
theorem evalBanach_eq_aeval_map {R : Type*} [CommRing R] [Algebra ℝ R] {L : ℕ}
    (p : CompPoly L) (x : Fin L → R) :
    p.evalBanach x = MvPolynomial.aeval x (MvPolynomial.map (algebraMap ℚ ℝ) p.toMvPoly) := by
  induction p with
  | C r => simp [CompPoly.evalBanach]
  | X i => simp [CompPoly.evalBanach]
  | add p q ihp ihq => simp only [CompPoly.evalBanach, CompPoly.toMvPoly, map_add, ihp, ihq]
  | sub p q ihp ihq => simp only [CompPoly.evalBanach, CompPoly.toMvPoly, map_sub, ihp, ihq]
  | mul p q ihp ihq => simp only [CompPoly.evalBanach, CompPoly.toMvPoly, map_mul, ihp, ihq]
  | neg p ih => simp only [CompPoly.evalBanach, CompPoly.toMvPoly, map_neg, ih]
  | smul r p ih => simp [CompPoly.evalBanach, ih, Algebra.smul_def]

section AlgebraHom

variable {R B : Type*} [CommRing R] [Algebra ℝ R]
  [CommRing B] [Algebra ℝ B]

/-- Polynomial interpretation commutes with a real algebra homomorphism. -/
theorem map_evalBanach (f : R →ₐ[ℝ] B) (p : CompPoly L) (a : Fin L → R) :
    f (p.evalBanach a) = p.evalBanach (fun i => f (a i)) := by
  rw [p.evalBanach_eq_aeval_map, p.evalBanach_eq_aeval_map, MvPolynomial.comp_aeval_apply]

end AlgebraHom

section Support

/-- Syntactic support bound: if every input sequence vanishes beyond `N`, the coefficient
evaluation of `p` vanishes beyond `supportBound N p`. General in `L`, `N`, `p`. -/
def supportBound (N : ℕ) : CompPoly L → ℕ
  | .C _ => 0
  | .X _ => N
  | .add p q => max (supportBound N p) (supportBound N q)
  | .sub p q => max (supportBound N p) (supportBound N q)
  | .mul p q => supportBound N p + supportBound N q
  | .neg p => supportBound N p
  | .smul _ p => supportBound N p

/-- The coefficient evaluation of `p` vanishes beyond `supportBound N p` when every input
sequence vanishes beyond `N`. General in `L`, `N`, `p`, `seqs`. -/
theorem evalCoeffSeq_eq_zero_of_support (N : ℕ) (p : CompPoly L) (seqs : Fin L → ℕ → ℚ)
    (hs : ∀ i n, N < n → seqs i n = 0) :
    ∀ n, supportBound N p < n → p.evalCoeffSeq seqs n = 0 := by
  induction p with
  | C r =>
      intro n hn
      simp only [supportBound] at hn
      simp [CompPoly.evalCoeffSeq, show n ≠ 0 by omega]
  | X i =>
      intro n hn
      simpa [CompPoly.evalCoeffSeq] using hs i n hn
  | add p q ihp ihq =>
      intro n hn
      simp only [supportBound] at hn
      simp only [CompPoly.evalCoeffSeq, ihp n (by omega), ihq n (by omega), add_zero]
  | sub p q ihp ihq =>
      intro n hn
      simp only [supportBound] at hn
      simp only [CompPoly.evalCoeffSeq, ihp n (by omega), ihq n (by omega), sub_zero]
  | mul p q ihp ihq =>
      intro n hn
      simp only [supportBound] at hn
      simp only [CompPoly.evalCoeffSeq, cauchyProduct.apply]
      refine Finset.sum_eq_zero fun kl hkl => ?_
      rw [Finset.mem_antidiagonal] at hkl
      by_cases hk : supportBound N p < kl.1
      · rw [ihp _ hk, zero_mul]
      · rw [ihq _ (by omega), mul_zero]
  | neg p ih =>
      intro n hn
      simp only [supportBound] at hn
      simp only [CompPoly.evalCoeffSeq, ih n hn, neg_zero]
  | smul r p ih =>
      intro n hn
      simp only [supportBound] at hn
      simp only [CompPoly.evalCoeffSeq, ih n hn, mul_zero]

end Support

end CompPoly

end MvPolyBridge
