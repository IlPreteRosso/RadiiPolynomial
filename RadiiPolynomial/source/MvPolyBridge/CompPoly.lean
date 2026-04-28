import RadiiPolynomial.source.MvPolyBridge.Basic

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
def φ_cpoly : Fin L → CompPoly L := fun _ => .X 0 * .X 0 - .X 0

def φ (a) l       := (φ_cpoly l).evalAlg a                     -- Banach algebra
def φ_spec (j)    := (φ_cpoly j).toMvPoly                      -- MvPolynomial bridge
def Dφ_Q (j m) k  := ((φ_cpoly j).pderiv m).evalCoeff arrs k  -- computable Jacobian
```
-/

open scoped BigOperators
open RadiiPolynomial MvPolyBridge

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
