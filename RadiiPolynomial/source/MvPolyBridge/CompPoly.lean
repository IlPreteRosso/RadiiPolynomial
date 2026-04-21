import RadiiPolynomial.source.MvPolyBridge.Basic

/-!
# Computable Polynomial AST

`MvPolynomial` evaluation and `pderiv` are noncomputable in Mathlib, blocking `native_decide`.
`CompPoly L` mirrors `MvPolynomial (Fin L) ℚ` with computable `evalCoeff` and `pderiv`,
connected via `evalCoeff_eq_mvPolyCoeffQ` and `pderiv_toMvPoly`.

## Usage

```lean
def φ_cpoly : Fin L → CompPoly L := fun _ => .X 0 * .X 0 - .X 0

def φ_spec (j : Fin L) : MvPolynomial (Fin L) ℚ := (φ_cpoly j).toMvPoly

def Dφ_pderiv_Q (j m : Fin L) (k : ℕ) : ℚ :=
  ((φ_cpoly j).pderiv m).evalCoeff abar_Q k

lemma Dφ_pderiv_bridge :=
  compPoly_Dφ_bridge φ_cpoly φ_spec (fun _ => rfl) abar_Q ā ha
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

def pderiv (m : Fin L) : CompPoly L → CompPoly L
  | .C _ => .C 0
  | .X i => if m = i then .C 1 else .C 0
  | .add p q => .add (pderiv m p) (pderiv m q)
  | .sub p q => .sub (pderiv m p) (pderiv m q)
  | .mul p q => .add (.mul (pderiv m p) q) (.mul p (pderiv m q))
  | .neg p => .neg (pderiv m p)

noncomputable def toMvPoly : CompPoly L → MvPolynomial (Fin L) ℚ
  | .C r => MvPolynomial.C r
  | .X i => MvPolynomial.X i
  | .add p q => p.toMvPoly + q.toMvPoly
  | .sub p q => p.toMvPoly - q.toMvPoly
  | .mul p q => p.toMvPoly * q.toMvPoly
  | .neg p => -p.toMvPoly

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

end CompPoly

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
