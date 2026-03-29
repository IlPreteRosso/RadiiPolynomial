import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# pderiv_simp: Normalize MvPolynomial pderiv expressions

Reduces `pderiv i (pderiv j p)` to `C r` for concrete degree ≤ 2 polynomials.

## Strategy

1. `dsimp` — unfold user definitions (match expressions on concrete `Fin` values)
2. `simp` — apply pderiv computation rules (Leibniz, Kronecker delta, etc.)
3. `ring` / `norm_cast` — normalize the result (e.g., `1 + 1 = 2`, `(2 : MvPoly) = C 2`)

## Usage

```
-- After fin_cases grounds all Fin variables:
fin_cases i <;> fin_cases j <;> pderiv_simp [φ_spec]
```
-/

-- Bridge: pderiv of numeric literals = 0 (OfNat goes through Nat.cast → Derivation.map_natCast)
@[simp] private theorem MvPolynomial.pderiv_ofNat {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.pderiv i (no_index (OfNat.ofNat n) : MvPolynomial σ R) = 0 := by
  show MvPolynomial.pderiv i ((n : ℕ) : MvPolynomial σ R) = 0
  exact Derivation.map_natCast _ _

open Lean.Parser.Tactic in
/-- Normalize MvPolynomial pderiv expressions. Unfolds definitions via `dsimp`,
applies pderiv computation rules via `simp`, then cleans up with `ring`/`norm_cast`. -/
macro "pderiv_simp" "[" defns:simpLemma,* "]" : tactic => `(tactic|
    -- Step 1: unfold definitions (match on concrete Fin values)
    -- Step 2: apply pderiv rules + cleanup
    -- Step 3: close with ring/norm_cast/rfl
    (dsimp only [$defns,*];
     first
     | rfl
     | (simp (config := { decide := true }) only [
          MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, MvPolynomial.pderiv_one,
          MvPolynomial.pderiv_ofNat,
          MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C_mul,
          map_add, map_sub, map_neg, map_zero, map_mul,
          map_ofNat, map_natCast, map_intCast,
          MvPolynomial.C_0, MvPolynomial.C_1,
          Pi.single_apply, Fin.isValue,
          mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
          add_zero, zero_add, neg_zero, sub_zero, zero_sub, neg_neg,
          if_true, if_false, ite_self]
       <;> first | rfl | ring | norm_cast)))
