import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# pderiv_simp: Normalize MvPolynomial pderiv expressions

Reduces `pderiv i (pderiv j p)` to `C r` for concrete degree ≤ 2 polynomials.

## Strategy

1. `dsimp` — unfold user definitions (match expressions on concrete `Fin` values);
   if `rfl` then closes the goal, stop
2. `simp` — apply pderiv computation rules (Leibniz, Kronecker delta, etc.)
3. `rfl` / `ring` / `norm_cast` — normalize the result (e.g., `1 + 1 = 2`,
   `(2 : MvPoly) = C 2`)

## Usage

```
-- After fin_cases grounds all Fin variables:
fin_cases i <;> fin_cases j <;> pderiv_simp [φ_spec]
```

## Role

Discharges the constant-second-derivative hypothesis `hD₂` of the semantic `Z₂` route
(`MvPolyBridge.norm_fderiv_diff_evalInBanach_of_const_second_pderiv`, and
`MvPolyBridge.fderiv_diff_zero_of_D₂_zero` for the inactive components of a system;
`Algebra/Polynomial/MvPolynomial/WeightedL1.lean`), which is sharper than the syntactic
`CompPoly.derivativeLipschitzBound` when an expression cancels to degree ≤ 2.

## Side effect

`MvPolynomial.pderiv_ofNat` is private but `@[simp]`: privacy hides the name, not the simp
registration. In every module importing this file (the root `RadiiPolynomial`, hence every
ReferenceBook file importing it) default `simp` rewrites `pderiv i (OfNat.ofNat n)` to `0`;
Mathlib's `map_ofNat` is not a simp lemma. The lemma stays private to avoid a future clash with
a Mathlib `MvPolynomial.pderiv_ofNat`.

## Tests

The `tests` section at the end invokes the macro, so the build resolves every name it quotes.
-/

-- Bridge: pderiv of numeric literals = 0 (OfNat goes through Nat.cast → Derivation.map_natCast)
@[simp] private theorem MvPolynomial.pderiv_ofNat {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.pderiv i (no_index (OfNat.ofNat n) : MvPolynomial σ R) = 0 := by
  show MvPolynomial.pderiv i ((n : ℕ) : MvPolynomial σ R) = 0
  exact Derivation.map_natCast _ _

open Lean.Parser.Tactic in
/-- Normalize MvPolynomial pderiv expressions. Unfolds definitions via `dsimp` and tries
`rfl`; otherwise applies pderiv computation rules via `simp`, then cleans up with
`rfl`/`ring`/`norm_cast`. -/
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
          ite_true, ite_false, ite_self]
       <;> first | rfl | ring | norm_cast)))

section tests

open MvPolynomial

/-- A degree-2 system in the usage shape of the module docstring. -/
private noncomputable def φ_test : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => X 0 * X 1 - 3 * X 0
  | 1 => X 1 * X 1 + C (1 / 2) * X 0

example : pderiv (0 : Fin 2) (pderiv (1 : Fin 2) (φ_test 0)) = C 1 := by pderiv_simp [φ_test]

example : pderiv (1 : Fin 2) (pderiv (1 : Fin 2) (φ_test 1)) = C 2 := by pderiv_simp [φ_test]

end tests
