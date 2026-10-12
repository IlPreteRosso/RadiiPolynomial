import RadiiPolynomial.Algebra.Convolution.Finite
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# Validation witnesses for the finite-fiber convolution core

Regression witnesses for `RadiiPolynomial/Algebra/Convolution/Finite.lean` (consensus
`CONSENSUS_finite_convolution.md`, N6). Not imported by any library module; check with
`lake env lean RadiiPolynomial/Examples/tests/CV/FiniteConvolution.lean` once the two imported
modules are built.

1. additive index `ℕ`: the Cauchy product bridge, and the laws specialize;
2. a multiplicative finite-fiber monoid, `Multiplicative ℕ`: two atoms and the unit atom;
3. a finite noncommutative, noncancellative monoid, `Function.End (Fin 2)` under composition,
   with a justified finite-fiber instance: two atoms and the unit atom;
4. a noncommutative coefficient semiring, `Matrix (Fin 2) (Fin 2) ℕ`: the ordered two-atom
   rule and associativity elaborate, and commutativity fails;
5. rejection controls: additive `ℤ` and multiplicative `ℕ` admit no finite-fiber instance.
-/

namespace RadiiPolynomial.FiniteConvolutionTests

open RadiiPolynomial

/-! ## 1. Additive index `ℕ` -/

section NatIndex

example (a b : ℕ → ℤ) : CauchyProduct a b = finiteAddConvolution a b :=
  CauchyProduct_eq_finiteAddConvolution a b

example (a b c : ℕ → ℤ) :
    CauchyProduct (CauchyProduct a b) c = CauchyProduct a (CauchyProduct b c) := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.assoc a b c

example (a b : ℕ → ℤ) : CauchyProduct a b = CauchyProduct b a := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.comm a b

example (f : ℕ → ℚ) : finiteAddConvolution (Pi.single 0 1) f = f :=
  finiteAddConvolution.single_zero_left zero_mul f

example (f : ℕ → ℚ) : finiteAddConvolution f (Pi.single 0 1) = f :=
  finiteAddConvolution.single_zero_right mul_zero f

/-- The two-atom rule on `ℕ`: `X^2 · 3` times `X^5 · 7` is `X^7 · 21`. -/
example : finiteAddConvolution (Pi.single 2 (3 : ℤ)) (Pi.single 5 7) = Pi.single 7 21 := by
  rw [finiteAddConvolution.single_single zero_mul mul_zero]
  norm_num

/-- A concrete coefficient: `(n ↦ n) ⋆ (n ↦ 1)` at `3` is `0 + 1 + 2 + 3 = 6`. -/
example : finiteAddConvolution (fun n : ℕ => (n : ℤ)) (fun _ => 1) 3 = 6 := by
  rw [← CauchyProduct_eq_finiteAddConvolution, CauchyProduct.apply_range]
  simp [Finset.sum_range_succ]

/-- External scalars with `S ≠ R`: an `ℕ`-action on `ℤ`-valued sequences. -/
example (c : ℕ) (a b : ℕ → ℤ) :
    finiteAddConvolution (c • a) b = c • finiteAddConvolution a b :=
  finiteAddConvolution.smul_left c a b

end NatIndex

/-! ## 2. A multiplicative finite-fiber monoid: `Multiplicative ℕ` -/

section MultiplicativeNat

example : Finset.HasMulAntidiagonal (Multiplicative ℕ) := inferInstance

example (r s : ℤ) :
    finiteMulConvolution (Pi.single (Multiplicative.ofAdd 2) r)
        (Pi.single (Multiplicative.ofAdd 3) s) =
      Pi.single (Multiplicative.ofAdd 5) (r * s) :=
  finiteMulConvolution.single_single zero_mul mul_zero _ _ r s

example (f : Multiplicative ℕ → ℤ) : finiteMulConvolution (Pi.single 1 1) f = f :=
  finiteMulConvolution.single_one_left zero_mul f

example (f : Multiplicative ℕ → ℤ) : finiteMulConvolution f (Pi.single 1 1) = f :=
  finiteMulConvolution.single_one_right mul_zero f

end MultiplicativeNat

/-! ## 3. A finite noncommutative, noncancellative monoid: `Function.End (Fin 2)` -/

section EndFin2

/-- The monoid of self-maps of `Fin 2` under composition (`(f * g) x = f (g x)`). -/
abbrev E := Function.End (Fin 2)

instance : Fintype E := inferInstanceAs (Fintype (Fin 2 → Fin 2))

instance : DecidableEq E := inferInstanceAs (DecidableEq (Fin 2 → Fin 2))

/-- Finite-fiber instance for `Function.End (Fin 2)`. Justification: the type is finite, so the
fiber `{(f, g) | f * g = n}` is a subset of the finite set `univ ×ˢ univ`, and filtering by the
decidable equation `f * g = n` gives exactly that fiber; `mem_mulAntidiagonal` is then the
membership characterization of the filter. `Finset.HasMulAntidiagonal` is a subsingleton class,
so no other (conflicting) instance exists. -/
instance : Finset.HasMulAntidiagonal E where
  mulAntidiagonal n := Finset.univ.filter fun fg : E × E => fg.1 * fg.2 = n
  mem_mulAntidiagonal := by simp

/-- The constant map with value `0`. -/
def c0 : E := fun _ => 0

/-- The swap of `0` and `1`. -/
def sw : E := fun i => if i = 0 then 1 else 0

/-- The index monoid is noncommutative and noncancellative:
`sw * c0 ≠ c0 * sw`, and `c0 * sw = c0 * 1` with `sw ≠ 1`. -/
example : sw * c0 ≠ c0 * sw ∧ c0 * sw = c0 * 1 ∧ sw ≠ 1 := by decide

/-- Two atoms over the noncancellative index: only the pair `(c0, sw)` contributes, although
the fiber over `c0 * sw = c0` also contains `(c0, 1)` and `(c0, c0)`. -/
example (r s : ℤ) :
    finiteMulConvolution (Pi.single c0 r) (Pi.single sw s) = Pi.single (c0 * sw) (r * s) :=
  finiteMulConvolution.single_single zero_mul mul_zero c0 sw r s

/-- The order of the index product is respected: the atom lands at `sw * c0`, not `c0 * sw`. -/
example (r s : ℤ) :
    finiteMulConvolution (Pi.single sw r) (Pi.single c0 s) (c0 * sw) = 0 ∧
      finiteMulConvolution (Pi.single sw r) (Pi.single c0 s) (sw * c0) = r * s := by
  rw [finiteMulConvolution.single_single zero_mul mul_zero]
  have h : c0 * sw ≠ sw * c0 := by decide
  exact ⟨by simp [h], by simp⟩

example (f : E → ℤ) : finiteMulConvolution (Pi.single 1 1) f = f :=
  finiteMulConvolution.single_one_left zero_mul f

example (f : E → ℤ) : finiteMulConvolution f (Pi.single 1 1) = f :=
  finiteMulConvolution.single_one_right mul_zero f

example (a b c : E → ℤ) :
    finiteMulConvolution (finiteMulConvolution a b) c =
      finiteMulConvolution a (finiteMulConvolution b c) :=
  finiteMulConvolution.assoc a b c

end EndFin2

/-! ## 4. A noncommutative coefficient semiring: `Matrix (Fin 2) (Fin 2) ℕ` -/

section MatrixCoefficients

abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

/-- The ordered two-atom rule with noncommutative coefficients. -/
example (i j : ℕ) (A B : Mat) :
    finiteAddConvolution (Pi.single i A) (Pi.single j B) = Pi.single (i + j) (A * B) :=
  finiteAddConvolution.single_single zero_mul mul_zero i j A B

example (a b c : ℕ → Mat) :
    finiteAddConvolution (finiteAddConvolution a b) c =
      finiteAddConvolution a (finiteAddConvolution b c) :=
  finiteAddConvolution.assoc a b c

/-- Two matrix units that do not commute. -/
def A₀ : Mat := !![0, 1; 0, 0]
def B₀ : Mat := !![0, 0; 1, 0]

/-- Commutativity is NOT available for matrix coefficients (`Mat` is not a `CommMagma`): the
two atoms `A₀` and `B₀` at index `0` do not commute under `finiteAddConvolution`. -/
example :
    finiteAddConvolution (Pi.single 0 A₀) (Pi.single 0 B₀) ≠
      finiteAddConvolution (Pi.single 0 B₀) (Pi.single 0 A₀) := by
  rw [finiteAddConvolution.single_single zero_mul mul_zero,
    finiteAddConvolution.single_single zero_mul mul_zero]
  intro h
  have h0 := congrFun h 0
  simp only [Pi.single_eq_same] at h0
  revert h0
  decide

end MatrixCoefficients

/-! ## 5. Rejection controls: no unrestricted finite fibers -/

section Rejection

/-- Additive `ℤ` has no registered `Finset.HasAntidiagonal` instance. -/
example : True := by
  fail_if_success have : Finset.HasAntidiagonal ℤ := inferInstance
  trivial

/-- Multiplicative `ℕ` has no registered `Finset.HasMulAntidiagonal` instance. -/
example : True := by
  fail_if_success have : Finset.HasMulAntidiagonal ℕ := inferInstance
  trivial

/-- No instance can exist for additive `ℤ`: the fiber over `0` contains every `(n, -n)`. -/
example : IsEmpty (Finset.HasAntidiagonal ℤ) := by
  refine ⟨fun h => ?_⟩
  let := h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n, -n))
    (fun a b hab => congrArg Prod.fst hab) (s := ↑(Finset.antidiagonal (0 : ℤ))) (fun n => ?_)
    (Finset.finite_toSet _)
  simp

/-- No instance can exist for multiplicative `ℕ`: the fiber over `0` contains every `(0, n)`. -/
example : IsEmpty (Finset.HasMulAntidiagonal ℕ) := by
  refine ⟨fun h => ?_⟩
  let := h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (0, n))
    (fun a b hab => congrArg Prod.snd hab) (s := ↑(Finset.mulAntidiagonal (0 : ℕ))) (fun n => ?_)
    (Finset.finite_toSet _)
  simp

end Rejection

end RadiiPolynomial.FiniteConvolutionTests
