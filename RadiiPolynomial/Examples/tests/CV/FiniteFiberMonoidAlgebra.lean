import RadiiPolynomial.Algebra.Convolution.FiniteFiber.MonoidAlgebra
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for the monoid algebra inside the finite-fiber convolution algebra

Regression witnesses for `RadiiPolynomial/Algebra/Convolution/FiniteFiber/MonoidAlgebra.lean`
(unit U-R10c, test requirements 3, 8 and 9 of the R10 design). Not imported by any library
module.

1. The obligations on the additive `ℕ` index: atoms go to atoms, coefficients are kept, the map
   is injective, the range is the set of finitely supported elements, and the explicit inverse.
2. Product order: matrix coefficients and the noncommutative finite index
   `Function.End (Fin 2)`.
3. Surjectivity on a finite index, and the degenerate surjectivity with a one-element coefficient
   ring.
4. A proper range on the additive `ℕ` index and on `Multiplicative ℕ` with integer coefficients;
   ordinary multiplicative `ℕ` has no finite fibers and is not a valid index.
5. The additive translation keeps the coefficient multiplication and the unit at index `0`.
6. External scalars of another type than the coefficients.
7. Mixed imports: the monoid algebra, the wrapper and raw `Pi` operations side by side.
-/

namespace RadiiPolynomial.FiniteFiberMonoidAlgebraTests

open RadiiPolynomial Finset

/-! ## 1. The obligations on the additive `ℕ` index -/

section Obligations

open FiniteFiberAddConvolution

/-- Atoms go to atoms. -/
example (m : ℕ) (r : ℤ) : ofAddMonoidAlgebra ℤ ℕ (AddMonoidAlgebra.single m r) = single m r :=
  ofAddMonoidAlgebra_single m r

/-- The coefficients are kept. -/
example (x : AddMonoidAlgebra ℤ ℕ) (m : ℕ) : coeff m (ofAddMonoidAlgebra ℤ ℕ x) = x.coeff m :=
  coeff_ofAddMonoidAlgebra x m

/-- A coefficient of the image of a product, computed on the wrapper: `3 δ₁ * 4 δ₁ = 12 δ₂`. -/
example :
    coeff 2 (ofAddMonoidAlgebra ℤ ℕ
      (AddMonoidAlgebra.single 1 3 * AddMonoidAlgebra.single 1 4)) = 12 := by
  rw [map_mul, ofAddMonoidAlgebra_single, ofAddMonoidAlgebra_single]
  decide

/-- Injectivity. -/
example (x y : AddMonoidAlgebra ℤ ℕ) (h : ofAddMonoidAlgebra ℤ ℕ x = ofAddMonoidAlgebra ℤ ℕ y) :
    x = y :=
  ofAddMonoidAlgebra_injective h

/-- The range contains the finitely supported atom `5 δ₃`, by the finite-support criterion. -/
theorem single_mem_rangeS : single 3 (5 : ℤ) ∈ (ofAddMonoidAlgebra ℤ ℕ).rangeS := by
  refine mem_rangeS_ofAddMonoidAlgebra.mpr ((Set.finite_singleton 3).subset fun m hm => ?_)
  by_contra h
  exact hm (by simp_all)

/-- The explicit inverse recovers the atom of the monoid algebra. -/
example (hf : (Function.support fun m => coeff m (single 3 (5 : ℤ))).Finite) :
    toAddMonoidAlgebra (single 3 (5 : ℤ)) hf = AddMonoidAlgebra.single 3 5 :=
  ofAddMonoidAlgebra_injective (by simp)

/-- The inverse of the isomorphism onto the range is `toAddMonoidAlgebra`, and it reads the
coefficients back. -/
example :
    ((ofAddMonoidAlgebraEquivRangeS ℤ ℕ).symm ⟨single 3 5, single_mem_rangeS⟩).coeff 3 = 5 := by
  simp

/-- The isomorphism onto the range is `ofAddMonoidAlgebra` on values. -/
example (x : AddMonoidAlgebra ℤ ℕ) :
    (ofAddMonoidAlgebraEquivRangeS ℤ ℕ x : FiniteFiberAddConvolution ℕ ℤ) =
      ofAddMonoidAlgebra ℤ ℕ x :=
  rfl

end Obligations

/-! ## 2. Product order: matrix coefficients and a noncommutative finite index -/

section ProductOrder

/-- Matrix coefficients: a noncommutative semiring. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

/-- A matrix unit; `A₀ * B₀ ≠ B₀ * A₀`. -/
def A₀ : Mat := !![0, 1; 0, 0]

/-- A matrix unit; `A₀ * B₀ ≠ B₀ * A₀`. -/
def B₀ : Mat := !![0, 0; 1, 0]

/-- The monoid of self-maps of `Fin 2` under composition (`(f * g) x = f (g x)`). -/
abbrev E := Function.End (Fin 2)

instance : Fintype E := inferInstanceAs (Fintype (Fin 2 → Fin 2))

instance : DecidableEq E := inferInstanceAs (DecidableEq (Fin 2 → Fin 2))

/-- Finite-fiber instance for `Function.End (Fin 2)`. Justification: the type is finite, so the
fiber `{(f, g) | f * g = n}` is the filter of `univ` by the decidable equation `f * g = n`. Mathlib
provides no instance for this type, so this test-local one is the only instance in scope. -/
instance : Finset.HasMulAntidiagonal E where
  mulAntidiagonal n := Finset.univ.filter fun fg : E × E => fg.1 * fg.2 = n
  mem_mulAntidiagonal := by simp

/-- The constant map with value `0`. -/
def c0 : E := fun _ => 0

/-- The swap of `0` and `1`. -/
def sw : E := fun i => if i = 0 then 1 else 0

open FiniteFiberConvolution

/-- The image of an ordered product of atoms is the ordered product of the image atoms. -/
example :
    ofMonoidAlgebra Mat E (MonoidAlgebra.single sw A₀ * MonoidAlgebra.single c0 B₀) =
      single (sw * c0) (A₀ * B₀) := by
  rw [map_mul, ofMonoidAlgebra_single, ofMonoidAlgebra_single, single_mul_single]

/-- The index order is kept: the two orders of a product land at the different indices
`sw * c0` and `c0 * sw`. -/
example :
    ofMonoidAlgebra ℤ E (MonoidAlgebra.single sw 1 * MonoidAlgebra.single c0 1) ≠
      ofMonoidAlgebra ℤ E (MonoidAlgebra.single c0 1 * MonoidAlgebra.single sw 1) := by
  rw [map_mul, map_mul, ofMonoidAlgebra_single, ofMonoidAlgebra_single, single_mul_single,
    single_mul_single]
  intro h
  have h1 := congrArg (coeff (sw * c0)) h
  have hne : c0 * sw ≠ sw * c0 := by decide
  simp [hne] at h1

/-- The coefficient order is kept: at the index unit, `A₀ B₀` and `B₀ A₀` differ. -/
example :
    ofMonoidAlgebra Mat E (MonoidAlgebra.single 1 A₀ * MonoidAlgebra.single 1 B₀) ≠
      ofMonoidAlgebra Mat E (MonoidAlgebra.single 1 B₀ * MonoidAlgebra.single 1 A₀) := by
  intro h
  have h1 := congrArg (coeff 1) h
  rw [coeff_ofMonoidAlgebra, coeff_ofMonoidAlgebra, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    mul_one, Finsupp.single_eq_same, Finsupp.single_eq_same] at h1
  revert h1
  decide

end ProductOrder

/-! ## 3. Surjectivity on a finite index and with a one-element coefficient ring -/

section Onto

open FiniteFiberConvolution

/-- On the finite index `Function.End (Fin 2)` every element has finite support, so the map is
surjective. -/
example : Function.Surjective (ofMonoidAlgebra ℤ E) := fun _ =>
  RingHom.mem_rangeS.mp (mem_rangeS_ofMonoidAlgebra.mpr (Set.toFinite _))

/-- The same for any finite index. -/
example {R M : Type*} [Semiring R] [Monoid M] [Finset.HasMulAntidiagonal M] [DecidableEq M]
    [Finite M] : Function.Surjective (ofMonoidAlgebra R M) := fun _ =>
  RingHom.mem_rangeS.mp (mem_rangeS_ofMonoidAlgebra.mpr (Set.toFinite _))

/-- With a one-element coefficient ring every support is empty, so the map is surjective even on
the infinite additive index `ℕ`. -/
example {R : Type*} [Semiring R] [Subsingleton R] :
    Function.Surjective (FiniteFiberAddConvolution.ofAddMonoidAlgebra R ℕ) := fun _ =>
  RingHom.mem_rangeS.mp (FiniteFiberAddConvolution.mem_rangeS_ofAddMonoidAlgebra.mpr
    (Set.finite_empty.subset fun _ hm => hm (Subsingleton.elim _ _)))

/-- The concrete one-element ring `PUnit`. -/
example : Function.Surjective (FiniteFiberAddConvolution.ofAddMonoidAlgebra PUnit.{1} ℕ) :=
  fun _ => RingHom.mem_rangeS.mp (FiniteFiberAddConvolution.mem_rangeS_ofAddMonoidAlgebra.mpr
    (Set.finite_empty.subset fun _ hm => hm (Subsingleton.elim _ _)))

end Onto

/-! ## 4. A proper range on infinite indices -/

section ProperRange

section AdditiveNat

open FiniteFiberAddConvolution

/-- The function with every coefficient `1` has infinite support on the additive index `ℕ`, so it
is not in the range. -/
theorem ofFun_one_notMem_rangeS :
    ofFun (fun _ => (1 : ℤ)) ∉ (ofAddMonoidAlgebra ℤ ℕ).rangeS := by
  rw [mem_rangeS_ofAddMonoidAlgebra]
  simp only [coeff_ofFun, Function.support_const one_ne_zero]
  exact Set.infinite_univ

/-- Hence the map is not surjective on the additive index `ℕ` with integer coefficients. -/
example : ¬ Function.Surjective (ofAddMonoidAlgebra ℤ ℕ) := fun h => by
  obtain ⟨x, hx⟩ := h (ofFun fun _ => 1)
  exact ofFun_one_notMem_rangeS (hx ▸ RingHom.mem_rangeS_self _ x)

end AdditiveNat

section MultiplicativeNat

open FiniteFiberConvolution

/-- `Multiplicative ℕ` has finite fibers through Mathlib's instance
`Finset.HasMulAntidiagonal.instMultiplicative` (from `Finset.HasAntidiagonal ℕ`). -/
example : Semiring (FiniteFiberConvolution (Multiplicative ℕ) ℤ) := inferInstance

/-- The constant function `1` is not in the range on `Multiplicative ℕ` either. -/
example : ¬ Function.Surjective (ofMonoidAlgebra ℤ (Multiplicative ℕ)) := fun h => by
  obtain ⟨x, hx⟩ := h (ofFun fun _ => 1)
  have hmem := hx ▸ RingHom.mem_rangeS_self _ x
  rw [mem_rangeS_ofMonoidAlgebra] at hmem
  simp only [coeff_ofFun, Function.support_const one_ne_zero] at hmem
  exact Set.infinite_of_injective_forall_mem Multiplicative.ofAdd.injective
    (fun n => Set.mem_univ (Multiplicative.ofAdd n)) hmem

end MultiplicativeNat

section OrdinaryNat

/-- Ordinary multiplicative `ℕ` is not a valid index: it does not have finite fibers at `0`,
because `0 = 0 * n` for every `n`. No instance is synthesized. -/
example : True := by
  fail_if_success have : Finset.HasMulAntidiagonal ℕ := inferInstance
  trivial

/-- No instance can exist: the fiber over `0` would contain every pair `(0, n)`. -/
example : IsEmpty (Finset.HasMulAntidiagonal ℕ) := by
  refine ⟨fun h => ?_⟩
  let := h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((0 : ℕ), n))
    (fun a b hab => congrArg Prod.snd hab) (s := ↑(Finset.mulAntidiagonal (0 : ℕ))) (fun n => ?_)
    (Finset.finite_toSet _)
  simp

end OrdinaryNat

end ProperRange

/-! ## 5. The additive translation -/

section Additive

open FiniteFiberAddConvolution

/-- The translated map: the index operation is addition; the coefficients are still
multiplied. -/
example : AddMonoidAlgebra ℤ ℕ →+* FiniteFiberAddConvolution ℕ ℤ := ofAddMonoidAlgebra ℤ ℕ

/-- Indices add and coefficients multiply. -/
example :
    ofAddMonoidAlgebra ℤ ℕ (AddMonoidAlgebra.single 2 3 * AddMonoidAlgebra.single 5 7) =
      single 7 21 := by
  simp

/-- The unit is the atom at index `0` with coefficient `1`. -/
example : ofAddMonoidAlgebra ℤ ℕ 1 = single 0 1 := by
  rw [map_one, one_def]

end Additive

/-! ## 6. External scalars of another type than the coefficients -/

section Scalars

/-- Integer scalars acting on rational coefficients. -/
example (q : ℤ) (x : AddMonoidAlgebra ℚ ℕ) :
    FiniteFiberAddConvolution.ofAddMonoidAlgebra ℚ ℕ (q • x) =
      q • FiniteFiberAddConvolution.ofAddMonoidAlgebra ℚ ℕ x :=
  FiniteFiberAddConvolution.ofAddMonoidAlgebra_smul q x

/-- Natural-number scalars acting on matrix coefficients over the noncommutative index. -/
example (n : ℕ) (x : MonoidAlgebra Mat E) :
    FiniteFiberConvolution.ofMonoidAlgebra Mat E (n • x) =
      n • FiniteFiberConvolution.ofMonoidAlgebra Mat E x :=
  FiniteFiberConvolution.ofMonoidAlgebra_smul n x

/-- A coefficient of a scaled image. -/
example :
    FiniteFiberAddConvolution.coeff 2
      (FiniteFiberAddConvolution.ofAddMonoidAlgebra ℚ ℕ
        ((3 : ℤ) • AddMonoidAlgebra.single 2 (1 / 2))) = 3 / 2 := by
  simp only [FiniteFiberAddConvolution.ofAddMonoidAlgebra_smul,
    FiniteFiberAddConvolution.ofAddMonoidAlgebra_single, FiniteFiberAddConvolution.coeff_smul,
    FiniteFiberAddConvolution.coeff_single, Pi.single_eq_same]
  norm_num

end Scalars

/-! ## 7. Mixed imports -/

section MixedImports

/-- The monoid algebra and the wrapper are both semirings, and raw functions keep their
pointwise ring. -/
noncomputable example : Semiring (AddMonoidAlgebra ℤ ℕ) := inferInstance

example : Semiring (FiniteFiberAddConvolution ℕ ℤ) := inferInstance

example : Semiring (ℕ → ℤ) := inferInstance

/-- Raw functions still multiply pointwise. -/
example (f g : ℕ → ℤ) : f * g = fun n => f n * g n := rfl

example : (Pi.single 1 1 * Pi.single 1 1 : ℕ → ℤ) = Pi.single 1 1 := by
  rw [← Pi.single_mul, mul_one]

/-- The monoid algebra still convolves. -/
example :
    (AddMonoidAlgebra.single 1 1 * AddMonoidAlgebra.single 1 1 : AddMonoidAlgebra ℤ ℕ) =
      AddMonoidAlgebra.single 2 1 := by
  simp

/-- The image of the square of `δ₁` is the convolution square `δ₂`, not the pointwise square
`δ₁`. -/
example :
    FiniteFiberAddConvolution.ofAddMonoidAlgebra ℤ ℕ (AddMonoidAlgebra.single 1 1 ^ 2) ≠
      FiniteFiberAddConvolution.ofFun (Pi.single 1 1 * Pi.single 1 1) := by
  intro h
  have h1 := congrArg (FiniteFiberAddConvolution.coeff 1) h
  simp [sq] at h1

end MixedImports

end RadiiPolynomial.FiniteFiberMonoidAlgebraTests
