import RadiiPolynomial.Algebra.Convolution.FiniteFiber
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pi

/-!
# Tests for the finite-fiber convolution wrapper

Regression witnesses for `RadiiPolynomial/Algebra/Convolution/FiniteFiber.lean` and the
general-coefficient laws of `RadiiPolynomial/Algebra/Convolution/Finite.lean` (contract
`CONSENSUS_r10.FINAL_8c6d01a0.md`, unit U-R10a, test requirements 1–5 and 9). Not imported by
any library module.

1. Convolution versus pointwise multiplication: on the additive `ℕ` wrapper `δ₁ * δ₁ = δ₂`,
   while raw functions `ℕ → ℤ` still multiply pointwise.
2. Additive `ℤ`: the finite-fiber prerequisite `Finset.HasAntidiagonal ℤ` is unavailable, so the
   wrapper has no multiplication; pointwise data can still be installed locally.
3. Noncommutative coefficients (`Matrix (Fin 2) (Fin 2) ℕ`) and a noncommutative finite
   index (`Function.End (Fin 2)`): product order is preserved and no commutative instance
   exists.
4. Weak contexts: each branch synthesizes exactly under its hypotheses, and a concrete
   nonassociative index magma gives a nonassociative wrapper.
5. Independent universes and scalars, the unit at index `0` of the additive twin, `Algebra`
   only with coefficient scalars, and centrality of `algebraMap` against an element of infinite
   support.
6. Mixed imports: wrapper and raw `Pi` instances side by side.
7. The live `CauchyProduct` delta and map statements follow from the general-coefficient laws.
8. Instance coherence: every path to the data, casts and scalar actions closes by
   `with_reducible_and_instances rfl`, for both twins.
-/

universe u v w

namespace RadiiPolynomial.FiniteFiberConvolutionTests

open RadiiPolynomial Finset

/-! ## 1. Convolution versus pointwise multiplication -/

section ConvolutionVsPointwise

open FiniteFiberAddConvolution

/-- The additive `ℕ` wrapper with integer coefficients. -/
abbrev WN := FiniteFiberAddConvolution ℕ ℤ

/-- `δ₁ * δ₁ = δ₂`: the product of two atoms at index `1` is the atom at index `2`. -/
example : (single 1 1 * single 1 1 : WN) = single 2 1 := by
  rw [single_mul_single]
  rfl

/-- The same product, coefficient by coefficient: the finite sum over `antidiagonal 2`. -/
example :
    coeff 2 (single 1 1 * single 1 1 : WN) = 1 ∧ coeff 1 (single 1 1 * single 1 1 : WN) = 0 := by
  decide

/-- On the wrapper the square of `δ₁` is not `δ₁`. -/
example : (single 1 1 * single 1 1 : WN) ≠ single 1 1 := by
  intro h
  have h1 := congrArg (coeff 1) h
  revert h1
  decide

/-- Simp interaction: the atom, zero, addition and delta rules compute coefficients. -/
example (f : WN) (r : ℤ) (m : ℕ) : coeff m (single 0 r * f + 0) = r * coeff m f := by simp

example : coeff 2 (single 1 2 * single 1 3 : WN) = 6 := by simp

example (f : WN) (m : ℕ) : coeff m (f * 1 - f) = 0 := by simp [one_def]

/-- Raw functions keep the pointwise multiplication of `Pi`. -/
example (f g : ℕ → ℤ) : f * g = fun n => f n * g n := rfl

/-- Pointwise, the square of `Pi.single 1 1` is itself. -/
example : (Pi.single 1 1 * Pi.single 1 1 : ℕ → ℤ) = Pi.single 1 1 := by
  ext n
  by_cases h : n = 1 <;> simp [h]

end ConvolutionVsPointwise

/-! ## 2. Additive `ℤ`: no finite fibers, no multiplication -/

section IntIndex

/-- No multiplication is synthesized on the additive `ℤ` wrapper. -/
example : True := by
  fail_if_success have : Mul (FiniteFiberAddConvolution ℤ ℚ) := inferInstance
  trivial

/-- The reason: `Finset.HasAntidiagonal ℤ` is uninhabited, since the fiber over `0` contains
every pair `(n, -n)`. -/
example : IsEmpty (Finset.HasAntidiagonal ℤ) := by
  refine ⟨fun h => ?_⟩
  let := h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n, -n))
    (fun a b hab => congrArg Prod.fst hab) (s := ↑(Finset.antidiagonal (0 : ℤ))) (fun n => ?_)
    (Finset.finite_toSet _)
  simp

/-- The pointwise additive and scalar structure needs no finite fibers. -/
example : AddCommGroup (FiniteFiberAddConvolution ℤ ℚ) := inferInstance

example : Module ℚ (FiniteFiberAddConvolution ℤ ℚ) := inferInstance

/-- Positive control: the synonym is not closed to multiplication as such; `Pi` data can be
installed on it explicitly and locally. -/
example (f g : FiniteFiberAddConvolution ℤ ℚ) (m : ℤ) :
    letI : Mul (FiniteFiberAddConvolution ℤ ℚ) := inferInstanceAs (Mul (ℤ → ℚ))
    FiniteFiberAddConvolution.coeff m (f * g) =
      FiniteFiberAddConvolution.coeff m f * FiniteFiberAddConvolution.coeff m g :=
  rfl

end IntIndex

/-! ## 3. Noncommutative coefficients and a noncommutative finite index -/

section Noncommutative

/-- Matrix coefficients: a noncommutative semiring. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

/-- Two matrix units that do not commute. -/
def A₀ : Mat := !![0, 1; 0, 0]

/-- Two matrix units that do not commute. -/
def B₀ : Mat := !![0, 0; 1, 0]

section Matrix

open FiniteFiberAddConvolution

/-- The ordered two-atom rule with matrix coefficients. -/
example (i j : ℕ) (A B : Mat) :
    (single i A * single j B : FiniteFiberAddConvolution ℕ Mat) = single (i + j) (A * B) :=
  single_mul_single i j A B

/-- The coefficient order is preserved: `δ₀ A₀ * δ₀ B₀ ≠ δ₀ B₀ * δ₀ A₀`. -/
example :
    (single 0 A₀ * single 0 B₀ : FiniteFiberAddConvolution ℕ Mat) ≠
      single 0 B₀ * single 0 A₀ := by
  rw [single_mul_single, single_mul_single]
  intro h
  have h0 := congrArg (coeff 0) h
  simp only [coeff_single, Pi.single_eq_same] at h0
  revert h0
  decide

example : Semiring (FiniteFiberAddConvolution ℕ Mat) := inferInstance

example : True := by
  fail_if_success have : CommSemiring (FiniteFiberAddConvolution ℕ Mat) := inferInstance
  trivial

end Matrix

section EndFin2

open FiniteFiberConvolution

/-- The monoid of self-maps of `Fin 2` under composition (`(f * g) x = f (g x)`). -/
abbrev E := Function.End (Fin 2)

instance : Fintype E := inferInstanceAs (Fintype (Fin 2 → Fin 2))

instance : DecidableEq E := inferInstanceAs (DecidableEq (Fin 2 → Fin 2))

/-- Finite-fiber instance for `Function.End (Fin 2)`. Justification: the type is finite, so the
fiber `{(f, g) | f * g = n}` is the filter of `univ` by the decidable equation `f * g = n`.
Any two such instances are propositionally equal by subsingleton elimination; the definitional
coherence of the enumerated instance paths is established by the diamond controls below, not by
subsingleton alone. -/
instance : Finset.HasMulAntidiagonal E where
  mulAntidiagonal n := Finset.univ.filter fun fg : E × E => fg.1 * fg.2 = n
  mem_mulAntidiagonal := by simp

/-- The constant map with value `0`. -/
def c0 : E := fun _ => 0

/-- The swap of `0` and `1`. -/
def sw : E := fun i => if i = 0 then 1 else 0

/-- The index product order is preserved on the wrapper: the two orders of a product of atoms
sit at the different indices `sw * c0` and `c0 * sw`. -/
example :
    (single sw (1 : ℤ) * single c0 1 : FiniteFiberConvolution E ℤ) ≠
      single c0 1 * single sw 1 := by
  rw [single_mul_single, single_mul_single]
  intro h
  have h1 := congrArg (coeff (sw * c0)) h
  have hne : c0 * sw ≠ sw * c0 := by decide
  simp [hne] at h1

example : Ring (FiniteFiberConvolution E ℤ) := inferInstance

example : True := by
  fail_if_success have : CommSemiring (FiniteFiberConvolution E ℤ) := inferInstance
  trivial

end EndFin2

end Noncommutative

/-! ## 4. Weak contexts and a nonassociative index -/

section WeakContexts

variable {M : Type u} {R : Type v}

example [Mul M] [HasMulAntidiagonal M] [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (FiniteFiberConvolution M R) := inferInstance

/-- A nonassociative index or nonassociative coefficients block the associative branch, and an
index without a unit blocks `One`. -/
example [Mul M] [HasMulAntidiagonal M] [DecidableEq M] [NonUnitalSemiring R] : True := by
  fail_if_success have : NonUnitalSemiring (FiniteFiberConvolution M R) := inferInstance
  fail_if_success have : One (FiniteFiberConvolution M R) := inferInstance
  trivial

example [Semigroup M] [HasMulAntidiagonal M] [NonUnitalNonAssocSemiring R] : True := by
  fail_if_success have : NonUnitalSemiring (FiniteFiberConvolution M R) := inferInstance
  trivial

example [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocSemiring R] :
    NonAssocSemiring (FiniteFiberConvolution M R) := inferInstance

example [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocSemiring R] : True := by
  fail_if_success have : NonUnitalSemiring (FiniteFiberConvolution M R) := inferInstance
  fail_if_success have : Semiring (FiniteFiberConvolution M R) := inferInstance
  trivial

/-- Without `DecidableEq M` there is no unit: the unital branches take the decidable equality
that `single 1 1` uses, and no classical unit is provided. -/
example [Monoid M] [HasMulAntidiagonal M] [Semiring R] : True := by
  fail_if_success have : One (FiniteFiberConvolution M R) := inferInstance
  trivial

/-- A two-element index magma that is not associative: `z * z = o` and every other product is
`z`. Then `(z * z) * o = z` but `z * (z * o) = o`. -/
inductive Mag
  | z
  | o
  deriving DecidableEq

instance : Fintype Mag := ⟨{.z, .o}, fun x => by cases x <;> simp⟩

instance : Mul Mag where
  mul
    | .z, .z => .o
    | _, _ => .z

/-- Finite-fiber instance for `Mag`: the filter of `univ` by the decidable equation
`x * y = m`. -/
instance : Finset.HasMulAntidiagonal Mag where
  mulAntidiagonal m := Finset.univ.filter fun xy : Mag × Mag => xy.1 * xy.2 = m
  mem_mulAntidiagonal := by simp

example : (Mag.z * Mag.z) * Mag.o ≠ Mag.z * (Mag.z * Mag.o) := by decide

example : NonUnitalNonAssocRing (FiniteFiberConvolution Mag ℤ) := inferInstance

example : True := by
  fail_if_success have : NonUnitalSemiring (FiniteFiberConvolution Mag ℤ) := inferInstance
  trivial

/-- The named nonassociative control: the wrapper over `Mag` is not associative. -/
example :
    (FiniteFiberConvolution.single Mag.z (1 : ℤ) * FiniteFiberConvolution.single Mag.z 1) *
        FiniteFiberConvolution.single Mag.o 1 ≠
      FiniteFiberConvolution.single Mag.z 1 *
        (FiniteFiberConvolution.single Mag.z 1 * FiniteFiberConvolution.single Mag.o 1) := by
  simp only [FiniteFiberConvolution.single_mul_single, mul_one]
  intro h
  have h0 := congrArg (FiniteFiberConvolution.coeff Mag.z) h
  revert h0
  decide

end WeakContexts

/-! ## 5. Universes, scalars, the additive unit and `Algebra` -/

section UniversesScalars

/-- The index and coefficient universes are independent. -/
example : Type u → Type v → Type (max u v) := FiniteFiberConvolution

example : Type u → Type v → Type (max u v) := FiniteFiberAddConvolution

variable {M : Type u} {R : Type v} {S : Type w}

example [Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommSemiring S] [Semiring R]
    [Algebra S R] : Algebra S (FiniteFiberConvolution M R) := inferInstance

example [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R] [DistribSMul S R]
    [IsScalarTower S R R] [SMulCommClass S R R] :
    IsScalarTower S (FiniteFiberConvolution M R) (FiniteFiberConvolution M R) ∧
      SMulCommClass S (FiniteFiberConvolution M R) (FiniteFiberConvolution M R) :=
  ⟨inferInstance, inferInstance⟩

/-- `Algebra` needs an `S`-algebra structure on the coefficients, not only a module. -/
example [Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommSemiring S] [Semiring R]
    [Module S R] : True := by
  fail_if_success have : Algebra S (FiniteFiberConvolution M R) := inferInstance
  trivial

/-- External scalars `ℕ` acting on `ℤ` coefficients (`S ≠ R`). -/
example (c : ℕ) (f g : FiniteFiberAddConvolution ℕ ℤ) : (c • f) * g = c • (f * g) :=
  smul_mul_assoc c f g

example (c : ℕ) (f g : FiniteFiberAddConvolution ℕ ℤ) : f * (c • g) = c • (f * g) :=
  mul_smul_comm c f g

section AdditiveUnit

open FiniteFiberAddConvolution

/-- The additive `ℕ` wrapper with coefficients `R`. -/
abbrev WZ (R : Type v) := FiniteFiberAddConvolution ℕ R

/-- The unit of the additive twin is the atom at index `0` with coefficient `1`. -/
example : coeff 0 (1 : FiniteFiberAddConvolution ℕ ℤ) = 1 := by simp

example : coeff 3 (1 : FiniteFiberAddConvolution ℕ ℤ) = 0 := by simp

example : (1 : FiniteFiberAddConvolution ℕ ℤ) ≠ 0 := by
  intro h
  have h0 := congrArg (coeff 0) h
  simp at h0

/-- Centrality of `algebraMap` against an element of infinite support with noncommutative
coefficients, checked coefficientwise. -/
example (A : Matrix (Fin 2) (Fin 2) ℤ) :
    algebraMap ℤ (WZ (Matrix (Fin 2) (Fin 2) ℤ)) 2 * ofFun (fun _ => A) =
      ofFun (fun _ => A) * algebraMap ℤ (WZ (Matrix (Fin 2) (Fin 2) ℤ)) 2 := by
  ext1 m
  rw [algebraMap_apply, coeff_single_zero_mul, coeff_mul_single_zero, coeff_ofFun]
  exact Algebra.commutes (2 : ℤ) A

end AdditiveUnit

end UniversesScalars

/-! ## 6. Mixed imports: wrapper and raw `Pi` instances side by side -/

section MixedImports

open FiniteFiberAddConvolution

example (f g : ℕ → ℤ) : toFun (ofFun f * ofFun g) = finiteAddConvolution f g := rfl

example (f g : ℕ → ℤ) : toFun (ofFun f + ofFun g) = f + g := rfl

example : (1 : ℕ → ℤ) = fun _ => 1 := rfl

/-- The wrapper unit is not the raw constant function `1`. -/
example : toFun (1 : FiniteFiberAddConvolution ℕ ℤ) ≠ (1 : ℕ → ℤ) := by
  intro h
  have h1 := congrFun h 1
  simp at h1

end MixedImports

/-! ## 7. The `CauchyProduct` delta and map laws from the general-coefficient laws -/

section CauchyProductCompat

variable {R : Type*}

/-- `CauchyProduct.delta_left`, statement copied verbatim. -/
example [Semiring R] (r : R) (f : ℕ → R) (n : ℕ) :
    CauchyProduct (fun k => if k = 0 then r else 0) f n = r * f n := by
  rw [show (fun k : ℕ => if k = 0 then r else 0) = Pi.single 0 r from
    funext fun k => (Pi.single_apply 0 r k).symm, CauchyProduct_eq_finiteAddConvolution,
    finiteAddConvolution.single_zero_left_apply zero_mul]

/-- `CauchyProduct.delta_right`, statement copied verbatim. -/
example [Semiring R] (f : ℕ → R) (r : R) (n : ℕ) :
    CauchyProduct f (fun k => if k = 0 then r else 0) n = f n * r := by
  rw [show (fun k : ℕ => if k = 0 then r else 0) = Pi.single 0 r from
    funext fun k => (Pi.single_apply 0 r k).symm, CauchyProduct_eq_finiteAddConvolution,
    finiteAddConvolution.single_zero_right_apply mul_zero]

/-- `CauchyProduct.map_CauchyProduct`, statement copied verbatim. -/
example {S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (a b : ℕ → R) (n : ℕ) :
    CauchyProduct (f ∘ a) (f ∘ b) n = f (CauchyProduct a b n) :=
  congrFun (map_finiteAddConvolution f.toAddMonoidHom (map_mul f) a b) n

end CauchyProductCompat

/-! ## 8. Instance coherence -/

section CoherenceMul

open FiniteFiberConvolution

section DiamondsMul

/-! Every path to the pointwise data, the convolution data, the casts and the scalar actions of
`FiniteFiberConvolution M R` closes by `with_reducible_and_instances rfl`. -/

variable {M : Type u} {R : Type v} {S : Type w}

example [AddCommMonoid R] :
    (instAddCommMonoid : AddCommMonoid (FiniteFiberConvolution M R)).toZero = instZero := by
  with_reducible_and_instances rfl

example [AddCommMonoid R] :
    (instAddCommMonoid : AddCommMonoid (FiniteFiberConvolution M R)).toAdd = instAdd := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberConvolution M R)).toNeg = instNeg := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberConvolution M R)).toSub = instSub := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberConvolution M R)).toAddCommMonoid =
      instAddCommMonoid := by
  with_reducible_and_instances rfl

example [Semiring S] [AddCommMonoid R] [Module S R] :
    (instModule : Module S (FiniteFiberConvolution M R)).toSMul = instSMul := by
  with_reducible_and_instances rfl

section NonUnital

variable [Mul M] [HasMulAntidiagonal M]

example [NonUnitalNonAssocSemiring R] :
    (instNonUnitalNonAssocSemiring :
      NonUnitalNonAssocSemiring (FiniteFiberConvolution M R)).toMul = instMul := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocSemiring R] :
    (instNonUnitalNonAssocSemiring :
      NonUnitalNonAssocSemiring (FiniteFiberConvolution M R)).toAddCommMonoid =
      instAddCommMonoid := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocRing R] :
    (instNonUnitalNonAssocRing :
      NonUnitalNonAssocRing (FiniteFiberConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocRing R] :
    (instNonUnitalNonAssocRing :
      NonUnitalNonAssocRing (FiniteFiberConvolution M R)).toAddCommGroup = instAddCommGroup := by
  with_reducible_and_instances rfl

end NonUnital

section Semigroup

variable [Semigroup M] [HasMulAntidiagonal M]

example [NonUnitalSemiring R] :
    (instNonUnitalSemiring :
      NonUnitalSemiring (FiniteFiberConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalRing R] :
    (instNonUnitalRing : NonUnitalRing (FiniteFiberConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalRing R] :
    (instNonUnitalRing : NonUnitalRing (FiniteFiberConvolution M R)).toNonUnitalNonAssocRing =
      instNonUnitalNonAssocRing := by
  with_reducible_and_instances rfl

end Semigroup

section MulOneClass

variable [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M]

example [NonAssocSemiring R] :
    (instNonAssocSemiring : NonAssocSemiring (FiniteFiberConvolution M R)).toOne = instOne := by
  with_reducible_and_instances rfl

example [NonAssocSemiring R] :
    (instNonAssocSemiring :
      NonAssocSemiring (FiniteFiberConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonAssocSemiring R] (n : ℕ) :
    (n : FiniteFiberConvolution M R) = single 1 (n : R) := by
  with_reducible_and_instances rfl

example [NonAssocRing R] :
    (instNonAssocRing : NonAssocRing (FiniteFiberConvolution M R)).toNonAssocSemiring =
      instNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonAssocRing R] :
    (instNonAssocRing : NonAssocRing (FiniteFiberConvolution M R)).toNonUnitalNonAssocRing =
      instNonUnitalNonAssocRing := by
  with_reducible_and_instances rfl

example [NonAssocRing R] (z : ℤ) :
    (z : FiniteFiberConvolution M R) = single 1 (z : R) := by
  with_reducible_and_instances rfl

end MulOneClass

section Monoid

variable [Monoid M] [HasMulAntidiagonal M] [DecidableEq M]

example [Semiring R] :
    (instSemiring : Semiring (FiniteFiberConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (instSemiring : Semiring (FiniteFiberConvolution M R)).toNonAssocSemiring =
      instNonAssocSemiring := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberConvolution M R)).toSemiring = instSemiring := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberConvolution M R)).toNonAssocRing = instNonAssocRing := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberConvolution M R)).toNonUnitalRing = instNonUnitalRing := by
  with_reducible_and_instances rfl

example [CommSemiring S] [Semiring R] [Algebra S R] :
    (instAlgebra : Algebra S (FiniteFiberConvolution M R)).toSMul = instSMul := by
  with_reducible_and_instances rfl

example [CommSemiring S] [Semiring R] [Algebra S R] :
    (Algebra.toModule : Module S (FiniteFiberConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (NSMul.toSMul : SMul ℕ (FiniteFiberConvolution M R)) = instSMul := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (AddCommMonoid.toNatModule : Module ℕ (FiniteFiberConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (Semiring.toNatAlgebra : Algebra ℕ (FiniteFiberConvolution M R)) = instAlgebra := by
  with_reducible_and_instances rfl

example [Ring R] :
    (ZSMul.toSMul : SMul ℤ (FiniteFiberConvolution M R)) = instSMul := by
  with_reducible_and_instances rfl

example [Ring R] :
    (AddCommGroup.toIntModule _ : Module ℤ (FiniteFiberConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Ring R] :
    (Ring.toIntAlgebra _ : Algebra ℤ (FiniteFiberConvolution M R)) = instAlgebra := by
  with_reducible_and_instances rfl

end Monoid

section Comm

example [CommMagma M] [HasMulAntidiagonal M] [NonUnitalNonAssocCommSemiring R] :
    (instNonUnitalNonAssocCommSemiring :
      NonUnitalNonAssocCommSemiring (FiniteFiberConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [CommSemigroup M] [HasMulAntidiagonal M] [NonUnitalCommSemiring R] :
    (instNonUnitalCommSemiring :
      NonUnitalCommSemiring (FiniteFiberConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommSemiring R] :
    (instCommSemiring : CommSemiring (FiniteFiberConvolution M R)).toSemiring =
      instSemiring := by
  with_reducible_and_instances rfl

example [CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommRing R] :
    (instCommRing : CommRing (FiniteFiberConvolution M R)).toRing = instRing := by
  with_reducible_and_instances rfl

example [CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommRing R] :
    (CommRing.toCommSemiring : CommSemiring (FiniteFiberConvolution M R)) =
      instCommSemiring := by
  with_reducible_and_instances rfl

end Comm

end DiamondsMul

end CoherenceMul

section CoherenceAdd

open FiniteFiberAddConvolution

section DiamondsAdd

/-! Every path to the pointwise data, the convolution data, the casts and the scalar actions of
`FiniteFiberAddConvolution M R` closes by `with_reducible_and_instances rfl`. -/

variable {M : Type u} {R : Type v} {S : Type w}

example [AddCommMonoid R] :
    (instAddCommMonoid : AddCommMonoid (FiniteFiberAddConvolution M R)).toZero = instZero := by
  with_reducible_and_instances rfl

example [AddCommMonoid R] :
    (instAddCommMonoid : AddCommMonoid (FiniteFiberAddConvolution M R)).toAdd = instAdd := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberAddConvolution M R)).toNeg = instNeg := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberAddConvolution M R)).toSub = instSub := by
  with_reducible_and_instances rfl

example [AddCommGroup R] :
    (instAddCommGroup : AddCommGroup (FiniteFiberAddConvolution M R)).toAddCommMonoid =
      instAddCommMonoid := by
  with_reducible_and_instances rfl

example [Semiring S] [AddCommMonoid R] [Module S R] :
    (instModule : Module S (FiniteFiberAddConvolution M R)).toSMul = instSMul := by
  with_reducible_and_instances rfl

section NonUnital

variable [Add M] [HasAntidiagonal M]

example [NonUnitalNonAssocSemiring R] :
    (instNonUnitalNonAssocSemiring :
      NonUnitalNonAssocSemiring (FiniteFiberAddConvolution M R)).toMul = instMul := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocSemiring R] :
    (instNonUnitalNonAssocSemiring :
      NonUnitalNonAssocSemiring (FiniteFiberAddConvolution M R)).toAddCommMonoid =
      instAddCommMonoid := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocRing R] :
    (instNonUnitalNonAssocRing :
      NonUnitalNonAssocRing (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalNonAssocRing R] :
    (instNonUnitalNonAssocRing :
      NonUnitalNonAssocRing (FiniteFiberAddConvolution M R)).toAddCommGroup = instAddCommGroup := by
  with_reducible_and_instances rfl

end NonUnital

section Semigroup

variable [AddSemigroup M] [HasAntidiagonal M]

example [NonUnitalSemiring R] :
    (instNonUnitalSemiring :
      NonUnitalSemiring (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalRing R] :
    (instNonUnitalRing : NonUnitalRing (FiniteFiberAddConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [NonUnitalRing R] :
    (instNonUnitalRing : NonUnitalRing (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocRing =
      instNonUnitalNonAssocRing := by
  with_reducible_and_instances rfl

end Semigroup

section MulOneClass

variable [AddZeroClass M] [HasAntidiagonal M] [DecidableEq M]

example [NonAssocSemiring R] :
    (instNonAssocSemiring : NonAssocSemiring (FiniteFiberAddConvolution M R)).toOne = instOne := by
  with_reducible_and_instances rfl

example [NonAssocSemiring R] :
    (instNonAssocSemiring :
      NonAssocSemiring (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonAssocSemiring R] (n : ℕ) :
    (n : FiniteFiberAddConvolution M R) = single 0 (n : R) := by
  with_reducible_and_instances rfl

example [NonAssocRing R] :
    (instNonAssocRing : NonAssocRing (FiniteFiberAddConvolution M R)).toNonAssocSemiring =
      instNonAssocSemiring := by
  with_reducible_and_instances rfl

example [NonAssocRing R] :
    (instNonAssocRing : NonAssocRing (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocRing =
      instNonUnitalNonAssocRing := by
  with_reducible_and_instances rfl

example [NonAssocRing R] (z : ℤ) :
    (z : FiniteFiberAddConvolution M R) = single 0 (z : R) := by
  with_reducible_and_instances rfl

end MulOneClass

section Monoid

variable [AddMonoid M] [HasAntidiagonal M] [DecidableEq M]

example [Semiring R] :
    (instSemiring : Semiring (FiniteFiberAddConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (instSemiring : Semiring (FiniteFiberAddConvolution M R)).toNonAssocSemiring =
      instNonAssocSemiring := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberAddConvolution M R)).toSemiring = instSemiring := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberAddConvolution M R)).toNonAssocRing = instNonAssocRing := by
  with_reducible_and_instances rfl

example [Ring R] :
    (instRing : Ring (FiniteFiberAddConvolution M R)).toNonUnitalRing = instNonUnitalRing := by
  with_reducible_and_instances rfl

example [CommSemiring S] [Semiring R] [Algebra S R] :
    (instAlgebra : Algebra S (FiniteFiberAddConvolution M R)).toSMul = instSMul := by
  with_reducible_and_instances rfl

example [CommSemiring S] [Semiring R] [Algebra S R] :
    (Algebra.toModule : Module S (FiniteFiberAddConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (NSMul.toSMul : SMul ℕ (FiniteFiberAddConvolution M R)) = instSMul := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (AddCommMonoid.toNatModule : Module ℕ (FiniteFiberAddConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Semiring R] :
    (Semiring.toNatAlgebra : Algebra ℕ (FiniteFiberAddConvolution M R)) = instAlgebra := by
  with_reducible_and_instances rfl

example [Ring R] :
    (ZSMul.toSMul : SMul ℤ (FiniteFiberAddConvolution M R)) = instSMul := by
  with_reducible_and_instances rfl

example [Ring R] :
    (AddCommGroup.toIntModule _ : Module ℤ (FiniteFiberAddConvolution M R)) = instModule := by
  with_reducible_and_instances rfl

example [Ring R] :
    (Ring.toIntAlgebra _ : Algebra ℤ (FiniteFiberAddConvolution M R)) = instAlgebra := by
  with_reducible_and_instances rfl

end Monoid

section Comm

example [AddCommMagma M] [HasAntidiagonal M] [NonUnitalNonAssocCommSemiring R] :
    (instNonUnitalNonAssocCommSemiring :
      NonUnitalNonAssocCommSemiring (FiniteFiberAddConvolution M R)).toNonUnitalNonAssocSemiring =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl

example [AddCommSemigroup M] [HasAntidiagonal M] [NonUnitalCommSemiring R] :
    (instNonUnitalCommSemiring :
      NonUnitalCommSemiring (FiniteFiberAddConvolution M R)).toNonUnitalSemiring =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl

example [AddCommMonoid M] [HasAntidiagonal M] [DecidableEq M] [CommSemiring R] :
    (instCommSemiring : CommSemiring (FiniteFiberAddConvolution M R)).toSemiring =
      instSemiring := by
  with_reducible_and_instances rfl

example [AddCommMonoid M] [HasAntidiagonal M] [DecidableEq M] [CommRing R] :
    (instCommRing : CommRing (FiniteFiberAddConvolution M R)).toRing = instRing := by
  with_reducible_and_instances rfl

example [AddCommMonoid M] [HasAntidiagonal M] [DecidableEq M] [CommRing R] :
    (CommRing.toCommSemiring : CommSemiring (FiniteFiberAddConvolution M R)) =
      instCommSemiring := by
  with_reducible_and_instances rfl

end Comm

end DiamondsAdd

end CoherenceAdd

end RadiiPolynomial.FiniteFiberConvolutionTests
