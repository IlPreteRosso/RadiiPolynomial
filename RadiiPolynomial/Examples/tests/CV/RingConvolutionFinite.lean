import RadiiPolynomial.Algebra.Convolution.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for the ring convolution on finite fibers and of two point masses

Regression witnesses for
`RadiiPolynomial.DiscreteConvolution.ringConvolution_eq_finiteMulConvolution` and
`RadiiPolynomial.DiscreteConvolution.single_ringConvolution_single` in
`RadiiPolynomial/Algebra/Convolution/Ring.lean` (contract `CONSENSUS_r10.FINAL_8c6d01a0.md`,
unit U-R10b, routed items S00-13 and S02-9). Not imported by any library module.

1. The operation equality at the additive index `ℕ`, with a test-local indiscrete (hence not
   Hausdorff) topology on the coefficients: no separation, continuity or summability hypothesis
   is used.
2. The operation equality at the multiplicative index `Multiplicative ℕ`.
3. Two point masses at the additive index `ℤ`, which has no finite-fiber instance, again with the
   indiscrete topology on the coefficients.
4. Two point masses with noncommutative coefficients `Matrix (Fin 2) (Fin 2) ℤ`: the product of
   the values keeps its order.
-/

open scoped DiscreteConvolution

namespace RadiiPolynomial.RingConvolutionFiniteTests

open RadiiPolynomial.DiscreteConvolution

/-! ## 1. Additive index `ℕ`, indiscrete coefficient topology -/

section AdditiveNat

/-- The indiscrete topology `⊤` on `ℤ`, local to this section. -/
local instance indiscreteInt : TopologicalSpace ℤ := ⊤

/-- The topology in use is the local one. -/
example : (inferInstance : TopologicalSpace ℤ) = ⊤ := rfl

/-- The local topology is not Hausdorff. -/
example : ¬ T2Space ℤ := fun _ => absurd (Inseparable.all (0 : ℤ) 1).eq (by decide)

example (f g : ℕ → ℤ) : f ⋆ᵣ₊ g = finiteAddConvolution f g :=
  addRingConvolution_eq_finiteAddConvolution f g

/-- The tsum convolution at `ℕ` is the Cauchy product. -/
example (f g : ℕ → ℤ) : f ⋆ᵣ₊ g = cauchyProduct f g :=
  addRingConvolution_eq_finiteAddConvolution f g

/-- A value computed through the finite sum. -/
example : (Pi.single 1 2 ⋆ᵣ₊ Pi.single 1 3 : ℕ → ℤ) 2 = 6 := by
  rw [addRingConvolution_eq_finiteAddConvolution]
  decide

/-- The same value from the two-atom rule, with no finiteness used. -/
example : (Pi.single 1 2 ⋆ᵣ₊ Pi.single 1 3 : ℕ → ℤ) = Pi.single 2 6 :=
  single_addRingConvolution_single 1 1 2 3

end AdditiveNat

/-! ## 2. Multiplicative index `Multiplicative ℕ` -/

section MultiplicativeNat

local instance indiscreteInt' : TopologicalSpace ℤ := ⊤

example : Finset.HasMulAntidiagonal (Multiplicative ℕ) := inferInstance

example (f g : Multiplicative ℕ → ℤ) : f ⋆ᵣ g = finiteMulConvolution f g :=
  ringConvolution_eq_finiteMulConvolution f g

example :
    (Pi.single (Multiplicative.ofAdd 2) 3 ⋆ᵣ Pi.single (Multiplicative.ofAdd 3) 4 :
        Multiplicative ℕ → ℤ) =
      Pi.single (Multiplicative.ofAdd 5) 12 :=
  single_ringConvolution_single _ _ 3 4

end MultiplicativeNat

/-! ## 3. Additive index `ℤ`: no finite fibers -/

section AdditiveInt

local instance indiscreteInt'' : TopologicalSpace ℤ := ⊤

/-- The topology in use is the local one. -/
example : (inferInstance : TopologicalSpace ℤ) = ⊤ := rfl

/-- `ℤ` has no registered finite-fiber instance, so the operation equality does not apply. -/
example : True := by
  fail_if_success have : Finset.HasAntidiagonal ℤ := inferInstance
  trivial

example : ¬ T2Space ℤ := fun _ => absurd (Inseparable.all (0 : ℤ) 1).eq (by decide)

/-- Two point masses at negative and positive indices. -/
example : (Pi.single 2 3 ⋆ᵣ₊ Pi.single (-5) 4 : ℤ → ℤ) = Pi.single (-3) 12 := by
  rw [single_addRingConvolution_single]
  norm_num

/-- The general statement at the index `ℤ`. -/
example (i j x y : ℤ) : (Pi.single i x ⋆ᵣ₊ Pi.single j y : ℤ → ℤ) = Pi.single (i + j) (x * y) :=
  single_addRingConvolution_single i j x y

end AdditiveInt

/-! ## 4. Noncommutative coefficients -/

section MatrixCoefficients

/-- The matrix coefficient ring. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

/-- The discrete topology `⊥` on the coefficients, local to this section. -/
local instance discreteMat : TopologicalSpace Mat := ⊥

/-- A matrix unit. -/
def A : Mat := !![0, 1; 0, 0]

/-- Another matrix unit, not commuting with `A`. -/
def B : Mat := !![0, 0; 1, 0]

example : A * B ≠ B * A := by decide

/-- The values are multiplied in the order of the factors. -/
example : (Pi.single 1 A ⋆ᵣ₊ Pi.single 2 B : ℤ → Mat) = Pi.single 3 (A * B) := by
  rw [single_addRingConvolution_single]
  norm_num

/-- Swapping the factors changes the result. -/
example : (Pi.single 1 A ⋆ᵣ₊ Pi.single 2 B : ℤ → Mat) ≠ Pi.single 2 B ⋆ᵣ₊ Pi.single 1 A := by
  rw [single_addRingConvolution_single, single_addRingConvolution_single, add_comm]
  intro h
  have h3 := congrFun h (2 + 1)
  rw [Pi.single_eq_same, Pi.single_eq_same] at h3
  exact absurd h3 (by decide)

end MatrixCoefficients

end RadiiPolynomial.RingConvolutionFiniteTests
