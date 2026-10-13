import RadiiPolynomial.Algebra.Convolution.FiniteFiber.PowerSeries
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for the power-series equivalences of the finite-fiber convolution algebra

Regression witnesses for `RadiiPolynomial/Algebra/Convolution/FiniteFiber/PowerSeries.lean`
(contract `CONSENSUS_r10.FINAL_8c6d01a0.md`, unit U-R10b, test requirements 6, 7 and 9). Not
imported by any library module; the file imports no topology.

1. One variable: the forward map is the raw coefficient map `cauchyProduct.toPowerSeries`, the
   inverse reads off coefficients, both inverse laws hold, and the product of the `ℕ` wrapper is
   the Cauchy product coefficient by coefficient.
2. The unit: `1` and the atom `single 0 1` both go to the power series `1`.
3. Noncommutative coefficients `Matrix (Fin 2) (Fin 2) ℕ`: the product order is preserved.
4. External scalars, tested separately from the coefficients: `ℕ` acting on `ℤ` and `ℚ` acting
   on `Matrix (Fin 2) (Fin 2) ℚ`.
5. Several variables at `σ = Fin 2`: coefficient laws, both antidiagonal formulas, the unit,
   matrix coefficients and scalars.
6. Several variables at an index type whose decidable equality is `Classical.decEq`.
7. One variable against `σ = Unit`: the two equivalences agree on coefficients after reindexing
   along `Finsupp.uniqueEquiv`.
-/

namespace RadiiPolynomial.FiniteFiberPowerSeriesTests

open RadiiPolynomial FiniteFiberAddConvolution Finset

/-! ## 1. One variable: forward map, inverse and product -/

section OneVariable

variable {R : Type*} [Semiring R]

/-- The forward map is the raw coefficient map of the underlying function. -/
example (f : FiniteFiberAddConvolution ℕ R) :
    toPowerSeriesRingEquiv R f = cauchyProduct.toPowerSeries (toFun f) := rfl

example (f : FiniteFiberAddConvolution ℕ R) :
    toPowerSeriesRingEquiv R f = PowerSeries.mk (toFun f) := rfl

/-- The inverse reads off coefficients. -/
example (φ : PowerSeries R) :
    (toPowerSeriesRingEquiv R).symm φ = ofFun fun n => PowerSeries.coeff n φ :=
  ext fun n => coeff_toPowerSeriesRingEquiv_symm φ n

/-- Both inverse laws. -/
example (f : FiniteFiberAddConvolution ℕ R) :
    (toPowerSeriesRingEquiv R).symm (toPowerSeriesRingEquiv R f) = f :=
  (toPowerSeriesRingEquiv R).symm_apply_apply f

example (φ : PowerSeries R) : toPowerSeriesRingEquiv R ((toPowerSeriesRingEquiv R).symm φ) = φ :=
  (toPowerSeriesRingEquiv R).apply_symm_apply φ

/-- The product of the `ℕ` wrapper is the Cauchy product of the underlying functions. -/
example (f g : FiniteFiberAddConvolution ℕ R) (n : ℕ) :
    coeff n (f * g) = cauchyProduct (toFun f) (toFun g) n := rfl

/-- Multiplicativity, read on coefficients through `PowerSeries.coeff_mul`. -/
example (f g : FiniteFiberAddConvolution ℕ R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeriesRingEquiv R (f * g)) =
      ∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g := by
  rw [map_mul, PowerSeries.coeff_mul]
  simp only [coeff_toPowerSeriesRingEquiv]

/-- `simp` normalizes coefficients through the equivalence and its inverse. -/
example (f : FiniteFiberAddConvolution ℕ R) (n : ℕ) :
    coeff n ((toPowerSeriesRingEquiv R).symm (toPowerSeriesRingEquiv R f)) = coeff n f := by
  simp

/-- A concrete product: `δ₁ * δ₁ = δ₂` on the wrapper is `X * X = X ^ 2`. -/
example : toPowerSeriesRingEquiv ℤ (single 1 1 * single 1 1) = PowerSeries.X ^ 2 := by
  ext n
  rw [coeff_toPowerSeriesRingEquiv, single_mul_single, coeff_single, PowerSeries.coeff_X_pow,
    Pi.single_apply]
  simp

end OneVariable

/-! ## 2. The unit -/

section Unit

variable {R : Type*} [Semiring R]

example : toPowerSeriesRingEquiv R 1 = 1 := map_one _

/-- The unit atom `single 0 1` goes to `1`, through `cauchyProduct.one_eq_single` and
`cauchyProduct.toPowerSeries_one`. -/
example : toPowerSeriesRingEquiv R (single 0 1) = 1 := by
  rw [toPowerSeriesRingEquiv_apply, single, toFun_ofFun, ← cauchyProduct.one_eq_single,
    cauchyProduct.toPowerSeries_one]

/-- The inverse of `1` is the Kronecker delta at the index `0`. -/
example (n : ℕ) : coeff n ((toPowerSeriesRingEquiv R).symm 1) = if n = 0 then 1 else 0 := by
  rw [coeff_toPowerSeriesRingEquiv_symm, PowerSeries.coeff_one]

end Unit

/-! ## 3. Noncommutative coefficients: the product order -/

section MatrixCoefficients

/-- The matrix coefficient ring, with the noncommuting pair `A * B ≠ B * A`. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

/-- A matrix unit. -/
def A : Mat := !![0, 1; 0, 0]

/-- Another matrix unit, not commuting with `A`. -/
def B : Mat := !![0, 0; 1, 0]

example : A * B ≠ B * A := by decide

/-- `e (δ₀A * δ₀B) = e (δ₀A) * e (δ₀B)`, in this order. -/
example :
    toPowerSeriesRingEquiv Mat (single 0 A * single 0 B) =
      toPowerSeriesRingEquiv Mat (single 0 A) * toPowerSeriesRingEquiv Mat (single 0 B) :=
  map_mul _ _ _

/-- The constant coefficient of the image of `δ₀A * δ₀B` is `A * B`. -/
example : PowerSeries.coeff 0 (toPowerSeriesRingEquiv Mat (single 0 A * single 0 B)) = A * B := by
  simp

/-- The reversed product has the different constant coefficient `B * A`. -/
example :
    toPowerSeriesRingEquiv Mat (single 0 A * single 0 B) ≠
      toPowerSeriesRingEquiv Mat (single 0 B * single 0 A) := by
  intro h
  have h0 := congrArg (PowerSeries.coeff 0) h
  simp only [coeff_toPowerSeriesRingEquiv, single_mul_single, coeff_single, add_zero,
    Pi.single_eq_same] at h0
  exact absurd h0 (by decide)

end MatrixCoefficients

/-! ## 4. External scalars -/

section Scalars

/-- `ℕ` acting on the coefficient ring `ℤ`. -/
example (f : FiniteFiberAddConvolution ℕ ℤ) :
    toPowerSeriesRingEquiv ℤ ((3 : ℕ) • f) = (3 : ℕ) • toPowerSeriesRingEquiv ℤ f :=
  toPowerSeriesRingEquiv_smul (3 : ℕ) f

/-- `ℚ` acting on the noncommutative coefficient ring `Matrix (Fin 2) (Fin 2) ℚ`. -/
example (q : ℚ) (f : FiniteFiberAddConvolution ℕ (Matrix (Fin 2) (Fin 2) ℚ)) :
    toPowerSeriesRingEquiv _ (q • f) = q • toPowerSeriesRingEquiv _ f :=
  toPowerSeriesRingEquiv_smul q f

/-- The scalar action computed on a coefficient. -/
example (q : ℚ) (f : FiniteFiberAddConvolution ℕ (Matrix (Fin 2) (Fin 2) ℚ)) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeriesRingEquiv _ (q • f)) = q • coeff n f := by
  simp

end Scalars

/-! ## 5. Several variables at `σ = Fin 2` -/

section FinTwo

variable {R : Type*} [Semiring R]

example (f : FiniteFiberAddConvolution (Fin 2 →₀ ℕ) R) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (toMvPowerSeriesRingEquiv (Fin 2) R f) = coeff n f := rfl

example (φ : MvPowerSeries (Fin 2) R) (n : Fin 2 →₀ ℕ) :
    coeff n ((toMvPowerSeriesRingEquiv (Fin 2) R).symm φ) = MvPowerSeries.coeff n φ := rfl

/-- The two antidiagonal formulas agree through the equivalence. -/
example (f g : FiniteFiberAddConvolution (Fin 2 →₀ ℕ) R) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (toMvPowerSeriesRingEquiv (Fin 2) R (f * g)) =
      ∑ p ∈ antidiagonal n, MvPowerSeries.coeff p.1 (toMvPowerSeriesRingEquiv (Fin 2) R f) *
        MvPowerSeries.coeff p.2 (toMvPowerSeriesRingEquiv (Fin 2) R g) := by
  rw [map_mul, MvPowerSeries.coeff_mul]

example (f g : FiniteFiberAddConvolution (Fin 2 →₀ ℕ) R) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (toMvPowerSeriesRingEquiv (Fin 2) R (f * g)) =
      ∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g := by
  rw [coeff_toMvPowerSeriesRingEquiv, coeff_mul]

/-- The unit, through the two Kronecker formulas `coeff_one` and `MvPowerSeries.coeff_one`. -/
example : toMvPowerSeriesRingEquiv (Fin 2) R 1 = 1 :=
  MvPowerSeries.ext fun n => by rw [coeff_toMvPowerSeriesRingEquiv, coeff_one,
    MvPowerSeries.coeff_one]

example : toMvPowerSeriesRingEquiv (Fin 2) R 1 = 1 := map_one _

/-- Matrix coefficients: the product order is preserved. -/
example :
    MvPowerSeries.coeff 0
        (toMvPowerSeriesRingEquiv (Fin 2) Mat (single 0 A * single 0 B)) = A * B := by
  simp

/-- External scalars at the same decidable-equality data. -/
example (q : ℚ) (f : FiniteFiberAddConvolution (Fin 2 →₀ ℕ) (Matrix (Fin 2) (Fin 2) ℚ)) :
    toMvPowerSeriesRingEquiv (Fin 2) _ (q • f) = q • toMvPowerSeriesRingEquiv (Fin 2) _ f :=
  toMvPowerSeriesRingEquiv_smul q f

example (f : FiniteFiberAddConvolution (Fin 2 →₀ ℕ) ℤ) :
    toMvPowerSeriesRingEquiv (Fin 2) ℤ ((3 : ℕ) • f) =
      (3 : ℕ) • toMvPowerSeriesRingEquiv (Fin 2) ℤ f :=
  toMvPowerSeriesRingEquiv_smul (3 : ℕ) f

end FinTwo

/-! ## 6. Several variables with classical decidable equality -/

section ClassicalIndex

variable {τ : Type*} {R : Type*} [Semiring R]

attribute [local instance] Classical.decEq

/-- The decidable equality in use is `Classical.decEq τ`. -/
example : (inferInstance : DecidableEq τ) = Classical.decEq τ := rfl

example (f g : FiniteFiberAddConvolution (τ →₀ ℕ) R) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n (toMvPowerSeriesRingEquiv τ R (f * g)) =
      ∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g := by
  rw [coeff_toMvPowerSeriesRingEquiv, coeff_mul]

example (φ : MvPowerSeries τ R) (n : τ →₀ ℕ) :
    coeff n ((toMvPowerSeriesRingEquiv τ R).symm φ) = MvPowerSeries.coeff n φ := by
  simp

example : toMvPowerSeriesRingEquiv τ R 1 = 1 := map_one _

end ClassicalIndex

/-! ## 7. One variable against `σ = Unit` -/

section UnitComparison

variable {R : Type*} [Semiring R]

/-- Reindexing along `Finsupp.uniqueEquiv : (Unit →₀ ℕ) ≃ ℕ` (noncomputable, as
`Finsupp.uniqueEquiv` is). -/
noncomputable def reindex (f : FiniteFiberAddConvolution ℕ R) :
    FiniteFiberAddConvolution (Unit →₀ ℕ) R :=
  ofFun fun d => coeff (Finsupp.uniqueEquiv (M := ℕ) () d) f

/-- The two equivalences agree on coefficients after reindexing. -/
example (f : FiniteFiberAddConvolution ℕ R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeriesRingEquiv R f) =
      MvPowerSeries.coeff (Finsupp.single () n)
        (toMvPowerSeriesRingEquiv Unit R (reindex f)) := by
  rw [coeff_toPowerSeriesRingEquiv, coeff_toMvPowerSeriesRingEquiv, reindex, coeff_ofFun,
    Finsupp.uniqueEquiv_apply, Finsupp.single_eq_same]

/-- Hence the two images are the same power series (`PowerSeries R` is `MvPowerSeries Unit R`). -/
example (f : FiniteFiberAddConvolution ℕ R) :
    toPowerSeriesRingEquiv R f = toMvPowerSeriesRingEquiv Unit R (reindex f) := rfl

end UnitComparison

end RadiiPolynomial.FiniteFiberPowerSeriesTests
