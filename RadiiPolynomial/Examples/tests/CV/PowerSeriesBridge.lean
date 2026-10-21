import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Real.Basic

/-!
# Coefficient reindexing through Mathlib's linear equivalence

These tests use `LinearEquiv.funCongrLeft` on `(Unit →₀ ℕ) ≃ ℕ` directly.
The local abbreviation records that expression once; it is not a library API.
The external scalars ℕ and ℚ and the noncommutative matrix coefficients retain
the original scope of the coefficient and inverse-law tests.
-/

namespace RadiiPolynomial.PowerSeriesBridgeTests

open RadiiPolynomial cauchyProduct

private noncomputable abbrev coeffReindex (S R : Type*) [Semiring S]
    [AddCommMonoid R] [Module S R] : (ℕ → R) ≃ₗ[S] PowerSeries R :=
  LinearEquiv.funCongrLeft S R (Finsupp.uniqueEquiv (M := ℕ) ())

section Computation

variable {R : Type*} [AddCommMonoid R] {S : Type*} [Semiring S] [Module S R]

example (a : ℕ → R) : coeffReindex S R a = toPowerSeries a := rfl
example (a : ℕ → R) : coeffReindex S R a = PowerSeries.mk a := rfl

example (φ : PowerSeries R) (n : ℕ) :
    (coeffReindex S R).symm φ n = φ (Finsupp.single () n) := rfl

example (a : ℕ → R) (n : ℕ) : (coeffReindex S R).symm (toPowerSeries a) n = a n := by
  change (coeffReindex S R).symm (coeffReindex S R a) n = a n
  exact congrFun ((coeffReindex S R).symm_apply_apply a) n

end Computation

section InverseLaws

example (a : ℕ → ℝ) : (coeffReindex ℕ ℝ).symm (coeffReindex ℕ ℝ a) = a :=
  (coeffReindex ℕ ℝ).symm_apply_apply a

example (φ : PowerSeries ℝ) : coeffReindex ℕ ℝ ((coeffReindex ℕ ℝ).symm φ) = φ :=
  (coeffReindex ℕ ℝ).apply_symm_apply φ

example (a : ℕ → Matrix (Fin 2) (Fin 2) ℕ) :
    (coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ)).symm
      (coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ) a) = a :=
  (coeffReindex _ _).symm_apply_apply a

example (φ : PowerSeries (Matrix (Fin 2) (Fin 2) ℕ)) :
    coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ)
      ((coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ)).symm φ) = φ :=
  (coeffReindex _ _).apply_symm_apply φ

example : ∃ A B : Matrix (Fin 2) (Fin 2) ℕ, A * B ≠ B * A :=
  ⟨Matrix.of ![![1, 0], ![0, 0]], Matrix.of ![![0, 1], ![0, 0]], by decide⟩

end InverseLaws

section MapLaws

example (a b : ℕ → ℝ) :
    coeffReindex ℚ ℝ (a + b) = coeffReindex ℚ ℝ a + coeffReindex ℚ ℝ b :=
  map_add (coeffReindex ℚ ℝ) a b

example : coeffReindex ℚ ℝ (0 : ℕ → ℝ) = 0 := map_zero (coeffReindex ℚ ℝ)

example (c : ℚ) (a : ℕ → ℝ) : coeffReindex ℚ ℝ (c • a) = c • coeffReindex ℚ ℝ a :=
  map_smul (coeffReindex ℚ ℝ) c a

variable {R : Type*} [Semiring R]

example (a b : ℕ → R) : toPowerSeries (a + b) = toPowerSeries a + toPowerSeries b :=
  map_add (coeffReindex R R) a b

example : toPowerSeries (0 : ℕ → R) = 0 := map_zero (coeffReindex R R)

example (c : R) (a : ℕ → R) : toPowerSeries (c • a) = c • toPowerSeries a :=
  map_smul (coeffReindex R R) c a

end MapLaws

section Coefficients

variable {R : Type*} [Semiring R]

example (a : ℕ → R) (n : ℕ) : PowerSeries.coeff n (coeffReindex R R a) = a n :=
  PowerSeries.coeff_mk n a

example (φ : PowerSeries R) (n : ℕ) :
    (coeffReindex R R).symm φ n = PowerSeries.coeff n φ := rfl

example (a b : ℕ → Matrix (Fin 2) (Fin 2) ℕ) (n : ℕ) :
    PowerSeries.coeff n
      (coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ) a *
       coeffReindex (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ) b) =
      cauchyProduct a b n := by
  change PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) = cauchyProduct a b n
  rw [PowerSeries.coeff_mul, cauchyProduct.apply]
  simp only [PowerSeries.coeff_mk]

end Coefficients

-- Actual current dependencies are printed; obsolete wrapper names are absent.
#print axioms coeffReindex
#print axioms LinearEquiv.funCongrLeft
#print axioms toPowerSeries

end RadiiPolynomial.PowerSeriesBridgeTests
