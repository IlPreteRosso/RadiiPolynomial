import RadiiPolynomial.Algebra.Convolution
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# Validation witnesses for the bundled power-series bridge

Regression witnesses for the linear equivalence `CauchyProduct.toPowerSeriesLinearEquiv` of
`RadiiPolynomial/Algebra/Convolution/CauchyProduct.lean` (consensus
`CONSENSUS_toPowerSeries_equiv.md`, E4). Not imported by any library module; build with
`lake build RadiiPolynomial.Examples.tests.CV.PowerSeriesBridge`.

1. The forward map of the bundle is the raw coefficient map `toPowerSeries`, and its inverse
   evaluates a power series at the exponent `Finsupp.single () n`.
2. Both inverse laws hold for a scalar semiring distinct from the coefficients (`ℕ` acting on `ℝ`)
   and for noncommutative coefficients acting on themselves (`Matrix (Fin 2) (Fin 2) ℕ`).
3. Additivity, the zero law and scalar compatibility hold at an external scalar (`ℚ` acting on
   `ℝ`). The three removed raw laws `toPowerSeries_add`, `toPowerSeries_zero` and
   `toPowerSeries_smul` are recovered from them at their old hypotheses.
4. `simp` normalizes coefficients and inverse values through the bundle to `PowerSeries.coeff`.
5. The axiom closures of the new declarations, and of the raw map and its injectivity.
-/

namespace RadiiPolynomial.PowerSeriesBridgeTests

open RadiiPolynomial CauchyProduct

/-! ## 1. Forward map and inverse computation -/

section Computation

variable {R : Type*} [AddCommMonoid R] {S : Type*} [Semiring S] [Module S R]

example (a : ℕ → R) : toPowerSeriesLinearEquiv S a = toPowerSeries a :=
  toPowerSeriesLinearEquiv_apply a

example (a : ℕ → R) : toPowerSeriesLinearEquiv S a = PowerSeries.mk a := rfl

example (φ : PowerSeries R) (n : ℕ) :
    (toPowerSeriesLinearEquiv S).symm φ n = φ (Finsupp.single () n) :=
  toPowerSeriesLinearEquiv_symm_apply φ n

/-- The inverse composed with the raw map reads back the sequence. -/
example (a : ℕ → R) (n : ℕ) : (toPowerSeriesLinearEquiv S).symm (toPowerSeries a) n = a n := by
  rw [← toPowerSeriesLinearEquiv_apply (S := S), LinearEquiv.symm_apply_apply]

end Computation

/-! ## 2. Inverse laws -/

section InverseLaws

/-- A scalar semiring distinct from the coefficients: `ℕ` acting on `ℝ`. -/
example (a : ℕ → ℝ) : (toPowerSeriesLinearEquiv ℕ).symm (toPowerSeriesLinearEquiv ℕ a) = a :=
  (toPowerSeriesLinearEquiv ℕ).symm_apply_apply a

example (φ : PowerSeries ℝ) :
    toPowerSeriesLinearEquiv ℕ ((toPowerSeriesLinearEquiv ℕ).symm φ) = φ :=
  (toPowerSeriesLinearEquiv ℕ).apply_symm_apply φ

/-- Noncommutative coefficients acting on themselves: `S := R := Matrix (Fin 2) (Fin 2) ℕ`. -/
example (a : ℕ → Matrix (Fin 2) (Fin 2) ℕ) :
    (toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ)).symm
      (toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ) a) = a :=
  (toPowerSeriesLinearEquiv _).symm_apply_apply a

example (φ : PowerSeries (Matrix (Fin 2) (Fin 2) ℕ)) :
    toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ)
      ((toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ)).symm φ) = φ :=
  (toPowerSeriesLinearEquiv _).apply_symm_apply φ

/-- The matrix coefficients are genuinely noncommutative. -/
example : ∃ A B : Matrix (Fin 2) (Fin 2) ℕ, A * B ≠ B * A :=
  ⟨Matrix.of ![![1, 0], ![0, 0]], Matrix.of ![![0, 1], ![0, 0]], by decide⟩

end InverseLaws

/-! ## 3. Linear structure at an external scalar, and the three removed laws -/

section MapLaws

example (a b : ℕ → ℝ) :
    toPowerSeriesLinearEquiv ℚ (a + b) =
      toPowerSeriesLinearEquiv ℚ a + toPowerSeriesLinearEquiv ℚ b :=
  map_add (toPowerSeriesLinearEquiv ℚ) a b

example : toPowerSeriesLinearEquiv ℚ (0 : ℕ → ℝ) = 0 :=
  map_zero (toPowerSeriesLinearEquiv ℚ)

example (c : ℚ) (a : ℕ → ℝ) :
    toPowerSeriesLinearEquiv ℚ (c • a) = c • toPowerSeriesLinearEquiv ℚ a :=
  map_smul (toPowerSeriesLinearEquiv ℚ) c a

variable {R : Type*} [Semiring R]

/-- Replacement of the removed `toPowerSeries_add`, at its old hypotheses. -/
example (a b : ℕ → R) : toPowerSeries (a + b) = toPowerSeries a + toPowerSeries b := by
  simpa only [toPowerSeriesLinearEquiv_apply] using map_add (toPowerSeriesLinearEquiv R) a b

/-- Replacement of the removed `toPowerSeries_zero`, at its old hypotheses. -/
example : toPowerSeries (0 : ℕ → R) = 0 := by
  simpa only [toPowerSeriesLinearEquiv_apply] using map_zero (toPowerSeriesLinearEquiv R)

/-- Replacement of the removed `toPowerSeries_smul`, at its old hypotheses. -/
example (c : R) (a : ℕ → R) : toPowerSeries (c • a) = c • toPowerSeries a := by
  simpa only [toPowerSeriesLinearEquiv_apply] using map_smul (toPowerSeriesLinearEquiv R) c a

end MapLaws

/-! ## 4. Coefficient normal form through the bundle -/

section CoefficientNormalForm

variable {R : Type*} [Semiring R]

example (a : ℕ → R) (n : ℕ) : PowerSeries.coeff n (toPowerSeriesLinearEquiv R a) = a n := by
  simp

example (φ : PowerSeries R) (n : ℕ) :
    (toPowerSeriesLinearEquiv R).symm φ n = PowerSeries.coeff n φ := by
  simp

/-- Over noncommutative coefficients, the normal form of a bundled product coefficient. -/
example (a b : ℕ → Matrix (Fin 2) (Fin 2) ℕ) (n : ℕ) :
    PowerSeries.coeff n
        (toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ) a *
          toPowerSeriesLinearEquiv (Matrix (Fin 2) (Fin 2) ℕ) b) =
      CauchyProduct a b n := by
  rw [toPowerSeriesLinearEquiv_apply, toPowerSeriesLinearEquiv_apply, eq_coeff_mul]

end CoefficientNormalForm

/-! ## 5. Axiom record

Output of `#print axioms` on each declaration (2026-10-12, Lean v4.34.1, Mathlib d13f23b7),
enforced below by `#guard_msgs`:

* `CauchyProduct.toPowerSeriesLinearEquiv`: `[propext, Classical.choice, Quot.sound]`
* `CauchyProduct.toPowerSeriesLinearEquiv_apply`: `[propext, Classical.choice, Quot.sound]`
* `CauchyProduct.toPowerSeriesLinearEquiv_symm_apply`: `[propext, Classical.choice, Quot.sound]`
* `CauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff`:
  `[propext, Classical.choice, Quot.sound]`
* `CauchyProduct.coeff_toPowerSeriesLinearEquiv`: `[propext, Classical.choice, Quot.sound]`
* `CauchyProduct.toPowerSeries`: `[propext, Classical.choice, Quot.sound]` (unchanged)
* `CauchyProduct.toPowerSeries_injective`: `[propext, Classical.choice, Quot.sound]` (unchanged)
-/

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeriesLinearEquiv

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeriesLinearEquiv_apply

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeriesLinearEquiv_symm_apply

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeriesLinearEquiv_symm_apply_coeff

/--
info: 'RadiiPolynomial.CauchyProduct.coeff_toPowerSeriesLinearEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms coeff_toPowerSeriesLinearEquiv

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeries

/--
info: 'RadiiPolynomial.CauchyProduct.toPowerSeries_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toPowerSeries_injective

end RadiiPolynomial.PowerSeriesBridgeTests
