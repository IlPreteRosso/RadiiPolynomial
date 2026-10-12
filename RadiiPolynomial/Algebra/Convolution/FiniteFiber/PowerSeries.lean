import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.Algebra.Convolution.CauchyProduct
import RadiiPolynomial.Algebra.Convolution.FiniteFiber

/-!
# Formal power series as finite-fiber convolution algebras

The finite-fiber convolution algebra `RadiiPolynomial.FiniteFiberAddConvolution M R` holds all
functions `M → R` and multiplies them by the finite sums over the fibers of the index addition.
For the index `ℕ` this is the Cauchy product, and for the index `σ →₀ ℕ` it is the product of
multivariate formal power series. This file records both identifications as ring equivalences.

## Main definitions

* `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv R`: the ring equivalence
  `FiniteFiberAddConvolution ℕ R ≃+* PowerSeries R`. Its forward map is the coefficient map
  `RadiiPolynomial.CauchyProduct.toPowerSeries` of the underlying function, and its inverse
  reads off coefficients.
* `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv σ R`: the ring equivalence
  `FiniteFiberAddConvolution (σ →₀ ℕ) R ≃+* MvPowerSeries σ R`, which keeps every coefficient.

## Main results

* `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv`,
  `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv_symm`: both directions
  of `toPowerSeriesRingEquiv` preserve the coefficients.
* `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv`,
  `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv_symm`: the same for
  `toMvPowerSeriesRingEquiv`.
* `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv_smul`,
  `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv_smul`: both equivalences
  commute with every external scalar semiring `S` acting on the coefficients.

## Implementation notes

Only a `Semiring` structure on the coefficients is assumed; the coefficients need not commute.
The equivalences are ring equivalences and not algebra equivalences. An `AlgEquiv` needs a
commutative scalar ring `S` with matching `algebraMap`s on both sides, and the scalar
statements `toPowerSeriesRingEquiv_smul` and `toMvPowerSeriesRingEquiv_smul` already hold at the
weaker hypothesis `[Module S R]`.

`toPowerSeriesRingEquiv` reuses the linear equivalence
`RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv` at `S = R`, acting on `R` by left
multiplication, as its underlying bijection. It is `noncomputable` because that equivalence is:
it reindexes along `Finsupp.uniqueEquiv`. The raw map `RadiiPolynomial.CauchyProduct.toPowerSeries`
and the multiplication of `FiniteFiberAddConvolution ℕ R` remain computable.

`MvPowerSeries σ R` is the type synonym of `(σ →₀ ℕ) → R`, so the forward map of
`toMvPowerSeriesRingEquiv` is the identity on coefficient functions and both coefficient laws
hold by `rfl`. The two ring structures are not definitionally the same, because they choose
decidable equality on `σ` differently:

* the multiplication and the unit of `MvPowerSeries σ R` use `Classical.decEq σ`, and
  `MvPowerSeries.coeff_mul` and `MvPowerSeries.coeff_one` restate them for any instance
  `[DecidableEq σ]`;
* the multiplication of `FiniteFiberAddConvolution (σ →₀ ℕ) R` sums over the fibers of the
  instance `Finsupp.instHasAntidiagonal`, which takes `[DecidableEq σ]` (and is
  `noncomputable`), and its unit `single 0 1` uses the same instance.

The equivalence therefore takes `[DecidableEq σ]` explicitly, following the policy of
`RadiiPolynomial.FiniteFiberConvolution` that unital structures take decidable equality as an
argument. Multiplicativity compares the two antidiagonal formulas `coeff_mul` and
`MvPowerSeries.coeff_mul` at this instance. When the chosen instance is `Classical.decEq σ`, the
two multiplications and units agree definitionally; at a general instance they agree
propositionally, through these coefficient formulas. No finiteness of `σ` is used.
-/

namespace RadiiPolynomial.FiniteFiberAddConvolution

/-! ### Power series in one variable -/

section PowerSeries

variable (R : Type*) [Semiring R]

/-- The finite-fiber convolution algebra over the additive index `ℕ` is the ring of formal power
series: `f` is sent to the power series whose coefficients are those of `f`.

The forward map is `RadiiPolynomial.CauchyProduct.toPowerSeries` of the underlying function
(`toPowerSeriesRingEquiv_apply`), and the inverse reads off the coefficients
(`coeff_toPowerSeriesRingEquiv_symm`). Only `Semiring R` is assumed. -/
noncomputable def toPowerSeriesRingEquiv : FiniteFiberAddConvolution ℕ R ≃+* PowerSeries R where
  toEquiv := toFun.trans (CauchyProduct.toPowerSeriesLinearEquiv R).toEquiv
  map_mul' f g := by
    change CauchyProduct.toPowerSeries (toFun (f * g)) =
      CauchyProduct.toPowerSeries (toFun f) * CauchyProduct.toPowerSeries (toFun g)
    rw [toFun_mul, ← CauchyProduct_eq_finiteAddConvolution, CauchyProduct.toPowerSeries_mul]
  map_add' f g := map_add (CauchyProduct.toPowerSeriesLinearEquiv R) (toFun f) (toFun g)

variable {R}

/-- The forward map of `toPowerSeriesRingEquiv` is the coefficient map
`RadiiPolynomial.CauchyProduct.toPowerSeries` of the underlying function. -/
theorem toPowerSeriesRingEquiv_apply (f : FiniteFiberAddConvolution ℕ R) :
    toPowerSeriesRingEquiv R f = CauchyProduct.toPowerSeries (toFun f) :=
  rfl

/-- The coefficients of `toPowerSeriesRingEquiv R f` are those of `f`. -/
@[simp]
theorem coeff_toPowerSeriesRingEquiv (f : FiniteFiberAddConvolution ℕ R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeriesRingEquiv R f) = coeff n f :=
  CauchyProduct.coeff_toPowerSeries (toFun f) n

/-- The inverse of `toPowerSeriesRingEquiv` reads off the coefficients of a power series. -/
@[simp]
theorem coeff_toPowerSeriesRingEquiv_symm (φ : PowerSeries R) (n : ℕ) :
    coeff n ((toPowerSeriesRingEquiv R).symm φ) = PowerSeries.coeff n φ :=
  CauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff (S := R) φ n

/-- `toPowerSeriesRingEquiv` commutes with every external scalar semiring `S` acting on the
coefficients. -/
@[simp]
theorem toPowerSeriesRingEquiv_smul {S : Type*} [Semiring S] [Module S R] (s : S)
    (f : FiniteFiberAddConvolution ℕ R) :
    toPowerSeriesRingEquiv R (s • f) = s • toPowerSeriesRingEquiv R f :=
  map_smul (CauchyProduct.toPowerSeriesLinearEquiv S) s (toFun f)

end PowerSeries

/-! ### Multivariate power series -/

section MvPowerSeries

variable (σ R : Type*) [DecidableEq σ] [Semiring R]

/-- The finite-fiber convolution algebra over the additive index `σ →₀ ℕ` is the ring of
multivariate formal power series in the variables `σ`. Both directions keep every coefficient
(`coeff_toMvPowerSeriesRingEquiv`, `coeff_toMvPowerSeriesRingEquiv_symm`).

The equivalence takes the decidable equality on `σ` used by the fibers of `σ →₀ ℕ` as an
argument; see the implementation notes of this file. -/
def toMvPowerSeriesRingEquiv :
    FiniteFiberAddConvolution (σ →₀ ℕ) R ≃+* MvPowerSeries σ R where
  toFun f := toFun f
  invFun φ := ofFun φ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' f g := MvPowerSeries.ext fun n =>
    (coeff_mul f g n).trans (MvPowerSeries.coeff_mul n (toFun f : MvPowerSeries σ R) (toFun g)).symm
  map_add' _ _ := rfl

variable {σ R}

/-- The coefficients of `toMvPowerSeriesRingEquiv σ R f` are those of `f`. -/
@[simp]
theorem coeff_toMvPowerSeriesRingEquiv (f : FiniteFiberAddConvolution (σ →₀ ℕ) R)
    (n : σ →₀ ℕ) : MvPowerSeries.coeff n (toMvPowerSeriesRingEquiv σ R f) = coeff n f :=
  rfl

/-- The inverse of `toMvPowerSeriesRingEquiv` keeps the coefficients of a power series. -/
@[simp]
theorem coeff_toMvPowerSeriesRingEquiv_symm (φ : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n ((toMvPowerSeriesRingEquiv σ R).symm φ) = MvPowerSeries.coeff n φ :=
  rfl

/-- `toMvPowerSeriesRingEquiv` commutes with every external scalar semiring `S` acting on the
coefficients. -/
@[simp]
theorem toMvPowerSeriesRingEquiv_smul {S : Type*} [Semiring S] [Module S R] (s : S)
    (f : FiniteFiberAddConvolution (σ →₀ ℕ) R) :
    toMvPowerSeriesRingEquiv σ R (s • f) = s • toMvPowerSeriesRingEquiv σ R f :=
  rfl

end MvPowerSeries

end RadiiPolynomial.FiniteFiberAddConvolution
