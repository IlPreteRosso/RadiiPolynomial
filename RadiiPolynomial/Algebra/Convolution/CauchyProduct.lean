import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.Algebra.Convolution.Finite

/-!
# Cauchy product of natural-index sequences

This module defines the finite-sum Cauchy product of natural-index sequences over a semiring.
It is the finite-fiber convolution `finiteAddConvolution` on the additive index `ℕ`
(`CauchyProduct_eq_finiteAddConvolution`). That general operation owns the algebraic laws:
associativity, distributivity, the zero laws, commutativity, the scalar laws and the two-atom
rule are specializations of its laws. The coefficient map to formal power series identifies
this product with power-series multiplication and supplies the unit laws. Its bundled view
`toPowerSeriesLinearEquiv` is an `S`-linear equivalence for every semiring `S` acting on the
coefficients, so additivity and scalar compatibility of the map are `map_add`, `map_zero` and
`map_smul`. Atom, support and finite Toeplitz formulas provide the concrete coefficient API.
Raw sequence multiplication remains pointwise; the bridge records compatibility with the
separately named Cauchy product.
-/

open scoped BigOperators

namespace RadiiPolynomial

section Generic

variable {R : Type*}

/-- Cauchy product (convolution) of sequences:
`(a ⋆ b)_n = ∑_{k+l=n} a_k b_l`.

Ref: Def. 7.4.2, Eq. (7.15). -/
def CauchyProduct [Semiring R] (a b : ℕ → R) : ℕ → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- The Cauchy product is the finite-fiber convolution over the additive index `ℕ`. -/
theorem CauchyProduct_eq_finiteAddConvolution [Semiring R] (a b : ℕ → R) :
    CauchyProduct a b = finiteAddConvolution a b := rfl

namespace CauchyProduct

scoped infixr:67 " ⋆ " => RadiiPolynomial.CauchyProduct

section Semiring

variable [Semiring R]

/-- Application of the Cauchy product: the antidiagonal sum. -/
theorem apply (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-- The Cauchy product as a sum over `range (n + 1)`, `∑ j, a (n - j) * b j`. -/
theorem apply_range (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  rw [apply, ← Finset.Nat.sum_antidiagonal_swap (f := fun p => a p.1 * b p.2)]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a j * b i) n

/-- Multiplicative identity sequence (`1,0,0,...`). -/
def one : ℕ → R := fun n => if n = 0 then 1 else 0

/-- The unit sequence at `0`. -/
@[simp] theorem one_zero : (one : ℕ → R) 0 = 1 := rfl

/-- The unit sequence at `n + 1`. -/
@[simp] theorem one_succ (n : ℕ) : (one : ℕ → R) (n + 1) = 0 := rfl

end Semiring

/-! ### The bridge to formal power series -/

section ToPowerSeries

/-- Bridge object: the sequence `a : ℕ → R` as a formal power series. -/
def toPowerSeries (a : ℕ → R) : PowerSeries R := PowerSeries.mk a

/-- A sequence is determined by its power series. -/
theorem toPowerSeries_injective : Function.Injective (toPowerSeries (R := R)) :=
  fun a b h => funext fun n => by
    simpa only [toPowerSeries, PowerSeries.mk, Finsupp.single_eq_same] using
      congrFun h (Finsupp.single () n)

section LinearEquiv

variable (S : Type*) [Semiring S] [AddCommMonoid R] [Module S R]

/-- The coefficient map `toPowerSeries` as an `S`-linear equivalence, for any semiring `S` acting
on the coefficients: the forward map is `toPowerSeries` (`toPowerSeriesLinearEquiv_apply`) and
the inverse reads off coefficients (`toPowerSeriesLinearEquiv_symm_apply`).

It is the reindexing of coordinates along `(Unit →₀ ℕ) ≃ ℕ`; no multiplication on `R` is
involved. Both the forward map and the inverse compute by `rfl`. -/
noncomputable def toPowerSeriesLinearEquiv : (ℕ → R) ≃ₗ[S] PowerSeries R :=
  LinearEquiv.funCongrLeft S R (Finsupp.uniqueEquiv (M := ℕ) ())

variable {S}

/-- The forward map of `toPowerSeriesLinearEquiv` is the raw coefficient map `toPowerSeries`. -/
theorem toPowerSeriesLinearEquiv_apply (a : ℕ → R) :
    toPowerSeriesLinearEquiv S a = toPowerSeries a :=
  rfl

/-- The inverse of `toPowerSeriesLinearEquiv` evaluates a power series at the exponent
`Finsupp.single () n`; over a semiring this is `PowerSeries.coeff n`
(`toPowerSeriesLinearEquiv_symm_apply_coeff`). -/
theorem toPowerSeriesLinearEquiv_symm_apply (φ : PowerSeries R) (n : ℕ) :
    (toPowerSeriesLinearEquiv S).symm φ n = φ (Finsupp.single () n) :=
  rfl

end LinearEquiv

variable [Semiring R]

/-- The coefficients of `toPowerSeries a` are the entries of `a`. -/
@[simp] theorem coeff_toPowerSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := PowerSeries.coeff_mk n a

/-- Over a semiring `R`, the inverse of `toPowerSeriesLinearEquiv` is coefficient extraction,
for any scalar semiring `S` acting on `R`. -/
@[simp] theorem toPowerSeriesLinearEquiv_symm_apply_coeff {S : Type*} [Semiring S] [Module S R]
    (φ : PowerSeries R) (n : ℕ) :
    (toPowerSeriesLinearEquiv S).symm φ n = PowerSeries.coeff n φ :=
  toPowerSeriesLinearEquiv_symm_apply φ n

/-- Over a semiring `R`, the coefficients of the bundled view are the entries of the sequence,
for any scalar semiring `S` acting on `R`. -/
@[simp] theorem coeff_toPowerSeriesLinearEquiv {S : Type*} [Semiring S] [Module S R]
    (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeriesLinearEquiv S a) = a n :=
  coeff_toPowerSeries a n

/-- The unit sequence maps to the power series `1`. -/
theorem toPowerSeries_one : toPowerSeries (one : ℕ → R) = 1 := by
  ext n
  rw [coeff_toPowerSeries, PowerSeries.coeff_one]
  rfl

/-- The atom `Pi.single i a` is the monomial `a X^i`. -/
theorem toPowerSeries_single (i : ℕ) (a : R) :
    toPowerSeries (Pi.single i a) = PowerSeries.monomial i a := by
  ext n
  rw [coeff_toPowerSeries, PowerSeries.coeff_monomial, Pi.single_apply]

/-- On index `ℕ`, Cauchy product matches power-series multiplication coefficients. -/
theorem toPowerSeries_mul (a b : ℕ → R) :
    toPowerSeries (CauchyProduct a b) = toPowerSeries a * toPowerSeries b := by
  ext n
  simp only [coeff_toPowerSeries, PowerSeries.coeff_mul, apply]

/-- Coefficient form of the bridge:
`(a ⋆ b)_n = coeff n ((toPowerSeries a) * (toPowerSeries b))`. -/
theorem eq_coeff_mul (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = PowerSeries.coeff n (toPowerSeries a * toPowerSeries b) := by
  rw [← coeff_toPowerSeries (CauchyProduct a b) n, toPowerSeries_mul]

end ToPowerSeries

section Semiring

variable [Semiring R]

/-! ### Algebraic laws

Specializations of the finite-fiber convolution laws (`finiteAddConvolution`), except the unit
laws, which are transported along the power-series bridge. -/

/-- Associativity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.11). -/
theorem assoc (a b c : ℕ → R) :
    CauchyProduct (CauchyProduct a b) c = CauchyProduct a (CauchyProduct b c) := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.assoc a b c

/-- Left distributivity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.12). -/
theorem left_distrib (a b c : ℕ → R) :
    CauchyProduct a (b + c) = CauchyProduct a b + CauchyProduct a c := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.add_right a b c

/-- Right distributivity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.12). -/
theorem right_distrib (a b c : ℕ → R) :
    CauchyProduct (a + b) c = CauchyProduct a c + CauchyProduct b c := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.add_left a b c

/-- The zero sequence is a left zero of the Cauchy product. -/
theorem zero_mul (a : ℕ → R) : CauchyProduct 0 a = 0 := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using
    finiteAddConvolution.zero_left MulZeroClass.zero_mul a

/-- The zero sequence is a right zero of the Cauchy product. -/
theorem mul_zero (a : ℕ → R) : CauchyProduct a 0 = 0 := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using
    finiteAddConvolution.zero_right MulZeroClass.mul_zero a

/-- Left identity for Cauchy product.

Ref: Def. 7.4.1 (unit element). -/
theorem one_mul (a : ℕ → R) : CauchyProduct one a = a :=
  toPowerSeries_injective <| by rw [toPowerSeries_mul, toPowerSeries_one, _root_.one_mul]

/-- Right identity for Cauchy product.

Ref: Def. 7.4.1 (unit element). -/
theorem mul_one (a : ℕ → R) : CauchyProduct a one = a :=
  toPowerSeries_injective <| by rw [toPowerSeries_mul, toPowerSeries_one, _root_.mul_one]

/-- Scalar compatibility on the left.

Ref: Def. 7.4.1, Eq. (7.13). -/
theorem smul_mul (c : R) (a b : ℕ → R) :
    CauchyProduct (c • a) b = c • CauchyProduct a b := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.smul_left c a b

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Commutativity of Cauchy product.

Ref: Thm. 7.4.4 and Cor. 7.4.5. -/
theorem comm (a b : ℕ → R) : CauchyProduct a b = CauchyProduct b a := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.comm a b

/-- Scalar compatibility on the right.

Ref: Def. 7.4.1, Eq. (7.13). -/
theorem mul_smul (c : R) (a b : ℕ → R) :
    CauchyProduct a (c • b) = c • CauchyProduct a b := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.smul_right c a b

end CommSemiring

section Semiring

variable [Semiring R]

/-! ### Atom, support and finite Toeplitz formulas -/

/-- The unit sequence is the atom `Pi.single 0 1`. -/
theorem one_eq_single : (one : ℕ → R) = Pi.single 0 1 :=
  funext fun n => (Pi.single_apply 0 1 n).symm

/-- Two-atom rule: the Cauchy product of two atoms is the atom at the summed index,
with the ordered product of the values. -/
theorem single_mul_single (i j : ℕ) (a b : R) :
    CauchyProduct (Pi.single i a) (Pi.single j b) = Pi.single (i + j) (a * b) := by
  simpa only [CauchyProduct_eq_finiteAddConvolution] using
    finiteAddConvolution.single_single MulZeroClass.zero_mul MulZeroClass.mul_zero i j a b

/-- If `a` and `b` vanish above `M`, their Cauchy product vanishes above `2 * M`. -/
theorem zero_of_support {a b : ℕ → R} {M : ℕ}
    (ha : ∀ n, M < n → a n = 0) (hb : ∀ n, M < n → b n = 0)
    (n : ℕ) (hn : 2 * M < n) :
    CauchyProduct a b n = 0 := by
  refine Finset.sum_eq_zero fun ⟨k, l⟩ hkl => ?_
  have hkl := Finset.mem_antidiagonal.mp hkl
  by_cases hk : M < k
  · simp [ha k hk]
  · simp [hb l (by omega)]

/-- If `a` vanishes above `N < n`, the `n`-th coefficient of `a ⋆ h` splits into the `k = 0`
term and a sum over `Icc 1 N`. -/
theorem apply_of_support_le_split {a h : ℕ → R} {N n : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hn : N < n) :
    CauchyProduct a h n = a 0 * h n + ∑ k ∈ Finset.Icc 1 N, a k * h (n - k) := by
  rw [apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * h l)]
  refine (Finset.sum_subset
    (Finset.range_mono (show N + 1 ≤ n + 1 by omega)) ?_).symm.trans ?_
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [ha k (by omega), MulZeroClass.zero_mul]
  · rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N),
      Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc, Nat.sub_zero]

/-- CauchyProduct as `Fin (N+1)`-indexed sum (Toeplitz form).

For `n ≤ N`, the antidiagonal sum `Σ_{k+l=n} f(k) * g(l)` can be rewritten as
a `Fin (N+1)`-indexed sum: `Σ_{p : Fin (N+1)} (if p ≤ n then f(n-p) else 0) * g(p)`.
Since all `l ≤ n ≤ N`, the `Fin (N+1)` range captures every antidiagonal pair.

This form matches `Matrix.mulVec` of a lower-triangular Toeplitz matrix built from `f`.
Used in `toSeq_fderiv_evalInBanach` (and through it in `ivp_hDF_block_nat`) to connect
the Cauchy product (from `fderiv_evalInBanach`) to Jacobian matrix entries. -/
lemma eq_sum_fin {N : ℕ} (f g : ℕ → R) {n : ℕ} (hn : n ≤ N) :
    CauchyProduct f g n =
      ∑ p : Fin (N + 1), (if (p : ℕ) ≤ n then f (n - (p : ℕ)) else 0) * g p := by
  rw [apply_range, Fin.sum_univ_eq_sum_range
    (fun j => (if j ≤ n then f (n - j) else 0) * g j)]
  simp_rw [ite_mul, MulZeroClass.zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- CauchyProduct with a Kronecker delta: `δ₀ · r ∗ f = r · f`.
Scalar multiplication in the power series ring. -/
@[simp] lemma delta_left (r : R) (f : ℕ → R) (n : ℕ) :
    CauchyProduct (fun k => if k = 0 then r else 0) f n = r * f n := by
  simpa only [CauchyProduct, PowerSeries.coeff_mul, PowerSeries.coeff_C,
    PowerSeries.coeff_mk] using PowerSeries.coeff_C_mul n (PowerSeries.mk f) r

/-- CauchyProduct with a Kronecker delta on the right: `f ∗ δ₀ · r = f · r`. -/
@[simp] lemma delta_right (f : ℕ → R) (r : R) (n : ℕ) :
    CauchyProduct f (fun k => if k = 0 then r else 0) n = f n * r := by
  simp [apply_range, mul_ite]

end Semiring

/-- Cauchy product commutes with ring homomorphisms. -/
lemma map_CauchyProduct {S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (a b : ℕ → R) (n : ℕ) :
    CauchyProduct (f ∘ a) (f ∘ b) n = f (CauchyProduct a b n) := by
  simp [CauchyProduct]

end CauchyProduct

end Generic

end RadiiPolynomial
