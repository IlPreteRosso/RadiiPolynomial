import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.Algebra.Convolution.Finite

/-!
# Cauchy product of natural-index sequences

This module defines the finite-sum Cauchy product over a semiring and its coefficient
formulas. `cauchyProduct_eq_finiteAddConvolution` identifies it with finite-fiber convolution
on the additive index `ℕ`; the operation keeps coefficient multiplication in its original order.
The retained API includes the range-sum formula, scalar multiplication in the first
input, finite-support splitting, finite sums, and the coefficient-map law `map_cauchyProduct`.

`toPowerSeries` is the coefficient view into formal power series, with
`coeff_toPowerSeries`. The additional algebraic laws and power-series compatibility are
owned by the finite-fiber and power-series recovery records. This module does not provide
a bundled `toPowerSeriesLinearEquiv`. Raw sequence multiplication remains pointwise.
-/

open scoped BigOperators

namespace RadiiPolynomial

section Generic

variable {R : Type*}

/-- Cauchy product (convolution) of sequences:
`(a ⋆ b)_n = ∑_{k+l=n} a_k b_l`.

Ref: Def. 7.4.2, Eq. (7.15). -/
def cauchyProduct [Semiring R] (a b : ℕ → R) : ℕ → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2


/-- The Cauchy product is the finite-fiber convolution over the additive index `ℕ`. -/
theorem cauchyProduct_eq_finiteAddConvolution [Semiring R] (a b : ℕ → R) :
    cauchyProduct a b = finiteAddConvolution a b := rfl

namespace cauchyProduct


section Semiring

variable [Semiring R]

/-- Application of the Cauchy product: the antidiagonal sum. -/
theorem apply (a b : ℕ → R) (n : ℕ) :
    cauchyProduct a b n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-- The Cauchy product as a sum over `range (n + 1)`, `∑ j, a (n - j) * b j`. -/
theorem apply_range (a b : ℕ → R) (n : ℕ) :
    cauchyProduct a b n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  rw [apply, ← Finset.Nat.sum_antidiagonal_swap (f := fun p => a p.1 * b p.2)]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a j * b i) n



end Semiring

/-! ### The bridge to formal power series -/

section ToPowerSeries

/-- Bridge object: the sequence `a : ℕ → R` as a formal power series. -/
def toPowerSeries (a : ℕ → R) : PowerSeries R := PowerSeries.mk a


section LinearEquiv

variable (S : Type*) [Semiring S] [AddCommMonoid R] [Module S R]


variable {S}



end LinearEquiv

variable [Semiring R]

/-- The coefficients of `toPowerSeries a` are the entries of `a`. -/
@[simp] theorem coeff_toPowerSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := PowerSeries.coeff_mk n a







end ToPowerSeries

section Semiring

variable [Semiring R]

/-! ### Algebraic laws

Specializations of the finite-fiber convolution laws (`finiteAddConvolution`), except the unit
laws, which are transported along the power-series bridge. -/








/-- Scalar compatibility on the left.

Ref: Def. 7.4.1, Eq. (7.13). -/
theorem smul_mul (c : R) (a b : ℕ → R) :
    cauchyProduct (c • a) b = c • cauchyProduct a b := by
  simpa only [cauchyProduct_eq_finiteAddConvolution] using finiteAddConvolution.smul_left c a b

end Semiring

section CommSemiring

variable [CommSemiring R]



end CommSemiring

section Semiring

variable [Semiring R]

/-! ### Atom, support and finite Toeplitz formulas -/




/-- If `a` vanishes above `N < n`, the `n`-th coefficient of `a ⋆ h` splits into the `k = 0`
term and a sum over `Icc 1 N`. -/
theorem apply_of_support_le_split {a h : ℕ → R} {N n : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hn : N < n) :
    cauchyProduct a h n = a 0 * h n + ∑ k ∈ Finset.Icc 1 N, a k * h (n - k) := by
  rw [apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * h l)]
  refine (Finset.sum_subset
    (Finset.range_mono (show N + 1 ≤ n + 1 by omega)) ?_).symm.trans ?_
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [ha k (by omega), MulZeroClass.zero_mul]
  · rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N),
      Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc, Nat.sub_zero]

/-- `cauchyProduct` as a `Fin (N+1)`-indexed sum (Toeplitz form).

For `n ≤ N`, the antidiagonal sum `Σ_{k+l=n} f(k) * g(l)` can be rewritten as
a `Fin (N+1)`-indexed sum: `Σ_{p : Fin (N+1)} (if p ≤ n then f(n-p) else 0) * g(p)`.
Since all `l ≤ n ≤ N`, the `Fin (N+1)` range captures every antidiagonal pair.

This form matches `Matrix.mulVec` of a lower-triangular Toeplitz matrix built from `f`.
Used in `MvPolyBridge.toSeq_fderiv_aeval` (and through it in `ivp_hDF_block_nat`) to connect
the Cauchy product (from `MvPolyBridge.fderiv_aeval`) to Jacobian matrix entries. -/
lemma eq_sum_fin {N : ℕ} (f g : ℕ → R) {n : ℕ} (hn : n ≤ N) :
    cauchyProduct f g n =
      ∑ p : Fin (N + 1), (if (p : ℕ) ≤ n then f (n - (p : ℕ)) else 0) * g p := by
  rw [apply_range, Fin.sum_univ_eq_sum_range
    (fun j => (if j ≤ n then f (n - j) else 0) * g j)]
  simp_rw [ite_mul, MulZeroClass.zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega



end Semiring

/-- Cauchy product commutes with ring homomorphisms. -/
lemma map_cauchyProduct {S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (a b : ℕ → R) (n : ℕ) :
    cauchyProduct (f ∘ a) (f ∘ b) n = f (cauchyProduct a b n) := by
  simp [cauchyProduct]

end cauchyProduct

end Generic

end RadiiPolynomial
