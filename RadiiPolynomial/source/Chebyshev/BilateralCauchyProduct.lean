import RadiiPolynomial.source.lpSpace.DiscreteConvolution

/-!
# Bilateral Cauchy Product (ℤ-indexed convolution)

The bilateral Cauchy product is `DiscreteConvolution.addRingConvolution` on `ℤ → ℝ`:
`(a * b)_k = ∑' (j, l) ∈ addFiber k, a_j * b_l = ∑' j, a_j * b_{k-j}`.

This is the product in the group algebra `ℓ¹(ℤ)`, used for Chebyshev series
multiplication (Chapter 14).

We provide a thin abbreviation and the key properties (identity, commutativity)
that follow from the general `DiscreteConvolution` framework.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

/-- Bilateral Cauchy product = additive ring convolution on ℤ. -/
abbrev BilateralCauchyProduct (a b : ℤ → ℝ) : ℤ → ℝ :=
  DiscreteConvolution.addRingConvolution a b

namespace BilateralCauchyProduct

/-- Multiplicative identity: Kronecker delta at 0. -/
def one : ℤ → ℝ := fun k => if k = 0 then 1 else 0

@[simp] lemma one_zero : one 0 = 1 := rfl
@[simp] lemma one_ne_zero {k : ℤ} (hk : k ≠ 0) : one k = 0 := if_neg hk

end BilateralCauchyProduct

end RadiiPolynomial
