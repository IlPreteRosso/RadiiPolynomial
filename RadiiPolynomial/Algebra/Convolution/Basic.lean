import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# Discrete convolution over monoids

The discrete convolution of functions on a monoid `M` is provided by Mathlib's
`Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution`. The value of `f ⋆[L] g` at `x` is
the unconditional sum of `L (f a) (g b)` over the multiplication fiber
`DiscreteConvolution.mulFiber x = {(a, b) | a * b = x}`, and the ring convolution `f ⋆ᵣ g`
combines the values by multiplication. The additive-index versions `addFiber`, `⋆₊[L]` and `⋆ᵣ₊`
sum over the fibers of addition. This file imports that module and adds one construction that
needs inverses in the index.

## Main definitions

* `RadiiPolynomial.DiscreteConvolution.mulFiberEquiv x`: for a group `M`, the fiber
  `mulFiber x` is parametrized by its second coordinate, `i ↦ (x / i, i)`.
* `RadiiPolynomial.DiscreteConvolution.addFiberEquiv x`: for an additive group, the fiber
  `addFiber x` is parametrized by `i ↦ (x - i, i)`.

## Implementation notes

The library's extensions of the convolution API live in the namespace
`RadiiPolynomial.DiscreteConvolution`, apart from Mathlib's namespace `DiscreteConvolution`.
The few Mathlib names used below are opened by name, outside any namespace; they resolve to the
Mathlib constants because no declaration under `RadiiPolynomial` carries these short names.
-/

open DiscreteConvolution (mulFiber mem_mulFiber)

namespace RadiiPolynomial.DiscreteConvolution

variable {M : Type*}

/-! ### Fibers over a group index -/

/-- For a group index, the fiber of multiplication at `x` is parametrized by its second
coordinate: `i ↦ (x / i, i)`. -/
@[to_additive /-- For an additive group index, the fiber of addition at `x` is parametrized by
its second coordinate: `i ↦ (x - i, i)`. -/]
def mulFiberEquiv [Group M] (x : M) : M ≃ mulFiber x where
  toFun i := ⟨(x / i, i), mem_mulFiber.mpr (div_mul_cancel x i)⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv := fun ⟨⟨a, b⟩, hab⟩ =>
    Subtype.ext (show (x / b, b) = (a, b) by
      rw [div_eq_iff_eq_mul.mpr (mem_mulFiber.mp hab).symm])

end RadiiPolynomial.DiscreteConvolution
