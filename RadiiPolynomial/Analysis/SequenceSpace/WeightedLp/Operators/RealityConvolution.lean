import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reality
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Convolution

/-!
# The conjugate reflection and the row-bounded product

On a commutative index `M` and `X = WeightedLp M (WeightedScalar ℂ w) 2` with
`hw : ∀ n, w (-n) = w n`, the conjugate reflection `conjReflL hw` of `Operators/Reality.lean`
commutes with the row-bounded product `convCLM` of `WeightedLp/Convolution.lean`:
`K (x ⋆ y) = K x ⋆ K y` (`conjReflL_convCLM`).

This is the one face of the reflection that needs a product on `X` (a `RowBound` and an additive
commutative index). The carrier faces (involution, isometry, fixed points, the real subspace, the
restriction and the diagonal, projection and finite-matrix commutations) stay in `Reality`, which
does not import the convolution; this module joins the two.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Product

variable {M : Type*} [AddCommGroup M] {w : M → ℝ} [PosWeight w] (hw : ∀ n, w (-n) = w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- On a commutative index the product commutes with `K`:
`K (x ⋆ y) = K x ⋆ K y`. Both fibre sums are reindexed over `M` (`addFiberEquiv`), the left one
also by `i ↦ -i`; no summability is needed. -/
theorem conjReflL_convCLM {K : ℝ}
    (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 K) (x y : X) :
    conjReflL hw (convCLM h x y) = convCLM h (conjReflL hw x) (conjReflL hw y) :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_convCLM, coeff_convCLM, DiscreteConvolution.addRingConvolution_apply,
      DiscreteConvolution.addRingConvolution_apply,
      ← (DiscreteConvolution.addFiberEquiv (-n)).tsum_eq,
      ← (DiscreteConvolution.addFiberEquiv n).tsum_eq, Complex.conj_tsum,
      ← (Equiv.neg M).tsum_eq, Equiv.neg_apply]
    exact tsum_congr fun i => by
      show starRingEnd ℂ (coeff x (-n - -i) * coeff y (-i)) =
        coeff (conjReflL hw x) (n - i) * coeff (conjReflL hw y) i
      rw [map_mul, coeff_conjReflL, coeff_conjReflL, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

end Product

end RadiiPolynomial.WeightedLp

end
