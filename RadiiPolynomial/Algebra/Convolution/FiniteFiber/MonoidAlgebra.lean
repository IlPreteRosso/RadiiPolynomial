import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import RadiiPolynomial.Algebra.Convolution.FiniteFiber

/-!
# The monoid algebra inside the finite-fiber convolution algebra

Let `M` be a monoid in which every element has only finitely many factorizations
(`Finset.HasMulAntidiagonal M`). The monoid algebra `MonoidAlgebra R M` consists of the
*finitely supported* functions `M → R` with the convolution product, while the finite-fiber
convolution algebra `RadiiPolynomial.FiniteFiberConvolution M R` consists of *all* functions
`M → R` with the same product formula. This file shows that the first sits inside the second as
the subsemiring of finitely supported elements.

This is a statement about indices with finite fibers only. For an arbitrary monoid the
convolution of two functions of infinite support is an infinite sum, and nothing here concerns
that case.

## Main definitions

* `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebra R M`: the ring homomorphism
  `MonoidAlgebra R M →+* FiniteFiberConvolution M R` that keeps every coefficient.
* `RadiiPolynomial.FiniteFiberConvolution.toMonoidAlgebra`: the finitely supported element of the
  monoid algebra with the coefficients of a finitely supported `f`.
* `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebraEquivRangeS R M`: the ring isomorphism
  between `MonoidAlgebra R M` and the range of `ofMonoidAlgebra R M`; its inverse is
  `toMonoidAlgebra`.

The additive-index twins `RadiiPolynomial.FiniteFiberAddConvolution.ofAddMonoidAlgebra`,
`RadiiPolynomial.FiniteFiberAddConvolution.toAddMonoidAlgebra` and
`RadiiPolynomial.FiniteFiberAddConvolution.ofAddMonoidAlgebraEquivRangeS` relate
`AddMonoidAlgebra R M` and `RadiiPolynomial.FiniteFiberAddConvolution M R`.

## Main results

* `RadiiPolynomial.FiniteFiberConvolution.coeff_ofMonoidAlgebra`: the coefficients are kept.
* `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebra_single`: atoms go to atoms.
* `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebra_injective`: the map is injective.
* `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebra_smul`: the map commutes with external
  scalars.
* `RadiiPolynomial.FiniteFiberConvolution.mem_rangeS_ofMonoidAlgebra`: an element lies in the range
  if and only if its coefficients have finite support.

## Implementation notes

The map is not surjective in general. On the additive index `ℕ` with integer coefficients, the
function with every coefficient equal to `1` has infinite support, so it is not in the range. The
map is surjective when `M` is finite, since every support is then finite, and also when `R` has
only one element. No theorem of this file asserts surjectivity; the regression tests check these
cases.

The range is the `RingHom.rangeS` of `ofMonoidAlgebra R M`, characterized by
`mem_rangeS_ofMonoidAlgebra`. No second finite-support subsemiring is defined, so there is only
one closure argument. This needs only a semiring of coefficients. A `Subring` version would need
a ring of coefficients and is not provided.

`ofMonoidAlgebra` reads the coefficients through `MonoidAlgebra.coeff` and the coercion of
`M →₀ R` to a function. Its multiplicativity is `MonoidAlgebra.coeff_mul_antidiag` at the fiber
`Finset.mulAntidiagonal m`, compared with
`RadiiPolynomial.FiniteFiberConvolution.coeff_mul`. The inverse `toMonoidAlgebra` is built with
`Finsupp.ofSupportFinite` and `MonoidAlgebra.ofCoeff`; it is `noncomputable` because
`Finsupp.ofSupportFinite` is. The isomorphism `ofMonoidAlgebraEquivRangeS` is assembled directly
from `RingHom.rangeSRestrict` and this inverse, so that `ofMonoidAlgebraEquivRangeS_symm_apply`
holds by `rfl`. (`RingEquiv.ofLeftInverseS` would need an inverse defined on all elements, while
`toMonoidAlgebra` needs a proof of finite support.)

Only the external scalars of the coefficients are compared here (`ofMonoidAlgebra_smul`). An
`AlgHom` version would need matching `Algebra` structures on both sides and is not provided.
-/

open Finset

universe u v w

namespace RadiiPolynomial

namespace FiniteFiberConvolution

variable {R : Type v} {M : Type u}

/-! ### The finitely supported inverse -/

section ToMonoidAlgebra

variable [Semiring R]

/-- The element of the monoid algebra with the coefficients of `f`, whose support is finite by
`hf`: `MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => coeff m f) hf)`. -/
@[to_additive (dont_translate := R)
  /-- The element of the additive monoid algebra with the coefficients of `f`, whose support is
  finite by `hf`: `AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => coeff m f) hf)`.
  -/]
noncomputable def toMonoidAlgebra (f : FiniteFiberConvolution M R)
    (hf : (Function.support fun m => coeff m f).Finite) : MonoidAlgebra R M :=
  MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => coeff m f) hf)

/-- The coefficients of `toMonoidAlgebra f hf` are those of `f`. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- The coefficients of `toAddMonoidAlgebra f hf` are those of `f`. -/]
theorem coeff_toMonoidAlgebra (f : FiniteFiberConvolution M R)
    (hf : (Function.support fun m => coeff m f).Finite) (m : M) :
    (toMonoidAlgebra f hf).coeff m = coeff m f :=
  rfl

end ToMonoidAlgebra

/-! ### The ring homomorphism -/

section OfMonoidAlgebra

variable (R M) [Semiring R] [Monoid M] [HasMulAntidiagonal M] [DecidableEq M]

/-- The monoid algebra `MonoidAlgebra R M` maps into the finite-fiber convolution algebra by
keeping every coefficient: `x ↦ ofFun ⇑x.coeff`. It is an injective ring homomorphism whose
range is the set of finitely supported elements (`mem_rangeS_ofMonoidAlgebra`); it is not
surjective in general. -/
@[to_additive (dont_translate := R)
  /-- The additive monoid algebra `AddMonoidAlgebra R M` maps into the additive-index
  finite-fiber convolution algebra by keeping every coefficient: `x ↦ ofFun ⇑x.coeff`. It is an
  injective ring homomorphism whose range is the set of finitely supported elements
  (`mem_rangeS_ofAddMonoidAlgebra`); it is not surjective in general. -/]
def ofMonoidAlgebra : MonoidAlgebra R M →+* FiniteFiberConvolution M R where
  toFun x := ofFun ⇑x.coeff
  map_one' := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_eq_pi_single]
    rfl
  map_mul' x y := ext fun m => by
    rw [coeff_ofFun, coeff_mul]
    exact MonoidAlgebra.coeff_mul_antidiag x y m _ mem_mulAntidiagonal
  map_zero' := rfl
  map_add' _ _ := rfl

variable {R M}

/-- `ofMonoidAlgebra R M x` is `ofFun ⇑x.coeff`. -/
@[to_additive (dont_translate := R)
  /-- `ofAddMonoidAlgebra R M x` is `ofFun ⇑x.coeff`. -/]
theorem ofMonoidAlgebra_apply (x : MonoidAlgebra R M) :
    ofMonoidAlgebra R M x = ofFun ⇑x.coeff :=
  rfl

/-- The coefficients of `ofMonoidAlgebra R M x` are those of `x`. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- The coefficients of `ofAddMonoidAlgebra R M x` are those of `x`. -/]
theorem coeff_ofMonoidAlgebra (x : MonoidAlgebra R M) (m : M) :
    coeff m (ofMonoidAlgebra R M x) = x.coeff m :=
  rfl

/-- `ofMonoidAlgebra` sends the atom `MonoidAlgebra.single m r` to the atom `single m r`. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- `ofAddMonoidAlgebra` sends the atom `AddMonoidAlgebra.single m r` to the atom
  `single m r`. -/]
theorem ofMonoidAlgebra_single (m : M) (r : R) :
    ofMonoidAlgebra R M (MonoidAlgebra.single m r) = single m r := by
  rw [ofMonoidAlgebra_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_pi_single]
  rfl

/-- `ofMonoidAlgebra` is injective: an element of the monoid algebra is determined by its
coefficients. -/
@[to_additive (dont_translate := R)
  /-- `ofAddMonoidAlgebra` is injective: an element of the additive monoid algebra is
  determined by its coefficients. -/]
theorem ofMonoidAlgebra_injective : Function.Injective (ofMonoidAlgebra R M) :=
  fun _ _ h => MonoidAlgebra.coeff_injective (DFunLike.coe_injective (congrArg toFun h))

/-- `ofMonoidAlgebra` commutes with external scalars acting on the coefficients. -/
@[to_additive (attr := simp) (dont_translate := S R) ofAddMonoidAlgebra_smul
  /-- `ofAddMonoidAlgebra` commutes with external scalars acting on the coefficients. -/]
theorem ofMonoidAlgebra_smul {S : Type w} [SMulZeroClass S R] (s : S) (x : MonoidAlgebra R M) :
    ofMonoidAlgebra R M (s • x) = s • ofMonoidAlgebra R M x :=
  rfl

/-- `ofMonoidAlgebra` is a left inverse of `toMonoidAlgebra`: it recovers `f`. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- `ofAddMonoidAlgebra` is a left inverse of `toAddMonoidAlgebra`: it recovers `f`. -/]
theorem ofMonoidAlgebra_toMonoidAlgebra (f : FiniteFiberConvolution M R)
    (hf : (Function.support fun m => coeff m f).Finite) :
    ofMonoidAlgebra R M (toMonoidAlgebra f hf) = f :=
  rfl

/-- `toMonoidAlgebra` is a left inverse of `ofMonoidAlgebra`, for any proof of finite
support. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- `toAddMonoidAlgebra` is a left inverse of `ofAddMonoidAlgebra`, for any proof of finite
  support. -/]
theorem toMonoidAlgebra_ofMonoidAlgebra (x : MonoidAlgebra R M)
    (hx : (Function.support fun m => coeff m (ofMonoidAlgebra R M x)).Finite) :
    toMonoidAlgebra (ofMonoidAlgebra R M x) hx = x :=
  MonoidAlgebra.ext (Finsupp.ext fun _ => rfl)

/-! ### The range: the finitely supported elements -/

/-- An element of the finite-fiber convolution algebra lies in the range of `ofMonoidAlgebra`
if and only if its coefficients have finite support. -/
@[to_additive (dont_translate := R)
  /-- An element of the additive-index finite-fiber convolution algebra lies in the range of
  `ofAddMonoidAlgebra` if and only if its coefficients have finite support. -/]
theorem mem_rangeS_ofMonoidAlgebra {f : FiniteFiberConvolution M R} :
    f ∈ (ofMonoidAlgebra R M).rangeS ↔ (Function.support fun m => coeff m f).Finite := by
  refine ⟨?_, fun hf => ⟨toMonoidAlgebra f hf, ofMonoidAlgebra_toMonoidAlgebra f hf⟩⟩
  rintro ⟨x, rfl⟩
  exact x.coeff.hasFiniteSupport

variable (R M)

/-- The monoid algebra is isomorphic, as a semiring, to the range of `ofMonoidAlgebra`, the
finitely supported elements of the finite-fiber convolution algebra. The map is
`(ofMonoidAlgebra R M).rangeSRestrict`, and the inverse is `toMonoidAlgebra`. -/
@[to_additive (dont_translate := R)
  /-- The additive monoid algebra is isomorphic, as a semiring, to the range of
  `ofAddMonoidAlgebra`, the finitely supported elements of the additive-index finite-fiber
  convolution algebra. The map is `(ofAddMonoidAlgebra R M).rangeSRestrict`, and the inverse is
  `toAddMonoidAlgebra`. -/]
noncomputable def ofMonoidAlgebraEquivRangeS :
    MonoidAlgebra R M ≃+* (ofMonoidAlgebra R M).rangeS where
  toFun := (ofMonoidAlgebra R M).rangeSRestrict
  invFun f := toMonoidAlgebra f.1 (mem_rangeS_ofMonoidAlgebra.mp f.2)
  left_inv x := toMonoidAlgebra_ofMonoidAlgebra x _
  right_inv f := Subtype.ext (ofMonoidAlgebra_toMonoidAlgebra f.1 _)
  map_mul' := map_mul _
  map_add' := map_add _

variable {R M}

/-- The isomorphism `ofMonoidAlgebraEquivRangeS` is `ofMonoidAlgebra`, with values in the
range. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- The isomorphism `ofAddMonoidAlgebraEquivRangeS` is `ofAddMonoidAlgebra`, with values in
  the range. -/]
theorem ofMonoidAlgebraEquivRangeS_apply (x : MonoidAlgebra R M) :
    (ofMonoidAlgebraEquivRangeS R M x : FiniteFiberConvolution M R) = ofMonoidAlgebra R M x :=
  rfl

/-- The inverse of `ofMonoidAlgebraEquivRangeS` is `toMonoidAlgebra`, that is
`MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => coeff m f) _)`. -/
@[to_additive (attr := simp) (dont_translate := R)
  /-- The inverse of `ofAddMonoidAlgebraEquivRangeS` is `toAddMonoidAlgebra`, that is
  `AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => coeff m f) _)`. -/]
theorem ofMonoidAlgebraEquivRangeS_symm_apply (f : (ofMonoidAlgebra R M).rangeS) :
    (ofMonoidAlgebraEquivRangeS R M).symm f =
      toMonoidAlgebra (f : FiniteFiberConvolution M R) (mem_rangeS_ofMonoidAlgebra.mp f.2) :=
  rfl

end OfMonoidAlgebra

end FiniteFiberConvolution

end RadiiPolynomial
