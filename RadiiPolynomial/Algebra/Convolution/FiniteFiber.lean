import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Pi
import RadiiPolynomial.Algebra.Convolution.Finite

/-!
# The finite-fiber convolution algebra of all functions

Let `M` be an index type with a multiplication in which every element has only finitely many
factorizations (`Finset.HasMulAntidiagonal M`). The finite-fiber convolution
`RadiiPolynomial.finiteMulConvolution` is then defined on *all* functions `M → R`, with no support
or summability condition. This file packages it as the multiplication of a type synonym, so that the
pointwise multiplication of `M → R` and the convolution multiplication never meet on one type.

The phrase "finite fiber" describes the index operation: each fiber
`Finset.mulAntidiagonal m` is finite. It says nothing about the support of the coefficients, and
the carrier holds every function `M → R`. No norm or topology is placed on it.

## Main definitions

* `RadiiPolynomial.FiniteFiberConvolution M R`: the type synonym of `M → R` carrying the
  convolution multiplication over a multiplicative index.
* `RadiiPolynomial.FiniteFiberAddConvolution M R`: its additive-index twin, the synonym of
  `M → R` carrying `RadiiPolynomial.finiteAddConvolution`. Only the index operation is additive;
  the coefficients are still multiplied, and the unit is the atom at index `0` with value `1`.
* `RadiiPolynomial.FiniteFiberConvolution.ofFun`, `RadiiPolynomial.FiniteFiberConvolution.toFun`:
  the identity equivalences between `M → R` and the synonym.
* `RadiiPolynomial.FiniteFiberConvolution.coeff`: the coefficient of an element at an index, the
  canonical computation face.
* `RadiiPolynomial.FiniteFiberConvolution.single`: the atom with one nonzero coefficient.

## Main results

* Pointwise `Zero`, `Add`, `Neg`, `Sub`, `SMul`, `AddCommMonoid`, `AddCommGroup` and `Module`
  instances, each under the coefficient class it uses and with no index hypothesis.
* Convolution `Mul` and unit `One := single 1 1`, and the semiring and ring branches
  (`NonUnitalNonAssocSemiring` through `CommRing`), each under the index and coefficient
  structure its laws use; `Finset.HasMulAntidiagonal M` is explicit on every branch.
* `RadiiPolynomial.FiniteFiberConvolution.instIsScalarTower`,
  `RadiiPolynomial.FiniteFiberConvolution.instSMulCommClass` and
  `RadiiPolynomial.FiniteFiberConvolution.instAlgebra`: external scalars.
* `RadiiPolynomial.FiniteFiberConvolution.coeff_mul`: the coefficient of a product is the finite
  sum over the fiber.
* `RadiiPolynomial.FiniteFiberConvolution.coeff_single_one_mul`,
  `RadiiPolynomial.FiniteFiberConvolution.coeff_mul_single_one`: an atom at the index unit
  multiplies every coefficient of an arbitrary element.
* `RadiiPolynomial.FiniteFiberConvolution.ext`: two elements are equal when all their
  coefficients are.

## Implementation notes

The carrier is a `def` synonym of `M → R` rather than a structure, following
`MvPowerSeries`. Instance resolution does not unfold it, so the pointwise `Mul` of `M → R` is
not available on the synonym, and the convolution `Mul` is never registered on `M → R`. The
carrier itself needs no class: every instance states only the classes its data and laws use.

The carriers `FiniteFiberConvolution` and `FiniteFiberAddConvolution` are linked by
`to_additive` and tagged `to_additive_dont_translate`, as `Monoid.End` is: when a declaration is
translated, only the index operation changes. The multiplication, the unit `1`, the coefficient
operations and external scalars of the carrier keep their names.

`coeff` is the canonical computation face; `ofFun` and `toFun` are the two inverse carrier views.
There is no `CoeFun` instance, so that the coefficients have one interface.

The unital instances take `[DecidableEq M]`, which `single 1 1` needs; no classical unit is
provided. Extensionality is by all coefficients. In particular the centrality of `algebraMap` is
proved coefficientwise for an arbitrary element (`coeff_single_one_mul`,
`coeff_mul_single_one`), not from its values on atoms: on an infinite index an element need not
be a finite sum of atoms.

No declaration is marked `noncomputable`. `Finset.HasMulAntidiagonal` supplies the fibers as
data, so whether a product can be evaluated depends on that instance.
-/

open Finset

universe u v w

namespace RadiiPolynomial

/-- The finite-fiber convolution algebra over a multiplicative index: a type synonym of *all*
functions `M → R`, with the multiplication `RadiiPolynomial.finiteMulConvolution`.

"Finite fiber" refers to the index multiplication (`Finset.HasMulAntidiagonal M`), not to the
support of the coefficients. The synonym needs no class to be formed; each operation states its
own hypotheses. -/
@[to_additive FiniteFiberAddConvolution
  /-- The finite-fiber convolution algebra over an additive index: a type synonym of *all*
  functions `M → R`, with the multiplication `RadiiPolynomial.finiteAddConvolution`. Only the
  index operation is additive; the coefficients are multiplied.

  "Finite fiber" refers to the index addition (`Finset.HasAntidiagonal M`), not to the support of
  the coefficients. The synonym needs no class to be formed; each operation states its own
  hypotheses. -/,
  to_additive_dont_translate]
def FiniteFiberConvolution (M : Type u) (R : Type v) : Type (max u v) := M → R

namespace FiniteFiberConvolution

variable {M : Type u} {R : Type v} {S : Type w}

/-! ### The carrier views -/

section Carrier

/-- View a function `M → R` as an element of the convolution algebra. -/
@[to_additive /-- View a function `M → R` as an element of the convolution algebra. -/]
def ofFun : (M → R) ≃ FiniteFiberConvolution M R := Equiv.refl _

/-- The function `M → R` underlying an element of the convolution algebra. -/
@[to_additive /-- The function `M → R` underlying an element of the convolution algebra. -/]
def toFun : FiniteFiberConvolution M R ≃ (M → R) := ofFun.symm

/-- The coefficient of `f` at the index `m`. -/
@[to_additive /-- The coefficient of `f` at the index `m`. -/]
def coeff (m : M) (f : FiniteFiberConvolution M R) : R := toFun f m

/-- The inverse of `ofFun` is `toFun`. -/
@[to_additive (attr := simp) /-- The inverse of `ofFun` is `toFun`. -/]
theorem ofFun_symm : (ofFun : (M → R) ≃ FiniteFiberConvolution M R).symm = toFun := rfl

/-- The inverse of `toFun` is `ofFun`. -/
@[to_additive (attr := simp) /-- The inverse of `toFun` is `ofFun`. -/]
theorem toFun_symm : (toFun : FiniteFiberConvolution M R ≃ (M → R)).symm = ofFun := rfl

/-- `toFun` undoes `ofFun`. -/
@[to_additive (attr := simp) /-- `toFun` undoes `ofFun`. -/]
theorem toFun_ofFun (a : M → R) : toFun (ofFun a) = a := rfl

/-- `ofFun` undoes `toFun`. -/
@[to_additive (attr := simp) /-- `ofFun` undoes `toFun`. -/]
theorem ofFun_toFun (f : FiniteFiberConvolution M R) : ofFun (toFun f) = f := rfl

/-- The coefficients of `ofFun a` are the values of `a`. -/
@[to_additive (attr := simp) /-- The coefficients of `ofFun a` are the values of `a`. -/]
theorem coeff_ofFun (a : M → R) (m : M) : coeff m (ofFun a) = a m := rfl

/-- The values of `toFun f` are the coefficients of `f`. -/
@[to_additive (attr := simp) /-- The values of `toFun f` are the coefficients of `f`. -/]
theorem toFun_apply (f : FiniteFiberConvolution M R) (m : M) : toFun f m = coeff m f := rfl

/-- Two elements are equal when all their coefficients are. -/
@[to_additive (attr := ext) /-- Two elements are equal when all their coefficients are. -/]
theorem ext {f g : FiniteFiberConvolution M R} (h : ∀ m, coeff m f = coeff m g) : f = g :=
  toFun.injective (funext h)

/-- Two elements are equal if and only if all their coefficients are. -/
add_decl_doc FiniteFiberConvolution.ext_iff

/-- Two elements are equal if and only if all their coefficients are. -/
add_decl_doc FiniteFiberAddConvolution.ext_iff

/-- The atom `single m r`: the coefficient `r` at the index `m`, and `0` elsewhere. -/
@[to_additive
  /-- The atom `single m r`: the coefficient `r` at the index `m`, and `0` elsewhere. -/]
def single [DecidableEq M] [Zero R] (m : M) (r : R) : FiniteFiberConvolution M R :=
  ofFun (Pi.single m r)

/-- The coefficients of an atom are those of `Pi.single`. -/
@[to_additive (attr := simp) /-- The coefficients of an atom are those of `Pi.single`. -/]
theorem coeff_single [DecidableEq M] [Zero R] (i : M) (r : R) (m : M) :
    coeff m (single i r) = (Pi.single i r : M → R) m := rfl

end Carrier

/-! ### Pointwise additive and scalar structure -/

section Pointwise

/-- The zero is the zero function. -/
@[to_additive /-- The zero is the zero function. -/]
instance instZero [Zero R] : Zero (FiniteFiberConvolution M R) := inferInstanceAs (Zero (M → R))

/-- Addition is pointwise. -/
@[to_additive /-- Addition is pointwise. -/]
instance instAdd [Add R] : Add (FiniteFiberConvolution M R) := inferInstanceAs (Add (M → R))

/-- Negation is pointwise. -/
@[to_additive /-- Negation is pointwise. -/]
instance instNeg [Neg R] : Neg (FiniteFiberConvolution M R) := inferInstanceAs (Neg (M → R))

/-- Subtraction is pointwise. -/
@[to_additive /-- Subtraction is pointwise. -/]
instance instSub [Sub R] : Sub (FiniteFiberConvolution M R) := inferInstanceAs (Sub (M → R))

/-- External scalars act pointwise. -/
@[to_additive (dont_translate := S R) instSMul /-- External scalars act pointwise. -/]
instance instSMul [SMul S R] : SMul S (FiniteFiberConvolution M R) :=
  inferInstanceAs (SMul S (M → R))

/-- The pointwise additive commutative monoid. -/
@[to_additive instAddCommMonoid /-- The pointwise additive commutative monoid. -/]
instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (FiniteFiberConvolution M R) :=
  inferInstanceAs (AddCommMonoid (M → R))

/-- The pointwise additive commutative group. -/
@[to_additive instAddCommGroup /-- The pointwise additive commutative group. -/]
instance instAddCommGroup [AddCommGroup R] : AddCommGroup (FiniteFiberConvolution M R) :=
  inferInstanceAs (AddCommGroup (M → R))

/-- The pointwise module structure. -/
@[to_additive (dont_translate := S R) /-- The pointwise module structure. -/]
instance instModule [Semiring S] [AddCommMonoid R] [Module S R] :
    Module S (FiniteFiberConvolution M R) where
  one_smul f := toFun.injective (one_smul S (toFun f))
  mul_smul c d f := toFun.injective (mul_smul c d (toFun f))
  smul_zero c := toFun.injective (smul_zero (A := M → R) c)
  smul_add c f g := toFun.injective (smul_add c (toFun f) (toFun g))
  add_smul c d f := toFun.injective (add_smul c d (toFun f))
  zero_smul f := toFun.injective (zero_smul S (toFun f))

/-- The coefficients of `0` vanish. -/
@[to_additive (attr := simp) /-- The coefficients of `0` vanish. -/]
theorem coeff_zero [Zero R] (m : M) : coeff m (0 : FiniteFiberConvolution M R) = 0 := rfl

/-- Coefficients are additive. -/
@[to_additive (attr := simp) /-- Coefficients are additive. -/]
theorem coeff_add [Add R] (f g : FiniteFiberConvolution M R) (m : M) :
    coeff m (f + g) = coeff m f + coeff m g := rfl

/-- The coefficients of `-f` are the negated coefficients of `f`. -/
@[to_additive (attr := simp) /-- The coefficients of `-f` are the negated coefficients of `f`. -/]
theorem coeff_neg [Neg R] (f : FiniteFiberConvolution M R) (m : M) :
    coeff m (-f) = -coeff m f := rfl

/-- The coefficients of `f - g` are the differences of coefficients. -/
@[to_additive (attr := simp)
  /-- The coefficients of `f - g` are the differences of coefficients. -/]
theorem coeff_sub [Sub R] (f g : FiniteFiberConvolution M R) (m : M) :
    coeff m (f - g) = coeff m f - coeff m g := rfl

/-- External scalars act on each coefficient. -/
@[to_additive (attr := simp) (dont_translate := S R) coeff_smul
  /-- External scalars act on each coefficient. -/]
theorem coeff_smul [SMul S R] (c : S) (f : FiniteFiberConvolution M R) (m : M) :
    coeff m (c • f) = c • coeff m f := rfl

end Pointwise

/-! ### Convolution multiplication and unit -/

section MulOne

/-- The multiplication of the convolution algebra is the finite-fiber convolution
`RadiiPolynomial.finiteMulConvolution`. -/
@[to_additive (dont_translate := R) instMul
  /-- The multiplication of the additive-index convolution algebra is the finite-fiber
  convolution `RadiiPolynomial.finiteAddConvolution`; the coefficients are multiplied. -/]
instance instMul [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R] :
    Mul (FiniteFiberConvolution M R) where
  mul f g := ofFun (finiteMulConvolution (toFun f) (toFun g))

/-- The unit of the convolution algebra is the atom `single 1 1`. -/
@[to_additive (dont_translate := R) instOne
  /-- The unit of the additive-index convolution algebra is the atom `single 0 1`, with index `0`
  and coefficient `1`. -/]
instance instOne [One M] [DecidableEq M] [Zero R] [One R] : One (FiniteFiberConvolution M R) where
  one := single 1 1

/-- The underlying function of a product is the finite-fiber convolution of the underlying
functions. -/
@[to_additive (dont_translate := R) toFun_mul
  /-- The underlying function of a product is the additive-index finite-fiber convolution of the
  underlying functions. -/]
theorem toFun_mul [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]
    (f g : FiniteFiberConvolution M R) :
    toFun (f * g) = finiteMulConvolution (toFun f) (toFun g) := rfl

/-- The coefficient of a product is the sum, over the finite fiber of the index, of the ordered
products of coefficients. -/
@[to_additive (dont_translate := R) coeff_mul
  /-- The coefficient of a product is the sum, over the finite additive fiber of the index, of
  the ordered products of coefficients. -/]
theorem coeff_mul [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]
    (f g : FiniteFiberConvolution M R) (m : M) :
    coeff m (f * g) = ∑ ij ∈ mulAntidiagonal m, coeff ij.1 f * coeff ij.2 g := rfl

/-- The unit is the atom `single 1 1`. -/
@[to_additive (dont_translate := R) one_def /-- The unit is the atom `single 0 1`. -/]
theorem one_def [One M] [DecidableEq M] [Zero R] [One R] :
    (1 : FiniteFiberConvolution M R) = single 1 1 := rfl

/-- The coefficients of the unit form the Kronecker delta at the index unit. -/
@[to_additive (attr := simp) (dont_translate := R) coeff_one
  /-- The coefficients of the unit form the Kronecker delta at the index `0`. -/]
theorem coeff_one [One M] [DecidableEq M] [Zero R] [One R] (m : M) :
    coeff m (1 : FiniteFiberConvolution M R) = if m = 1 then 1 else 0 := by
  rw [one_def, coeff_single, Pi.single_apply]

/-- The product of two atoms is the atom at the product index, with the ordered product of the
coefficients. -/
@[to_additive (attr := simp) (dont_translate := R) single_mul_single
  /-- The product of two atoms is the atom at the sum of the indices, with the ordered product of
  the coefficients. -/]
theorem single_mul_single [Mul M] [HasMulAntidiagonal M] [DecidableEq M]
    [NonUnitalNonAssocSemiring R] (i j : M) (r s : R) :
    single i r * single j s = (single (i * j) (r * s) : FiniteFiberConvolution M R) :=
  toFun.injective (finiteMulConvolution.single_single zero_mul mul_zero i j r s)

/-- An atom at the index unit multiplies every coefficient of an arbitrary element on the
left. -/
@[to_additive (attr := simp) (dont_translate := R) coeff_single_zero_mul
  /-- An atom at the index `0` multiplies every coefficient of an arbitrary element on the
  left. -/]
theorem coeff_single_one_mul [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M]
    [NonUnitalNonAssocSemiring R] (r : R) (f : FiniteFiberConvolution M R) (m : M) :
    coeff m (single 1 r * f) = r * coeff m f :=
  finiteMulConvolution.single_one_left_apply zero_mul r (toFun f) m

/-- An atom at the index unit multiplies every coefficient of an arbitrary element on the
right. -/
@[to_additive (attr := simp) (dont_translate := R) coeff_mul_single_zero
  /-- An atom at the index `0` multiplies every coefficient of an arbitrary element on the
  right. -/]
theorem coeff_mul_single_one [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M]
    [NonUnitalNonAssocSemiring R] (f : FiniteFiberConvolution M R) (r : R) (m : M) :
    coeff m (f * single 1 r) = coeff m f * r :=
  finiteMulConvolution.single_one_right_apply mul_zero (toFun f) r m

end MulOne

/-! ### Semiring branches -/

section Semiring

/-- The convolution algebra over a multiplicative index with finite fibers is a nonunital
nonassociative semiring. -/
@[to_additive (dont_translate := R)
  /-- The convolution algebra over an additive index with finite fibers is a nonunital
  nonassociative semiring. -/]
instance instNonUnitalNonAssocSemiring [Mul M] [HasMulAntidiagonal M]
    [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (FiniteFiberConvolution M R) where
  __ := instAddCommMonoid
  __ := instMul
  zero_mul f := toFun.injective (finiteMulConvolution.zero_left zero_mul (toFun f))
  mul_zero f := toFun.injective (finiteMulConvolution.zero_right mul_zero (toFun f))
  left_distrib f g h :=
    toFun.injective (finiteMulConvolution.add_right (toFun f) (toFun g) (toFun h))
  right_distrib f g h :=
    toFun.injective (finiteMulConvolution.add_left (toFun f) (toFun g) (toFun h))

/-- Over a semigroup index, the convolution is associative. -/
@[to_additive (dont_translate := R)
  /-- Over an additive semigroup index, the convolution is associative. -/]
instance instNonUnitalSemiring [Semigroup M] [HasMulAntidiagonal M] [NonUnitalSemiring R] :
    NonUnitalSemiring (FiniteFiberConvolution M R) where
  __ := instNonUnitalNonAssocSemiring
  mul_assoc f g h := toFun.injective (finiteMulConvolution.assoc (toFun f) (toFun g) (toFun h))

/-- Over an index with a unit, the atom `single 1 1` is a two-sided unit; the natural-number
cast is `n ↦ single 1 n`. -/
@[to_additive (dont_translate := R)
  /-- Over an additive index with a zero, the atom `single 0 1` is a two-sided unit; the
  natural-number cast is `n ↦ single 0 n`. -/]
instance instNonAssocSemiring [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M]
    [NonAssocSemiring R] : NonAssocSemiring (FiniteFiberConvolution M R) where
  __ := instNonUnitalNonAssocSemiring
  __ := instOne
  natCast n := single 1 (n : R)
  natCast_zero := toFun.injective <| by
    change (Pi.single 1 ((0 : ℕ) : R) : M → R) = 0
    rw [Nat.cast_zero, Pi.single_zero]
  natCast_succ n := toFun.injective <| by
    change (Pi.single 1 ((n + 1 : ℕ) : R) : M → R) = Pi.single 1 (n : R) + Pi.single 1 1
    rw [Nat.cast_succ, Pi.single_add]
  one_mul f := toFun.injective (finiteMulConvolution.single_one_left zero_mul (toFun f))
  mul_one f := toFun.injective (finiteMulConvolution.single_one_right mul_zero (toFun f))

/-- Over a monoid index, the convolution algebra is a semiring. -/
@[to_additive (dont_translate := R)
  /-- Over an additive monoid index, the convolution algebra is a semiring. -/]
instance instSemiring [Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [Semiring R] :
    Semiring (FiniteFiberConvolution M R) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

/-- Over a commutative magma index with commutative coefficients, the convolution is
commutative. -/
@[to_additive (dont_translate := R)
  /-- Over a commutative additive magma index with commutative coefficients, the convolution is
  commutative. -/]
instance instNonUnitalNonAssocCommSemiring [CommMagma M] [HasMulAntidiagonal M]
    [NonUnitalNonAssocCommSemiring R] :
    NonUnitalNonAssocCommSemiring (FiniteFiberConvolution M R) where
  __ := instNonUnitalNonAssocSemiring
  mul_comm f g := toFun.injective (finiteMulConvolution.comm (toFun f) (toFun g))

/-- Over a commutative semigroup index with commutative coefficients, the convolution algebra
is a nonunital commutative semiring. -/
@[to_additive (dont_translate := R)
  /-- Over a commutative additive semigroup index with commutative coefficients, the
  convolution algebra is a nonunital commutative semiring. -/]
instance instNonUnitalCommSemiring [CommSemigroup M] [HasMulAntidiagonal M]
    [NonUnitalCommSemiring R] : NonUnitalCommSemiring (FiniteFiberConvolution M R) where
  __ := instNonUnitalSemiring
  mul_comm f g := toFun.injective (finiteMulConvolution.comm (toFun f) (toFun g))

/-- Over a commutative monoid index with commutative coefficients, the convolution algebra is a
commutative semiring. -/
@[to_additive (dont_translate := R)
  /-- Over a commutative additive monoid index with commutative coefficients, the convolution
  algebra is a commutative semiring. -/]
instance instCommSemiring [CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M]
    [CommSemiring R] : CommSemiring (FiniteFiberConvolution M R) where
  __ := instSemiring
  mul_comm f g := toFun.injective (finiteMulConvolution.comm (toFun f) (toFun g))

/-- The natural-number cast is `n ↦ single 1 n`. -/
@[to_additive (dont_translate := R) /-- The natural-number cast is `n ↦ single 0 n`. -/]
theorem natCast_def [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocSemiring R]
    (n : ℕ) : (n : FiniteFiberConvolution M R) = single 1 (n : R) := rfl

end Semiring

/-! ### Ring branches -/

section Ring

/-- With coefficients in a nonunital nonassociative ring, the convolution algebra is a nonunital
nonassociative ring; negation is pointwise. -/
@[to_additive (dont_translate := R)
  /-- With coefficients in a nonunital nonassociative ring, the additive-index convolution
  algebra is a nonunital nonassociative ring; negation is pointwise. -/]
instance instNonUnitalNonAssocRing [Mul M] [HasMulAntidiagonal M] [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (FiniteFiberConvolution M R) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

/-- Over a semigroup index with coefficients in a nonunital ring, the convolution algebra is a
nonunital ring. -/
@[to_additive (dont_translate := R)
  /-- Over an additive semigroup index with coefficients in a nonunital ring, the convolution
  algebra is a nonunital ring. -/]
instance instNonUnitalRing [Semigroup M] [HasMulAntidiagonal M] [NonUnitalRing R] :
    NonUnitalRing (FiniteFiberConvolution M R) where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

/-- Over an index with a unit and coefficients in a nonassociative ring, the convolution algebra
is a nonassociative ring; the integer cast is `z ↦ single 1 z`. -/
@[to_additive (dont_translate := R)
  /-- Over an additive index with a zero and coefficients in a nonassociative ring, the
  convolution algebra is a nonassociative ring; the integer cast is `z ↦ single 0 z`. -/]
instance instNonAssocRing [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M]
    [NonAssocRing R] : NonAssocRing (FiniteFiberConvolution M R) where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  intCast z := single 1 (z : R)
  intCast_ofNat n := toFun.injective <| by
    change (Pi.single 1 ((n : ℤ) : R) : M → R) = Pi.single 1 (n : R)
    rw [Int.cast_natCast]
  intCast_negSucc n := toFun.injective <| by
    change (Pi.single 1 ((Int.negSucc n : ℤ) : R) : M → R) = -Pi.single 1 ((n + 1 : ℕ) : R)
    rw [Int.cast_negSucc, Pi.single_neg]

/-- Over a monoid index with coefficients in a ring, the convolution algebra is a ring. -/
@[to_additive (dont_translate := R)
  /-- Over an additive monoid index with coefficients in a ring, the convolution algebra is a
  ring. -/]
instance instRing [Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [Ring R] :
    Ring (FiniteFiberConvolution M R) where
  __ := instSemiring
  __ := instNonAssocRing

/-- Over a commutative monoid index with coefficients in a commutative ring, the convolution
algebra is a commutative ring. -/
@[to_additive (dont_translate := R)
  /-- Over a commutative additive monoid index with coefficients in a commutative ring, the
  convolution algebra is a commutative ring. -/]
instance instCommRing [CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommRing R] :
    CommRing (FiniteFiberConvolution M R) where
  __ := instRing
  __ := instCommSemiring

/-- The integer cast is `z ↦ single 1 z`. -/
@[to_additive (dont_translate := R) /-- The integer cast is `z ↦ single 0 z`. -/]
theorem intCast_def [MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocRing R]
    (z : ℤ) : (z : FiniteFiberConvolution M R) = single 1 (z : R) := rfl

end Ring

/-! ### External scalars -/

section Scalar

/-- External scalars commute with the convolution in its first input. -/
@[to_additive (dont_translate := S R) instIsScalarTower
  /-- External scalars commute with the additive-index convolution in its first input. -/]
instance instIsScalarTower [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]
    [DistribSMul S R] [IsScalarTower S R R] :
    IsScalarTower S (FiniteFiberConvolution M R) (FiniteFiberConvolution M R) where
  smul_assoc c f g := toFun.injective (finiteMulConvolution.smul_left c (toFun f) (toFun g))

/-- External scalars commute with the convolution in its second input. -/
@[to_additive (dont_translate := S R) instSMulCommClass
  /-- External scalars commute with the additive-index convolution in its second input. -/]
instance instSMulCommClass [Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]
    [DistribSMul S R] [SMulCommClass S R R] :
    SMulCommClass S (FiniteFiberConvolution M R) (FiniteFiberConvolution M R) where
  smul_comm c f g := (toFun.injective (finiteMulConvolution.smul_right c (toFun f) (toFun g))).symm

/-- An `S`-algebra structure on the coefficients makes the convolution algebra over a monoid
index an `S`-algebra, with `algebraMap S _ s = single 1 (algebraMap S R s)`. Centrality and the
scalar action are checked coefficientwise on arbitrary elements. -/
@[to_additive (dont_translate := S R)
  /-- An `S`-algebra structure on the coefficients makes the convolution algebra over an
  additive monoid index an `S`-algebra, with `algebraMap S _ s = single 0 (algebraMap S R s)`.
  Centrality and the scalar action are checked coefficientwise on arbitrary elements. -/]
instance instAlgebra [CommSemiring S] [Semiring R] [Algebra S R] [Monoid M]
    [HasMulAntidiagonal M] [DecidableEq M] : Algebra S (FiniteFiberConvolution M R) where
  algebraMap :=
    { toFun s := single 1 (algebraMap S R s)
      map_one' := by rw [map_one]; rfl
      map_mul' s t := by rw [single_mul_single, one_mul, map_mul]
      map_zero' := by rw [map_zero]; exact toFun.injective (Pi.single_zero 1)
      map_add' s t := by rw [map_add]; exact toFun.injective (Pi.single_add 1 _ _) }
  commutes' s f := ext fun m => by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_single_one_mul,
      coeff_mul_single_one, Algebra.commutes]
  smul_def' s f := ext fun m => by
    simp only [coeff_smul, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_single_one_mul,
      Algebra.smul_def]

/-- The algebra map sends `s` to the atom `single 1 (algebraMap S R s)`. -/
@[to_additive (dont_translate := S R)
  /-- The algebra map sends `s` to the atom `single 0 (algebraMap S R s)`. -/]
theorem algebraMap_apply [CommSemiring S] [Semiring R] [Algebra S R] [Monoid M]
    [HasMulAntidiagonal M] [DecidableEq M] (s : S) :
    algebraMap S (FiniteFiberConvolution M R) s = single 1 (algebraMap S R s) := rfl

end Scalar

end FiniteFiberConvolution

end RadiiPolynomial
