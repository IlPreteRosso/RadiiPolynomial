import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Data.Set.MulAntidiagonal

/-!
# Minimal Discrete Convolution API

This file keeps discrete-convolution pieces currently used by
`source.lpSpace.CauchyProduct`:

- `convolution` / `addConvolution`
- `ringConvolution` / `addRingConvolution`
- `convolution_eq_sum_mulAntidiagonal` / `addConvolution_eq_sum_antidiagonal`

The multiplicative versions are primary; additive versions are generated via `@[to_additive]`.
-/

open scoped BigOperators

noncomputable section

/-! ### HasMulAntidiagonal

Multiplicative analog of `Finset.HasAntidiagonal`, defined locally until upstreamed to Mathlib. -/

namespace Finset

/-- The class of multiplicative monoids with a multiplicative antidiagonal. -/
@[to_additive existing HasAntidiagonal]
class HasMulAntidiagonal (M : Type*) [Monoid M] where
  /-- The multiplicative antidiagonal of `n` is the finset of pairs `(i, j)` such that
  `i * j = n`. -/
  mulAntidiagonal : M → Finset (M × M)
  /-- A pair belongs to `mulAntidiagonal n` iff the product of its components equals `n`. -/
  mem_mulAntidiagonal {n} {a} : a ∈ mulAntidiagonal n ↔ a.fst * a.snd = n

export HasMulAntidiagonal (mulAntidiagonal mem_mulAntidiagonal)

attribute [simp] mem_mulAntidiagonal

end Finset

namespace DiscreteConvolution

variable {M S E E' F R : Type*}

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`.
This is `Set.mulAntidiagonal Set.univ Set.univ x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`.
This is `Set.addAntidiagonal Set.univ Set.univ x`. -/]
def mulFiber [Monoid M] (x : M) : Set (M × M) :=
  Set.mulAntidiagonal Set.univ Set.univ x

/-- Membership characterization for `mulFiber`. -/
@[to_additive /-- Membership characterization for `addFiber`. -/]
lemma mem_mulFiber [Monoid M] {x : M} {ab : M × M} :
    ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := by
  unfold mulFiber; simp only [Set.mem_mulAntidiagonal, Set.mem_univ, true_and]

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: `(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/]
def convolution [Monoid M] [CommSemiring S]
    [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
    [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map. -/
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

/-- Convolution using ring multiplication. This is `convolution (LinearMap.mul ℕ R)`. -/
@[to_additive (dont_translate := R) addRingConvolution
  /-- Additive convolution using ring multiplication. -/]
def ringConvolution [Monoid M] [Semiring R] [TopologicalSpace R]
    (f g : M → R) : M → R := convolution (LinearMap.mul ℕ R) f g

/-- Notation for ring multiplication convolution. -/
scoped notation:67 f:68 " ⋆ᵣ " g:67 => ringConvolution f g

/-- Notation for additive ring convolution. -/
scoped notation:67 f:68 " ⋆ᵣ₊ " g:67 => addRingConvolution f g

section AntidiagonalBridge

variable [Monoid M] [Finset.HasMulAntidiagonal M]
variable [CommSemiring S] [AddCommMonoid E] [Module S E]

/-- For types with `HasMulAntidiagonal`, the multiplicative fiber equals the mulAntidiagonal. -/
@[to_additive addFiber_eq_antidiagonal
  /-- For types with `HasAntidiagonal`, the additive fiber equals the antidiagonal. -/]
private lemma mulFiber_eq_mulAntidiagonal (x : M) :
    mulFiber x = ↑(Finset.mulAntidiagonal x) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_coe, Finset.mem_mulAntidiagonal, mem_mulFiber]

variable [AddCommMonoid E'] [Module S E'] [AddCommMonoid F] [Module S F]
variable [TopologicalSpace F]

/-- For `HasMulAntidiagonal` types, convolution equals a finite sum over the mulAntidiagonal. -/
@[to_additive (dont_translate := S) addConvolution_eq_sum_antidiagonal
  /-- For `HasAntidiagonal` types, additive convolution equals a finite sum
  over the antidiagonal. -/]
lemma convolution_eq_sum_mulAntidiagonal
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑ ab ∈ Finset.mulAntidiagonal x, L (f ab.1) (g ab.2) := by
  simp only [convolution]
  rw [← (Finset.mulAntidiagonal x).tsum_subtype fun ab => L (f ab.1) (g ab.2)]
  exact (Equiv.setCongr (mulFiber_eq_mulAntidiagonal x)).tsum_eq
    (fun ab => (L (f ab.1.1)) (g ab.1.2))

end AntidiagonalBridge

end DiscreteConvolution

end
