import RadiiPolynomial.source.lpSpace.DiscreteConvolution
import RadiiPolynomial.source.lpSpace.CauchyProduct
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Ring Axioms for Discrete Convolution

Tsum-based ring axioms for `ringConvolution` on monoids.
Additive versions (for additive groups like ℤ, used in Chebyshev series) are
generated via `@[to_additive]`.

## Main definitions

* `delta e` / `addDelta e` — identity for convolution: `δ₁(x) = e` if `x = 1`, else `0`
* `mulMap` / `addMap` — uncurried operation `(a, b) ↦ a * b`
* `tripleMulFiber x` / `tripleAddFiber x` — all triples `(a, b, c)` with `a * b * c = x`
* `TripleConvolutionSummable` / `AddTripleConvolutionSummable` — summability predicate
* `leftMulAssocEquiv` / `leftAddAssocEquiv` — reindex nested sums ↔ triple fiber sums
* `rightMulAssocEquiv` / `rightAddAssocEquiv` — reindex nested sums ↔ triple fiber sums

## Main results

* `delta_ringConvolution'` / `addDelta_addRingConvolution'` — left identity
* `ringConvolution_delta'` / `addRingConvolution_addDelta'` — right identity
* `zero_ringConvolution` / `zero_addRingConvolution` — zero annihilation
* `ringConvolution_zero` / `addRingConvolution_zero` — zero annihilation
* `ringConvolution_add` / `addRingConvolution_add` — right distributivity
* `add_ringConvolution` / `add_addRingConvolution` — left distributivity
* `ringConvolution_comm` / `addRingConvolution_comm` — commutativity
* `ringConvolution_assoc` — full associativity (manual mul + add versions)
-/

open scoped BigOperators Topology

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {R : Type*}

/-! ### Multiplication Map -/

section MulMap

variable [Monoid M]

/-- The multiplication map `(a, b) ↦ a * b` (uncurried). -/
@[to_additive /-- The addition map `(a, b) ↦ a + b` (uncurried). -/]
def mulMap : M × M → M := fun ⟨a, b⟩ => a * b

@[to_additive (attr := simp)]
theorem mulMap_apply (ab : M × M) : mulMap ab = ab.1 * ab.2 := rfl

/-- `mulFiber x` equals `mulMap ⁻¹' {x}`. -/
@[to_additive /-- `addFiber x` equals `addMap ⁻¹' {x}`. -/]
theorem mulFiber_eq_preimage (x : M) : mulFiber x = mulMap ⁻¹' {x} := by
  ext ⟨a, b⟩; simp [mulFiber, mulMap]

end MulMap

section SigmaFiber

variable [Monoid M]

/-- Sigma-fiber equivalence: `(Σ k, mulFiber k) ≃ M × M`.
Maps `⟨k, ((j, l), h)⟩` to `(j, l)`. Inverse: `(j, l) ↦ ⟨j * l, ((j, l), rfl)⟩`. -/
@[to_additive /-- Sigma-fiber equivalence: `(Σ k, addFiber k) ≃ M × M`.
Maps `⟨k, ((j, l), h)⟩` to `(j, l)`. Inverse: `(j, l) ↦ ⟨j + l, ((j, l), rfl)⟩`. -/]
def sigmaMulFiberEquiv : (Σ k : M, mulFiber k) ≃ M × M where
  toFun := fun ⟨_, ab⟩ => ab.1
  invFun := fun ⟨j, l⟩ => ⟨j * l, ⟨(j, l), mem_mulFiber.mpr rfl⟩⟩
  left_inv := fun ⟨k, ⟨⟨j, l⟩, h⟩⟩ => by
    simp only [mem_mulFiber] at h; subst h; rfl
  right_inv := fun ⟨_, _⟩ => rfl

end SigmaFiber

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] {E : Type*} [Zero E]

/-- The identity for multiplicative convolution: `δ₁(x) = e` if `x = 1`, else `0`. -/
@[to_additive addDelta
  /-- The identity for additive convolution: `δ₀(x) = e` if `x = 0`, else `0`. -/]
def delta (e : E) : M → E := Pi.single 1 e

@[to_additive (attr := simp) addDelta_zero_eq]
theorem delta_one_eq (e : E) : delta e (1 : M) = e := by
  simp [delta]

@[to_additive addDelta_ne]
theorem delta_ne (e : E) {x : M} (hx : x ≠ 1) : delta e x = 0 := by
  simp [delta, hx.symm]

end Identity

/-! ### Convolution Apply Lemma -/

section ApplyLemma

variable [Monoid M] [CommSemiring R] [TopologicalSpace R]

/-- `ringConvolution` unfolds to pointwise multiplication over fibers. -/
@[to_additive (attr := simp) (dont_translate := R) addRingConvolution_apply_eq]
theorem ringConvolution_apply_eq (f g : M → R) (x : M) :
    ringConvolution f g x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := by
  simp only [ringConvolution, convolution, LinearMap.mul_apply']

end ApplyLemma

/-! ### Ring Axioms: Zero -/

section ZeroLaws

variable [Monoid M] [CommSemiring R] [TopologicalSpace R]

@[to_additive (attr := simp) (dont_translate := R) zero_addRingConvolution]
theorem zero_ringConvolution (f : M → R) :
    ringConvolution (0 : M → R) f = 0 := by
  ext x; simp [ringConvolution_apply_eq]

@[to_additive (attr := simp) (dont_translate := R) addRingConvolution_zero]
theorem ringConvolution_zero (f : M → R) :
    ringConvolution f (0 : M → R) = 0 := by
  ext x; simp [ringConvolution_apply_eq]

end ZeroLaws

/-! ### Ring Axioms: Distributivity -/

section Distributivity

variable [Monoid M] [CommSemiring R] [TopologicalSpace R] [T2Space R] [ContinuousAdd R]

@[to_additive (dont_translate := R) addRingConvolution_add]
theorem ringConvolution_add (f g h : M → R)
    (hfg : ∀ x, Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2)
    (hfh : ∀ x, Summable fun ab : mulFiber x => f ab.1.1 * h ab.1.2) :
    ringConvolution f (g + h) = ringConvolution f g + ringConvolution f h := by
  ext x
  simp only [ringConvolution_apply_eq, Pi.add_apply, mul_add]
  exact (hfg x).tsum_add (hfh x)

@[to_additive (dont_translate := R) add_addRingConvolution]
theorem add_ringConvolution (f g h : M → R)
    (hfh : ∀ x, Summable fun ab : mulFiber x => f ab.1.1 * h ab.1.2)
    (hgh : ∀ x, Summable fun ab : mulFiber x => g ab.1.1 * h ab.1.2) :
    ringConvolution (f + g) h = ringConvolution f h + ringConvolution g h := by
  ext x
  simp only [ringConvolution_apply_eq, Pi.add_apply, add_mul]
  exact (hfh x).tsum_add (hgh x)

end Distributivity

/-! ### Ring Axioms: Identity -/

section IdentityLaws

variable [Monoid M] [DecidableEq M] [CommSemiring R] [TopologicalSpace R]

/-- Left identity: `(δ₁ e ⋆ f) x = e * f x`. -/
@[to_additive (dont_translate := R) addDelta_addRingConvolution'
  /-- Left identity: `(δ₀ e ⋆ f) x = e * f x`. -/]
theorem delta_ringConvolution' (e : R) (f : M → R) (x : M) :
    ringConvolution (delta e) f x = e * f x := by
  rw [ringConvolution_apply_eq]
  simp only [delta, Pi.single_apply]
  rw [tsum_eq_single ⟨(1, x), by simp [mem_mulFiber]⟩]
  · simp only [↓reduceIte]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, not_and] at hne
    have ha : a ≠ 1 := fun h => hne h (by simp [← hab, h])
    simp [ha]

/-- Right identity: `(f ⋆ δ₁ e) x = f x * e`. -/
@[to_additive (dont_translate := R) addRingConvolution_addDelta'
  /-- Right identity: `(f ⋆ δ₀ e) x = f x * e`. -/]
theorem ringConvolution_delta' (f : M → R) (e : R) (x : M) :
    ringConvolution f (delta e) x = f x * e := by
  rw [ringConvolution_apply_eq]
  simp only [delta, Pi.single_apply]
  rw [tsum_eq_single ⟨(x, 1), by simp [mem_mulFiber]⟩]
  · simp only [↓reduceIte]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_mulFiber] at hab
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, not_and] at hne
    have hb : b ≠ 1 := fun h => hne (by simp [← hab, h]) h
    simp [hb]

end IdentityLaws

/-! ### Scalar Multiplication -/

section ScalarMul

variable [Monoid M] [CommSemiring R] [TopologicalSpace R] [T2Space R] [ContinuousMul R]

@[to_additive (dont_translate := R) smul_addRingConvolution]
theorem smul_ringConvolution (c : R) (f g : M → R)
    (hfg : ∀ x, Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2) :
    ringConvolution (c • f) g = c • ringConvolution f g := by
  ext x; simp only [ringConvolution_apply_eq, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]; rw [← smul_eq_mul]
  exact Summable.tsum_const_smul c (hfg x)

@[to_additive (dont_translate := R) addRingConvolution_smul]
theorem ringConvolution_smul (c : R) (f g : M → R)
    (hfg : ∀ x, Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2) :
    ringConvolution f (c • g) = c • ringConvolution f g := by
  ext x; simp only [ringConvolution_apply_eq, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ ab : mulFiber x, f ab.1.1 * (c * g ab.1.2) =
    c * (f ab.1.1 * g ab.1.2) from fun _ => by ring]
  rw [← smul_eq_mul]
  exact Summable.tsum_const_smul c (hfg x)

end ScalarMul

/-! ### Commutativity -/

section Commutativity

variable [CommMonoid M] [CommSemiring R] [TopologicalSpace R]

@[to_additive (dont_translate := R) addRingConvolution_comm]
theorem ringConvolution_comm (f g : M → R) :
    ringConvolution f g = ringConvolution g f := by
  ext x
  simp only [ringConvolution_apply_eq]
  let e : mulFiber x ≃ mulFiber x :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by rw [mem_mulFiber] at h ⊢; rw [mul_comm]; exact h⟩,
     fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by rw [mem_mulFiber] at h ⊢; rw [mul_comm]; exact h⟩,
     fun _ => by rfl,
     fun _ => by rfl⟩
  rw [← e.tsum_eq]
  congr 1
  funext ⟨⟨a, b⟩, _⟩
  exact mul_comm _ _

end Commutativity

/-! ### Triple Fiber and Associativity Equivalences -/

section TripleFiber

variable [Monoid M]

/-- The triple multiplication map `(a, b, c) ↦ a * b * c`. -/
@[to_additive /-- The triple addition map `(a, b, c) ↦ a + b + c`. -/]
def tripleMulMap : M × M × M → M := fun ⟨a, b, c⟩ => a * b * c

/-- Fiber over `x` under triple multiplication: `{(a, b, c) | a * b * c = x}`. -/
@[to_additive /-- Fiber over `x` under triple addition: `{(a, b, c) | a + b + c = x}`. -/]
def tripleMulFiber (x : M) : Set (M × M × M) := tripleMulMap ⁻¹' {x}

@[to_additive (attr := simp)]
theorem mem_tripleMulFiber {x : M} {abc : M × M × M} :
    abc ∈ tripleMulFiber x ↔ abc.1 * abc.2.1 * abc.2.2 = x := Set.mem_preimage

/-- Left association equivalence for associativity proof.
Maps `((c, d), (a, b))` where `c * d = x` and `a * b = c` to `(a, b, d)`.

**Performance note:** When using `Equiv.hasSum_iff.mpr` with this equiv, do NOT provide
a type annotation that forces function-level `isDefEq`. Instead, split via `.congr_fun`
with destructured pointwise `rfl`:
```
(leftMulAssocEquiv x).hasSum_iff.mpr hs |>.congr_fun fun ⟨⟨⟨_,_⟩,_⟩, ⟨⟨_,_⟩,_⟩⟩ => rfl
```
This forces per-point evaluation of `toFun` on a constructor (instant) rather than
symbolic unfolding on a generic variable (expensive). -/
@[to_additive /-- Left association equivalence for associativity proof.
Maps `((c, d), (a, b))` where `c + d = x` and `a + b = c` to `(a, b, d)`. -/]
def leftMulAssocEquiv (x : M) :
    (Σ cd : mulFiber x, mulFiber cd.1.1) ≃ tripleMulFiber x where
  toFun := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      rw [mem_tripleMulFiber]; rw [mem_mulFiber] at hcd hab; rw [← hcd, ← hab, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a * b, d⟩, by rw [mem_mulFiber]; rw [mem_tripleMulFiber] at habd; exact habd⟩,
     ⟨⟨a, b⟩, by rw [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, hab⟩⟩ => by
    simp only [mem_mulFiber] at hab; subst hab; rfl
  right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl

/-- Right association equivalence for associativity proof.
Maps `((a, e), (b, d))` where `a * e = x` and `b * d = e` to `(a, b, d)`.

See `leftMulAssocEquiv` performance note — same `congr_fun` pattern applies,
with `(mul_assoc ..).symm` instead of `rfl` since the fiber function is right-associated. -/
@[to_additive /-- Right association equivalence for associativity proof.
Maps `((a, e), (b, d))` where `a + e = x` and `b + d = e` to `(a, b, d)`. -/]
def rightMulAssocEquiv (x : M) :
    (Σ ae : mulFiber x, mulFiber ae.1.2) ≃ tripleMulFiber x where
  toFun := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      rw [mem_tripleMulFiber]; rw [mem_mulFiber] at hae hbd; rw [← hae, ← hbd, mul_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a, b * d⟩, by
      rw [mem_mulFiber]; rw [mem_tripleMulFiber] at habd; rw [← mul_assoc]; exact habd⟩,
     ⟨⟨b, d⟩, by rw [mem_mulFiber]⟩⟩
  left_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, hbd⟩⟩ => by
    simp only [mem_mulFiber] at hbd; subst hbd; rfl
  right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl

end TripleFiber

/-! ### HasSum Bridge Lemmas

These wrap `Equiv.hasSum_iff` with `congr_fun` to avoid expensive function-level `isDefEq`
checks. Without these, Lean must eta-expand a generic sigma-subtype-product variable through
3+ layers to evaluate the `Equiv.toFun` pattern match — ~4.5s. With destructured pointwise
`rfl`, each point resolves by direct constructor evaluation — instant.
-/

section HasSumBridge

variable [Monoid M] [NormedCommRing R]

/-- Left-assoc `HasSum` bridge: triple fiber → nested sigma fiber (pointwise `rfl`). -/
@[to_additive (dont_translate := R)
  /-- Left-assoc `HasSum` bridge: triple fiber → nested sigma fiber (pointwise `rfl`). -/]
theorem HasSum.leftMulAssocEquiv_sigma {f g h : M → R} {x : M} {a : R}
    (hs : HasSum (fun p : tripleMulFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2) a) :
    HasSum (fun p : Σ cd : mulFiber x, mulFiber cd.1.1 =>
      (f p.2.1.1 * g p.2.1.2) * h p.1.1.2) a :=
  ((leftMulAssocEquiv x).hasSum_iff.mpr hs).congr_fun
    fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => rfl

/-- Right-assoc `HasSum` bridge: triple fiber → nested sigma fiber (pointwise `mul_assoc`). -/
@[to_additive (dont_translate := R)
  /-- Right-assoc `HasSum` bridge: triple fiber → nested sigma fiber (pointwise `mul_assoc`). -/]
theorem HasSum.rightMulAssocEquiv_sigma {f g h : M → R} {x : M} {a : R}
    (hs : HasSum (fun p : tripleMulFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2) a) :
    HasSum (fun p : Σ ae : mulFiber x, mulFiber ae.1.2 =>
      f p.1.1.1 * (g p.2.1.1 * h p.2.1.2)) a :=
  ((rightMulAssocEquiv x).hasSum_iff.mpr hs).congr_fun
    fun ⟨⟨⟨a, _⟩, _⟩, ⟨⟨b, d⟩, _⟩⟩ => (mul_assoc (f a) (g b) (h d)).symm

end HasSumBridge

/-! ### Triple Convolution Summability -/

section TripleConvSummable

variable [Monoid M] [CommSemiring R] [TopologicalSpace R]

/-- Summability predicate for triple convolution (multiplicative). -/
@[to_additive (dont_translate := R) AddTripleConvolutionSummable
  /-- Summability predicate for triple convolution (additive). -/]
def TripleConvolutionSummable (f g h : M → R) (x : M) : Prop :=
  Summable fun p : tripleMulFiber x => f p.1.1 * g p.1.2.1 * h p.1.2.2

end TripleConvSummable

/-! ### Associativity Theorems

These are stated manually for both multiplicative and additive because `@[to_additive]`
cannot distinguish ring `*` (in fiber products `f a * g b`) from monoid `*` (in `mulFiber`).

**Heartbeats:** Working at the `HasSum` level (rather than `tsum` rewriting with `rw`/`convert`/
`simp_rw`) avoids expensive `isDefEq` pattern matching. Splitting `Equiv.hasSum_iff` from the
type annotation via `congr_fun` forces per-point checking after destructuring (fast beta +
projection) instead of a whole-function `isDefEq` check (slow equiv unfolding).
-/

section Associativity

variable [Monoid M] [NormedCommRing R]

/-- Left-associated nested convolution sum equals triple fiber sum (multiplicative). -/
@[to_additive (dont_translate := R) addRingConvolution_assoc_left]
theorem ringConvolution_assoc_left (f g h : M → R) (x : M)
    (hfg : ∀ k, Summable fun ab : mulFiber k => f ab.1.1 * g ab.1.2)
    (htriple : TripleConvolutionSummable f g h x) :
    ∑' cd : mulFiber x,
      (∑' ab : mulFiber cd.1.1, f ab.1.1 * g ab.1.2) * h cd.1.2 =
    ∑' p : tripleMulFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have hs := htriple.hasSum
  have hs_sigma := HasSum.leftMulAssocEquiv_sigma hs
  have hs_iter := hs_sigma.sigma fun cd => (hfg cd.1.1).mul_right (h cd.1.2) |>.hasSum
  have hs_goal := hs_iter.congr_fun fun cd =>
    ((hfg cd.1.1).hasSum.mul_right _).tsum_eq.symm
  exact hs_goal.tsum_eq.trans hs.tsum_eq.symm

/-- Right-associated nested convolution sum equals triple fiber sum (multiplicative). -/
@[to_additive (dont_translate := R) addRingConvolution_assoc_right]
theorem ringConvolution_assoc_right (f g h : M → R) (x : M)
    (hgh : ∀ k, Summable fun ab : mulFiber k => g ab.1.1 * h ab.1.2)
    (htriple : TripleConvolutionSummable f g h x) :
    ∑' ae : mulFiber x,
      f ae.1.1 * (∑' bd : mulFiber ae.1.2, g bd.1.1 * h bd.1.2) =
    ∑' p : tripleMulFiber x, f p.1.1 * g p.1.2.1 * h p.1.2.2 := by
  have hs := htriple.hasSum
  have hs_sigma' := HasSum.rightMulAssocEquiv_sigma hs
  have hs_iter := hs_sigma'.sigma fun ae => (hgh ae.1.2).mul_left (f ae.1.1) |>.hasSum
  have hs_goal := hs_iter.congr_fun fun ae =>
    ((hgh ae.1.2).hasSum.mul_left _).tsum_eq.symm
  exact hs_goal.tsum_eq.trans hs.tsum_eq.symm

/-- Full associativity of `ringConvolution` (multiplicative). -/
@[to_additive (dont_translate := R) addRingConvolution_assoc]
theorem ringConvolution_assoc (f g h : M → R)
    (hfg : ∀ k, Summable fun ab : mulFiber k => f ab.1.1 * g ab.1.2)
    (hgh : ∀ k, Summable fun ab : mulFiber k => g ab.1.1 * h ab.1.2)
    (htriple : ∀ x, TripleConvolutionSummable f g h x) :
    ringConvolution (ringConvolution f g) h =
      ringConvolution f (ringConvolution g h) := by
  ext x
  simp only [ringConvolution_apply_eq]
  exact (ringConvolution_assoc_left f g h x hfg (htriple x)).trans
    (ringConvolution_assoc_right f g h x hgh (htriple x)).symm

end Associativity

end DiscreteConvolution

namespace RadiiPolynomial

namespace CauchyProduct

variable {R : Type*} [Semiring R] [TopologicalSpace R]

/-- On `ℕ`, `CauchyProduct` agrees with the additive ring convolution from
`DiscreteConvolution` once `tsum` is reduced to the antidiagonal finite sum. -/
theorem eq_addRingConvolution (a b : ℕ → R) :
    CauchyProduct a b = DiscreteConvolution.addRingConvolution (M := ℕ) a b := by
  funext n
  simpa [CauchyProduct, DiscreteConvolution.addRingConvolution] using
    (DiscreteConvolution.addConvolution_eq_sum_antidiagonal
      (M := ℕ) (S := ℕ) (E := R) (E' := R) (F := R)
      (L := LinearMap.mul ℕ R) a b n).symm

end CauchyProduct

end RadiiPolynomial

end
