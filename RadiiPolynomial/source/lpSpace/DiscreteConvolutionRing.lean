import RadiiPolynomial.source.lpSpace.DiscreteConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Ring Axioms for Additive Discrete Convolution

Tsum-based ring axioms for `addRingConvolution` on additive groups (e.g., ℤ).
These are needed for ℤ-indexed convolution (Chebyshev series) where antidiagonals
are infinite, so the finite-sum `CauchyProduct` approach doesn't apply.

Ported from the local Mathlib fork `DiscreteConvolutionTestAPI.lean.disable`,
taking the additive versions directly (no `@[to_additive]`).

## Main definitions

* `addDelta e` — identity for additive convolution: `δ₀(x) = e` if `x = 0`, else `0`
* `addMap` — uncurried addition `(a, b) ↦ a + b`
* `tripleAddFiber x` — all triples `(a, b, c)` with `a + b + c = x`
* `leftAddAssocEquiv` / `rightAddAssocEquiv` — reindex nested sums ↔ triple fiber sums

## Main results

* `addDelta_addRingConvolution'` / `addRingConvolution_addDelta'` — identity laws
* `zero_addRingConvolution` / `addRingConvolution_zero` — zero annihilation
* `addRingConvolution_add` / `add_addRingConvolution` — distributivity
* `addRingConvolution_comm` — commutativity (for `AddCommMonoid`)
-/

open scoped BigOperators Topology

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {R : Type*}

/-! ### Additive Map -/

section AddMap

variable [AddMonoid M]

/-- The addition map `(a, b) ↦ a + b` (uncurried). -/
def addMap : M × M → M := fun ⟨a, b⟩ => a + b

@[simp] theorem addMap_apply (ab : M × M) : addMap ab = ab.1 + ab.2 := rfl

/-- `addFiber x` equals `addMap ⁻¹' {x}`. -/
theorem addFiber_eq_preimage (x : M) : addFiber x = addMap ⁻¹' {x} := by
  ext ⟨a, b⟩; simp [addFiber, addMap]

end AddMap

section SigmaFiber

variable [AddGroup M]

/-- Sigma-fiber equivalence: `(Σ k, addFiber k) ≃ M × M`.
Maps `⟨k, ((j, l), h)⟩` to `(j, l)`. Inverse: `(j, l) ↦ ⟨j + l, ((j, l), rfl)⟩`. -/
def sigmaAddFiberEquiv : (Σ k : M, addFiber k) ≃ M × M where
  toFun := fun ⟨_, ab⟩ => ab.1
  invFun := fun ⟨j, l⟩ => ⟨j + l, ⟨(j, l), mem_addFiber.mpr rfl⟩⟩
  left_inv := fun ⟨k, ⟨⟨j, l⟩, h⟩⟩ => by
    simp only [mem_addFiber] at h; subst h; rfl
  right_inv := fun ⟨_, _⟩ => rfl

end SigmaFiber

/-! ### Identity Element -/

section Identity

variable [AddMonoid M] [DecidableEq M] {E : Type*} [Zero E]

/-- The identity for additive convolution: `δ₀(x) = e` if `x = 0`, else `0`. -/
def addDelta (e : E) : M → E := Pi.single 0 e

@[simp] theorem addDelta_zero_eq (e : E) : addDelta e (0 : M) = e := by
  simp [addDelta]

theorem addDelta_ne (e : E) {x : M} (hx : x ≠ 0) : addDelta e x = 0 := by
  simp [addDelta, hx.symm]

end Identity

/-! ### Convolution Apply Lemma -/

section ApplyLemma

variable [AddMonoid M] [CommSemiring R] [TopologicalSpace R]

/-- `addRingConvolution` unfolds to pointwise multiplication over fibers. -/
@[simp] theorem addRingConvolution_apply_eq (f g : M → R) (x : M) :
    addRingConvolution f g x = ∑' ab : addFiber x, f ab.1.1 * g ab.1.2 := by
  simp only [addRingConvolution, addConvolution, LinearMap.mul_apply']

end ApplyLemma

/-! ### Ring Axioms: Zero -/

section ZeroLaws

variable [AddMonoid M] [CommSemiring R] [TopologicalSpace R]

@[simp] theorem zero_addRingConvolution (f : M → R) :
    addRingConvolution (0 : M → R) f = 0 := by
  ext x; simp [addRingConvolution_apply_eq]

@[simp] theorem addRingConvolution_zero (f : M → R) :
    addRingConvolution f (0 : M → R) = 0 := by
  ext x; simp [addRingConvolution_apply_eq]

end ZeroLaws

/-! ### Ring Axioms: Distributivity -/

section Distributivity

variable [AddMonoid M] [CommSemiring R] [TopologicalSpace R] [T2Space R] [ContinuousAdd R]

theorem addRingConvolution_add (f g h : M → R)
    (hfg : ∀ x, Summable fun ab : addFiber x => f ab.1.1 * g ab.1.2)
    (hfh : ∀ x, Summable fun ab : addFiber x => f ab.1.1 * h ab.1.2) :
    addRingConvolution f (g + h) = addRingConvolution f g + addRingConvolution f h := by
  ext x
  simp only [addRingConvolution_apply_eq, Pi.add_apply, mul_add]
  exact (hfg x).tsum_add (hfh x)

theorem add_addRingConvolution (f g h : M → R)
    (hfh : ∀ x, Summable fun ab : addFiber x => f ab.1.1 * h ab.1.2)
    (hgh : ∀ x, Summable fun ab : addFiber x => g ab.1.1 * h ab.1.2) :
    addRingConvolution (f + g) h = addRingConvolution f h + addRingConvolution g h := by
  ext x
  simp only [addRingConvolution_apply_eq, Pi.add_apply, add_mul]
  exact (hfh x).tsum_add (hgh x)

end Distributivity

/-! ### Ring Axioms: Identity -/

section IdentityLaws

variable [AddMonoid M] [DecidableEq M] [CommSemiring R] [TopologicalSpace R]

/-- Left identity: `(δ₀ e ⋆ f) x = e * f x`. -/
theorem addDelta_addRingConvolution' (e : R) (f : M → R) (x : M) :
    addRingConvolution (addDelta e) f x = e * f x := by
  rw [addRingConvolution_apply_eq]
  simp only [addDelta, Pi.single_apply]
  rw [tsum_eq_single ⟨(0, x), by simp [mem_addFiber]⟩]
  · simp only [↓reduceIte]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_addFiber] at hab
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, not_and] at hne
    have ha : a ≠ 0 := fun h => hne h (by simp [← hab, h])
    simp [ha]

/-- Right identity: `(f ⋆ δ₀ e) x = f x * e`. -/
theorem addRingConvolution_addDelta' (f : M → R) (e : R) (x : M) :
    addRingConvolution f (addDelta e) x = f x * e := by
  rw [addRingConvolution_apply_eq]
  simp only [addDelta, Pi.single_apply]
  rw [tsum_eq_single ⟨(x, 0), by simp [mem_addFiber]⟩]
  · simp only [↓reduceIte]
  · intro ⟨⟨a, b⟩, hab⟩ hne
    simp only [mem_addFiber] at hab
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, not_and] at hne
    have hb : b ≠ 0 := fun h => hne (by simp [← hab, h]) h
    simp [hb]

end IdentityLaws

/-! ### Scalar Multiplication -/

section ScalarMul

variable [AddMonoid M] [CommSemiring R] [TopologicalSpace R] [T2Space R] [ContinuousMul R]

theorem smul_addRingConvolution (c : R) (f g : M → R)
    (hfg : ∀ x, Summable fun ab : addFiber x => f ab.1.1 * g ab.1.2) :
    addRingConvolution (c • f) g = c • addRingConvolution f g := by
  ext x; simp only [addRingConvolution_apply_eq, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]; rw [← smul_eq_mul]
  exact Summable.tsum_const_smul c (hfg x)

theorem addRingConvolution_smul (c : R) (f g : M → R)
    (hfg : ∀ x, Summable fun ab : addFiber x => f ab.1.1 * g ab.1.2) :
    addRingConvolution f (c • g) = c • addRingConvolution f g := by
  ext x; simp only [addRingConvolution_apply_eq, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ ab : addFiber x, f ab.1.1 * (c * g ab.1.2) =
    c * (f ab.1.1 * g ab.1.2) from fun _ => by ring]
  rw [← smul_eq_mul]
  exact Summable.tsum_const_smul c (hfg x)

end ScalarMul

/-! ### Commutativity -/

section Commutativity

variable [AddCommMonoid M] [CommSemiring R] [TopologicalSpace R]

theorem addRingConvolution_comm (f g : M → R) :
    addRingConvolution f g = addRingConvolution g f := by
  ext x
  simp only [addRingConvolution_apply_eq]
  let e : addFiber x ≃ addFiber x :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by rw [mem_addFiber] at h ⊢; rw [add_comm]; exact h⟩,
     fun ⟨⟨a, b⟩, h⟩ => ⟨⟨b, a⟩, by rw [mem_addFiber] at h ⊢; rw [add_comm]; exact h⟩,
     fun _ => by rfl,
     fun _ => by rfl⟩
  rw [← e.tsum_eq]
  congr 1
  funext ⟨⟨a, b⟩, _⟩
  exact mul_comm _ _

end Commutativity

/-! ### Triple Fiber and Associativity Equivalences -/

section TripleFiber

variable [AddMonoid M]

/-- The triple addition map `(a, b, c) ↦ a + b + c`. -/
def tripleAddMap : M × M × M → M := fun ⟨a, b, c⟩ => a + b + c

/-- Fiber over `x` under triple addition: `{(a, b, c) | a + b + c = x}`. -/
def tripleAddFiber (x : M) : Set (M × M × M) := tripleAddMap ⁻¹' {x}

@[simp] theorem mem_tripleAddFiber {x : M} {abc : M × M × M} :
    abc ∈ tripleAddFiber x ↔ abc.1 + abc.2.1 + abc.2.2 = x := Set.mem_preimage

/-- Left association equivalence for associativity proof.
Maps `((c, d), (a, b))` where `c + d = x` and `a + b = c` to `(a, b, d)`. -/
def leftAddAssocEquiv (x : M) :
    (Σ cd : addFiber x, addFiber cd.1.1) ≃ tripleAddFiber x where
  toFun := fun ⟨⟨⟨c, d⟩, hcd⟩, ⟨⟨a, b⟩, hab⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      rw [mem_tripleAddFiber]; rw [mem_addFiber] at hcd hab; rw [← hcd, ← hab, add_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a + b, d⟩, by rw [mem_addFiber]; rw [mem_tripleAddFiber] at habd; exact habd⟩,
     ⟨⟨a, b⟩, by rw [mem_addFiber]⟩⟩
  left_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, hab⟩⟩ => by
    simp only [mem_addFiber] at hab; subst hab; rfl
  right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl

/-- Right association equivalence for associativity proof.
Maps `((a, e), (b, d))` where `a + e = x` and `b + d = e` to `(a, b, d)`. -/
def rightAddAssocEquiv (x : M) :
    (Σ ae : addFiber x, addFiber ae.1.2) ≃ tripleAddFiber x where
  toFun := fun ⟨⟨⟨a, e⟩, hae⟩, ⟨⟨b, d⟩, hbd⟩⟩ =>
    ⟨⟨a, b, d⟩, by
      rw [mem_tripleAddFiber]; rw [mem_addFiber] at hae hbd; rw [← hae, ← hbd, add_assoc]⟩
  invFun := fun ⟨⟨a, b, d⟩, habd⟩ =>
    ⟨⟨⟨a, b + d⟩, by
      rw [mem_addFiber]; rw [mem_tripleAddFiber] at habd; rw [← add_assoc]; exact habd⟩,
     ⟨⟨b, d⟩, by rw [mem_addFiber]⟩⟩
  left_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, hbd⟩⟩ => by
    simp only [mem_addFiber] at hbd; subst hbd; rfl
  right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl

end TripleFiber

end DiscreteConvolution

end
