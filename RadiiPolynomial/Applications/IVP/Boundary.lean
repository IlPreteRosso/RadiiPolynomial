import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Split boundary data for coefficient-space IVPs

A boundary row is first of all a split continuous linear map.  Its kernel is
the space of zero-boundary coefficients, and the splitting gives a canonical
projection onto that kernel.  Algebra-character structure is an optional
strengthening supplied by particular realizations; it is not required here.

This file contains only the representation-independent linear mechanism.
-/

noncomputable section

namespace RadiiPolynomial

namespace IVP

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- A boundary trace together with a continuous extension of boundary data.

The equation `trace (extension b) = b` makes the boundary row split.  This is
explicit data rather than a typeclass because a coefficient space normally
has many evaluation points. -/
structure SplitBoundary (𝕜 A B : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] where
  trace : A →L[𝕜] B
  extension : B →L[𝕜] A
  trace_extension : Function.RightInverse extension trace

namespace SplitBoundary

@[simp]
theorem trace_extension_apply (d : SplitBoundary 𝕜 A B) (b : B) :
    d.trace (d.extension b) = b :=
  d.trace_extension b

/-- The canonical continuous splitting into boundary data and zero-boundary
coefficients. -/
def equiv (d : SplitBoundary 𝕜 A B) : A ≃L[𝕜] B × d.trace.ker :=
  ContinuousLinearEquiv.equivOfRightInverse d.trace d.extension d.trace_extension

@[simp]
theorem equiv_fst (d : SplitBoundary 𝕜 A B) (a : A) : (d.equiv a).1 = d.trace a :=
  rfl

@[simp]
theorem equiv_snd_coe (d : SplitBoundary 𝕜 A B) (a : A) :
    ((d.equiv a).2 : A) = a - d.extension (d.trace a) :=
  rfl

/-- Projection onto the zero-boundary coefficients. -/
def zeroPart (d : SplitBoundary 𝕜 A B) : A →L[𝕜] d.trace.ker :=
  d.trace.projKerOfRightInverse d.extension d.trace_extension

@[simp]
theorem zeroPart_coe (d : SplitBoundary 𝕜 A B) (a : A) :
    (d.zeroPart a : A) = a - d.extension (d.trace a) :=
  rfl

@[simp]
theorem trace_zeroPart (d : SplitBoundary 𝕜 A B) (a : A) :
    d.trace (d.zeroPart a : A) = 0 :=
  (d.zeroPart a).2

/-- Every coefficient splits as its extended boundary value plus a
zero-boundary part. -/
theorem extension_add_zeroPart (d : SplitBoundary 𝕜 A B) (a : A) :
    d.extension (d.trace a) + (d.zeroPart a : A) = a := by
  rw [zeroPart_coe]
  abel

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace 𝕜 C]

/-- Normalize any primitive at the chosen boundary by projecting it into the
zero-boundary kernel. -/
def anchoredPrimitive (d : SplitBoundary 𝕜 A B) (I : C →L[𝕜] A) :
    C →L[𝕜] d.trace.ker :=
  d.zeroPart.comp I

@[simp]
theorem trace_anchoredPrimitive (d : SplitBoundary 𝕜 A B) (I : C →L[𝕜] A) (c : C) :
    d.trace (d.anchoredPrimitive I c : A) = 0 :=
  (d.anchoredPrimitive I c).2

/-- A prescribed-boundary fiber is the affine translate of the zero-boundary
kernel by the chosen extension. -/
theorem fiber_eq_translate_ker (d : SplitBoundary 𝕜 A B) (b : B) :
    {a : A | d.trace a = b} =
      {a : A | ∃ k : d.trace.ker, a = d.extension b + (k : A)} := by
  ext a
  constructor
  · intro ha
    refine ⟨⟨a - d.extension b, ?_⟩, ?_⟩
    · change d.trace (a - d.extension b) = 0
      rw [map_sub, ha, d.trace_extension_apply, sub_self]
    · change a = d.extension b + (a - d.extension b)
      abel
  · rintro ⟨k, rfl⟩
    change d.trace (d.extension b + (k : A)) = b
    have hk : d.trace (k : A) = 0 := k.2
    rw [map_add, d.trace_extension_apply, hk, add_zero]

end SplitBoundary

end IVP

end RadiiPolynomial
