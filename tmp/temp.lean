import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The fiber design problem for ℓ¹_ν

## How ℝ gets its norm in Mathlib

The norm on ℝ is defined in three independent layers, then bundled:

1. `Real.norm` defines ‖r‖ := |r|              (Norm instance, direct definition)
2. `Real.pseudoMetricSpace` defines dist x y := |x - y|  (independent definition)
3. `Real.normedAddCommGroup` proves compatibility:
     dist x y = ‖x - y‖   unfolds to   |x - y| = |x - y|   which is rfl.

The norm is NOT derived from the metric. Both independently use absolute value,
and `normedAddCommGroup` certifies they agree.
-/

-- Layer 1: the norm itself. ‖r‖ = |r| by definition.
#check @Real.norm               -- instance Norm ℝ where norm r := |r|
example (x : ℝ) : ‖x‖ = |x| := rfl  -- definitional equality, not a theorem

-- Layer 2: the metric. dist x y = |x - y| by definition.
#check Real.pseudoMetricSpace
example (x y : ℝ) : dist x y = |x - y| := rfl  -- also definitional

-- Layer 3: compatibility. dist = ‖· - ·‖ is trivial since both are |· - ·|.
#check @Real.normedAddCommGroup

-- The full chain: NormedAddCommGroup → NormedCommRing → NormedField
-- Each layer adds multiplicative structure, but the norm ‖r‖ = |r| never changes.
#check @Real.normedField

/-!
## Problem: this norm is locked to ℝ

Lean's typeclass system has at most one `NormedAddCommGroup` per type.
Since ℝ already has one (with ‖x‖ = |x|), we cannot register a second
instance with ‖x‖ = |x| · νⁿ on the same type.

When `lp E p` looks up `NormedAddCommGroup (E i)` and `E i = ℝ`,
it always finds ‖x‖ = |x| — regardless of the index i.
-/

-- lp needs NormedAddCommGroup on each fiber:
#check @lp  -- (E : α → Type*) → [∀ i, NormedAddCommGroup (E i)] → ...

-- If E i := ℝ for all i, every fiber gets ‖x‖ = |x|. No way to vary by index.

/-!
## Solution: WeightedScalar — an opaque wrapper around ℝ

`def` (not `abbrev`) prevents typeclass resolution from unfolding to ℝ,
so we can register a *different* NormedAddCommGroup on it.
-/

def MyWeighted (ν : ℝ) (n : ℕ) := ℝ  -- opaque to typeclass search

namespace MyWeighted

def ofReal (x : ℝ) : MyWeighted ν n := x
def toReal (x : MyWeighted ν n) : ℝ := x

-- Custom norm: |x| · νⁿ — different at each index n!
noncomputable instance (ν : ℝ) (n : ℕ) : Norm (MyWeighted ν n) where
  norm x := |toReal x| * ν ^ n

-- The key point: different indices, different norms, from a SINGLE instance.
example (x : MyWeighted ν 0) : ‖x‖ = |MyWeighted.toReal x| * ν ^ 0 := rfl
example (x : MyWeighted ν 3) : ‖x‖ = |MyWeighted.toReal x| * ν ^ 3 := rfl

-- Meanwhile, ℝ still has its own norm, unaffected:
example (x : ℝ) : ‖x‖ = |x| := rfl

end MyWeighted

/-!
## Why `def` and not `abbrev`?

`abbrev` is transparent to typeclass resolution: Lean unfolds `MyWeightedBad ν n`
to `ℝ`, finds `Real.normedAddCommGroup`, and gives ‖x‖ = |x| at every index.

`def` is opaque: Lean sees `MyWeighted ν n` as a distinct type and only finds
instances registered on `MyWeighted`.
-/

abbrev MyWeightedBad (ν : ℝ) (n : ℕ) := ℝ  -- transparent to typeclass search

-- Lean finds ℝ's NormedAddCommGroup through the abbrev:
#check (inferInstance : NormedAddCommGroup (MyWeightedBad 2 5))
-- This is ℝ's norm ‖x‖ = |x|, NOT a weighted norm.
