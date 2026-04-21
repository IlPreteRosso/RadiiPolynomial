import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Lean 4 `structure`: what it generates and how to use it

A `structure` is Lean's way to declare a record type — a type whose values
are tuples of named fields. Under the hood, it creates a single-constructor
inductive type, plus one projection function per field.

## 1. The minimal example
-/

structure Point where
  x : Float
  y : Float

-- Lean auto-generates THREE things from this declaration:
--
-- (a) The constructor `Point.mk : Float → Float → Point`
-- (b) A projector for each field:
--        Point.x : Point → Float
--        Point.y : Point → Float
-- (c) Anonymous-constructor notation `⟨_, _⟩` and `{ x := _, y := _ }`

#check @Point.mk  -- Float → Float → Point
#check @Point.x   -- Point → Float
#check @Point.y   -- Point → Float

-- Four equivalent ways to build a Point:
example : Point := Point.mk 1.0 2.0           -- named constructor
example : Point := ⟨1.0, 2.0⟩                  -- anonymous constructor
example : Point := { x := 1.0, y := 2.0 }      -- record syntax
example : Point := { x := 1.0, y := 2.0 : Point }

-- Two ways to destruct:
example (p : Point) : Float := p.x             -- dot notation (sugar for Point.x p)
example (p : Point) : Float := Point.x p

/-!
## 2. Single-field structures — the "wrapper" pattern

A common idiom: wrap an existing type `T` in a one-field structure to get
a fresh nominal type. This is what `lpOneAlg` does with `lp E 1`.
-/

structure Wrapped where
  unwrap : Nat

#check @Wrapped.mk      -- Nat → Wrapped
#check @Wrapped.unwrap  -- Wrapped → Nat

-- `mk` and `unwrap` are INVERSES by definitional equality:
example (n : Nat) : Wrapped.unwrap (Wrapped.mk n) = n := rfl
example (w : Wrapped) : Wrapped.mk (Wrapped.unwrap w) = w := rfl

-- This is exactly why `lpOneAlg.equiv`'s left_inv/right_inv are `rfl`.

/-!
## 3. Renaming the constructor

The default constructor is always named `.mk`. Use `::` to pick a custom name.
-/

structure Vec2 where
  mk' ::             -- constructor is now `Vec2.mk'` instead of `Vec2.mk`
  x : Float
  y : Float

#check @Vec2.mk'   -- Float → Float → Vec2
-- #check @Vec2.mk -- would error: does not exist

/-!
## 4. Fields with dependencies

Later fields can mention earlier ones — this is what makes `structure`
strictly more expressive than plain tuples.
-/

structure Sigma2 where
  n : Nat
  vec : Fin n → Float    -- type depends on `n`

example : Sigma2 := ⟨3, fun i => i.val.toFloat⟩

/-!
## 5. Type parameters and implicit arguments

Parameters before `where` become arguments of the type constructor.
-/

structure Pair (α β : Type) where
  fst : α
  snd : β

#check @Pair.mk    -- {α β : Type} → α → β → Pair α β
#check @Pair.fst   -- {α β : Type} → Pair α β → α

example : Pair Nat String := ⟨42, "hi"⟩

/-!
## 6. `extends`: inheritance by field inclusion

`extends` copies the parent's fields into the child. Parent projectors
still work on the child thanks to a generated coercion.
-/

structure Point3 extends Point where
  z : Float

#check @Point3.mk       -- Point → Float → Point3     (NOT (Float × Float × Float))
#check @Point3.toPoint  -- Point3 → Point              (coercion to parent)

example : Point3 := ⟨⟨1, 2⟩, 3⟩                        -- nested anonymous
example : Point3 := { x := 1, y := 2, z := 3 }         -- flat record syntax
example (p : Point3) : Float := p.x                    -- inherited projection

/-!
## 7. The record-update syntax `{ p with ... }`

Copy a struct and override some fields.
-/

def origin : Point := ⟨0, 0⟩
def shifted : Point := { origin with x := 5 }   -- y := 0 inherited
example : shifted.y = 0 := rfl

/-!
## 8. `structure` is an `inductive` under the hood

You can write the same thing manually — but you'd lose the nice record
syntax and auto-generated projectors.
-/

inductive Point' where
  | mk : Float → Float → Point'

-- No field names → no dot projections, no `{ ... }` syntax, no record update.

/-!
## 9. Why `structure` matters for typeclass design

A `structure` creates a NEW TYPE that typeclass search treats as distinct
from its underlying representation. That's the whole reason `lpOneAlg M E`
(a `structure` wrapping `lp E 1`) can carry its own `Ring` / `Algebra 𝕜`
instances without colliding with any that might exist on `lp E 1`.

Contrast with `def Wrapped := T`, which is transparent to the kernel but
OPAQUE to typeclass search (see `MyWeighted` in `temp.lean`). Both achieve
"fresh type for typeclass purposes," but:

  structure S where x : T     -- new inductive type; auto mk/projector;
                              --   arithmetic must be re-derived
  def S := T                  -- type synonym; inherits data defeq with T;
                              --   write `ofT`/`toT` manually
                              --   typeclass search still sees a distinct type

Rule of thumb:
  * Use `structure` when you want to BUNDLE data (multiple fields) or
    when the wrapper's algebraic structure should be built from scratch.
  * Use `def` type synonym when you want to REUSE the underlying type's
    operations but OVERRIDE specific typeclass instances (like `Norm`).
-/

/-!
## 10. Putting it together: `lpOneAlg`-style wrapper

This mirrors the pattern in `source/lpSpace/LpOneAlg.lean`.
-/

section lpOneAlgStyle

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

-- A one-field wrapper around `lp E 1`.
structure MyLpWrap (M : Type*) (E : M → Type*) [∀ m, NormedAddCommGroup (E m)] where
  toLp : lp E 1

-- Auto-generated: MyLpWrap.mk : lp E 1 → MyLpWrap M E
--                 MyLpWrap.toLp : MyLpWrap M E → lp E 1

-- The equiv to the underlying type — 4 fields of `≃`, not of `lp`:
protected def MyLpWrap.equiv : MyLpWrap M E ≃ lp E 1 where
  toFun := MyLpWrap.toLp   -- unwrap
  invFun := MyLpWrap.mk    -- wrap
  left_inv _ := rfl        -- unwrap ∘ wrap = id     (holds definitionally)
  right_inv _ := rfl       -- wrap ∘ unwrap = id     (holds definitionally)

-- Transfer the norm from `lp E 1` along the equiv — zero-cost pullback.
noncomputable instance : NormedAddCommGroup (MyLpWrap M E) :=
  MyLpWrap.equiv.normedAddCommGroup

end lpOneAlgStyle
