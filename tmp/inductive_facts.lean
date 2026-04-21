/-!
# Facts about `inductive` types in Lean 4

`inductive` is Lean's primitive for defining new types. Almost every
data type you'll meet (`Bool`, `Nat`, `List`, `Option`, `Sum`, `Prod`, ...)
is an inductive. Propositions like `Eq`, `And`, `Or`, `False`, `Exists`
are also inductives — the Curry-Howard correspondence means "proofs"
and "data" share the same machinery.

This file is a runnable reference. Every example typechecks.
-/

------------------------------------------------------------------------
-- 1. What an `inductive` declaration DOES
------------------------------------------------------------------------

/-!
Writing an `inductive` adds FIVE things to the environment:
  (a) A new type constant
  (b) One constructor per `|` clause
  (c) A recursor `T.rec` that captures structural induction
  (d) A cases-analyzer `T.casesOn` (non-recursive pattern match)
  (e) `noConfusion` principles — distinct constructors are not equal
-/

inductive Shape where
  | circle   (radius : Float) : Shape
  | rect     (width height : Float) : Shape
  | triangle (a b c : Float) : Shape

#check @Shape              -- Shape : Type
#check @Shape.circle       -- Float → Shape
#check @Shape.rect         -- Float → Float → Shape
#check @Shape.triangle     -- Float → Float → Float → Shape
#check @Shape.rec          -- (structural recursor, huge type)
#check @Shape.casesOn      -- case-analysis eliminator
#check @Shape.noConfusion  -- constructors-are-distinct

------------------------------------------------------------------------
-- 2. Constructors ARE functions
------------------------------------------------------------------------

/-!
A constructor is just a function that produces a value of the type,
tagged with which constructor it came from.
Constructors are NEVER equal to each other — this is built in.
-/

example : Shape := Shape.circle 1.0               -- partial application works
example : Float → Shape := Shape.rect 2.0          -- partially applied
example : Shape := .circle 1.0                    -- anonymous ctor (type inferred)

/-!
`noConfusion` lets you derive `False` from `ctorA x ≠ ctorB y`. You rarely
invoke it directly — `cases`/`contradiction`/`simp` use it under the hood.
-/

example (r : Float) (w h : Float) : Shape.circle r ≠ Shape.rect w h := by
  intro h; cases h  -- noConfusion closes the goal

------------------------------------------------------------------------
-- 3. Recursion: a type can mention ITSELF
------------------------------------------------------------------------

/-!
Recursive inductives must obey "strict positivity" — self-references
can only appear in positions that aren't "to the left of an arrow."
`Tree` below is fine; `BadType` commented below is not.
-/

inductive Tree where
  | leaf : Tree
  | node (left right : Tree) : Tree

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

-- BAD: self-reference to the left of an arrow (non-positive)
-- inductive BadType where
--   | mk : (BadType → BadType) → BadType
--
-- Lean rejects this because it would permit Russell-paradox-style constructions.

------------------------------------------------------------------------
-- 4. Polymorphism: parameters vs indices
------------------------------------------------------------------------

/-!
PARAMETERS appear before the colon in the type; they are FIXED across
all constructors. INDICES appear after the colon; they can VARY per
constructor.

`List α` is parameterized by `α`. `Vec α n` is indexed by `n`
(and parameterized by `α`).
-/

-- Parameterized only:
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- Parameters + indices (classic length-indexed vector):
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

-- Parameters are fixed: every `cons` returns `Vec α (n+1)` for the SAME α.
-- The index `n` varies: `nil` gives `Vec α 0`, `cons` gives `Vec α (n+1)`.

example : Vec Nat 0 := .nil
example : Vec Nat 2 := .cons 1 (.cons 2 .nil)

------------------------------------------------------------------------
-- 5. Pattern matching = using the recursor
------------------------------------------------------------------------

/-!
`match` is syntactic sugar for applying `T.rec` or `T.casesOn`. Every
constructor case in a match corresponds to a recursor argument.
-/

def Shape.area : Shape → Float
  | .circle r      => 3.14159 * r * r
  | .rect w h      => w * h
  | .triangle a b c =>
      let s := (a + b + c) / 2
      (s * (s-a) * (s-b) * (s-c)).sqrt

#eval Shape.area (.circle 1.0)           -- 3.14159
#eval Shape.area (.rect 2.0 3.0)         -- 6.0

------------------------------------------------------------------------
-- 6. Structural recursion + termination
------------------------------------------------------------------------

/-!
Lean's termination checker accepts recursive calls on STRUCTURALLY SMALLER
arguments (direct sub-terms of the match). This covers most "fold"-style
functions automatically.
-/

def MyList.length : MyList α → Nat
  | .nil       => 0
  | .cons _ xs => 1 + xs.length  -- xs is structurally smaller than `.cons _ xs`

-- For non-structural recursion, give `termination_by` (the measure) and
-- often `decreasing_by` (how to show the measure shrinks).
def myGcd : Nat → Nat → Nat
  | 0,   b => b
  | a+1, b => myGcd (b % (a+1)) (a+1)
termination_by a _ => a
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

------------------------------------------------------------------------
-- 7. `structure` is a one-constructor `inductive` + sugar
------------------------------------------------------------------------

/-!
These two declarations produce equivalent types. The `structure` form
adds record syntax, auto-projectors, structure eta, and `{ · with · }`
update syntax.
-/

structure PointS where
  x : Float
  y : Float

inductive PointI where
  | mk (x y : Float) : PointI

-- PointS has these extras:
example : PointS := { x := 1, y := 2 }   -- record syntax
example (p : PointS) : Float := p.x       -- auto-projector
example (p : PointS) : p = ⟨p.x, p.y⟩ := rfl  -- structure eta

-- PointI has only the constructor — you'd define `x`/`y` yourself:
def PointI.x : PointI → Float | .mk x _ => x
def PointI.y : PointI → Float | .mk _ y => y

------------------------------------------------------------------------
-- 8. `class` is `structure` + typeclass-registration
------------------------------------------------------------------------

/-!
A `class` is literally a `structure` with an `@[class]` attribute —
which makes Lean use typeclass inference for its arguments.
-/

class MyAdd (α : Type) where
  add : α → α → α

-- Equivalent (more verbose) declaration:
@[class] structure MyAdd' (α : Type) where
  add : α → α → α

-- You rarely write the second form; `class` is idiomatic.

------------------------------------------------------------------------
-- 9. `Prop` in depth: the universe of propositions
------------------------------------------------------------------------

/-!
## The core idea

In Lean, a PROPOSITION is a TYPE, and a PROOF is an ELEMENT of that type.

  "There exists a proof of P"   ≡   "the type P is inhabited"

The type of a proof IS the proposition it proves.
-/

#check (2 = 2 : Prop)           -- 2 = 2 is a TYPE
#check (rfl : (2 = 2))          -- rfl is a VALUE of that type — a proof

/-!
## The universe hierarchy

`Prop` sits BESIDE `Type`, not above/below. Both are "universes of types."
The split is SEMANTIC: what do the members represent?

  Prop       : Type          ← universe of propositions
  Type       : Type 1        ← universe of small data
  Type 1     : Type 2
  ...
-/

#check @Prop         -- Prop : Type
#check @Type         -- Type : Type 1

/-!
## Prop vs Type — the two defining rules

                    Prop                    Type
                    ─────                   ──────
  Members           propositions            data types
                    (2=2, p∧q, ∀x, P x)     (Nat, List α, Point)

  Their inhabitants proofs                  values

  Proof / value     PROOF IRRELEVANCE:      distinct values distinguishable
  distinguishability  all proofs of the     (42 ≠ 7 even though both : Nat)
                     same statement are
                     definitionally equal

  Runtime           ERASED (no info beyond  KEPT
                    "statement is true")
-/

-- Rule 1 demonstration: proof irrelevance
example (p q : 2 = 2) : p = q := rfl        -- always works in Prop!

-- Compare Type: values are NOT interchangeable
-- example : (42 : Nat) = (7 : Nat) := rfl  -- ERROR: values are distinct

/-!
## Curry-Howard: implication IS function type

The deepest fact about Prop: logical implication `P → Q` is literally
the SAME language construct as the function type `P → Q` (Π-type).
A proof of "P implies Q" is a function taking proofs-of-P to proofs-of-Q.

Similarly:
   ∀ x, P x       =  dependent function (x : α) → P x
   ∃ x, P x       =  inductive (Σ-like, but in Prop)
   P ∧ Q          =  inductive with one ctor holding both proofs
   P ∨ Q          =  inductive with two ctors (inl, inr)
   ¬ P            =  P → False
   True           =  inductive with one (trivial) ctor
   False          =  inductive with NO ctors (so no proof exists)
-/

-- Implication as function:
example (P Q : Prop) : P → Q → P :=
  fun hp _ => hp                                  -- just a function!

-- Modus ponens = function application:
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := hpq hp

-- Universal quantifier as Π-type:
example : ∀ n : Nat, n ≥ 0 := fun n => Nat.zero_le n

/-!
## Propositions are inductive types

Core logical connectives are declared as `inductive` types in `Prop`,
with constructors as the proof-introduction rules.

(Mathlib/core already has these; we re-declare for illustration.)
-/

inductive MyAnd (p q : Prop) : Prop where
  | intro : p → q → MyAnd p q
  -- One ctor = one way to prove: provide both sides.

inductive MyOr (p q : Prop) : Prop where
  | inl : p → MyOr p q
  | inr : q → MyOr p q
  -- Two ctors = two ways to prove: left or right.

inductive MyFalse : Prop
  -- Zero ctors = NO proofs possible. Uninhabited.

inductive MyTrue : Prop where
  | intro : MyTrue
  -- One ctor taking no args = trivially provable.

inductive MyEq {α : Type} (a : α) : α → Prop where
  | refl : MyEq a a
  -- The only way to prove `a = b` is when Lean sees a ≡ b definitionally.

-- `∃ x, P x` is inductive too — the Prop version of Σ:
inductive MyExists {α : Type} (p : α → Prop) : Prop where
  | intro (witness : α) (h : p witness) : MyExists p
  -- Provide a witness + a proof that the witness satisfies p.

/-!
## Proofs compose like programs

`cases h` on a proof of `p ∧ q` gives you `hp : p` and `hq : q` — same as
`cases x` on a `Prod` value gives the two components. `match` on a proof
of `p ∨ q` gives two branches. Proofs USE THE SAME ELIMINATION STORY as
programs. That's the whole Curry-Howard deal.
-/

example (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩
example (p q : Prop) (h : p ∨ q) : q ∨ p :=
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

/-!
## Why Prop is separate from Type

Four reasons:
  1. PROOF IRRELEVANCE — for propositions, only truth-value matters, not
     the particular proof. Equating all proofs of P lets Lean's kernel
     treat proofs as interchangeable. (In Type, that'd be catastrophic:
     equating 42 and 7 would break arithmetic.)
  2. RUNTIME ERASURE — propositions carry no computational content, so
     compiled code drops all `Prop`-valued fields. A `Subtype {x // P x}`
     at runtime is just its underlying value.
  3. AVOIDING PARADOXES — allowing proposition-typed values to freely
     mix with data (Curry-Howard isomorphism without restriction) leads
     to inconsistencies. Lean's impredicative `Prop` + predicative `Type`
     hierarchy is the standard fix.
  4. LARGE ELIMINATION RESTRICTION — you generally can't eliminate a
     Prop-valued inductive INTO Type (can't produce data from a mere
     proof of existence). Exceptions: subsingleton Props like `True`,
     `False`, or any Prop with ≤1 ctor — these can eliminate into Type.
-/

-- Demonstration of erasure: Subtype at runtime is just the value
example : {n : Nat // n > 0} := ⟨1, Nat.one_pos⟩
-- After compilation, this is just `1`. The proof `Nat.one_pos` vanishes.

/-!
## Key takeaway

Prop IS a universe of types — the SAME inductive/Π machinery as Type,
with two add-ons: proof irrelevance + runtime erasure. Every logical
connective you'll ever use (∀, ∃, ∧, ∨, →, ¬, =, True, False, Iff)
is either an inductive Prop or a Π-type landing in Prop.

  RULE OF THUMB:
    Type gives you DATA (values you can compute with).
    Prop gives you FACTS about that data (proofs you can cite).
    Together: dependent types = programming + proving in one language.
-/

-- Sanity-check with the reals:
example (_h : (2 : Nat) + 2 = 4) : True := trivial
example : (2 : Nat) + 2 = 4 := by rfl
example (h : True ∧ True) : True := h.1   -- projection from ∧

------------------------------------------------------------------------
-- 10. Mutual and nested inductives
------------------------------------------------------------------------

/-!
Several types can reference each other via `mutual`. Nested inductives
(constructors whose arguments use already-defined inductives like `List`)
are also supported.
-/

mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n+1)

  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n+1)
end

-- Nested: uses `List` in a constructor argument
inductive RoseTree (α : Type) where
  | node (value : α) (children : List (RoseTree α)) : RoseTree α

------------------------------------------------------------------------
-- 11. Universes
------------------------------------------------------------------------

/-!
Every inductive lives in some universe. Lean picks the smallest one that
contains all constructor arguments. `Prop`-valued inductives have special
rules (propositional universe, elimination restrictions for "large"
elimination into `Type`).
-/

#check @MyList       -- Type u → Type u
#check @MyAnd        -- Prop → Prop → Prop
#check @MyExists     -- {α : Type} → (α → Prop) → Prop

------------------------------------------------------------------------
-- 12. Anonymous constructor notation `⟨·⟩`
------------------------------------------------------------------------

/-!
For any SINGLE-constructor inductive (including every `structure`),
`⟨a, b, c⟩` builds the value. The type must be known from context.
-/

example : PointS     := ⟨1, 2⟩                     -- structure
example : Prod Nat String := ⟨3, "hi"⟩             -- product
example : MyAnd True True := ⟨.intro, .intro⟩      -- proposition

-- Does NOT work for multi-constructor inductives:
-- example : Vec Nat 2 := ⟨1, 2, ()⟩                -- ERROR: Vec has two ctors
-- You must name the constructor instead:
example : Vec Nat 2  := .cons 1 (.cons 2 .nil)

------------------------------------------------------------------------
-- 13. Constructor dot-notation `.ctor`
------------------------------------------------------------------------

/-!
`.ctor args` is short for `T.ctor args` when `T` is the expected type.
Works anywhere the expected type is known.
-/

example : MyList Nat := .cons 1 (.cons 2 .nil)     -- no need for MyList. prefix
example : Option Nat := .some 5                    -- same
example : Vec Nat 1  := .cons 0 .nil

------------------------------------------------------------------------
-- 14. Key principles (summary)
------------------------------------------------------------------------

/-!
  • An inductive introduces a new type + constructors + a recursor
    (structural induction principle).
  • Constructors are fully distinguishable — `ctorA ≠ ctorB`,
    `ctor a = ctor b ↔ a = b` (injectivity).
  • Strict positivity: self-references can't appear to the left of `→`.
  • Parameters are fixed across constructors; indices vary.
  • `match` / `cases` / `induction` are sugar for the recursor.
  • `structure` = one-constructor inductive + record sugar.
  • `class` = `structure` with typeclass resolution.
  • `Prop` connectives (`And`, `Or`, `Eq`, `Exists`, `False`) are all inductives.
  • Termination: structural recursion works automatically; otherwise use
    `termination_by` + `decreasing_by`.
  • Two patterns for recursion:
      – Structural (recur on sub-term of match argument)  — free termination proof
      – Well-founded (recur on smaller measure)            — manual termination proof
-/
