import Mathlib.Data.Real.Basic

/-!
# Lean 4 kernel primitives — a live tour

Everything in Lean/Mathlib is built from FIVE kernel primitives:

  1. Universes       `Sort u`, `Prop = Sort 0`, `Type u = Sort (u+1)`
  2. Function types  `(x : α) → β`       (Π-types)
  3. Inductive types `inductive T where | ...`
  4. Quotients       `Quot r`, `Quotient s`
  5. Definitions     `def`, `axiom` (glue, no new type-forming power)

Everything else — `structure`, `class`, `theorem`, `abbrev` — is SUGAR
that elaborates down to these. This file exhibits each primitive with a
runnable example.
-/

------------------------------------------------------------------------
-- 1. Universes: the type of types
------------------------------------------------------------------------

/-!
`Sort u` is the universe hierarchy. Two special names:
  `Prop = Sort 0`         — propositions (proof-irrelevant)
  `Type u = Sort (u+1)`   — data (proof-relevant)

Universes prevent Russell's paradox (no "set of all sets").
-/

#check Prop         -- Prop : Type
#check Type         -- Type : Type 1
#check Type 1       -- Type 1 : Type 2
#check Sort 0       -- Prop : Type
#check Sort 1       -- Type : Type 1

-- Universe-polymorphic declarations:
universe u v
def id' {α : Sort u} (x : α) : α := x    -- works in any universe
#check @id'                              -- {α : Sort u_1} → α → α

------------------------------------------------------------------------
-- 2. Function types (Π-types): the universal primitive
------------------------------------------------------------------------

/-!
`(x : α) → β` is the DEPENDENT function type. When `β` doesn't mention
`x`, it collapses to `α → β` (simple function).

Every function, every quantifier, every implication uses this.
-/

-- Simple function type:
#check (fun n : Nat => n + 1)        -- Nat → Nat

-- Dependent function type — return type depends on the argument value:
def replicate : (n : Nat) → α → List α
  | 0,     _ => []
  | n+1,   x => x :: replicate n x

-- Quantifier ∀ is JUST a Π-type:
#check @Nat.zero_le         -- ∀ (n : ℕ), 0 ≤ n     i.e.,   (n : Nat) → 0 ≤ n

-- Implication → is JUST a non-dependent Π-type:
example (p q : Prop) : p → q → p := fun hp _ => hp

------------------------------------------------------------------------
-- 3. Inductive types: the main type-former for data
------------------------------------------------------------------------

/-!
`inductive T where | c1 : ... | c2 : ...` declares a new type with
constructors, recursor, no-confusion principle.

`structure` is sugar for a one-constructor inductive.
`class` is sugar for a structure marked as a typeclass.
-/

inductive MyBool where | false | true      -- sum type
inductive MyNat  where | zero | succ (n : MyNat)   -- recursive
inductive MyList (α : Type) where          -- polymorphic
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- Structure = 1-ctor inductive + record sugar:
structure Pt where
  x : Float
  y : Float

-- Class = structure + @[class]:
class MyAdd (α : Type) where
  add : α → α → α

-- All three show their inductive nature via the recursor:
#check @MyList.rec    -- structural induction principle
#check @Pt.rec        -- structure has a recursor too (trivial)
#check @MyAdd.rec     -- class has a recursor (typeclass dictionary eliminator)

------------------------------------------------------------------------
-- 4. Quotient types: the "small but critical" primitive
------------------------------------------------------------------------

/-!
`Quot r : Type` takes a relation `r : α → α → Prop` and gives a type
where `a` and `b` are identified when `r a b` holds. `Quot.mk` sends
values in, `Quot.lift` lets you define functions out (provided they
respect `r`).

`Quotient s` is the specialized version requiring `s` to be an equivalence.

Used for: ℝ (Cauchy completion), ℤ/n, free groups, tensor products,
colimits, localizations — anything "set of equivalence classes."
-/

-- Baby example: build ℤ from pairs of Nats via the relation
-- (a, b) ~ (c, d) ↔ a + d = c + b
def IntRel : (Nat × Nat) → (Nat × Nat) → Prop
  | (a, b), (c, d) => a + d = c + b

def MyInt : Type := Quot IntRel

-- Introduce elements:
def MyInt.mk (a b : Nat) : MyInt := Quot.mk IntRel (a, b)

example : MyInt := MyInt.mk 5 3   -- represents 5 - 3 = 2

-- Two representatives are EQUAL in MyInt (not just related) if they agree:
example : MyInt.mk 5 3 = MyInt.mk 7 5 := Quot.sound (by
  show 5 + 5 = 7 + 3
  rfl)

-- This is exactly how Mathlib's ℝ works under the hood:
--   ℝ = Real (structure wrapper)
--        └── field: cauchy : CauSeq.Completion.Cauchy abs
--                    └── defined as Quot of an equivalence on CauSeqs

------------------------------------------------------------------------
-- 5. Definitions: gluing without adding type-forming power
------------------------------------------------------------------------

/-!
`def` introduces a named value. It doesn't add new types, just names
existing ones / binds values. `abbrev` is `def` + `@[reducible]`.
`theorem` is `def` whose type lives in `Prop`.
`axiom` postulates a value without a body (use sparingly!).
-/

def two : Nat := 2                      -- names a value
abbrev TwoNat : Type := Nat             -- transparent alias
theorem two_eq_two : two = 2 := rfl    -- proof (= def into Prop)
-- axiom bigAxiom : False               -- NEVER write this in real code

------------------------------------------------------------------------
-- 6. How Mathlib's "types" decompose into primitives
------------------------------------------------------------------------

/-!
A quick audit of types you'd encounter, tagged with their primitive:

  Nat, Int, List α, Option α, Prod α β, Sum α β   → inductive
  Bool, Char, String                              → inductive
  Fin n, Subtype p                                → inductive (structure)

  And, Or, Exists, Eq, True, False, Iff           → inductive (in Prop)
  ∀, ∃, →                                         → Π-types

  ℚ                                               → inductive (structure)
  ℝ                                               → inductive (structure)
                                                     wrapping a Quot
  ℂ                                               → inductive (structure)
                                                     of two ℝ's

  Group, Ring, Field, Module, Algebra             → inductive (class/structure)
  NormedAddCommGroup, NormedField                 → inductive (class)

  Quotient groups ℤ/n, G/H                        → Quot
  Free group, tensor product V ⊗ W                → Quot
  Limits / colimits in a category                 → Quot (when concrete)

  Function space α → β, linear maps α →ₗ[R] β     → Π-type / structure
-/

------------------------------------------------------------------------
-- 7. Everything together: ℝ's decomposition
------------------------------------------------------------------------

/-!
Mathlib's `Real` (= ℝ), from `Mathlib/Data/Real/Basic.lean`:

    structure Real where ofCauchy ::
      cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)

How this uses all FIVE primitives:

  • `structure` — inductive with one ctor (`ofCauchy`)
  • `Cauchy abs` — defined as `Quot r` where `r` is
                    "difference tends to 0" on Cauchy sequences
  • `CauSeq` — structure (inductive) holding a sequence + Cauchy proof
  • sequence = function `Nat → ℚ` — Π-type
  • `ℚ` itself — structure wrapping `Int × Nat` plus a coprimality proof
  • `Int` — inductive (`ofNat | negSucc`)
  • `Nat` — inductive (`zero | succ`)
  • Everything types at universe levels via `Sort u`

So ℝ's full definition chain touches:
  inductive + structure + Π-type + Quot + def + universes
  = every kernel primitive.
-/

#check @Real                 -- Real : Type
#check @Real.ofCauchy        -- Cauchy abs → Real     (inductive ctor)
#check @Real.cauchy          -- Real → Cauchy abs     (projector)

------------------------------------------------------------------------
-- 8. What's NOT in the kernel (common sugar)
------------------------------------------------------------------------

/-!
These elaborate to the primitives above, but are NOT kernel features:

  `structure ... where`         →  inductive + projectors + eta
  `class ... where`             →  structure + @[class] attribute
  `theorem T : P := ...`        →  def T : P := ...
  `abbrev A := ...`             →  def A := ... with @[reducible]
  `instance : C X := ...`       →  def anonymous_n : C X := ... + @[instance]
  `@[simp]`, `@[to_additive]`   →  elaborator hooks, not primitives
  `match ... with | ...`        →  applies the recursor of the matched type
  `let x := e in ...`           →  ((fun x => ...) e)   [Π-type]
  `do` notation                 →  translates to `>>=` / `pure`  [function + Π]
  `⟨a, b, c⟩`                   →  constructor application  [inductive]

Nothing here is "new" to the kernel — just ergonomic syntax.
-/

------------------------------------------------------------------------
-- 9. The absolute-minimum kernel (cheat sheet)
------------------------------------------------------------------------

/-!
  ┌──────────────────────────────────────────────────────────────┐
  │ Lean 4 kernel type-formers:                                  │
  │                                                              │
  │   Sort u              — universes                            │
  │   (x : α) → β         — function types (Π)                   │
  │   inductive T         — inductive types + recursor           │
  │   Quot r              — quotients                            │
  │                                                              │
  │ Plus:                                                        │
  │   def name : T := e   — naming / binding                     │
  │   axiom name : T      — postulation (reduces trust)          │
  │                                                              │
  │ Everything else in Mathlib reduces to these five primitives. │
  └──────────────────────────────────────────────────────────────┘
-/
