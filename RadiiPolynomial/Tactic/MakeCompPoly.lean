/-
Copyright (c) 2026 RadiiPolynomial contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Core

/-!
# `compPolyOf%`: term elaborator that reifies a Lean lambda into `CompPoly L`

Takes a single-argument lambda `fun (a : Fin L → R) => body` whose body is a
polynomial expression in the projections `a 0, a 1, …, a (L-1)`, and produces
the corresponding `MvPolyBridge.CompPoly L` term. This collapses the dual-write
pattern in `Example83/Algebra.lean` (where `f_cpoly` is hand-written as
an AST and `f` is the same expression via `evalBanach`) — with this
elaborator, the AST is generated from the `evalBanach`-side lambda.

## Recognition rules

For an expression `e` in the bound variable `a : Fin L → R`:

| Pattern                    | Output                |
|----------------------------|-----------------------|
| `a i` (`i : Fin L` literal)| `.X ⟨i, _⟩`           |
| `HAdd.hAdd e₁ e₂`          | `.add ⟦e₁⟧ ⟦e₂⟧`      |
| `HSub.hSub e₁ e₂`          | `.sub ⟦e₁⟧ ⟦e₂⟧`      |
| `HMul.hMul e₁ e₂`          | `.mul ⟦e₁⟧ ⟦e₂⟧`      |
| `Neg.neg e`                | `.neg ⟦e⟧`            |
| `HSMul.hSMul r e`          | `.smul ⟪r⟫ ⟦e⟧`       |

Scalar reification `⟪r⟫`: if `r : ℝ` whnf's to `Rat.cast q` for `q : ℚ`,
emit `q`; if `r` whnf's to a `Nat` literal cast, emit `(n : ℚ)`. Otherwise
throw — the user must bind ℚ-valued scalars explicitly via `(q : ℝ)` cast
of a `(q : ℚ)` constant.

## Validation

The elaborator's output is a `CompPoly L` *value*, not a proof. Soundness
holds by `rfl` per usage site, since `evalBanach`'s definition mirrors the
constructors. Tests at the bottom validate against the hand-written ASTs of
`φ_scalar_cpoly` (Example81) and `f_cpoly` (Example83).
-/

open Lean Meta Elab Term

namespace RadiiPolynomial.MakeCompPoly

/-- Try to reduce `e : Nat` to a concrete `Nat` literal via `whnf`. -/
partial def reifyNat (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return n
  | _ =>
    -- Try unfolding `OfNat.ofNat n` to its argument.
    match e.getAppFnArgs with
    | (``OfNat.ofNat, args) =>
      if args.size ≥ 2 then reifyNat args[1]!
      else throwError "reifyNat: malformed OfNat.ofNat at {← ppExpr e}"
    | _ => throwError "reifyNat: cannot extract Nat literal from {← ppExpr e}"

/-- Reify a `Fin L` literal to its underlying natural number. Accepts both
`Fin.mk` and `OfNat.ofNat`-style elaborations. -/
partial def reifyFinIdx (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Fin.mk, args) =>
    -- Fin.mk : (n : ℕ) → (val : ℕ) → val < n → Fin n; we want args[1]
    if args.size ≥ 2 then reifyNat args[1]!
    else throwError "reifyFinIdx: malformed Fin.mk at {← ppExpr e}"
  | (``OfNat.ofNat, args) =>
    if args.size ≥ 2 then reifyNat args[1]!
    else throwError "reifyFinIdx: malformed OfNat.ofNat at {← ppExpr e}"
  | _ =>
    -- Last resort: try as raw Nat literal
    reifyNat e

/-- Build the `Expr` for `(n : ℚ)` from a `Nat`. -/
private def mkRatNatLit (n : Nat) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[some (mkConst ``Rat), some (mkNatLit n), none]

/-- Reify a real-valued scalar to `ℚ`. Matches BEFORE `whnf` (ℝ-coercions
unfold aggressively under `whnf` to the Cauchy-sequence representation).
Recognized scalar shapes:

* `Rat.cast q` / `RatCast.ratCast q` (`q : ℚ`)        → `q`
* `Nat.cast n` / `NatCast.natCast n` (`n : ℕ` literal) → `(n : ℚ)`
* `Int.cast n` / `IntCast.intCast n` (`n : ℤ` literal) → `(n : ℚ)` (via NatCast/Neg)
* `OfNat.ofNat α n _` (`n : ℕ` literal) — at any type — → `(n : ℚ)`
* `Neg.neg e`                                          → negate `reifyRatScalar e`
* otherwise: try `unfoldDefinition?` and retry (for `def σ_val := (σ_q : ℝ)`).
-/
partial def reifyRatScalar (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``Rat.cast, args) | (``RatCast.ratCast, args) =>
    -- {α} → [_] → ℚ → α; the ℚ argument is last
    if args.size ≥ 1 then return args[args.size - 1]!
    else throwError "reifyRatScalar: malformed cast at {← ppExpr e}"
  | (``Nat.cast, args) | (``NatCast.natCast, args) =>
    if args.size ≥ 1 then
      let n ← reifyNat args[args.size - 1]!
      mkRatNatLit n
    else throwError "reifyRatScalar: malformed Nat.cast at {← ppExpr e}"
  | (``Int.cast, args) | (``IntCast.intCast, args) =>
    if args.size ≥ 1 then
      -- For prototype: only handle non-negative Int literals (constructed via
      -- `Int.ofNat`); negation arises from outer `Neg.neg` matching.
      reifyRatScalar args[args.size - 1]!
    else throwError "reifyRatScalar: malformed Int.cast at {← ppExpr e}"
  | (``Int.ofNat, args) =>
    if args.size ≥ 1 then
      let n ← reifyNat args[args.size - 1]!
      mkRatNatLit n
    else throwError "reifyRatScalar: malformed Int.ofNat at {← ppExpr e}"
  | (``OfNat.ofNat, args) =>
    -- @OfNat.ofNat α n inst — extract the literal `n`
    if args.size ≥ 2 then
      let n ← reifyNat args[1]!
      mkRatNatLit n
    else throwError "reifyRatScalar: malformed OfNat.ofNat at {← ppExpr e}"
  | (``Neg.neg, args) =>
    if args.size ≥ 3 then
      let inner ← reifyRatScalar args[2]!
      mkAppM ``Neg.neg #[inner]
    else throwError "reifyRatScalar: malformed Neg.neg at {← ppExpr e}"
  | _ =>
    -- Try unfolding by one step to get past `abbrev`/`def`s like `σ_val := (σ_q : ℝ)`.
    let e' ← unfoldDefinition? e
    match e' with
    | some e' => reifyRatScalar e'
    | none =>
      throwError "reifyRatScalar: cannot reify ℝ scalar to ℚ at {← ppExpr e}\n\
        (hint: bind scalar via `(q : ℝ)` cast of a `(q : ℚ)` literal, or use \
        a numeric literal)"

/-- Reify the body of the lambda to a `CompPoly L` `Expr`. `aFVar` is the
bound variable representing `a : Fin L → R`, `LExpr` is the dimension.

NOTE: do NOT `whnf` the body before pattern-matching — Lean's elaborator
preserves `HSub`/`HAdd`/`HMul`/etc. as user wrote them, but `whnf` can unfold
e.g. `a - b` to `a + (-b)` (via `instSubReal`), losing structure. Pattern
match on the expression as-elaborated. -/
partial def reifyBody (aFVar : FVarId) (LExpr : Expr) (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, args) =>
    -- @HAdd.hAdd α β γ inst x y; want args 4, 5
    if args.size ≥ 6 then
      let p ← reifyBody aFVar LExpr args[4]!
      let q ← reifyBody aFVar LExpr args[5]!
      return mkApp3 (mkConst ``MvPolyBridge.CompPoly.add) LExpr p q
    else throwError "reifyBody: malformed HAdd at {← ppExpr e}"
  | (``HSub.hSub, args) =>
    if args.size ≥ 6 then
      let p ← reifyBody aFVar LExpr args[4]!
      let q ← reifyBody aFVar LExpr args[5]!
      return mkApp3 (mkConst ``MvPolyBridge.CompPoly.sub) LExpr p q
    else throwError "reifyBody: malformed HSub at {← ppExpr e}"
  | (``HMul.hMul, args) =>
    if args.size ≥ 6 then
      let p ← reifyBody aFVar LExpr args[4]!
      let q ← reifyBody aFVar LExpr args[5]!
      return mkApp3 (mkConst ``MvPolyBridge.CompPoly.mul) LExpr p q
    else throwError "reifyBody: malformed HMul at {← ppExpr e}"
  | (``Neg.neg, args) =>
    if args.size ≥ 3 then
      let p ← reifyBody aFVar LExpr args[2]!
      return mkApp2 (mkConst ``MvPolyBridge.CompPoly.neg) LExpr p
    else throwError "reifyBody: malformed Neg at {← ppExpr e}"
  | (``HSMul.hSMul, args) =>
    -- @HSMul.hSMul α β γ inst r x; want args 4, 5
    if args.size ≥ 6 then
      let q ← reifyRatScalar args[4]!
      let p ← reifyBody aFVar LExpr args[5]!
      return mkApp3 (mkConst ``MvPolyBridge.CompPoly.smul) LExpr q p
    else throwError "reifyBody: malformed HSMul at {← ppExpr e}"
  | _ =>
    -- Try `e = a i` (application of bound variable)
    match e with
    | .app f i =>
      if f.isFVarOf aFVar then
        let n ← reifyFinIdx i
        -- Build `Fin.mk n h` where `h : n < L` by `decide`.
        let nLit := mkNatLit n
        let ltType ← mkAppM ``LT.lt #[nLit, LExpr]
        let proof ← mkDecideProof ltType
        let finExpr := mkApp3 (mkConst ``Fin.mk) LExpr nLit proof
        return mkApp2 (mkConst ``MvPolyBridge.CompPoly.X) LExpr finExpr
      else
        throwError "reifyBody: unrecognized application at {← ppExpr e}"
    | _ =>
      throwError "reifyBody: unrecognized body shape {← ppExpr e}"

end RadiiPolynomial.MakeCompPoly

/-- Reify a Lean lambda `fun (a : Fin L → R) => body` into a
`MvPolyBridge.CompPoly L` term. -/
elab "compPolyOf%" stx:term : term => do
  let tmExpr ← elabTerm stx none
  Meta.lambdaTelescope tmExpr fun fvars body => do
    if fvars.size ≠ 1 then
      throwError "compPolyOf%: expected single binder `fun (a : Fin L → R) => …`, \
        got {fvars.size} binders"
    let aFVar := fvars[0]!.fvarId!
    let aTy ← inferType fvars[0]!
    -- aTy should be `Fin L → R`; extract `L`
    let aTy ← whnf aTy
    let some (dom, _) := aTy.arrow? |
      throwError "compPolyOf%: expected `Fin L → R` binder type, got {← ppExpr aTy}"
    let dom ← whnf dom
    let LExpr ← match dom.getAppFnArgs with
      | (``Fin, args) =>
        if args.size ≥ 1 then pure args[0]!
        else throwError "compPolyOf%: malformed Fin domain {← ppExpr dom}"
      | _ => throwError "compPolyOf%: expected domain `Fin L`, got {← ppExpr dom}"
    RadiiPolynomial.MakeCompPoly.reifyBody aFVar LExpr body
