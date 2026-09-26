import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

/-!
# Rational grid helpers

Small facts about the `Array` encodings of rational certificate data (columns, coefficient
lists) that exact-arithmetic certificates read back into `Fin`-indexed matrices.

- `getD_ofFn_fin`: `getD` of `Array.ofFn` at a `Fin` index
-/

namespace RadiiPolynomial.Certification.Rational

/-- `getD` of `Array.ofFn` at a `Fin` index. General in `α`, `n`, `f`, `d`. -/
theorem getD_ofFn_fin {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

end RadiiPolynomial.Certification.Rational
