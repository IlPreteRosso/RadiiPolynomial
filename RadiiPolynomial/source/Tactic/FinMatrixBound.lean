/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.BridgeNative
import LeanCert.Tactic.IntervalAuto
import RadiiPolynomial.source.LeanCertEval

/-!
# `finmatrix_bound`: Matrix Norm Tactic via native_decide

Proves bounds of the form `finWeightedMatrixNorm ν M ≤ C` (or block-level
`finiteBlockMatrixNorm ν A ≤ C`) using a bridge lemma + `native_decide`.

The user provides the bridge lemma fully applied except for the final
`hle : ... ≤ C` argument. The tactic closes that argument with `native_decide`.

## Usage

```lean
-- Single matrix: finWeightedMatrixNorm ν M ≤ C
finmatrix_bound (l1Weighted.finWeightedMatrixNorm_le_of_Q_le _ cols ν_q hcols hν)

-- Block matrix: finiteBlockMatrixNorm ν A ≤ C  (1 native_decide instead of L×L)
finmatrix_bound (finiteBlockMatrixNorm_le_of_Q_le _ blockCols ν_q hcols hν)
```

## Architecture

The tactic:
1. Elaborates the bridge term (which has one remaining argument of type `_ ≤ _`)
2. Creates a fresh mvar for the `hle` argument
3. Applies the bridge proof with the mvar
4. Calls `closeBridgeWithNativeDecide` to close `hle` with `native_decide`
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

/-- Prove a matrix norm bound by applying a bridge lemma and closing
    the ℚ certificate check with `native_decide`.

    Usage: `finmatrix_bound bridgeTerm` where `bridgeTerm` is the bridge
    lemma applied to all arguments except the final `hle : ... ≤ C`. -/
syntax (name := finMatrixBound) "finmatrix_bound" term : tactic

elab_rules : tactic
  | `(tactic| finmatrix_bound $bridgeTm) => do
    let goal ← getMainGoal
    let goalType ← goal.getType

    goal.withContext do
      -- Elaborate the bridge term to get its type
      -- The bridge should have type: (hle : X ≤ C) → goalType
      -- i.e., it's a function waiting for the ℚ check proof
      let bridgeExpr ← Tactic.elabTerm bridgeTm none

      -- Infer the type to find the remaining argument
      let bridgeTy ← inferType bridgeExpr

      -- The bridge type should be a forall/arrow: (hle : checkExpr) → result
      -- Extract the check type
      let checkTy ← match bridgeTy with
        | .forallE _ ty _ _ => pure ty
        | _ =>
          -- Maybe the bridge is already fully applied — try direct assignment
          if ← isDefEq bridgeTy goalType then
            goal.assign bridgeExpr
            return
          throwError "finmatrix_bound: bridge term has unexpected type.\n\
            Expected: (hle : _ ≤ _) → {← ppExpr goalType}\n\
            Got: {← ppExpr bridgeTy}"

      -- Create mvar for the check proof
      let checkMVar ← mkFreshExprMVar (some checkTy) (kind := .syntheticOpaque)

      -- Apply bridge with the check mvar
      let proof := mkApp bridgeExpr checkMVar

      -- Close with native_decide (+ converter fallback)
      closeBridgeWithNativeDecide goal goalType proof checkMVar "finmatrix_bound" #[
        do evalTactic (← `(tactic| intro h; exact h)),
        do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
      ]

/-- Prove a matrix norm bound by decomposing into per-column sums and closing
    each with `finsum_bound using colNormTermEval`.

    Usage: `finmatrix_bound using cols hcols ν_q hν`
    where:
    - `cols : Fin (N+1) → Array ℚ` — ℚ column arrays for the matrix
    - `hcols : ∀ j i, M i j = ((cols j).getD i 0 : ℝ)` — bridge proof
    - `ν_q : ℚ` — weight as ℚ
    - `hν : (ν : ℝ) = (ν_q : ℝ)` — weight bridge

    Unlike `finmatrix_bound (bridge)` which uses exact ℚ arithmetic + `native_decide`,
    this variant uses dyadic interval arithmetic via `finsum_bound`, avoiding potential
    rational blowup for large N. The tactic automates the `max_j (∑_i ...)` aggregation:
    1. Decomposes `finWeightedMatrixNorm` into per-column `matrixColNorm` bounds
    2. Bridges each column to `arrayColNormIccSum`
    3. Calls `finsum_bound using colNormTermEval` for each column -/
syntax (name := finMatrixDyadic)
  "finmatrix_dyadic" term "," term "," term "," term : tactic

elab_rules : tactic
  | `(tactic| finmatrix_dyadic $cols, $hcols, $nuQ, $hnu) => do
    -- Use the decomposition bridge (takes M explicitly) + per-column finsum_bound
    evalTactic (← `(tactic|
      exact RadiiPolynomial.FiniteWeightedNorm.finWeightedMatrixNorm_le_via_cols
        _ $cols _ $hcols (fun j => by
          unfold RadiiPolynomial.FiniteWeightedNorm.arrayColNormIccSum
          have hν_rw := $hnu; rw [hν_rw]
          fin_cases j <;>
            finsum_bound using
              (RadiiPolynomial.colNormTermEval _ $nuQ _)
              (fun k _ _ => RadiiPolynomial.colNormTermEval_correct _ $nuQ _ k _))))

end LeanCert.Tactic
