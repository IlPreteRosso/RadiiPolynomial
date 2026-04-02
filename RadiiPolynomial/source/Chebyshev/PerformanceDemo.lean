import RadiiPolynomial.source.Chebyshev.L1ChebyshevAlgebra

/-!
# Performance Demo: Subtype Elaboration Cost

## What Lean is doing in the timeout

When `comp_injective` checks `(fun k => ‖c k‖) ∘ (· + 1) =?= fun k => ‖c (k + 1)‖`
at the `l1Chebyshev` level, Lean's `isDefEq` unfolds `‖c k‖` through:

```
‖c k‖
= ‖(c : lpOneAlg ℤ (ScaledRealZ ν)) k‖                  -- abbrev l1Chebyshev
= ‖c.toLp k‖                                         -- CoeFun (lpOneAlg)
= ‖(c.toLp : lp (ScaledRealZ ν) 1) k‖                -- structure field
= ‖(c.toLp.val k : ScaledRealZ ν k)‖                 -- Subtype coercion
= |ScaledRealZ.toReal (c.toLp.val k)| * ↑ν ^ k.natAbs -- ScaledRealZ.instNorm
```

This expansion happens on BOTH sides of the `=?=` check, with `k` vs `k + 1`.
Each side produces deeply nested terms with dependent types (the `k` in `ScaledRealZ ν k`
changes the type). Lean structurally compares these huge terms, consuming 800k+ heartbeats.

## The fix

`lpOneAlg.summable_norm_shift` proves at the generic `lpOneAlg M E` level where `‖f m‖` is
an OPAQUE norm — no `ScaledRealZ` to unfold. The `comp_injective` check becomes
`‖f (m + s)‖ =?= (fun m => ‖f m‖) (m + s)` which is a single beta reduction. Instant.
-/

open scoped BigOperators Topology NNReal ENNReal
open RadiiPolynomial

noncomputable section

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-! ## Demo 1: SLOW — comp_injective at l1Chebyshev level (TIMEOUT at 200k) -/

-- Uncomment to see the timeout:
-- set_option maxHeartbeats 200000 in
-- #check fun (c : l1Chebyshev ν) =>
--   (lpOneAlg.summable_norm c).comp_injective (add_left_injective (1 : ℤ))
-- -- ERROR: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)

-- With 1.6M heartbeats it works — proving the math is correct but elaboration is expensive:
set_option maxHeartbeats 1600000 in
theorem slow_shift (c : l1Chebyshev ν) :
    Summable (fun k : ℤ => ‖c (k + 1)‖) :=
  (lpOneAlg.summable_norm c).comp_injective (add_left_injective 1)

/-! ## Demo 2: FAST — pre-proved at lpOneAlg level (default 200k, instant) -/

-- Same result, default heartbeats. comp_injective was already resolved generically.
theorem fast_shift (c : l1Chebyshev ν) :
    Summable (fun k : ℤ => ‖c (k + 1)‖) :=
  lpOneAlg.summable_norm_shift c 1

/-! ## Demo 3: Equiv.tsum_eq — type annotation matters for rw

`Equiv.tsum_eq` returns `∑' k, f (⇑(Equiv.addRight s) k) = ∑' k, f k`.
The LHS has `Equiv.addRight s` which doesn't syntactically match `k + s`.
Providing an explicit type annotation forces the definitional check at
definition time, so `rw` can match later. -/

-- BAD pattern (rw fails):
example (c : l1Chebyshev ν) (goal : ∑' k : ℤ, ‖c (k + 1)‖ = 0) : False := by
  have ht := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => ‖c k‖)
  -- ht : ∑' k, ‖c (⇑(Equiv.addRight 1) k)‖ = ∑' k, ‖c k‖
  -- rw [ht] at goal  -- would FAIL: can't match Equiv.addRight vs k + 1
  sorry  -- just demonstrating rw failure

-- GOOD pattern (rw works):
example (c : l1Chebyshev ν) (goal : ∑' k : ℤ, ‖c (k + 1)‖ = 0) : False := by
  have ht : ∑' k : ℤ, ‖c (k + 1)‖ = ∑' k : ℤ, ‖c k‖ :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => ‖c k‖)
  -- ht : ∑' k, ‖c (k + 1)‖ = ∑' k, ‖c k‖   ← matches!
  rw [ht] at goal  -- works!
  sorry  -- just demonstrating rw success

end
