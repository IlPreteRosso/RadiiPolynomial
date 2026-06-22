import RadiiPolynomial.examples.Example77.Certificate
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Example 7.7 — Analytic branch corollary (function-space side)

`Certificate.lean` produced `main_theorem`: a unique sequence-space zero
`xTilde ∈ closedBall sol.toL1 r₀` of `F lam0 = a*a - c(lam0)`. This file lifts
that to the function-space identity:
$$\big(\text{eval}(\tilde a,\, t)\big)^2 = \lambda_0 + t \quad \text{for } |t| \le \nu.$$

The analytic series `t ↦ eval(xTilde, t)` is a square root of `λ₀ + t` on the
disk of convergence — the analytic branch of `√λ` near `λ₀`.

## "0-degree ODE" framing

Examples 81/83 are first-order IVPs: their `F(a) = 0` encodes
`(d/dt)x(t) = f(x(t))` via the differential shift `(n+1)·a_{n+1}`. Example 77
is a *0-degree ODE* — an algebraic constraint `f(x(t), t) = 0` with no
derivative — encoded as `F(a) = banachField ψ(a) - c = 0` (no shift). The
forward bridge collapses to a single application of `eval_mul` (Mertens) plus
a finite-support computation of `eval(c, t)`.

## Surface

- `xTilde` (`def`): canonical sequence-space zero.
- `x_analytic` (`def`): canonical analytic branch `t ↦ eval(xTilde, t)`.
- `x_analytic_sq_eq`: pinning theorem — the canonical branch satisfies
  `x_analytic(t)² = λ₀ + t` on `|t| ≤ ν`.

Branch *uniqueness* among analytic candidates with the right initial value
and trajectory bound (using IFT or elementary continuity since `2x_0 ≠ 0`)
is currently not formalized — deferred until paper section needs it.
-/

open Set Metric RadiiPolynomial

noncomputable section

namespace Example77.Cert

open Example77

/-- The eval of the parameter sequence `c(λ₀) = (λ₀, 1, 0, 0, …)` at `t` is
the affine `λ₀ + t`. The tsum collapses because `paramSeq` has support `{0, 1}`. -/
lemma eval_c_eq (lam0 : ℝ) (t : ℝ) :
    l1Weighted.eval (c lam0 : l1Weighted ν_val) t = lam0 + t := by
  show ∑' n, l1Weighted.toSeq (c lam0) n * t ^ n = lam0 + t
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) ?_]
  · simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)),
      Finset.sum_singleton]
    show l1Weighted.toSeq (c lam0) 0 * t ^ 0 +
         l1Weighted.toSeq (c lam0) 1 * t ^ 1 = lam0 + t
    simp [c, paramSeq]
  · intro n hn
    have h0 : n ≠ 0 := fun h => hn (by simp [h])
    have h1 : n ≠ 1 := fun h => hn (by simp [h])
    show l1Weighted.toSeq (c (ν := ν_val) lam0) n * t ^ n = 0
    have h : l1Weighted.toSeq (c (ν := ν_val) lam0) n = 0 := by
      simp only [c, l1Weighted.mk_apply]
      cases n with
      | zero => exact absurd rfl h0
      | succ k =>
        cases k with
        | zero => exact absurd rfl h1
        | succ m => simp [paramSeq]
    rw [h]; ring

/-- The canonical sequence-space zero (witness of `main_theorem`'s existential). -/
def xTilde : l1Weighted ν_val := main_theorem.exists.choose

private lemma xTilde_spec :
    xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀ ∧
    F lam0 xTilde = 0 :=
  main_theorem.exists.choose_spec

lemma xTilde_ball : xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀ :=
  xTilde_spec.1

lemma xTilde_F_zero : F lam0 xTilde = 0 := xTilde_spec.2

/-- The canonical analytic branch: `t ↦ eval(xTilde, t)`. -/
def x_analytic : ℝ → ℝ := fun t => l1Weighted.eval xTilde t

/-- **Pinning theorem**: the canonical analytic branch satisfies
`x_analytic(t)² = λ₀ + t` on `|t| ≤ ν`. Forward bridge content: `F xTilde = 0
→ xTilde · xTilde = c(λ₀) → eval(xTilde, t)² = eval(c(λ₀), t) = λ₀ + t`. The
middle step uses `eval_mul` (Mertens). -/
theorem x_analytic_sq_eq {t : ℝ} (ht : |t| ≤ (ν_val : ℝ)) :
    (x_analytic t) ^ 2 = (lam0 : ℝ) + t := by
  have hF : xTilde * xTilde - c lam0 = 0 := xTilde_F_zero
  have hsq : xTilde * xTilde = (c lam0 : l1Weighted ν_val) := sub_eq_zero.mp hF
  show (l1Weighted.eval xTilde t) ^ 2 = (lam0 : ℝ) + t
  rw [pow_two, l1Weighted.eval_mul xTilde xTilde ht, hsq, eval_c_eq]

end Example77.Cert
