import RadiiPolynomial.Operators.BlockDiagonal.Scalar
import RadiiPolynomial.Core.AlgebraZ2

/-!
# Polynomial zeros on `ℓ¹_ν`: the real-side operators and bounds

The family `P(x) - c = 0` on `ℓ¹_ν` for a univariate polynomial `P : CompPoly 1` of any degree
(`polyMap P c`). A `PolyZeroReal` carries the real data of one member: the polynomial, the
truncation `N`, the finite block `Afin` of the approximate inverse `A`, its tail diagonal `tail`,
and the coefficients `dcoef` of `P′(x̄)`. From them:

* `A` — the approximate inverse (finite block `Afin`, constant tail `tail`);
* `Adag` — the approximate derivative `A† = DF^(N)(x̄)`: the lower-triangular Cauchy matrix of
  `dcoef` with tail `dcoef 0`;
* `E` — the tail operator `-leftMul (P′(x̄) - dcoef 0 · 1)` that dominates `A† - DF(x̄)`.

The bounds hold for any `ν`, `x̄`, `c`; the only link to `x̄` is the coefficient hypothesis
`∀ n, (P′(x̄))ₙ = dcoef n`. Exact arithmetic on concrete data lives in the certification layer.

## Main results

- `A_toSeq` — the action of `A` coefficientwise
- `tailCancel` — `A·A† = 1` on tail modes when `tail · dcoef 0 = 1`
- `fin_kill`, `tail_eq` — `A† - DF(x̄)` vanishes on finite modes and equals `E` on tail modes
- `Z₁_le` — `‖A (A† - DF(x̄))‖ ≤ |tail| · ‖P′(x̄) - dcoef 0 · 1‖`
- `Z₂_le` — `‖A (DF(c') - DF(x̄))‖ ≤ derivativeLipschitzBound P (‖x̄‖ + r₀) · ‖A‖ · r₀` on the ball
-/

open MvPolyBridge
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le)

namespace RadiiPolynomial

/-- The real data of one member of the family `P(x) - c = 0` on `ℓ¹_ν`: a univariate polynomial
`P` of any degree, the truncation `N`, the finite block `Afin` and tail diagonal `tail` of the
approximate inverse, and the coefficients `dcoef` of `P′(x̄)`. General in every field. -/
structure PolyZeroReal where
  /-- The polynomial `P`. -/
  P : CompPoly 1
  /-- The truncation: modes `0..N` are finite. -/
  N : ℕ
  /-- Finite block of the approximate inverse `A`. -/
  Afin : Fin (N + 1) → Fin (N + 1) → ℝ
  /-- Tail diagonal of the approximate inverse `A`. -/
  tail : ℝ
  /-- Coefficients of `P′(x̄)`, `P′ = pderiv 0 P`. -/
  dcoef : ℕ → ℝ

namespace PolyZeroReal

variable (d : PolyZeroReal)

/-- Approximate inverse `A`: finite block `Afin`, constant tail `tail`. -/
noncomputable def A : ScalarBlockDiagData d.N :=
  ScalarBlockDiagData.ofParts (fun i j => d.Afin i j) (fun _ => d.tail) |d.tail| (fun _ _ => le_rfl)

/-- Approximate derivative `A† = DF^(N)(x̄)`: the Cauchy matrix of `dcoef`, tail `dcoef 0`. -/
noncomputable def Adag : ScalarBlockDiagData d.N :=
  ScalarBlockDiagData.ofParts
    (fun i j => if (j : ℕ) ≤ i then d.dcoef ((i : ℕ) - j) else 0)
    (fun _ => d.dcoef 0) |d.dcoef 0| (fun _ _ => le_rfl)

/-- The dominating operator for `A† - DF(x̄)` on tail modes:
`-leftMul (P′(x̄) - dcoef 0 · 1)`. -/
noncomputable def E {ν : PosReal} (xbar : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  -leftMul ((d.P.pderiv 0).evalBanach (fun _ => xbar) - d.dcoef 0 • (1 : l1Weighted ν))

variable {d}

section Bounds

variable {ν : PosReal} {xbar c : l1Weighted ν}

/-- Action of `A` coefficientwise. -/
lemma A_toSeq (v : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (d.A.toScalarCLM (ν := ν) v) n =
      if h : n ≤ d.N then
        ∑ k : Fin (d.N + 1), d.Afin ⟨n, Nat.lt_succ_of_le h⟩ k * l1Weighted.toSeq v k
      else d.tail * l1Weighted.toSeq v n := by
  split_ifs with hn
  · exact d.A.toScalarCLM_toSeq_fin v ⟨n, Nat.lt_succ_of_le hn⟩
  · exact d.A.toScalarCLM_toSeq_tail v n (by omega)

/-- Tail cancellation `A·A† = 1` on tail modes. -/
lemma tailCancel (h : d.tail * d.dcoef 0 = 1) :
    ∀ n, d.N < n → d.A.tailDiag0 n * d.Adag.tailDiag0 n = 1 :=
  fun _ _ => h

/-- `A† - DF(x̄)` kills finite modes. -/
lemma fin_kill
    (hD : ∀ n, l1Weighted.toSeq ((d.P.pderiv 0).evalBanach (fun _ => xbar)) n = d.dcoef n)
    (h : l1Weighted ν) (n : ℕ) (hn : n ≤ d.N) :
    l1Weighted.toSeq ((d.Adag.toScalarCLM (ν := ν) -
      fderiv ℝ (CompPoly.polyMap d.P c) xbar) h) n = 0 := by
  have hfin : ∀ i j : Fin (d.N + 1), d.Adag.finBlock0 i j =
      if (j : ℕ) ≤ i then (fun k => l1Weighted.toSeq
        ((d.P.pderiv 0).evalBanach (fun _ => xbar)) k) ((i : ℕ) - (j : ℕ)) else 0 := by
    intro i j
    show (if (j : ℕ) ≤ i then d.dcoef ((i : ℕ) - j) else 0) = _
    simp only [hD]
  rw [sub_apply, l1Weighted.sub_toSeq, CompPoly.fderiv_polyMap,
    ScalarBlockDiagData.toScalarCLM_toSeq_fin_eq_cauchy (ν := ν) d.Adag _ hfin h n hn,
    ContinuousLinearMap.mul_apply', l1Weighted.toSeq_mul, sub_self]

/-- On tail modes `A† - DF(x̄) = E`. -/
lemma tail_eq (h : l1Weighted ν) (n : ℕ) (hn : d.N < n) :
    l1Weighted.toSeq ((d.Adag.toScalarCLM (ν := ν) -
      fderiv ℝ (CompPoly.polyMap d.P c) xbar) h) n =
      l1Weighted.toSeq (d.E xbar h) n := by
  rw [sub_apply, l1Weighted.sub_toSeq, CompPoly.fderiv_polyMap,
    d.Adag.toScalarCLM_toSeq_tail h n hn,
    show d.Adag.tailDiag0 n = d.dcoef 0 from rfl, PolyZeroReal.E,
    neg_apply, leftMul_apply, ContinuousLinearMap.mul_apply',
    sub_mul, smul_mul_assoc, one_mul, l1Weighted.neg_toSeq, l1Weighted.sub_toSeq,
    l1Weighted.smul_toSeq]
  ring

/-- `Z₁ ≤ |tail| · ‖P′(x̄) - dcoef 0 · 1‖`. -/
lemma Z₁_le
    (hD : ∀ n, l1Weighted.toSeq ((d.P.pderiv 0).evalBanach (fun _ => xbar)) n = d.dcoef n) :
    ‖(d.A.toScalarCLM (ν := ν)).comp
      (d.Adag.toScalarCLM (ν := ν) - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
      |d.tail| * ‖(d.P.pderiv 0).evalBanach (fun _ => xbar) - d.dcoef 0 • (1 : l1Weighted ν)‖ := by
  refine ScalarBlockDiagData.Z₁_le_of_fin_kill_tail_dom d.N d.A _ (d.E xbar)
    (fun h n hn => fin_kill hD h n hn) (fun h n hn => tail_eq h n hn) _ ?_
  have hE : ‖d.E xbar‖ ≤
      ‖(d.P.pderiv 0).evalBanach (fun _ => xbar) - d.dcoef 0 • (1 : l1Weighted ν)‖ := by
    rw [PolyZeroReal.E, norm_neg]
    exact norm_leftMul_le _
  exact mul_le_mul_of_nonneg_left hE d.A.tailBound_nonneg

/-- `Z₂ ≤ derivativeLipschitzBound P (‖x̄‖ + r₀) · ‖A‖ · r₀` on the ball, through the
polynomial-map face (any degree). -/
lemma Z₂_le (r₀ : ℝ) :
    ∀ c' ∈ Metric.closedBall xbar r₀,
      ‖(d.A.toScalarCLM (ν := ν)).comp
        (fderiv ℝ (CompPoly.polyMap d.P c) c' - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
        d.P.derivativeLipschitzBound (fun _ => ‖xbar‖ + r₀) * ‖d.A.toScalarCLM (ν := ν)‖ * r₀ :=
  fun c' hc' => Z₂_ball_bound_of_polyMap d.P c le_rfl (d.A.toScalarCLM (ν := ν)) c' hc'

end Bounds

end PolyZeroReal

end RadiiPolynomial
