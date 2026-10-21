import RadiiPolynomial.Applications.PowerSeries.PolynomialZero
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.Witness
import RadiiPolynomial.Certification.Rational.Grid
import RadiiPolynomial.Certification.RadiiPolynomialQ

/-!
# Polynomial zeros on `ℓ¹_ν`: rational certificate data

`PolyZeroData` is the exact-rational certificate of one member of the family `P(x) - c = 0` on
`ℓ¹_ν`: a univariate polynomial `P` of any degree, a finitely supported forcing `c`, a finitely
supported approximate zero `x̄`, the finite columns of the approximate inverse `A`, and the
claimed bounds. Every bound is computed exactly in `ℚ` (the `CompPoly` coefficient interpreter,
the syntactic support and Lipschitz constants) and compared with the claim in one decidable
proposition `Checks`, discharged by `decide +kernel`.

`toReal` reads the record as a `PolyZeroReal`; the real operators `A` and `A†` of the
application layer are the casts of the rational data. `certified` gives all hypotheses of the
general radii polynomial theorem at `A = d.toReal.A`, `A† = d.toReal.Adag`; `existsUnique` and
`existsUnique_ofArray` give the unique zero.

This module is a specialized adapter: it imports the application discretization
(`Applications/PowerSeries/PolynomialZero`) to verify its concrete certificate data.
-/

open MvPolyBridge
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le)

namespace RadiiPolynomial

/-- The `ℚ` data of one member of the family `P(x) - c = 0` on `ℓ¹_ν`: a univariate polynomial
`P` of any degree, a finitely supported forcing `c`, a finitely supported approximate zero
`x̄`, the finite columns of the approximate inverse `A` (modes `0..N`; its tail diagonal is
the exact reciprocal of the tail of `A† = DF^(N)(x̄)`, computed, never supplied), and the
claimed bounds. General in `P`, `N`, `νq`, `aQ`, `cQ`, `Acols`, the bounds. -/
structure PolyZeroData where
  /-- The polynomial `P`. -/
  P : CompPoly 1
  /-- The truncation: modes `0..N` are finite. -/
  N : ℕ
  /-- The weight `ν`, as a rational. -/
  νq : ℚ
  /-- Coefficients of the approximate zero `x̄` (zero-padded). -/
  aQ : Array ℚ
  /-- Coefficients of the forcing `c` (zero-padded). -/
  cQ : Array ℚ
  /-- Finite columns of the approximate inverse `A`. -/
  Acols : Fin (N + 1) → Array ℚ
  /-- The radius. -/
  r₀ : ℚ
  /-- Claimed `Y₀`. -/
  Y₀ : ℚ
  /-- Claimed `Z₀`. -/
  Z₀ : ℚ
  /-- Claimed `Z₁`. -/
  Z₁ : ℚ
  /-- Claimed constant `Z₂`. -/
  Z₂ : ℚ

namespace PolyZeroData

variable (d : PolyZeroData)

/-! ### ℚ mirror

The readings of `M`, `K₁` as support bounds of `F(x̄)`, `P′(x̄)` and of `Y₀Q`, `Z₁Q`,
`abarNormQ` as exact norms hold for real `x̄`, `c` with coefficients `a`, `cq`, at `ν = νq`, when
`aQ.size ≤ N + 1` (a clause of `Checks`): `FQ_eq_zero`, `dQ_eq_zero`, `norm_xbar`, and inside
the proofs of `Y₀_le`, `Z₁_le`. -/

/-- `x̄` coefficients. -/
def a (k : ℕ) : ℚ := d.aQ.getD k 0
/-- `c` coefficients. -/
def cq (k : ℕ) : ℚ := d.cQ.getD k 0
/-- `F(x̄) = P(x̄) - c` coefficientwise (the `CompPoly` coefficient interpreter). -/
def FQ (n : ℕ) : ℚ := d.P.evalCoeffSeq (fun _ => d.a) n - d.cq n
/-- Coefficients of `P′(x̄)`, `P′ = pderiv 0 P` (the `CompPoly` formal derivative). -/
def dQ (n : ℕ) : ℚ := (d.P.pderiv 0).evalCoeffSeq (fun _ => d.a) n
/-- Tail diagonal of `A`: the exact reciprocal of `(P′(x̄))₀`. -/
def tailQ : ℚ := 1 / d.dQ 0
/-- Support bound for `F(x̄)` (≥ N), from the syntax of `P` and the supports. -/
def M : ℕ := max d.N (CompPoly.supportBound d.N d.P) + d.cQ.size
/-- Support bound for `P′(x̄)`, from the syntax of `P′`. -/
def K₁ : ℕ := CompPoly.supportBound d.N (d.P.pderiv 0)
/-- `A F(x̄)` coefficientwise. -/
def actQ (n : ℕ) : ℚ :=
  if n ≤ d.N then ∑ k : Fin (d.N + 1), (d.Acols k).getD n 0 * d.FQ k
  else d.tailQ * d.FQ n
/-- Exact ℚ value of `‖A F(x̄)‖`. -/
def Y₀Q : ℚ := ∑ n ∈ Finset.Icc 0 d.M, |d.actQ n| * d.νq ^ n
/-- Columns of `DF^(N)(x̄)`: the lower-triangular Cauchy matrix of `P′(x̄)`. -/
def DFcols (j : Fin (d.N + 1)) : Array ℚ :=
  Array.ofFn fun i : Fin (d.N + 1) => if (j : ℕ) ≤ i then d.dQ ((i : ℕ) - j) else 0
/-- Columns of `I - A·DF^(N)`. -/
def defectCols (j : Fin (d.N + 1)) : Array ℚ :=
  Array.ofFn fun i : Fin (d.N + 1) => defectMatQ d.Acols d.DFcols i j
/-- Exact ℚ value of the finite `Z₀`. -/
def Z₀Q : ℚ := finWeightedMatrixNormQ d.defectCols d.νq
/-- Exact ℚ `Z₁ = |tail(A)| · ‖P′(x̄) - (P′(x̄))₀·1‖`, summed over the support of `P′(x̄)`. -/
def Z₁Q : ℚ := |d.tailQ| *
  ∑ n ∈ Finset.Icc 0 d.K₁, |d.dQ n - (if n = 0 then d.dQ 0 else 0)| * d.νq ^ n
/-- Exact ℚ value of `‖x̄‖`. -/
def abarNormQ : ℚ := ∑ n ∈ Finset.Icc 0 d.N, |d.a n| * d.νq ^ n
/-- `Z₂ = derivativeLipschitzBound P (‖x̄‖ + r₀) · max(‖A_fin‖, |tail(A)|)`. -/
def Z₂Q : ℚ := d.P.derivativeLipschitzBound (fun _ => d.abarNormQ + d.r₀) *
  max (finWeightedMatrixNormQ d.Acols d.νq) |d.tailQ|

/-- The only certificate obligation: a ℚ-decidable conjunction (one `decide +kernel`). -/
def Checks : Prop :=
  d.dQ 0 ≠ 0 ∧ d.aQ.size ≤ d.N + 1 ∧ d.Y₀Q ≤ d.Y₀ ∧ d.Z₀Q ≤ d.Z₀ ∧ d.Z₀ < 1 ∧
    d.Z₁Q ≤ d.Z₁ ∧ d.Z₂Q ≤ d.Z₂ ∧ 0 < d.r₀ ∧
    d.Z₂ * d.r₀ ^ 2 - (1 - d.Z₀ - d.Z₁) * d.r₀ + d.Y₀ < 0

instance : Decidable d.Checks := by unfold Checks; infer_instance

/-! ### ℝ objects -/

/-- The real data read off the rational record: `A` has the cast columns and the tail
`1/(P′(x̄))₀`; `P′(x̄)` has the cast coefficients `dQ`. Reducible, so that `d.toReal.N` and
`d.N` are the same index for rewriting. -/
noncomputable abbrev toReal : PolyZeroReal where
  P := d.P
  N := d.N
  Afin i j := (((d.Acols j).getD (i : ℕ) 0 : ℚ) : ℝ)
  tail := ((d.tailQ : ℚ) : ℝ)
  dcoef n := ((d.dQ n : ℚ) : ℝ)

variable {d}

lemma a_eq_zero_of_lt (h : d.aQ.size ≤ d.N + 1) (k : ℕ) (hk : d.N < k) : d.a k = 0 := by
  simp [a, Array.getD_eq_getD_getElem?, show d.aQ.size ≤ k by omega]

lemma cq_eq_zero_of_le (k : ℕ) (hk : d.cQ.size ≤ k) : d.cq k = 0 := by
  simp [cq, Array.getD_eq_getD_getElem?, hk]

lemma FQ_eq_zero (h : d.aQ.size ≤ d.N + 1) (n : ℕ) (hn : d.M < n) : d.FQ n = 0 := by
  unfold PolyZeroData.M at hn
  rw [PolyZeroData.FQ, CompPoly.evalCoeffSeq_eq_zero_of_support d.N d.P (fun _ => d.a)
    (fun _ k hk => a_eq_zero_of_lt h k hk) n (by omega), cq_eq_zero_of_le n (by omega),
    sub_zero]

lemma dQ_eq_zero (h : d.aQ.size ≤ d.N + 1) (n : ℕ) (hn : d.K₁ < n) : d.dQ n = 0 :=
  CompPoly.evalCoeffSeq_eq_zero_of_support d.N (d.P.pderiv 0) (fun _ => d.a)
    (fun _ k hk => a_eq_zero_of_lt h k hk) n hn

/-- The tail of `A` is the reciprocal of the tail of `A†`. -/
private lemma tail_mul_dcoef (h0 : d.dQ 0 ≠ 0) : d.toReal.tail * d.toReal.dcoef 0 = 1 := by
  have h0' : ((d.dQ 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h0
  show ((d.tailQ : ℚ) : ℝ) * ((d.dQ 0 : ℚ) : ℝ) = 1
  simp only [PolyZeroData.tailQ]
  push_cast
  field_simp

section Bounds
variable {ν : PosReal} (hν : (ν : ℝ) = (d.νq : ℝ)) {xbar c : l1Weighted ν}
  (hx : ∀ n, l1Weighted.toSeq xbar n = (d.a n : ℝ))
  (hc : ∀ n, l1Weighted.toSeq c n = (d.cq n : ℝ))
include hν hx hc

omit hν hc in
/-- `P′(x̄)` coefficientwise = ℚ cast. -/
lemma D_toSeq (n : ℕ) :
    l1Weighted.toSeq ((d.P.pderiv 0).evalBanach (fun _ => xbar)) n = (d.dQ n : ℝ) :=
  CompPoly.toSeq_evalBanach_of_coeffs _ _ (fun _ => d.a) (fun _ k => hx k) n

omit hν in
/-- `F(x̄)` coefficientwise = ℚ cast. -/
lemma F_toSeq (n : ℕ) : l1Weighted.toSeq (CompPoly.polyMap d.P c xbar) n = (d.FQ n : ℝ) := by
  rw [CompPoly.polyMap, l1Weighted.sub_toSeq,
    CompPoly.toSeq_evalBanach_of_coeffs _ _ (fun _ => d.a) (fun _ k => hx k) n, hc,
    PolyZeroData.FQ, Rat.cast_sub]

/-- `Y₀` from the exact ℚ value. -/
lemma Y₀_le (h : d.aQ.size ≤ d.N + 1) (hY : d.Y₀Q ≤ d.Y₀) :
    ‖d.toReal.A.toScalarCLM (ν := ν) (CompPoly.polyMap d.P c xbar)‖ ≤ (d.Y₀ : ℝ) := by
  rw [ScalarBlockDiagData.norm_toScalarCLM_action_eq_Icc_sum _ _ d.M
    (by show d.N ≤ d.M; unfold PolyZeroData.M; omega)
    (fun n hn => by rw [F_toSeq hx hc, FQ_eq_zero h n hn, Rat.cast_zero])]
  have hact : ∀ n, l1Weighted.toSeq (d.toReal.A.toScalarCLM (ν := ν)
      (CompPoly.polyMap d.P c xbar)) n = (d.actQ n : ℝ) := by
    intro n
    rw [PolyZeroReal.A_toSeq]
    dsimp only [PolyZeroData.toReal]
    simp only [PolyZeroData.actQ, F_toSeq hx hc]
    split_ifs <;> push_cast <;> rfl
  simp_rw [hact, hν]
  have hR : ((d.Y₀Q : ℚ) : ℝ) ≤ (d.Y₀ : ℝ) := by exact_mod_cast hY
  unfold PolyZeroData.Y₀Q at hR
  push_cast at hR
  exact hR

omit hx hc in
/-- Finite defect norm ≤ exact ℚ `Z₀Q`. -/
lemma defect_le :
    FiniteWeightedNorm.finWeightedMatrixNorm ν
      (1 - d.toReal.A.finBlock0 * d.toReal.Adag.finBlock0) ≤ (d.Z₀Q : ℝ) :=
  FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le _ d.defectCols d.νq
    (fun j i => by
      rw [defectMatQ_correct d.toReal.A.finBlock0 d.toReal.Adag.finBlock0 d.Acols d.DFcols
        (fun j i => rfl)
        (fun j i => by
          rw [PolyZeroData.DFcols, Certification.Rational.getD_ofFn_fin]
          show (if (j : ℕ) ≤ i then ((d.dQ ((i : ℕ) - j) : ℚ) : ℝ) else 0) = _
          split_ifs <;> push_cast <;> rfl) i j]
      simp only [PolyZeroData.defectCols, Certification.Rational.getD_ofFn_fin])
    hν le_rfl

omit hx hc in
/-- `Z₀` from the exact ℚ value. -/
lemma Z₀_le (h0 : d.dQ 0 ≠ 0) (hZ : d.Z₀Q ≤ d.Z₀) :
    ‖ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (d.toReal.A.toScalarCLM (ν := ν)).comp (d.toReal.Adag.toScalarCLM (ν := ν))‖ ≤
      (d.Z₀ : ℝ) :=
  ((ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel (ν := ν) _ _
    (PolyZeroReal.tailCancel (tail_mul_dcoef h0))).trans (defect_le hν)).trans
    (by exact_mod_cast hZ)

omit hc in
/-- `Z₁` from the exact ℚ value. -/
lemma Z₁_le (hsz : d.aQ.size ≤ d.N + 1) (hZ : d.Z₁Q ≤ d.Z₁) :
    ‖(d.toReal.A.toScalarCLM (ν := ν)).comp
      (d.toReal.Adag.toScalarCLM (ν := ν) - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
      (d.Z₁ : ℝ) := by
  refine (PolyZeroReal.Z₁_le (d := d.toReal) (c := c) (fun n => D_toSeq hx n)).trans ?_
  show |((d.tailQ : ℚ) : ℝ)| *
      ‖(d.P.pderiv 0).evalBanach (fun _ => xbar) - ((d.dQ 0 : ℚ) : ℝ) • (1 : l1Weighted ν)‖ ≤
      (d.Z₁ : ℝ)
  set D := (d.P.pderiv 0).evalBanach (fun _ => xbar)
  have hseq : ∀ n, l1Weighted.toSeq (D - ((d.dQ 0 : ℚ) : ℝ) • (1 : l1Weighted ν)) n =
      ((d.dQ n - (if n = 0 then d.dQ 0 else 0) : ℚ) : ℝ) := by
    intro n
    rw [l1Weighted.sub_toSeq, l1Weighted.smul_toSeq, l1Weighted.one_toSeq_eq, D_toSeq hx]
    split_ifs <;> push_cast <;> ring
  have hnorm : ‖D - ((d.dQ 0 : ℚ) : ℝ) • (1 : l1Weighted ν)‖ =
      ∑ n ∈ Finset.Icc 0 d.K₁, |((d.dQ n - (if n = 0 then d.dQ 0 else 0) : ℚ) : ℝ)| *
        (d.νq : ℝ) ^ n := by
    rw [l1Weighted.norm_eq_Icc_sum_of_support _ d.K₁ (fun n hn => by
      rw [hseq, dQ_eq_zero hsz n hn, ite_eq_right (by omega)]; simp)]
    simp_rw [hseq, hν]
  have hR : ((d.Z₁Q : ℚ) : ℝ) ≤ (d.Z₁ : ℝ) := by exact_mod_cast hZ
  unfold PolyZeroData.Z₁Q at hR
  push_cast at hR
  rw [hnorm]
  push_cast
  exact hR

omit hx hc in
/-- `‖A‖` from the exact ℚ column norms. -/
lemma norm_A_le :
    ‖d.toReal.A.toScalarCLM (ν := ν)‖ ≤
      ((max (finWeightedMatrixNormQ d.Acols d.νq) |d.tailQ| : ℚ) : ℝ) :=
  norm_toScalarCLM_le_of_Q (ν := ν) d.toReal.A d.Acols d.νq |d.tailQ|
    (fun j i => rfl) hν
    (by simp [PolyZeroReal.A, ScalarBlockDiagData.ofParts, PolyZeroData.toReal]) le_rfl

omit hc in
/-- `‖x̄‖` = exact ℚ value. -/
lemma norm_xbar (hsz : d.aQ.size ≤ d.N + 1) : ‖xbar‖ = (d.abarNormQ : ℝ) :=
  l1Weighted.norm_eq_ratCast_sum_of_support _ _ _ hx hν d.N (a_eq_zero_of_lt hsz)

omit hc in
/-- `Z₂` from the exact ℚ value, through the polynomial-map face (any degree). -/
lemma Z₂_le (hsz : d.aQ.size ≤ d.N + 1) (hZ : d.Z₂Q ≤ d.Z₂) :
    ∀ c' ∈ Metric.closedBall xbar (d.r₀ : ℝ),
      ‖(d.toReal.A.toScalarCLM (ν := ν)).comp
        (fderiv ℝ (CompPoly.polyMap d.P c) c' - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
        (fun _ => (d.Z₂ : ℝ)) (d.r₀ : ℝ) * d.r₀ := by
  intro c' hc'
  have hr : (0 : ℝ) ≤ d.r₀ := Metric.nonempty_closedBall.mp ⟨c', hc'⟩
  have hR : ‖xbar‖ + (d.r₀ : ℝ) = ((d.abarNormQ + d.r₀ : ℚ) : ℝ) := by
    rw [norm_xbar hν hx hsz]; push_cast; rfl
  have h := PolyZeroReal.Z₂_le (d := d.toReal) (c := c) (d.r₀ : ℝ) c' hc'
  rw [hR, ← CompPoly.derivativeLipschitzBound_ratCast] at h
  have hL : (0 : ℝ) ≤
      ((d.P.derivativeLipschitzBound (fun _ => d.abarNormQ + d.r₀) : ℚ) : ℝ) := by
    rw [CompPoly.derivativeLipschitzBound_ratCast]
    exact CompPoly.derivativeLipschitzBound_nonneg _ _ fun _ =>
      (add_nonneg (norm_nonneg xbar) hr).trans hR.le
  have hR2 : ((d.Z₂Q : ℚ) : ℝ) ≤ (d.Z₂ : ℝ) := by exact_mod_cast hZ
  unfold PolyZeroData.Z₂Q at hR2
  push_cast at hR2
  refine h.trans ?_
  show _ ≤ (d.Z₂ : ℝ) * d.r₀
  refine mul_le_mul_of_nonneg_right ?_ hr
  refine (mul_le_mul_of_nonneg_left (norm_A_le hν) hL).trans ?_
  push_cast
  exact hR2

end Bounds

/-- **The family face, bound form.** From the ℚ-decidable `Checks` and the two coefficient
bridges, all eight hypotheses of the general radii polynomial theorem at `A = d.toReal.A`,
`A† = d.toReal.Adag`, for any univariate polynomial `P`. -/
theorem certified (d : PolyZeroData) {ν : PosReal} (hν : (ν : ℝ) = (d.νq : ℝ))
    {xbar c : l1Weighted ν}
    (hx : ∀ n, l1Weighted.toSeq xbar n = (d.a n : ℝ))
    (hc : ∀ n, l1Weighted.toSeq c n = (d.cq n : ℝ))
    (h : d.Checks) :
    (0 : ℝ) < d.r₀ ∧
    ‖d.toReal.A.toScalarCLM (ν := ν) (CompPoly.polyMap d.P c xbar)‖ ≤ (d.Y₀ : ℝ) ∧
    ‖ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (d.toReal.A.toScalarCLM (ν := ν)).comp (d.toReal.Adag.toScalarCLM (ν := ν))‖ ≤
      (d.Z₀ : ℝ) ∧
    ‖(d.toReal.A.toScalarCLM (ν := ν)).comp
      (d.toReal.Adag.toScalarCLM (ν := ν) - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
      (d.Z₁ : ℝ) ∧
    (∀ c' ∈ Metric.closedBall xbar (d.r₀ : ℝ),
      ‖(d.toReal.A.toScalarCLM (ν := ν)).comp
        (fderiv ℝ (CompPoly.polyMap d.P c) c' - fderiv ℝ (CompPoly.polyMap d.P c) xbar)‖ ≤
        (fun _ => (d.Z₂ : ℝ)) (d.r₀ : ℝ) * d.r₀) ∧
    Differentiable ℝ (CompPoly.polyMap d.P c) ∧
    generalRadiiPolynomial (d.Y₀ : ℝ) (d.Z₀ : ℝ) (d.Z₁ : ℝ) (fun _ => (d.Z₂ : ℝ)) (d.r₀ : ℝ)
      < 0 ∧
    Function.Injective (d.toReal.A.toScalarCLM (ν := ν)) := by
  obtain ⟨h0, hsz, hY, hZ0, hZ0lt, hZ1, hZ2, hr, hrad⟩ := h
  have hr' : (0 : ℝ) < d.r₀ := by exact_mod_cast hr
  refine ⟨hr', Y₀_le hν hx hc hsz hY, Z₀_le hν h0 hZ0, Z₁_le hν hx hsz hZ1,
    Z₂_le hν hx hsz hZ2, CompPoly.differentiable_polyMap d.P c, ?_, ?_⟩
  · exact generalRadiiPolynomial_neg_of_Q_const _ _ _ _ _ hrad
  refine ScalarBlockDiagData.injective_toScalarCLM_of_finBlock_mul_close_to_one d.toReal.A
    d.toReal.Adag.finBlock0 ((defect_le hν).trans_lt (by exact_mod_cast hZ0.trans_lt hZ0lt)) ?_
  intro n _
  show ((d.tailQ : ℚ) : ℝ) ≠ 0
  exact_mod_cast one_div_ne_zero h0

/-- **The family face.** Every member of `P(x) - c = 0` whose ℚ data pass `Checks` has a
unique zero near `x̄`. General in `P` (any degree), `c`, `N`, `ν`. -/
theorem existsUnique (d : PolyZeroData) {ν : PosReal} (hν : (ν : ℝ) = (d.νq : ℝ))
    (xbar c : l1Weighted ν)
    (hx : ∀ n, l1Weighted.toSeq xbar n = (d.a n : ℝ))
    (hc : ∀ n, l1Weighted.toSeq c n = (d.cq n : ℝ))
    (h : d.Checks) :
    ∃! x ∈ Metric.closedBall xbar (d.r₀ : ℝ), CompPoly.polyMap d.P c x = 0 :=
  let ⟨hr, hY, hZ0, hZ1, hZ2, hd, hp, hi⟩ := d.certified hν hx hc h
  general_radii_polynomial_theorem hr hY hZ0 hZ1 hZ2 hd hp hi


end PolyZeroData

end RadiiPolynomial
