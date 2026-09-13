import RadiiPolynomial.Applications.IVP.Chebyshev.Lambda
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev.Bounds

/-!
# Polynomial adapter for the Chebyshev IVP recipe

The coefficient residual remains a raw sequence. Finite rational data are
interpreted with symmetric Laurent multiplication before the existing bounded
preconditioned map is formed. The adapter supplies residual and Jacobian cast
bridges, differentiability, and exact finite-output columns. A finite square
Jacobian check does not identify unrestricted finite-output rows: Chebyshev
multiplication can send high input modes to low output modes. The remaining
tail coupling is part of the Z₁ certificate.
-/

open scoped BigOperators
open RadiiPolynomial
open MvPolyBridge

namespace ChebyshevIVP

/-- The rational boundary row for a zero-padded Chebyshev coefficient array. -/
def chebBoundaryQ (a : Array ℚ) (p : ℚ) : ℚ :=
  p - a.getD 0 0 -
    2 * ∑ n ∈ Finset.range a.size, (-1 : ℚ) ^ (n + 1) * a.getD (n + 1) 0

/-- Exact rational residual from one polynomial system and stored arrays. -/
def compPolyIvpCoeffsQ {L : ℕ} (f : Fin L → CompPoly L)
    (arrs : Fin L → Array ℚ) (p : Fin L → ℚ) (l : Fin L) : ℕ → ℚ
  | 0 => chebBoundaryQ (arrs l) (p l)
  | k + 1 => 2 * ((k : ℚ) + 1) * (arrs l).getD (k + 1) 0 +
      (f l).evalChebCoeff arrs (↑(k + 2) : ℤ) - (f l).evalChebCoeff arrs (k : ℤ)

/-- A stored coordinate becomes one Laurent atom at zero and two otherwise. -/
def compPolyDphiQ {L : ℕ} (p : CompPoly L) (m : Fin L)
    (arrs : Fin L → Array ℚ) (k : ℕ) (n : ℤ) : ℚ :=
  if k = 0 then (p.pderiv m).evalChebCoeff arrs n
  else (p.pderiv m).evalChebCoeff arrs (n - k) +
    (p.pderiv m).evalChebCoeff arrs (n + k)

/-- Finite Jacobian entries of the raw Chebyshev equations. -/
def compPolyDFQ {L : ℕ} (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ)
    (l m : Fin L) (row col : ℕ) : ℚ :=
  match row with
  | 0 => if l = m then (if col = 0 then -1 else -2 * (-1 : ℚ) ^ col) else 0
  | k + 1 => (if l = m ∧ k + 1 = col then 2 * ((k : ℚ) + 1) else 0) +
      compPolyDphiQ (f l) m arrs col (↑(k + 2) : ℤ) -
      compPolyDphiQ (f l) m arrs col (k : ℤ)

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

omit [NeZero L] in
/-- The Chebyshev coefficient nonlinearity of a polynomial system: the Chebyshev mirror
of `IVP.banachField`. Each component is interpreted through the symmetrization into the
physical algebra, so this is the `φ` the Chebyshev recipe consumes; a certificate then
supplies only the syntax `f`. -/
noncomputable def banachField (f : Fin L → CompPoly L) (a : XCheb ν L) (l : Fin L) :
    l1Chebyshev ν :=
  CompPoly.Chebyshev.eval (f l) a

omit [NeZero L] in
@[simp] lemma banachField_apply (f : Fin L → CompPoly L) (a : XCheb ν L) (l : Fin L) :
    banachField f a l = CompPoly.Chebyshev.eval (f l) a := rfl

/-- The infinite boundary row reduces to the finite rational array calculation. -/
lemma StdChebIVPData.boundary_abar_eq_cast
    (d : StdChebIVPData ν L N) (p : Fin L → ℚ) (l : Fin L) :
    (p l : ℝ) - l1Chebyshev.toSeq (d.abar l) 0 -
      2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) *
        l1Chebyshev.toSeq (d.abar l) (↑(n + 1) : ℤ) =
      (chebBoundaryQ (d.abar_Q l) (p l) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range (d.abar_Q l).size) (fun n hn => by
    rw [d.abar_toSeq_eq]
    have hout : ¬n + 1 < (d.abar_Q l).size := by
      simp only [Finset.mem_range] at hn
      omega
    simp [Array.getD, hout])]
  rw [show l1Chebyshev.toSeq (d.abar l) 0 = ((d.abar_Q l).getD 0 0 : ℝ) from
    d.abar_toSeq_eq l 0]
  simp only [chebBoundaryQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_sum,
    Rat.cast_ofNat, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  congr 2
  exact Finset.sum_congr rfl fun n _ => by rw [d.abar_toSeq_eq]

/-- The raw residual at the numerical candidate is exactly the rational computation. -/
lemma StdChebIVPData.ivpCoeffs_abar_eq_cast_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℚ) (l : Fin L) (n : ℕ) :
    chebyshevIvpCoeffs (banachField f) (fun j => (p j : ℝ)) d.abar l n =
      (compPolyIvpCoeffsQ f d.abar_Q p l n : ℝ) := by
  cases n with
  | zero => exact d.boundary_abar_eq_cast p l
  | succ n =>
      simp only [chebyshevIvpCoeffs, compPolyIvpCoeffsQ, banachField,
        CompPoly.Chebyshev.eval]
      rw [d.abar_toSeq_eq,
        (f l).toSeq_evalBanach_cheb_of_coeffs d.abar d.abar_Q d.abar_toSeq_eq,
        (f l).toSeq_evalBanach_cheb_of_coeffs d.abar d.abar_Q d.abar_toSeq_eq]
      push_cast
      rfl

/-- The derivative of a polynomial system, assembled from its component derivatives. -/
noncomputable def compPolyDerivative (f : Fin L → CompPoly L) (a : XCheb ν L) :
    XCheb ν L →L[ℝ] XCheb ν L :=
  ContinuousLinearMap.pi fun l => CompPoly.Chebyshev.derivative (f l) a

omit [NeZero L] in
lemma hasFDerivAt_compPoly (f : Fin L → CompPoly L) (a : XCheb ν L) :
    HasFDerivAt (banachField f) (compPolyDerivative f a) a := by
  rw [hasFDerivAt_pi']
  intro l
  rw [compPolyDerivative, ContinuousLinearMap.proj_pi]
  exact CompPoly.Chebyshev.hasFDerivAt_eval (f l) a

/-- The existing affine decomposition supplies the full preconditioned derivative. -/
lemma StdChebIVPData.hasFDerivAt_G_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (a : XCheb ν L) :
    HasFDerivAt (d.G (banachField f) p)
      (d.TA + d.TC.comp (compPolyDerivative f a)) a :=
  d.hasFDerivAt_G _ p a _ (hasFDerivAt_compPoly f a)

lemma StdChebIVPData.differentiable_G_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ) :
    Differentiable ℝ (d.G (banachField f) p) :=
  fun a => (d.hasFDerivAt_G_of_compPoly f p a).differentiableAt

lemma StdChebIVPData.fderiv_G_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (a : XCheb ν L) :
    fderiv ℝ (d.G (banachField f) p) a =
      d.TA + d.TC.comp (compPolyDerivative f a) :=
  (d.hasFDerivAt_G_of_compPoly f p a).fderiv

omit [NeZero L] [Fact (1 ≤ (ν : ℝ))] in
private lemma FAseq_single (k n : ℕ) :
    FAseq (l1Chebyshev.single (ν := ν) (k : ℤ) 1) n =
      match n with
      | 0 => if k = 0 then -1 else -2 * (-1 : ℝ) ^ k
      | j + 1 => if j + 1 = k then 2 * ((j : ℝ) + 1) else 0 := by
  cases n with
  | zero =>
      cases k with
      | zero =>
          simp [FAseq, l1Chebyshev.toSeq_single,
            show ∀ n : ℕ, (n : ℤ) + 1 ≠ 0 by omega]
      | succ k =>
          have hs : (∑' j : ℕ, (-1 : ℝ) ^ (j + 1) *
              l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν) (↑(k + 1) : ℤ) 1)
                (↑(j + 1) : ℤ)) = (-1 : ℝ) ^ (k + 1) := by
            rw [tsum_eq_single k (fun j hj => by
              rw [l1Chebyshev.toSeq_single, if_neg (fun h => hj (by omega)), mul_zero])]
            simp [l1Chebyshev.toSeq_single]
          simp only [FAseq, hs]
          rw [l1Chebyshev.toSeq_single, if_neg (by omega)]
          simp
  | succ j =>
      simp only [FAseq, l1Chebyshev.toSeq_single, Nat.cast_add, Nat.cast_one]
      split_ifs with h h' h'
      · simp
      · omega
      · omega
      · simp

omit [NeZero L] in
/-- The rational Jacobian column includes the symmetric extension of the direction. -/
lemma compPoly_derivative_single_toSeq_eq_cast (p : CompPoly L)
    (a : XCheb ν L) (arrs : Fin L → Array ℚ)
    (ha : ∀ i (k : ℕ), l1Chebyshev.toSeq (a i) (k : ℤ) = ((arrs i).getD k 0 : ℝ))
    (m : Fin L) (k : ℕ) (n : ℤ) :
    l1Chebyshev.toSeq
      (CompPoly.Chebyshev.derivative p a (Pi.single m (l1Chebyshev.single (k : ℤ) 1))) n =
      (compPolyDphiQ p m arrs k n : ℝ) := by
  rw [CompPoly.Chebyshev.derivative_single_toSeq]
  simp only [CompPoly.Chebyshev.eval, compPolyDphiQ]
  split_ifs
  · exact (p.pderiv m).toSeq_evalBanach_cheb_of_coeffs a arrs ha n
  · rw [(p.pderiv m).toSeq_evalBanach_cheb_of_coeffs a arrs ha,
      (p.pderiv m).toSeq_evalBanach_cheb_of_coeffs a arrs ha, Rat.cast_add]

/-- The two linear row contributions agree with the computable raw Jacobian. -/
lemma StdChebIVPData.rawDerivative_single_eq_cast_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (l m : Fin L) (row col : ℕ) :
    FAseq ((Pi.single m (l1Chebyshev.single (ν := ν) (col : ℤ) 1) : XCheb ν L) l) row +
      FCseq (compPolyDerivative f d.abar
        (Pi.single m (l1Chebyshev.single (col : ℤ) 1)) l) row =
      (compPolyDFQ f d.abar_Q l m row col : ℝ) := by
  have hcol (n : ℤ) := compPoly_derivative_single_toSeq_eq_cast (f l)
    d.abar d.abar_Q d.abar_toSeq_eq m col n
  cases row with
  | zero =>
      simp only [FCseq, add_zero, compPolyDFQ]
      by_cases hl : l = m
      · subst l
        simp only [Pi.single_eq_same, FAseq_single]
        split_ifs <;> push_cast <;> rfl
      · simp [hl, FAseq, l1Chebyshev.toSeq_zero]
  | succ row =>
      change FAseq ((Pi.single m (l1Chebyshev.single (ν := ν) (col : ℤ) 1) : XCheb ν L) l)
        (row + 1) +
        (l1Chebyshev.toSeq (CompPoly.Chebyshev.derivative (f l) d.abar
          (Pi.single m (l1Chebyshev.single (col : ℤ) 1))) (↑(row + 2) : ℤ) -
        l1Chebyshev.toSeq (CompPoly.Chebyshev.derivative (f l) d.abar
          (Pi.single m (l1Chebyshev.single (col : ℤ) 1))) (row : ℤ)) = _
      rw [hcol, hcol]
      by_cases hl : l = m
      · subst l
        simp only [Pi.single_eq_same, FAseq_single, compPolyDFQ, true_and]
        split_ifs <;> push_cast <;> ring
      · simp [hl, FAseq, compPolyDFQ,
          l1Chebyshev.toSeq_zero, Rat.cast_sub]

/-- Finite output rows still read the full input direction through the nonlinear rows. -/
lemma StdChebIVPData.fderiv_G_fin_toSeq_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (a h : XCheb ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (fderiv ℝ (d.G (banachField f) p) a h l) (n : ℤ) =
      ∑ j : Fin L, ∑ k : Fin (N + 1), d.approxInverse.finBlock l j ⟨n, by omega⟩ k *
        (FAseq (h j) (k : ℕ) + FCseq (compPolyDerivative f a h j) (k : ℕ)) := by
  rw [d.fderiv_G_of_compPoly]
  change l1Chebyshev.toSeq (d.TAfun h l +
    (d.TCblockFun (compPolyDerivative f a h) l +
      TCtailElem N (compPolyDerivative f a h l))) (n : ℤ) = _
  rw [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_add,
    d.TAfun_toSeq_nat, d.TCblockFun_toSeq_nat, TCtailElem_toSeq_nat,
    if_neg (not_lt.mpr hn), add_zero,
    SystemBlockDiagData.action_finite _ _ _ _ hn]
  rw [TCblockSeq, SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
  simp_rw [mul_add, Finset.sum_add_distrib]

/-- Every nonnegative input column has an exact rational finite-output formula,
including the columns beyond the stored finite block. -/
lemma StdChebIVPData.fderiv_G_single_fin_eq_cast_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (l m : Fin L) (n : Fin (N + 1)) (col : ℕ) :
    l1Chebyshev.toSeq
      (fderiv ℝ (d.G (banachField f) p) d.abar
        (Pi.single m (l1Chebyshev.single (col : ℤ) 1)) l) (↑(n : ℕ) : ℤ) =
      ((∑ j : Fin L, ∑ k : Fin (N + 1), (d.A_col l j (k : ℕ)).getD (n : ℕ) 0 *
        compPolyDFQ f d.abar_Q j m (k : ℕ) col : ℚ) : ℝ) := by
  rw [d.fderiv_G_fin_toSeq_of_compPoly f p d.abar _ l (n : ℕ) (Fin.is_le n)]
  simp_rw [d.rawDerivative_single_eq_cast_of_compPoly]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rfl


/-! ## Certificate constants from syntax

The Z₁ operator constant `K` and the Z₂ Lipschitz constant of the system derivative are
read off the polynomial syntax, with the input radii stated on the symmetrized candidate.
These are the system (`Fin L`-valued) faces of the componentwise lemmas in
`CompPoly/Chebyshev/Bounds.lean`; a certificate whose Z₁ theorem is componentwise
(`chebyshev_Z₁_le_relaxed`) uses `norm_derivative_apply_le` directly. -/

/-- Operator norm of the system derivative, from the per-component syntactic constants.
System face kept for a future system-level `Z₁` theorem: today's certificates bound `Z₁`
componentwise (`chebyshev_Z₁_le_relaxed` with `CompPoly.Chebyshev.norm_derivative_apply_le`),
so this lemma has no consumer yet. -/
theorem norm_compPolyDerivative_le (f : Fin L → CompPoly L) (a : XCheb ν L) (R : Fin L → ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i) (B : ℝ)
    (hB : ∀ l, CompPoly.Chebyshev.derivativeBound (f l) R ≤ B) :
    ‖compPolyDerivative f a‖ ≤ B := by
  have hB0 : 0 ≤ B := (CompPoly.Chebyshev.derivativeBound_nonneg (f 0) R
    fun i => (norm_nonneg _).trans (ha i)).trans (hB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (norm_nonneg _))).mpr fun l => ?_
  rw [compPolyDerivative, ContinuousLinearMap.pi_apply]
  exact (CompPoly.Chebyshev.norm_derivative_apply_le (f l) a R ha h).trans
    (mul_le_mul_of_nonneg_right (hB l) (norm_nonneg _))

/-- Lipschitz bound on the system derivative in the raw displacement `‖a - b‖`: `B` dominates
every component's `2 · derivativeLipschitzBound` (the `2` is the symmetrization of the
displacement), so a certificate states `B` as a single number (Example 14.2.1: `8`). -/
theorem norm_compPolyDerivative_sub_le (f : Fin L → CompPoly L) (a b : XCheb ν L)
    (R : Fin L → ℝ)
    (ha : ∀ i, ‖l1Chebyshev.symmetrize (a i)‖ ≤ R i)
    (hb : ∀ i, ‖l1Chebyshev.symmetrize (b i)‖ ≤ R i) (B : ℝ)
    (hB : ∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l) R ≤ B) :
    ‖compPolyDerivative f a - compPolyDerivative f b‖ ≤ B * ‖a - b‖ := by
  have hB0 : 0 ≤ B := (mul_nonneg zero_le_two
    (CompPoly.Chebyshev.derivativeLipschitzBound_nonneg (f 0) R
      fun i => (norm_nonneg _).trans (ha i))).trans (hB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  show ‖compPolyDerivative f a h l - compPolyDerivative f b h l‖ ≤ _
  simp only [compPolyDerivative, ContinuousLinearMap.pi_apply]
  have h1 := CompPoly.Chebyshev.norm_derivative_sub_le_of_norm_sub (f l) a b R ha hb
  have h2 := (CompPoly.Chebyshev.derivative (f l) a
    - CompPoly.Chebyshev.derivative (f l) b).le_opNorm h
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_right
    (h1.trans (mul_le_mul_of_nonneg_right (hB l) (norm_nonneg _))) (norm_nonneg _)

/-- Ball-free form of `norm_compPolyDerivative_sub_le`: the radii are the two candidates'
own symmetrized norms. -/
theorem norm_compPolyDerivative_sub_le_max (f : Fin L → CompPoly L) (a b : XCheb ν L) (B : ℝ)
    (hB : ∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
      (fun i => max ‖l1Chebyshev.symmetrize (a i)‖ ‖l1Chebyshev.symmetrize (b i)‖) ≤ B) :
    ‖compPolyDerivative f a - compPolyDerivative f b‖ ≤ B * ‖a - b‖ :=
  norm_compPolyDerivative_sub_le f a b _ (fun _ => le_max_left _ _)
    (fun _ => le_max_right _ _) B hB

/-! ## Certificate faces

The two coefficient-level faces a Chebyshev certificate calls. Both take the polynomial
system `f` in place of the coefficient nonlinearity and derive its differentiability
witness from the syntax: `Z₂_le_of_compPoly_max` absorbs the plumbing between the
syntactic Lipschitz constant of the derivative and the ball statement the radii polynomial
expects; `existsUnique_of_compPoly` takes the four bounds (`Z₀` in the finite-block form
the certificate proves) and the radii-polynomial inequality. The function-level faces
(`solution_existsUnique_of_compPoly`, `solution_existsUnique_of_two_le_of_compPoly`,
`analytic_solution_existsUnique_of_two_le_of_compPoly`) live in
`Chebyshev/AnalyticPolynomial.lean`. There is no `Z₁` face yet: a certificate's `Z₁`
theorem is componentwise (`chebyshev_Z₁_le_relaxed` + `norm_derivative_apply_le`), see
`norm_compPolyDerivative_le`. -/

/-- `Z₂` from syntax: with `C` a bound for the tail-composition operator `TC` and `B` a
bound, over the certificate ball `closedBall ā r₀`, for twice the syntactic derivative
Lipschitz constant of each component, the preconditioned derivative is
`(C * B)`-Lipschitz on that ball.

The syntactic constant is taken at the radii `max ‖S(cᵢ)‖ ‖S(āᵢ)‖` — the two candidates'
own symmetrized norms — so `hB` is quantified over the ball, not over the whole space. For
a syntactically quadratic presentation, the partials have radius-independent syntactic
Lipschitz bounds: the certificate discharges `hB` by `simp; norm_num` without bounding
`‖S(c)‖` (Example 14.2.1: `B = 8`). Semantic degree `≤ 2` after cancellation does not
ensure this, since the bound reads the unreduced AST. When the syntactic constant depends
on the radii, bound them through `‖S(cᵢ)‖ ≤ 2 (‖āᵢ‖ + r₀)` first. -/
theorem StdChebIVPData.Z₂_le_of_compPoly_max
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    {C B r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r₀)
    (hTC : ∀ w : XCheb ν L, ‖d.TC w‖ ≤ C * ‖w‖)
    (hB : ∀ c ∈ Metric.closedBall d.abar r₀, ∀ l,
      2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
        (fun i => max ‖l1Chebyshev.symmetrize (c i)‖
                      ‖l1Chebyshev.symmetrize (d.abar i)‖) ≤ B) :
    ∀ c ∈ Metric.closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c
        - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (C * B) * r₀ := by
  intro c hc
  have hcball : ‖c - d.abar‖ ≤ r₀ := by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hc
  have hB0 : 0 ≤ B := by
    have := hB d.abar (Metric.mem_closedBall_self hr₀) 0
    refine le_trans (mul_nonneg zero_le_two
      (CompPoly.Chebyshev.derivativeLipschitzBound_nonneg (f 0) _
        (fun i => le_max_of_le_left (norm_nonneg _)))) this
  rw [d.fderiv_G_of_compPoly f p, d.fderiv_G_of_compPoly f p]
  have hdiff : (d.TA + d.TC.comp (compPolyDerivative f c))
      - (d.TA + d.TC.comp (compPolyDerivative f d.abar))
      = d.TC.comp (compPolyDerivative f c - compPolyDerivative f d.abar) := by
    rw [ContinuousLinearMap.comp_sub]; abel
  rw [hdiff]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  show ‖d.TC ((compPolyDerivative f c - compPolyDerivative f d.abar) h)‖ ≤ _
  have hop : ‖compPolyDerivative f c - compPolyDerivative f d.abar‖ ≤ B * ‖c - d.abar‖ :=
    norm_compPolyDerivative_sub_le_max f c d.abar B (hB c hc)
  have hwnorm : ‖(compPolyDerivative f c - compPolyDerivative f d.abar) h‖
      ≤ B * ‖c - d.abar‖ * ‖h‖ :=
    ((compPolyDerivative f c - compPolyDerivative f d.abar).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg h))
  refine le_trans (hTC _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hwnorm hC) ?_
  have h1 : B * ‖c - d.abar‖ * ‖h‖ ≤ B * r₀ * ‖h‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcball hB0) (norm_nonneg h)
  have h2 := mul_le_mul_of_nonneg_left h1 hC
  linarith [h2]

/-- Existence and uniqueness of the coefficient zero for a polynomial system. The
Chebyshev counterpart of `IVP.StdIVPData.existsUnique_of_compPoly`: differentiability of
the preconditioned map is derived from the syntax, and `Z₀` is taken in the finite-block
form the certificate proves, so that `defect_finBlockNorm_lt_one_of_radii` consumes the
very same hypothesis. -/
theorem StdChebIVPData.existsUnique_of_compPoly
    (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G (banachField f) p d.abar‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall d.abar r₀, d.G (banachField f) p xTilde = 0 :=
  d.existsUnique (banachField f) p (d.differentiable_G_of_compPoly f p) hr₀ hY₀
    (d.Z₀_le hZ₀fin) hZ₁ hZ₂ h_radii

end ChebyshevIVP
