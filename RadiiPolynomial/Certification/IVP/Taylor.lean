import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.Rational.Grid
import RadiiPolynomial.Certification.ColumnTailBound
import RadiiPolynomial.Certification.Witness
import RadiiPolynomial.Certification.RadiiPolynomialQ

/-!
# Taylor certification adapter

Exact-ℚ clauses for the standard Taylor IVP bundle `IVP.StdIVPData` and a `CompPoly` vector
field, with their soundness at every real realization. The module imports the Taylor
discretization (`Applications/IVP/Taylor`) and the certification evaluators; no reusable module
below `Certification` imports it.

## Contents

1. `IVP.abarNormQ`, `IVP.seqNormQ`, `IVP.DfExactQ`, `IVP.DLipBoundQ`, `IVP.activeQ`,
   `IVP.evalArr`, `IVP.colSupQ`, `IVP.actionQ`, `IVP.supportM`, `IVP.Y₀Q`, `IVP.Z₁colQ` —
   the computable ℚ quantities read off the stored data and the syntax.
2. Bound faces on a bundle `d : IVP.StdIVPData ν L N`: the support and membership of `F(ā)`
   (`d.ivpCoeffs_abar_eq_zero_of_compPoly`, `d.ivpCoeffs_abar_mem_of_compPoly`, any real `x₀`),
   `d.Y₀_le_of_Q`, `d.Z₁_le_of_Q` (recipe `Z₁`), `d.Z₁_le_col_of_Q` (exact column `Z₁`),
   `d.Z₂_le_of_Q` (`activeBlockNormQ` at the computed scale `ν_q · DLipBoundQ`), with their
   helpers.
3. `IVP.StdIVPDataQ` — the ν-free rational record, its realization `toStdIVPData`, and the
   decidable clauses `ChecksDF`, `ChecksZ₀`, `ChecksZ₀By` (slot and grid denominator),
   `ChecksY₀`, `ChecksZ₁`, `ChecksZ₁col`, `ChecksZ₁By` (slot), `ChecksZ₂`, each with its
   soundness lemma.
4. `IVP.TaylorCertQ` (the five certificate numbers), the override face
   `StdIVPDataQ.certified_of_bounds` and the all-generated face
   `StdIVPDataQ.certified_of_checksBy` (and their source-residual forms).
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace IVP

/-! ## Computable ℚ quantities of the stored data and the syntax -/

section TaylorQ

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- Exact ℚ weighted norm of the stored approximate solution, per component. -/
def abarNormQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (i : Fin L) : ℚ :=
  ∑ k ∈ Finset.Icc 0 N, |(abar_Q i).getD k 0| * ν_q ^ k

/-- Exact ℚ weighted norm of `p` evaluated at the stored coefficients (finite support
`CompPoly.supportBound N p`). -/
def seqNormQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (p : CompPoly L) : ℚ :=
  ∑ n ∈ Finset.Icc 0 (CompPoly.supportBound N p), |p.evalCoeff abar_Q n| * ν_q ^ n

/-- Exact evaluated derivative constant `max_l Σ_m ‖∂_m f_l (ā)‖` (at the stored data,
`norm_evalBanach_abar_eq`); intended to be no larger than the syntactic `derivativeBound` at
the norms of `ā` (that comparison is not proved here). -/
def DfExactQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (f_cpoly : Fin L → CompPoly L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ m : Fin L, seqNormQ N abar_Q ν_q ((f_cpoly l).pderiv m)

/-- Syntactic derivative-Lipschitz constant `max_l derivativeLipschitzBound (f_l) S` at the
radii `S`. -/
def DLipBoundQ (f_cpoly : Fin L → CompPoly L) (S : Fin L → ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l => (f_cpoly l).derivativeLipschitzBound S

/-- Components with a nonzero syntactic derivative-Lipschitz constant at the radii `S`
(computed from the syntax). A component outside the set has syntactic constant `0` at every
nonnegative radii below `S` (monotonicity; used in `StdIVPData.Z₂_le_of_Q`); a component inside
it need not have a moving derivative, since the syntax can contain cancelling terms. -/
def activeQ (f_cpoly : Fin L → CompPoly L) (S : Fin L → ℚ) : Finset (Fin L) :=
  Finset.univ.filter fun l => (f_cpoly l).derivativeLipschitzBound S ≠ 0

/-- Coefficient array of `p` evaluated at `ā` over its syntactic support window. -/
def evalArr (N : ℕ) (abar_Q : Fin L → Array ℚ) (p : CompPoly L) : Array ℚ :=
  Array.mk ((List.range (CompPoly.supportBound N p + 1)).map fun k => p.evalCoeff abar_Q k)

/-- Exact weighted column sup of `π_{>N} ∘ shiftDivN ∘ leftMul (p(ā))`, a finite ℚ maximum
over the columns `M ≤ N`.  For a system, the tail operator of component `l` is bounded by
`Σ_m colSupQ (∂_m f_l)` (the sum of per-pair column sups; the per-column sum of the pairs is
not a bound when `L > 1`, and the two agree when `L = 1`). -/
def colSupQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (p : CompPoly L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun M : Fin (N + 1) =>
    colTailQ (evalArr N abar_Q p) ν_q N (M : ℕ) (CompPoly.supportBound N p) / ν_q ^ (M : ℕ)

/-- Exact rational action of the stored preconditioner on a rational coefficient sequence. -/
def actionQ (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (c : Fin L → ℕ → ℚ) (l : Fin L)
    (n : ℕ) : ℚ :=
  if n ≤ N then ∑ j : Fin L, ∑ k : Fin (N + 1), (A_col l j (k : ℕ)).getD n 0 * c j k
  else c l n / n

/-- Support index of `F(ā)`: past `N` and past the syntactic support of every component. -/
def supportM (f_cpoly : Fin L → CompPoly L) (N : ℕ) : ℕ :=
  max N (Finset.univ.sup fun l => CompPoly.supportBound N (f_cpoly l)) + 1

/-- Exact ℚ value of `‖(A F(ā))_l‖` (the `Y₀` numerator). -/
def Y₀Q (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f_cpoly : Fin L → CompPoly L) (x₀_q : Fin L → ℚ) (l : Fin L) : ℚ :=
  ∑ n ∈ Finset.Icc 0 (supportM f_cpoly N),
    |actionQ N A_col (IVP.ivpCoeffsQ f_cpoly abar_Q x₀_q) l n| * ν_q ^ n

/-- The computed column `Z₁`: `max_l Σ_m colSupQ (∂_m f_l)`. -/
def Z₁colQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (f_cpoly : Fin L → CompPoly L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ m : Fin L, colSupQ N abar_Q ν_q ((f_cpoly l).pderiv m)

/-! ### Column `Z₁` helpers

The tail operator of `Z₁` at component `l` is `h ↦ π_{>N} shiftDivN (Σ_m b_{lm} · h_m)` with
`b_{lm} = ∂_m f_l(ā)`. Per pair `(l, m)` the exact weighted column sup of
`π_{>N} ∘ shiftDivN ∘ leftMul b_{lm}` is the finite ℚ maximum `colSupQ` over `M ≤ N`
(columns above `N` are antitone, `shiftDivN_leftMul_tail_cols_le_of_Q`). Since `‖h‖` is the
sup over components, the operator bound is `Σ_m colSupQ_{lm}`; the per-`M` sum
`sup_M Σ_m` would NOT be sound for `L > 1` (different components can peak at different `M`).
For `L = 1` the two coincide. -/

omit [NeZero L] in
/-- `evalArr N abar_Q p` vanishes past the syntactic support window `CompPoly.supportBound N p`. -/
theorem evalArr_getD_eq_zero (p : CompPoly L) (abar_Q : Fin L → Array ℚ) (k : ℕ)
    (hk : CompPoly.supportBound N p < k) : (evalArr N abar_Q p).getD k 0 = 0 := by
  simp [evalArr, Array.getD, show ¬ k < CompPoly.supportBound N p + 1 by omega]

omit [NeZero L] in
/-- The exact column sup `colSupQ` is nonnegative at a positive rational weight `ν_q`. -/
theorem colSupQ_nonneg (abar_Q : Fin L → Array ℚ) {ν_q : ℚ} (hν : 0 < ν_q) (p : CompPoly L) :
    0 ≤ colSupQ N abar_Q ν_q p :=
  (div_nonneg (colTailQ_nonneg _ hν.le N 0 _) (pow_nonneg hν.le 0)).trans
    (Finset.le_sup' (fun M : Fin (N + 1) =>
      colTailQ (evalArr N abar_Q p) ν_q N (M : ℕ) (CompPoly.supportBound N p) / ν_q ^ (M : ℕ))
      (Finset.mem_univ 0))

@[deprecated RadiiPolynomial.tail_shiftDivN_sum_le (since := "2026-10-05")]
alias tail_shiftDivN_sum_le := RadiiPolynomial.tail_shiftDivN_sum_le

end TaylorQ

/-! ## Bound faces on a bundle -/

namespace StdIVPData

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- The stored rational weight of a bundle is positive (it casts to `ν > 0`). -/
theorem ν_q_pos (d : IVP.StdIVPData ν L N) : 0 < d.ν_q := by
  have h : (0 : ℝ) < (d.ν_q : ℝ) := d.hν ▸ ν.2
  exact_mod_cast h

/-- The stored approximate solution has no coefficients past `N`: `(abar_Q i)[k] = 0` for
`N < k` (from the array size `N + 1`). -/
theorem abar_Q_getD_eq_zero (d : IVP.StdIVPData ν L N) (i : Fin L) (k : ℕ) (hk : N < k) :
    (d.abar_Q i).getD k 0 = 0 := by
  simp [Array.getD, show ¬ k < (d.abar_Q i).size by rw [d.habar_size i]; omega]

/-- The rational weighted norm `abarNormQ` of each stored component is nonnegative. -/
theorem abarNormQ_nonneg (d : IVP.StdIVPData ν L N) (i : Fin L) :
    0 ≤ abarNormQ N d.abar_Q d.ν_q i :=
  Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (pow_nonneg (ν_q_pos d).le k)

/-- The weighted ℓ¹ norm of the realized component `ā_i` equals the cast of its exact
rational norm `abarNormQ`. -/
theorem norm_abar_eq (d : IVP.StdIVPData ν L N) (i : Fin L) :
    ‖d.abar i‖ = (abarNormQ N d.abar_Q d.ν_q i : ℝ) :=
  l1Weighted.norm_eq_ratCast_sum_of_support _ _ _ (d.abar_toSeq_eq i) d.hν N
    (abar_Q_getD_eq_zero d i)

/-- `Z₂` from one exact-ℚ check of `activeBlockNormQ` at the computed scale
`C_q = ν_q · DLipBoundQ`: the derivative-Lipschitz constant of the polynomial field and its
active components are computed from the syntax at the radii `‖ā_i‖ + r₀`, so every degree is
covered and no constant is supplied by the caller. -/
theorem Z₂_le_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ) {r₀ : ℚ} (hr₀ : 0 ≤ r₀) {Z₂ : ℚ}
    (hle : activeBlockNormQ L N (fun l j k => d.A_col l j (k : ℕ)) d.ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N))
      (d.ν_q * DLipBoundQ f_cpoly (fun i => abarNormQ N d.abar_Q d.ν_q i + r₀))
      (activeQ f_cpoly (fun i => abarNormQ N d.abar_Q d.ν_q i + r₀)) ≤ Z₂) :
    ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ),
      Z₂_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (Z₂ : ℝ) * (r₀ : ℝ) := by
  set S : Fin L → ℚ := fun i => abarNormQ N d.abar_Q d.ν_q i + r₀
  have hS0 : ∀ i, (0 : ℚ) ≤ S i := fun i => add_nonneg (abarNormQ_nonneg d i) hr₀
  have hmax : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ), ∀ i,
      max ‖c i‖ ‖d.abar i‖ ≤ ((S i : ℚ) : ℝ) := fun c hc i => by
    have hd : ‖c - d.abar‖ ≤ (r₀ : ℝ) := by rw [← dist_eq_norm]; exact hc
    have hci : ‖c i - d.abar i‖ ≤ ‖c - d.abar‖ := norm_le_pi_norm (c - d.abar) i
    have hr : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
    have ha := norm_abar_eq d i
    simp only [S]; push_cast
    refine max_le ?_ (by linarith)
    have := norm_le_insert' (c i) (d.abar i)
    linarith [norm_sub_norm_le (c i) (d.abar i)]
  have hmono : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ), ∀ l,
      (f_cpoly l).derivativeLipschitzBound (fun i => max ‖c i‖ ‖d.abar i‖) ≤
        (((f_cpoly l).derivativeLipschitzBound S : ℚ) : ℝ) := fun c hc l => by
    rw [CompPoly.derivativeLipschitzBound_ratCast]
    exact CompPoly.derivativeLipschitzBound_mono _ (fun i => le_max_of_le_left (norm_nonneg _))
      (hmax c hc)
  have hBnn : 0 ≤ DLipBoundQ f_cpoly S :=
    (CompPoly.derivativeLipschitzBound_nonneg (f_cpoly 0) S hS0).trans
      (Finset.le_sup' (fun l => (f_cpoly l).derivativeLipschitzBound S) (Finset.mem_univ 0))
  refine d.Z₂_le_of_compPoly f_cpoly x₀ (activeQ f_cpoly S)
    (B := (DLipBoundQ f_cpoly S : ℝ))
    (fun l => ?_) (by exact_mod_cast hr₀) ?_ ?_
  · have h := activeBlockNorm_component_le d.approxInverse
      (fun l j k => d.A_col l j (k : ℕ)) d.ν_q _ _ (activeQ f_cpoly S)
      (fun l j k i => d.A_finBlock_eq l j i k) d.hν d.approxInverse_tailBound_eq
      (mul_nonneg (ν_q_pos d).le hBnn) hle l
    have e : ((DLipBoundQ f_cpoly S : ℚ) : ℝ) * (ν : ℝ) =
        ((d.ν_q * DLipBoundQ f_cpoly S : ℚ) : ℝ) := by
      rw [d.hν]; push_cast; ring
    rw [e]; exact h
  · intro j hj c hc
    have h0 : (f_cpoly j).derivativeLipschitzBound S = 0 := by
      simpa [activeQ] using hj
    refine le_antisymm ?_ (CompPoly.derivativeLipschitzBound_nonneg _ _
      (fun i => le_max_of_le_left (norm_nonneg _)))
    have := hmono c hc j
    rw [h0, Rat.cast_zero] at this
    exact this
  · intro c hc l
    refine (hmono c hc l).trans ?_
    exact_mod_cast Finset.le_sup' (fun l => (f_cpoly l).derivativeLipschitzBound S)
      (Finset.mem_univ l)

/-- On a sequence with rational coefficients `cq`, the action of the stored preconditioner
`approxInverse` is the cast of the exact rational action `actionQ` (finite block for `n ≤ N`,
diagonal tail `c n / n` above). -/
theorem action_eq_actionQ (d : IVP.StdIVPData ν L N) (c : SystemCoeff L)
    (cq : Fin L → ℕ → ℚ) (hc : ∀ l n, c l n = (cq l n : ℝ)) (l : Fin L) (n : ℕ) :
    d.approxInverse.action c l n = (actionQ N d.A_col cq l n : ℝ) := by
  rw [d.approxInverse.action_eq_blockActionQ (fun l j k => d.A_col l j (k : ℕ))
    (fun _ n => 1 / (n : ℚ)) (fun l j k i => d.A_finBlock_eq l j i k)
    (fun l n hn => by rw [d.htail_diag_inv l n hn]; push_cast; rfl) c cq hc l n]
  unfold blockActionQ actionQ
  split_ifs <;> first | rfl | (push_cast; ring)

/-- The rational IVP coefficients at `ā` vanish past `supportM f_cpoly N`, the support index
read off the syntax. -/
theorem ivpCoeffsQ_support (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀_q : Fin L → ℚ) (l : Fin L) (n : ℕ) (hn : supportM f_cpoly N < n) :
    IVP.ivpCoeffsQ f_cpoly d.abar_Q x₀_q l n = 0 := by
  have hsb : CompPoly.supportBound N (f_cpoly l) ≤
      Finset.univ.sup fun l => CompPoly.supportBound N (f_cpoly l) :=
    Finset.le_sup (f := fun l => CompPoly.supportBound N (f_cpoly l)) (Finset.mem_univ l)
  unfold supportM at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [IVP.ivpCoeffsQ]
  rw [abar_Q_getD_eq_zero d l (m + 1) (by omega), CompPoly.evalCoeff,
    CompPoly.evalCoeffSeq_eq_zero_of_support N (f_cpoly l) _
      (fun i k hk => abar_Q_getD_eq_zero d i k hk) m (by omega)]
  ring

/-- The real IVP coefficients `F(ā)` of a `CompPoly` field vanish past `supportM f_cpoly N`, for
every real initial value `x₀` (`x₀` enters `ivpCoeffs` only at `n = 0`, and `n > 0` here): the
rational bridge at zero initial data and `ivpCoeffsQ_support`. -/
theorem ivpCoeffs_abar_eq_zero_of_compPoly (d : IVP.StdIVPData ν L N)
    (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (l : Fin L) (n : ℕ)
    (hn : supportM f_cpoly N < n) :
    IVP.ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ d.abar l n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by unfold supportM at hn; omega⟩
  have h := d.ivpCoeffs_abar_eq_cast_of_compPoly f_cpoly 0 0 (fun _ => by simp) l (m + 1)
  rw [ivpCoeffsQ_support d f_cpoly 0 l (m + 1) hn, Rat.cast_zero] at h
  exact h

/-- Each component of `F(ā)` lies in `ℓ¹_ν` (finite support `supportM f_cpoly N`), for every real
initial value `x₀`. -/
theorem ivpCoeffs_abar_mem_of_compPoly (d : IVP.StdIVPData ν L N)
    (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (l : Fin L) :
    l1Weighted.Mem ν
      (fun n => IVP.ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ d.abar l n) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (supportM f_cpoly N)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [ivpCoeffs_abar_eq_zero_of_compPoly d f_cpoly x₀ l n (by omega)]

/-- `Y₀` from one exact-ℚ check. -/
theorem Y₀_le_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ) (x₀_q : Fin L → ℚ) (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) {Y₀ : ℚ}
    (hle : ∀ l, Y₀Q N d.A_col d.abar_Q d.ν_q f_cpoly x₀_q l ≤ Y₀) :
    Y₀_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar
      (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ (Y₀ : ℝ) := by
  set φ : XL1 ν L → Fin L → l1Weighted ν := IVP.banachField f_cpoly
  set M := supportM f_cpoly N
  have hF : ∀ l n, IVP.ivpCoeffs φ x₀ d.abar l n =
      (IVP.ivpCoeffsQ f_cpoly d.abar_Q x₀_q l n : ℝ) :=
    fun l n => d.ivpCoeffs_abar_eq_cast_of_compPoly f_cpoly x₀ x₀_q hx₀ l n
  have hsupp : ∀ l n, M < n → IVP.ivpCoeffs φ x₀ d.abar l n = 0 := fun l n hn => by
    rw [hF, ivpCoeffsQ_support d f_cpoly x₀_q l n hn, Rat.cast_zero]
  have hmem : ∀ l, l1Weighted.Mem ν (IVP.ivpCoeffs φ x₀ d.abar l) := fun l => by
    rw [l1Weighted.mem_iff]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 M) fun n hn => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp [hsupp l n (by omega)]
  set v : XL1 ν L := ofCoeff (IVP.ivpCoeffs φ x₀ d.abar) hmem
  have hG : d.G φ x₀ d.abar = d.approxInverse.toCLM (ν := ν) v := by
    funext l; apply l1Weighted.ext; intro n
    exact (d.G_coeff φ x₀ d.abar l n).trans (by
      have := SystemBlockDiagData.toCoeff_toCLM (ν := ν) d.approxInverse v l n
      simp only [toCoeff] at this; exact this.symm)
  have hc : toCoeff (ν := ν) v = IVP.ivpCoeffs φ x₀ d.abar := by
    ext l n; simp [v, toCoeff_ofCoeff]
  have hY0 : (0 : ℝ) ≤ (Y₀ : ℝ) := by
    have : 0 ≤ Y₀Q N d.A_col d.abar_Q d.ν_q f_cpoly x₀_q 0 := Finset.sum_nonneg fun n _ =>
      mul_nonneg (abs_nonneg _) (pow_nonneg (ν_q_pos d).le n)
    exact_mod_cast this.trans (hle 0)
  show ‖d.G φ x₀ d.abar‖ ≤ _
  rw [hG]
  refine d.approxInverse.norm_toCLM_apply_le v M (by simp only [M, supportM]; omega)
    (fun l n hn => by rw [hc]; exact hsupp l n hn) hY0 (fun l => ?_)
  rw [hc]
  refine le_of_eq_of_le ?_
    (by exact_mod_cast hle l : ((Y₀Q N d.A_col d.abar_Q d.ν_q f_cpoly x₀_q l : ℚ) : ℝ) ≤ Y₀)
  unfold Y₀Q
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [action_eq_actionQ d _ _ hF l n, d.hν]

/-- The weighted norm of a `CompPoly` evaluated at `ā` equals the cast of the exact
rational sum `seqNormQ` over its syntactic support window. -/
theorem norm_evalBanach_abar_eq (d : IVP.StdIVPData ν L N) (p : CompPoly L) :
    ‖p.evalBanach d.abar‖ = (seqNormQ N d.abar_Q d.ν_q p : ℝ) :=
  l1Weighted.norm_eq_ratCast_sum_of_support _ _ _
    (p.toSeq_evalBanach d.abar d.abar_Q d.abar_toSeq_eq) d.hν _ fun n hn => by
      rw [CompPoly.evalCoeff, CompPoly.evalCoeffSeq_eq_zero_of_support N p _
        (fun i k hk => abar_Q_getD_eq_zero d i k hk) n hn]

/-- `Z₁` from the finite Jacobian check `hDF` and one ℚ inequality; the derivative
constant is the exact evaluated one, computed from the bundle and the syntax. -/
theorem Z₁_le_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ)
    (hDF : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    {Z₁ : ℚ} (hle : d.ν_q / ((N : ℚ) + 1) * DfExactQ N d.abar_Q d.ν_q f_cpoly ≤ Z₁) :
    Z₁_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ (Z₁ : ℝ) := by
  set K := DfExactQ N d.abar_Q d.ν_q f_cpoly
  have hK : ∀ l, ∑ m : Fin L, ‖evalInBanach (MvPolynomial.pderiv m (f_cpoly l).toMvPoly)
      d.abar‖ ≤ (K : ℝ) := fun l => by
    simp_rw [← CompPoly.pderiv_toMvPoly, ← compPoly_evalBanach_eq_evalInBanach,
      norm_evalBanach_abar_eq d]
    exact_mod_cast Finset.le_sup'
      (fun l => ∑ m : Fin L, seqNormQ N d.abar_Q d.ν_q ((f_cpoly l).pderiv m))
      (Finset.mem_univ l)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hK 0)
  refine d.Z₁_le_of_compPoly f_cpoly x₀
    (d.composedApprox_eq_fderiv_G_fin_of_compPoly f_cpoly x₀ hDF)
    (fun h l => (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) d.abar) h)
    (fun _ _ => rfl) hK0
    (fun h l => IVP.ivp_Dφ_norm_le (IVP.banachField f_cpoly) (fun l => (f_cpoly l).toMvPoly)
      d.abar (fun a l => compPoly_evalBanach_eq_evalInBanach (f_cpoly l) a) hK h l) ?_
  rw [d.hν]
  exact_mod_cast hle

/-- Every entry of `evalArr N d.abar_Q p` (in or past the support window) is the exact
coefficient `p.evalCoeff d.abar_Q k`. -/
theorem evalArr_getD (d : IVP.StdIVPData ν L N) (p : CompPoly L) (k : ℕ) :
    (evalArr N d.abar_Q p).getD k 0 = p.evalCoeff d.abar_Q k := by
  by_cases hk : k < CompPoly.supportBound N p + 1
  · simp [evalArr, Array.getD, hk]
  · rw [CompPoly.evalCoeff, CompPoly.evalCoeffSeq_eq_zero_of_support N p _
      (fun i n hn => abar_Q_getD_eq_zero d i n hn) k (by omega)]
    simp [evalArr, Array.getD, hk]

/-- Per-pair soundness: the tail of `shiftDivN (p(ā) · x)` is at most `colSupQ p · ‖x‖`. -/
theorem tail_evalBanach_mul_le (d : IVP.StdIVPData ν L N) (p : CompPoly L)
    (x : l1Weighted ν) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (p.evalBanach d.abar * x)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ (colSupQ N d.abar_Q d.ν_q p : ℝ) * ‖x‖ := by
  have hνq := ν_q_pos d
  refine shiftDivN_leftMul_tail_le_of_cols _ N
    (shiftDivN_leftMul_tail_cols_le_of_Q (p.evalBanach d.abar) (evalArr N d.abar_Q p) d.ν_q
      (CompPoly.supportBound N p) N
      (fun k => by rw [p.toSeq_evalBanach d.abar d.abar_Q d.abar_toSeq_eq k, evalArr_getD d])
      (fun k hk => evalArr_getD_eq_zero p d.abar_Q k hk) d.hν
      (fun M => (div_le_iff₀ (pow_pos hνq _)).mp
        (Finset.le_sup' (fun M : Fin (N + 1) =>
          colTailQ (evalArr N d.abar_Q p) d.ν_q N (M : ℕ) (CompPoly.supportBound N p) /
            d.ν_q ^ (M : ℕ)) (Finset.mem_univ M)))) x

/-- The derivative of a `CompPoly` component at `ā`, as a sum of left multiplications. -/
theorem fderiv_banachField_apply (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) d.abar) h =
      ∑ m : Fin L, ((f_cpoly l).pderiv m).evalBanach d.abar * h m :=
  fderiv_banachField_apply' f_cpoly d.abar h l

/-- **Column `Z₁` face (generic in `L`)**: the finite Jacobian check `hDF` and one ℚ
inequality `Σ_m colSupQ (∂_m f_l) ≤ Z₁` per component give the `Z₁` operator bound, through
`StdIVPData.Z₁_le_exact_of_compPoly`. -/
theorem Z₁_le_col_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ)
    (hDF : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    {Z₁ : ℚ} (hle : ∀ l, ∑ m : Fin L, colSupQ N d.abar_Q d.ν_q ((f_cpoly l).pderiv m) ≤ Z₁) :
    Z₁_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ (Z₁ : ℝ) := by
  have hνq := ν_q_pos d
  have hC : (0 : ℝ) ≤ (Z₁ : ℝ) := by
    have := (Finset.sum_nonneg fun m _ =>
      colSupQ_nonneg d.abar_Q hνq ((f_cpoly 0).pderiv m)).trans (hle 0)
    exact_mod_cast this
  refine d.Z₁_le_exact_of_compPoly f_cpoly x₀
    (d.composedApprox_eq_fderiv_G_fin_of_compPoly f_cpoly x₀ hDF)
    (fun h l => (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) d.abar) h)
    (fun _ _ => rfl) hC (fun h l => ?_) le_rfl
  rw [fderiv_banachField_apply d f_cpoly h l]
  refine (RadiiPolynomial.tail_shiftDivN_sum_le Finset.univ _).trans ?_
  refine (Finset.sum_le_sum fun m _ =>
    (tail_evalBanach_mul_le d ((f_cpoly l).pderiv m) (h m)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm h m)
        (by exact_mod_cast colSupQ_nonneg d.abar_Q hνq ((f_cpoly l).pderiv m)))).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact_mod_cast hle l

end StdIVPData

/-! ## The ν-free record, its clauses and the certificate faces -/

/-- The five certificate numbers — the only data a certificate supplies beyond its record. -/
structure TaylorCertQ where
  Y₀ : ℚ
  Z₀ : ℚ
  Z₁ : ℚ
  Z₂ : ℚ
  r₀ : ℚ

/-- Exact ℚ value of the radii polynomial `Z₂ r₀² − (1 − Z₀ − Z₁) r₀ + Y₀`. -/
def TaylorCertQ.margin (C : TaylorCertQ) : ℚ :=
  C.Z₂ * C.r₀ ^ 2 - (1 - C.Z₀ - C.Z₁) * C.r₀ + C.Y₀

/-- The radii clause: positive radius and negative margin. -/
abbrev TaylorCertQ.ChecksRadii (C : TaylorCertQ) : Prop := 0 < C.r₀ ∧ C.margin < 0

/-- Which generated `Z₁` clause a certificate uses: the recipe majorant or the exact
column sums. -/
inductive Z₁Slot
  | recipe
  | column
  deriving DecidableEq

/-- **ν-free rational Taylor-IVP record**: the ℚ fields of `IVP.StdIVPData` and its stored
shape invariant, without the real weight.

Usage sketch (symbolic): a certificate supplies
`q : StdIVPDataQ L N := ⟨A_col, DF_col, abar_Q, ν_q, habar_size⟩` with
`habar_size : ∀ l, (abar_Q l).size = N + 1`, and realizes it at a real weight `ν` with a
bridge `hν : (ν : ℝ) = (ν_q : ℝ)` as `q.toStdIVPData ν hν : IVP.StdIVPData ν L N`; every
clause below is a decidable proposition on `q` alone. -/
structure StdIVPDataQ (L N : ℕ) [NeZero L] where
  A_col : Fin L → Fin L → ℕ → Array ℚ
  DF_col : Fin L → Fin L → ℕ → Array ℚ
  abar_Q : Fin L → Array ℚ
  ν_q : ℚ
  habar_size : ∀ l, (abar_Q l).size = N + 1

namespace StdIVPDataQ

variable {L N : ℕ} [NeZero L]

/-- Realization at a real weight with its rational bridge. -/
def toStdIVPData (q : StdIVPDataQ L N) (ν : PosReal) (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ)) :
    IVP.StdIVPData ν L N where
  A_col := q.A_col
  DF_col := q.DF_col
  abar_Q := q.abar_Q
  ν_q := q.ν_q
  hν := hν
  habar_size := q.habar_size

/-- `Z₀` exact clause of the record (one-line specialisation of `DefectExact`). -/
abbrev ChecksZ₀ (q : StdIVPDataQ L N) (Z₀ : ℚ) : Prop :=
  DefectExact L N q.A_col q.DF_col q.ν_q Z₀

/-- `Z₀` clause at a slot and grid denominator (one-line specialisation of `DefectBy`). -/
abbrev ChecksZ₀By (q : StdIVPDataQ L N) (s : Z₀Slot) (S : ℕ) (Z₀ : ℚ) : Prop :=
  DefectBy L N q.A_col q.DF_col q.ν_q s S Z₀

/-- `Z₂` clause: `activeBlockNormQ` at the computed scale `ν_q · DLipBoundQ` and the computed
active set, both at the radii `‖āᵢ‖ + r₀`. -/
abbrev ChecksZ₂ (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L) (r₀ Z₂ : ℚ) : Prop :=
  activeBlockNormQ L N (fun l j k => q.A_col l j (k : ℕ)) q.ν_q
    (IVP.StdIVPData.approxInverse_tailBound_q (N := N))
    (q.ν_q * DLipBoundQ f_cpoly (fun i => abarNormQ N q.abar_Q q.ν_q i + r₀))
    (activeQ f_cpoly (fun i => abarNormQ N q.abar_Q q.ν_q i + r₀)) ≤ Z₂

/-- The weight read off a record with positive rational weight. -/
def weight (q : StdIVPDataQ L N) (hpos : 0 < q.ν_q) : PosReal :=
  ⟨(q.ν_q : ℝ), by exact_mod_cast hpos⟩

/-- Default realization: `ν` chosen as the cast of `ν_q`, `hν := rfl`. -/
def toStd (q : StdIVPDataQ L N) (hpos : 0 < q.ν_q) : IVP.StdIVPData (q.weight hpos) L N :=
  q.toStdIVPData (q.weight hpos) rfl

/-- Forgetful map from an existing bundle: its ℚ fields and size invariant, forgetting `hν`
(`toStdIVPData_ofStd` is the definitional round trip). -/
def ofStd {ν : PosReal} (d : IVP.StdIVPData ν L N) : StdIVPDataQ L N :=
  ⟨d.A_col, d.DF_col, d.abar_Q, d.ν_q, d.habar_size⟩

/-- Round trip: every existing bundle is the realization of its ν-free record. -/
theorem toStdIVPData_ofStd {ν : PosReal} (d : IVP.StdIVPData ν L N) :
    (ofStd d).toStdIVPData ν d.hν = d := rfl

/-! #### Soundness bridges for the exact stored data -/

section Bridges

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))

/-- The realization keeps the stored preconditioner columns `A_col`. -/
@[simp] theorem toStdIVPData_A_col : (q.toStdIVPData ν hν).A_col = q.A_col := rfl
/-- The realization keeps the stored Jacobian columns `DF_col`. -/
@[simp] theorem toStdIVPData_DF_col : (q.toStdIVPData ν hν).DF_col = q.DF_col := rfl
/-- The realization keeps the stored approximate solution `abar_Q`. -/
@[simp] theorem toStdIVPData_abar_Q : (q.toStdIVPData ν hν).abar_Q = q.abar_Q := rfl
/-- The realization keeps the stored rational weight `ν_q`. -/
@[simp] theorem toStdIVPData_ν_q : (q.toStdIVPData ν hν).ν_q = q.ν_q := rfl

/-- The coefficients of the realized `ā_i` are the casts of the stored rationals. -/
theorem abar_toSeq (i : Fin L) (k : ℕ) :
    l1Weighted.toSeq ((q.toStdIVPData ν hν).abar i) k = ((q.abar_Q i).getD k 0 : ℝ) :=
  (q.toStdIVPData ν hν).abar_toSeq_eq i k

/-- The realized `‖ā_i‖` is the cast of the ν-free rational norm `abarNormQ`. -/
theorem norm_abar (i : Fin L) :
    ‖(q.toStdIVPData ν hν).abar i‖ = (abarNormQ N q.abar_Q q.ν_q i : ℝ) :=
  StdIVPData.norm_abar_eq (q.toStdIVPData ν hν) i

/-- The finite block of the realized preconditioner reads the stored rational columns
`A_col` (definitional). -/
theorem A_finBlock_eq (l j : Fin L) (i k : Fin (N + 1)) :
    (q.toStdIVPData ν hν).A_finBlock l j i k = ((q.A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) :=
  rfl

/-- The finite block of the realized Jacobian reads the stored rational columns `DF_col`
(definitional). -/
theorem DF_finBlock_eq (l j : Fin L) (i k : Fin (N + 1)) :
    (q.toStdIVPData ν hν).DF_finBlock l j i k = ((q.DF_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) :=
  rfl

end Bridges

/-! #### ν-free slot checks (each decidable, no `ν`) -/

section Checks

variable (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L)

/-- Jacobian clause: the stored `DF` is the exact finite Jacobian of `f_cpoly` at `ā`. -/
abbrev ChecksDF : Prop :=
  ∀ (j m : Fin L) (row col : Fin (N + 1)),
    (q.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
      IVP.ivp_DF_of_Dφ_nat (fun j m k => ((f_cpoly j).pderiv m).evalCoeff q.abar_Q k)
        j m (row : ℕ) (col : ℕ)

/-- `Y₀` clause: exact ℚ norm of `A F(ā)`, per component. -/
abbrev ChecksY₀ (x₀_q : Fin L → ℚ) (Y₀ : ℚ) : Prop :=
  ∀ l, Y₀Q N q.A_col q.abar_Q q.ν_q f_cpoly x₀_q l ≤ Y₀

/-- `Z₁` recipe clause: `ν/(N+1) · max_l Σ_m ‖∂_m f_l(ā)‖ ≤ Z₁` (generated majorant). -/
abbrev ChecksZ₁ (Z₁ : ℚ) : Prop :=
  q.ν_q / ((N : ℚ) + 1) * DfExactQ N q.abar_Q q.ν_q f_cpoly ≤ Z₁

/-- Column `Z₁` clause: `Σ_m colSupQ (∂_m f_l) ≤ Z₁` for every component. -/
abbrev ChecksZ₁col (Z₁ : ℚ) : Prop :=
  ∀ l, ∑ m : Fin L, colSupQ N q.abar_Q q.ν_q ((f_cpoly l).pderiv m) ≤ Z₁

/-- The `Z₁` slot at a chosen route: the recipe majorant or the exact column sums. -/
def ChecksZ₁By : Z₁Slot → ℚ → Prop
  | .recipe, Z₁ => q.ChecksZ₁ f_cpoly Z₁
  | .column, Z₁ => q.ChecksZ₁col f_cpoly Z₁

/-- The `Z₁` slot clause is decidable at either route, so `decide` can discharge it. -/
instance instDecidableChecksZ₁By (s : Z₁Slot) (Z₁ : ℚ) :
    Decidable (q.ChecksZ₁By f_cpoly s Z₁) :=
  match s with
  | .recipe => inferInstanceAs (Decidable (q.ChecksZ₁ f_cpoly Z₁))
  | .column => inferInstanceAs (Decidable (q.ChecksZ₁col f_cpoly Z₁))

end Checks

/-- All generated clauses, with the `Z₀` clause at slot `s₀` and grid denominator `S` and the
`Z₁` clause at slot `s₁`. -/
abbrev _root_.IVP.TaylorCertQ.ChecksBy (s₀ : Z₀Slot) (S : ℕ) (s₁ : Z₁Slot) (C : TaylorCertQ)
    (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L) (x₀_q : Fin L → ℚ) : Prop :=
  q.ChecksDF f_cpoly ∧ q.ChecksZ₀By s₀ S C.Z₀ ∧ q.ChecksY₀ f_cpoly x₀_q C.Y₀ ∧
    q.ChecksZ₁By f_cpoly s₁ C.Z₁ ∧ q.ChecksZ₂ f_cpoly C.r₀ C.Z₂ ∧ C.ChecksRadii

section Sound

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))

/-- The exact `Z₀` clause bounds the finite block norm of the realized defect `I - A·A†`. -/
theorem Z₀_sound {Z₀ : ℚ} (h : q.ChecksZ₀ Z₀) :
    finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (Z₀ : ℝ) :=
  finiteBlockMatrixNorm_defect_le_of_Q _ _ q.A_col q.DF_col q.ν_q
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hν h

/-- The slot/grid `Z₀` clause (at slot `s`, grid denominator `S`) implies the exact `Z₀`
clause. -/
theorem ChecksZ₀By_sound (s : Z₀Slot) (S : ℕ) {Z₀ : ℚ} (h : q.ChecksZ₀By s S Z₀) :
    q.ChecksZ₀ Z₀ :=
  defectBy_sound s S h

/-- The slot/grid `Z₀` clause bounds the finite block norm of the realized defect. -/
theorem defectZBy_sound (s : Z₀Slot) (S : ℕ) {Z₀ : ℚ} (h : q.ChecksZ₀By s S Z₀) :
    finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (Z₀ : ℝ) :=
  q.Z₀_sound hν (q.ChecksZ₀By_sound s S h)

/-- The `Z₂` clause, at a nonnegative radius `r₀`, gives the `Z₂` bound `Z₂ · r₀` on the
closed ball of radius `r₀` around the realized `ā`. -/
theorem Z₂_sound (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) {r₀ Z₂ : ℚ} (hr₀ : 0 ≤ r₀)
    (h : q.ChecksZ₂ f_cpoly r₀ Z₂) :
    ∀ c ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (r₀ : ℝ),
      Z₂_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (Z₂ : ℝ) * (r₀ : ℝ) :=
  StdIVPData.Z₂_le_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ hr₀ h

end Sound

/-! #### Soundness of the remaining slots and the certificate faces -/

section Faces

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))
  (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)

/-- The `Y₀` clause bounds `‖A F(ā)‖` for the realization, given that the initial value
`x₀` is the cast of the rational `x₀_q`. -/
theorem Y₀_sound (x₀_q : Fin L → ℚ) (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) {Y₀ : ℚ}
    (h : q.ChecksY₀ f_cpoly x₀_q Y₀) :
    Y₀_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
      (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ (Y₀ : ℝ) :=
  StdIVPData.Y₀_le_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ x₀_q hx₀ h

/-- The Jacobian clause gives the finite-mode identification every `Z₁` route needs
(recipe or override). -/
theorem composedApprox_eq_of_checksDF (h : q.ChecksDF f_cpoly) :
    ∀ (v : XL1 ν L) (l : Fin L) (n : ℕ), n ≤ N →
      toCoeff (ν := ν) ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν) v)
          l n =
        toCoeff (ν := ν) ((fderiv ℝ ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀)
          (q.toStdIVPData ν hν).abar) v) l n :=
  fun v l n hn =>
    (q.toStdIVPData ν hν).composedApprox_eq_fderiv_G_fin_of_compPoly f_cpoly x₀ h v l n hn

/-- The recipe `Z₁` clause, together with the Jacobian clause `ChecksDF`, bounds the
`Z₁` operator norm of the realization. -/
theorem Z₁_sound {Z₁ : ℚ} (hDF : q.ChecksDF f_cpoly) (h : q.ChecksZ₁ f_cpoly Z₁) :
    Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (Z₁ : ℝ) :=
  StdIVPData.Z₁_le_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ hDF h

/-- The radii clause makes the general radii polynomial negative at the certificate's
numbers `Y₀ Z₀ Z₁ Z₂ r₀`. -/
theorem radii_sound (C : TaylorCertQ) (h : C.ChecksRadii) :
    generalRadiiPolynomial (C.Y₀ : ℝ) (C.Z₀ : ℝ) (C.Z₁ : ℝ) (fun _ => (C.Z₂ : ℝ)) (C.r₀ : ℝ)
      < 0 :=
  generalRadiiPolynomial_neg_of_Q_const _ _ _ _ _ h.2

/-! #### The override face (the `_of_le` pattern, slot by slot) -/

/-- **Override face.** Each of `Y₀ Z₀ Z₁ Z₂` is a user-supplied rational with a PROOF
that it bounds the true quantity of the realization; each proof may come from the matching
slot check (`Y₀_sound`, `Z₀_sound`, `Z₁_sound`, `Z₂_sound`) or from a hand proof of a sharper
bound. Only the radii clause is ℚ-decidable here. -/
theorem certified_of_bounds (C : TaylorCertQ)
    (hY₀ : Y₀_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀)
      (q.toStdIVPData ν hν).abar (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ (C.Y₀ : ℝ))
    (hZ₀ : finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (C.Z₀ : ℝ))
    (hZ₁ : Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀)
      (q.toStdIVPData ν hν).abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (C.Z₁ : ℝ))
    (hZ₂ : ∀ c ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      Z₂_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (C.Z₂ : ℝ) * (C.r₀ : ℝ))
    (hrad : C.ChecksRadii) :
    ∃! xTilde ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      (q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀ xTilde = 0 :=
  (q.toStdIVPData ν hν).existsUnique_of_compPoly f_cpoly x₀ (Z₂ := fun _ => (C.Z₂ : ℝ))
    (by exact_mod_cast hrad.1) hY₀ hZ₀ hZ₁ hZ₂ (radii_sound C hrad)

/-- Source-residual form of `certified_of_bounds` (same hypotheses). -/
theorem certified_ivpCoeffs_of_bounds (C : TaylorCertQ)
    (hY₀ : Y₀_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀)
      (q.toStdIVPData ν hν).abar (ContinuousLinearMap.id ℝ (XL1 ν L)) ≤ (C.Y₀ : ℝ))
    (hZ₀ : finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (C.Z₀ : ℝ))
    (hZ₁ : Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀)
      (q.toStdIVPData ν hν).abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (C.Z₁ : ℝ))
    (hZ₂ : ∀ c ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      Z₂_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (C.Z₂ : ℝ) * (C.r₀ : ℝ))
    (hrad : C.ChecksRadii) :
    ∃! xTilde ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      ∀ l n, IVP.ivpCoeffs (IVP.banachField f_cpoly) x₀ xTilde l n = 0 :=
  (q.toStdIVPData ν hν).existsUnique_ivpCoeffs_of_compPoly f_cpoly x₀
    (Z₂ := fun _ => (C.Z₂ : ℝ))
    (by exact_mod_cast hrad.1) hY₀ hZ₀ hZ₁ hZ₂ (radii_sound C hrad)

/-! #### Soundness of the column slot and of the slot choice -/

/-- The column `Z₁` clause, together with the Jacobian clause `ChecksDF`, bounds the
`Z₁` operator norm of the realization. -/
theorem Z₁col_sound {Z₁ : ℚ} (hDF : q.ChecksDF f_cpoly) (h : q.ChecksZ₁col f_cpoly Z₁) :
    Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (Z₁ : ℝ) :=
  StdIVPData.Z₁_le_col_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ hDF h

/-- The `Z₁` clause at either slot (recipe or column), together with the Jacobian clause
`ChecksDF`, bounds the `Z₁` operator norm of the realization. -/
theorem Z₁By_sound (s : Z₁Slot) {Z₁ : ℚ} (hDF : q.ChecksDF f_cpoly)
    (h : q.ChecksZ₁By f_cpoly s Z₁) :
    Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (Z₁ : ℝ) :=
  match s, h with
  | .recipe, h => q.Z₁_sound hν f_cpoly x₀ hDF h
  | .column, h => q.Z₁col_sound hν f_cpoly x₀ hDF h

/-! #### The all-generated face: the override face with every slot from its check -/

/-- **Taylor family face, slot-choice form**: one `decide +kernel` discharges
`h : C.ChecksBy s₀ S s₁ q …` (no `ν`); the `Z₀` slot is the exact columns or the grid at
denominator `S`, the `Z₁` slot is the recipe or the exact column sums. -/
theorem certified_of_checksBy (s₀ : Z₀Slot) (S : ℕ) (s₁ : Z₁Slot) (x₀_q : Fin L → ℚ)
    (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) (C : TaylorCertQ)
    (h : C.ChecksBy s₀ S s₁ q f_cpoly x₀_q) :
    ∃! xTilde ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      (q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀ xTilde = 0 :=
  q.certified_of_bounds hν f_cpoly x₀ C
    (q.Y₀_sound hν f_cpoly x₀ x₀_q hx₀ h.2.2.1) (q.defectZBy_sound hν s₀ S h.2.1)
    (q.Z₁By_sound hν f_cpoly x₀ s₁ h.1 h.2.2.2.1)
    (q.Z₂_sound hν f_cpoly x₀ h.2.2.2.2.2.1.le h.2.2.2.2.1) h.2.2.2.2.2

/-- Slot-choice source-residual form. -/
theorem certified_ivpCoeffs_of_checksBy (s₀ : Z₀Slot) (S : ℕ) (s₁ : Z₁Slot) (x₀_q : Fin L → ℚ)
    (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) (C : TaylorCertQ)
    (h : C.ChecksBy s₀ S s₁ q f_cpoly x₀_q) :
    ∃! xTilde ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (C.r₀ : ℝ),
      ∀ l n, IVP.ivpCoeffs (IVP.banachField f_cpoly) x₀ xTilde l n = 0 :=
  q.certified_ivpCoeffs_of_bounds hν f_cpoly x₀ C
    (q.Y₀_sound hν f_cpoly x₀ x₀_q hx₀ h.2.2.1) (q.defectZBy_sound hν s₀ S h.2.1)
    (q.Z₁By_sound hν f_cpoly x₀ s₁ h.1 h.2.2.2.1)
    (q.Z₂_sound hν f_cpoly x₀ h.2.2.2.2.2.1.le h.2.2.2.2.1) h.2.2.2.2.2

end Faces

end StdIVPDataQ

end IVP
