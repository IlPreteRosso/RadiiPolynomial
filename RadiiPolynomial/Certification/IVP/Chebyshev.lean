import RadiiPolynomial.Applications.IVP.Chebyshev.Polynomial
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.Rational.Grid
import RadiiPolynomial.Certification.RadiiPolynomialQ

/-!
# Chebyshev certification adapter

Exact-ℚ clauses for the standard Chebyshev IVP bundle `ChebyshevIVP.StdChebIVPData` and a
`CompPoly` system, with their soundness at every real realization. The module imports the
Chebyshev discretization through its narrow owner `Applications/IVP/Chebyshev/Polynomial` and
the exact-rational certification layer; no reusable module below `Certification` imports it.

## Contents

1. `ChebyshevIVP.actionQ`, `radiusF`, `MY`, `Y₀Q`, `SnormQ` — the computable ℚ quantities of
   the residual and of the symmetrized candidate.
2. Bridges on a bundle `d : StdChebIVPData ν L N`: `d.defect_finBlockNorm_le_of_Q` (exact block
   norm of the family-neutral `defectCols`), `d.Z₀_sound` (any `DefectBy` slot),
   `d.Y₀_le_of_Q`.
3. `Z₂`: the `TC` column norms `TCcolQ`, `TCcolNormQ`, `TCblockGen`, `TCnormGen`; the operator
   bound `d.TC_norm_le_gen`, the exact `‖S(āᵢ)‖` (`d.norm_symmetrize_abar_eq`) and
   `d.Z₂_le_of_Q`.
4. `Z₁`: the leakage columns `jacColQ`, `DcolAux`, `colNormAux`, `chebColNormQ`, `Mfar`,
   `rowA0Q`, `epsBlockGen`, `epsGen`; the hypotheses `d.Z₁_hneg`, `d.Z₁_htail`, `d.Z₁_hDφ`,
   `d.Z₁_hfin` of `chebyshev_Z₁_le_relaxed`, `d.Z₁_le_of_Q`, and its semi-major sibling
   `d.Z₁_le_semiMajor_of_Q` (tail factor `(ν⁻¹ + ν)/(2(N+1))`, `chebyshev_Z₁_le_semiMajor`).
5. The family face: `ChebCertQ` (the certificate numbers and override slots),
   `ChebCertQ.Checks` (all obligations as one ℚ-decidable conjunction),
   `d.certified_of_Y₀Z₀` and `d.certified_of_checks`.
6. The kernel-scale checker: the clipped Laurent interpreter `evalFast` (`evalFast_eq`), the
   sparse leakage columns `colNormS` (`colNormS_eq`), the closed-form `TC` rows `TCnormF`
   (`TCnormF_eq`), the obligations `ChebCertQ.ChecksK` (with a `DefectBy` slot for `Z₀` and
   per-block leakage data `E`), `checks_of_checksK`, `d.Z₁_le_of_checksK`, its semi-major
   sibling `d.Z₁_le_semiMajor_of_checksK` and the family face `d.certified_of_checksK`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

/-! ### ℚ layer (ν-free; the definitions of this section are computable)

The formulas take arbitrary rational data. The readings of `Y₀Q` and `SnormQ` as exact norms
hold at the stored data of a bundle `d : StdChebIVPData ν L N` (`ν_q = d.ν_q`, `p` the cast of
`p_q`): for `Y₀Q` inside the proof of `StdChebIVPData.Y₀_le_of_Q`, for `SnormQ` as
`StdChebIVPData.norm_symmetrize_abar_eq`. -/

section QLayer

variable {L : ℕ}

/-- Exact action of the stored Chebyshev preconditioner (tail `1/(2n)`). -/
def actionQ (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (c : Fin L → ℕ → ℚ) (l : Fin L)
    (n : ℕ) : ℚ :=
  if n ≤ N then ∑ j : Fin L, ∑ k : Fin (N + 1), (A_col l j (k : ℕ)).getD n 0 * c j k
  else c l n / (2 * n)

/-- Laurent support radius of the nonlinearity on the stored arrays. -/
def radiusF (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) : ℕ :=
  Finset.univ.sup fun l => (f l).laurentRadius (fun i => (arrs i).size)

/-- Support index of the residual `F(ā)` (and of `G(ā)`). -/
def MY (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (N : ℕ) : ℕ :=
  max N (radiusF f arrs + 1)

/-- Exact ℚ value of `‖G(ā)_l‖`. -/
def Y₀Q (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) (l : Fin L) : ℚ :=
  ∑ n : Fin (MY f abar_Q N + 1),
    |actionQ N A_col (compPolyIvpCoeffsQ f abar_Q p_q) l n| * ν_q ^ (n : ℕ)

/-- Exact ℚ value of `‖S(ā_i)‖` (bilateral, support `|k| ≤ N`). -/
def SnormQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (i : Fin L) : ℚ :=
  (∑ n : Fin (N + 1), |(abar_Q i).getD n 0| * ν_q ^ (n : ℕ)) +
    ∑ n : Fin N, |(abar_Q i).getD ((n : ℕ) + 1) 0| * ν_q ^ ((n : ℕ) + 1)

end QLayer

namespace StdChebIVPData

/-! ### Bridges -/

section Bridges

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

theorem ν_q_pos (d : StdChebIVPData ν L N) : 0 < d.ν_q := by
  have h : (0 : ℝ) < (d.ν_q : ℝ) := d.hν ▸ ν.2
  exact_mod_cast h

theorem one_le_ν_q (d : StdChebIVPData ν L N) : 1 ≤ d.ν_q := by
  have h : (1 : ℝ) ≤ (d.ν_q : ℝ) := d.hν ▸ (Fact.out : (1 : ℝ) ≤ ν)
  exact_mod_cast h

theorem abar_Q_getD_eq_zero (d : StdChebIVPData ν L N) (i : Fin L) (k : ℕ) (hk : N < k) :
    (d.abar_Q i).getD k 0 = 0 := by
  simp [Array.getD, show ¬ k < (d.abar_Q i).size by rw [d.habar_size i]; omega]

/-! #### Z₀ -/

/-- `Z₀` from the exact ℚ block norm of the family-neutral defect columns. -/
theorem defect_finBlockNorm_le_of_Q (d : StdChebIVPData ν L N) {Z₀ : ℚ}
    (hle : finiteBlockMatrixNormQ L N (defectCols d.A_col d.DF_col) d.ν_q ≤ Z₀) :
    finiteBlockMatrixNorm ν d.defect.finBlock ≤ (Z₀ : ℝ) :=
  finiteBlockMatrixNorm_defect_le_of_Q d.approxInverse d.approxDeriv d.A_col d.DF_col d.ν_q
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) d.hν hle

/-- Operator-level `Z₀` for a Chebyshev bundle from the family-neutral clause. -/
theorem Z₀_sound (d : ChebyshevIVP.StdChebIVPData ν L N) (s : Z₀Slot) (S : ℕ) {Z₀ : ℚ}
    (h : DefectBy L N d.A_col d.DF_col d.ν_q s S Z₀) :
    finiteBlockMatrixNorm ν d.defect.finBlock ≤ (Z₀ : ℝ) :=
  finiteBlockMatrixNorm_defect_le_of_Q d.approxInverse d.approxDeriv d.A_col d.DF_col d.ν_q
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) d.hν (defectBy_sound s S h)

/-! #### Y₀ -/

theorem action_eq_actionQ (d : StdChebIVPData ν L N) (c : SystemCoeff L)
    (cq : Fin L → ℕ → ℚ) (hc : ∀ l n, c l n = (cq l n : ℝ)) (l : Fin L) (n : ℕ) :
    d.approxInverse.action c l n = (actionQ N d.A_col cq l n : ℝ) := by
  rw [d.approxInverse.action_eq_blockActionQ (fun l j k => d.A_col l j (k : ℕ))
    (fun _ n => 1 / (2 * (n : ℚ))) (fun l j k i => rfl)
    (fun l n hn => by rw [d.htail_diag_inv l n hn]; push_cast; ring) c cq hc l n]
  unfold blockActionQ actionQ
  split_ifs <;> first | rfl | (push_cast; ring)

theorem ivpCoeffsQ_support (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p_q : Fin L → ℚ) (l : Fin L) (n : ℕ) (hn : MY f d.abar_Q N < n) :
    compPolyIvpCoeffsQ f d.abar_Q p_q l n = 0 := by
  have hsb : (f l).laurentRadius (fun i => (d.abar_Q i).size) ≤ radiusF f d.abar_Q :=
    Finset.le_sup (f := fun l => (f l).laurentRadius (fun i => (d.abar_Q i).size))
      (Finset.mem_univ l)
  unfold MY at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [compPolyIvpCoeffsQ]
  rw [abar_Q_getD_eq_zero d l (m + 1) (by omega),
    CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by simp; omega),
    CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by simp; omega)]
  ring

/-- `Y₀` from one exact-ℚ check per component. -/
theorem Y₀_le_of_Q (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) {Y₀ : ℚ}
    (hle : ∀ l, Y₀Q N d.A_col d.abar_Q d.ν_q f p_q l ≤ Y₀) :
    ‖d.G (banachField f) p d.abar‖ ≤ (Y₀ : ℝ) := by
  have hpf : p = fun j => (p_q j : ℝ) := funext hp
  subst hpf
  set M := MY f d.abar_Q N
  have hF : ∀ l n, chebyshevIvpCoeffs (banachField f) (fun j => (p_q j : ℝ)) d.abar l n =
      (compPolyIvpCoeffsQ f d.abar_Q p_q l n : ℝ) :=
    fun l n => d.ivpCoeffs_abar_eq_cast_of_compPoly f p_q l n
  have hY0 : (0 : ℝ) ≤ (Y₀ : ℝ) := by
    have : 0 ≤ Y₀Q N d.A_col d.abar_Q d.ν_q f p_q 0 := Finset.sum_nonneg fun n _ =>
      mul_nonneg (abs_nonneg _) (pow_nonneg (ν_q_pos d).le _)
    exact_mod_cast this.trans (hle 0)
  refine (pi_norm_le_iff_of_nonneg hY0).mpr fun l => ?_
  rw [lpOneAlg.norm_eq_natFinSum_of_finSupp
    (d.G (banachField f) (fun j => (p_q j : ℝ)) d.abar l) M
    (fun m => rfl)
    (fun n hn => by
      show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n)
        (d.approxInverse.action
          (chebyshevIvpCoeffs (banachField f) (fun j => (p_q j : ℝ)) d.abar) l n)‖ = 0
      rw [SystemBlockDiagData.action_tail _ _ _ _ (show N < n by
          simp only [M, MY] at hn; omega),
        hF, ivpCoeffsQ_support d f p_q l n hn]
      simp)]
  refine le_of_eq_of_le ?_ (by exact_mod_cast hle l :
    ((Y₀Q N d.A_col d.abar_Q d.ν_q f p_q l : ℚ) : ℝ) ≤ Y₀)
  unfold Y₀Q
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑(n : ℕ))
    (d.approxInverse.action
      (chebyshevIvpCoeffs (banachField f) (fun j => (p_q j : ℝ)) d.abar) l n)‖ = _
  rw [ScaledRealZ.norm_equiv_apply, action_eq_actionQ d _ _ hF l n, d.hν]
  simp

end Bridges

end StdChebIVPData

/-! ### Z₂: the `TC` column norms (generic in `L`, `N`) -/

section QLayerTC

variable {L : ℕ}

/-- Column `mn` of the raw `c`-rows (`c_{k+2} − c_k`) on the basis vector `e_mn`. -/
def FCe (mn : ℕ) : ℕ → ℚ
  | 0 => 0
  | (k + 1) => (if k + 2 = mn then 1 else 0) - (if k = mn then 1 else 0)

/-- Row `n` of column `mn` of the block `(l, j)` of the preconditioned `c`-part. -/
def TCcolQ (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) : ℚ :=
  ∑ k : Fin (N + 1), (A_col l j (k : ℕ)).getD n 0 * FCe mn k

/-- Exact ℚ weighted norm of that column. -/
def TCcolNormQ (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L)
    (mn : ℕ) : ℚ :=
  ∑ n : Fin (N + 1), |TCcolQ N A_col l j mn n| * ν_q ^ (n : ℕ)

/-- Generated block constant: the largest weighted column ratio (columns `≥ N+2` vanish). -/
def TCblockGen (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun mn : Fin (N + 2) =>
    TCcolNormQ N A_col ν_q l j mn / ν_q ^ (mn : ℕ)

/-- Generated operator constant of the full `TC` (block + `ν/(N+1)` tail on the diagonal). -/
def TCnormGen [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l : Fin L =>
    ∑ j : Fin L, (TCblockGen N A_col ν_q l j + if l = j then ν_q / ((N : ℚ) + 1) else 0)

theorem TCcolQ_eq_zero_of_ge (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L)
    {mn : ℕ} (hmn : N + 2 ≤ mn) (n : Fin (N + 1)) : TCcolQ N A_col l j mn n = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := k.isLt
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
  · rw [hk0, show FCe mn 0 = 0 from rfl, mul_zero]
  · obtain ⟨kv, hkv⟩ : ∃ kv, (k : ℕ) = kv + 1 := ⟨(k : ℕ) - 1, by omega⟩
    rw [hkv, show FCe mn (kv + 1)
        = (if kv + 2 = mn then 1 else 0) - (if kv = mn then 1 else 0) from rfl,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    ring

theorem TCblockGen_nonneg (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) {ν_q : ℚ}
    (hν : 0 < ν_q) (l j : Fin L) : 0 ≤ TCblockGen N A_col ν_q l j :=
  (div_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hν.le _))
    (pow_nonneg hν.le _)).trans
    (Finset.le_sup' (fun mn : Fin (N + 2) => TCcolNormQ N A_col ν_q l j mn / ν_q ^ (mn : ℕ))
      (Finset.mem_univ 0))

theorem TCcolNormQ_le (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) {ν_q : ℚ}
    (hν : 0 < ν_q) (l j : Fin L) (mn : ℕ) :
    TCcolNormQ N A_col ν_q l j mn ≤ TCblockGen N A_col ν_q l j * ν_q ^ mn := by
  rcases lt_or_ge mn (N + 2) with hmn | hmn
  · have h := Finset.le_sup' (fun mn : Fin (N + 2) =>
      TCcolNormQ N A_col ν_q l j mn / ν_q ^ (mn : ℕ)) (Finset.mem_univ ⟨mn, hmn⟩)
    exact (div_le_iff₀ (pow_pos hν _)).mp h
  · have hz : TCcolNormQ N A_col ν_q l j mn = 0 := Finset.sum_eq_zero fun n _ => by
      rw [TCcolQ_eq_zero_of_ge N A_col l j hmn n, abs_zero, zero_mul]
    rw [hz]
    exact mul_nonneg (TCblockGen_nonneg N A_col hν l j) (pow_nonneg hν.le _)

theorem TCnormGen_nonneg [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) {ν_q : ℚ}
    (hν : 0 < ν_q) : 0 ≤ TCnormGen N A_col ν_q :=
  (Finset.sum_nonneg fun j _ => add_nonneg (TCblockGen_nonneg N A_col hν 0 j)
    (by split_ifs <;> positivity)).trans
    (Finset.le_sup' (fun l : Fin L =>
      ∑ j : Fin L, (TCblockGen N A_col ν_q l j + if l = j then ν_q / ((N : ℚ) + 1) else 0))
      (Finset.mem_univ 0))

end QLayerTC

section RowHelpers

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The raw `c`-rows vanish on a direction with no nonnegative modes. -/
theorem FCseq_eq_zero_of_nat (v : l1Chebyshev ν) (hv : ∀ n : ℕ, l1Chebyshev.toSeq v n = 0)
    (k : ℕ) : FCseq v k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
      show l1Chebyshev.toSeq v (↑(k + 2) : ℤ) - l1Chebyshev.toSeq v (↑k : ℤ) = 0
      rw [hv, hv, sub_zero]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The raw `a`-rows vanish on a direction with no nonnegative modes. -/
theorem FAseq_eq_zero_of_nat (v : l1Chebyshev ν) (hv : ∀ n : ℕ, l1Chebyshev.toSeq v n = 0)
    (k : ℕ) : FAseq v k = 0 := by
  cases k with
  | zero =>
      show -(l1Chebyshev.toSeq v 0) - 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) *
        l1Chebyshev.toSeq v (↑(n + 1) : ℤ) = 0
      simp only [show l1Chebyshev.toSeq v 0 = 0 from hv 0, hv, mul_zero, tsum_zero]
      ring
  | succ k =>
      show 2 * ((k : ℝ) + 1) * l1Chebyshev.toSeq v (↑(k + 1) : ℤ) = 0
      rw [hv, mul_zero]

theorem toSeq_pi_single_nat {L : ℕ} (j l : Fin L) (m : ℤ) (n : ℕ) :
    l1Chebyshev.toSeq ((Pi.single j (l1Chebyshev.single (ν := ν) m 1) :
      Fin L → l1Chebyshev ν) l) n = if l = j ∧ (n : ℤ) = m then 1 else 0 := by
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same, l1Chebyshev.toSeq_single]
    simp
  · rw [Pi.single_eq_of_ne hl, l1Chebyshev.toSeq_zero, ite_eq_right (fun h => hl h.1)]

theorem toSeq_pi_single_negSucc_nat {L : ℕ} (j l : Fin L) (m : ℕ) (n : ℕ) :
    l1Chebyshev.toSeq ((Pi.single j (l1Chebyshev.single (ν := ν) (Int.negSucc m) 1) :
      Fin L → l1Chebyshev ν) l) n = 0 := by
  rw [toSeq_pi_single_nat, ite_eq_right (fun h => by have := h.2; omega)]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem FCseq_single_nat (mn k : ℕ) :
    FCseq (ν := ν) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) k = (FCe mn k : ℝ) := by
  cases k with
  | zero => simp [FCseq, FCe]
  | succ k' =>
    show l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑(k' + 2) : ℤ)
          - l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑k' : ℤ) = _
    rw [l1Chebyshev.toSeq_single, l1Chebyshev.toSeq_single,
      show FCe mn (k' + 1)
        = (if k' + 2 = mn then 1 else 0) - (if k' = mn then 1 else 0) from rfl]
    simp only [Nat.cast_inj, Rat.cast_sub, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one,
      Rat.cast_zero]

end RowHelpers

section BridgesTCOps

/-- Componentwise block decomposition of a continuous linear map between finite products (the
component form of Mathlib's `ContinuousLinearMap.sum_comp_single`); used on
`XCheb ν L = Fin L → l1Chebyshev ν`. -/
theorem clm_apply_eq_sum {R : Type*} [Semiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
    [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
    (T : (ι → X) →L[R] (ι → Y)) (w : ι → X) (l : ι) :
    T w l = ∑ j, T (Pi.single j (w j)) l := by
  rw [← Finset.sum_apply, ← ContinuousLinearMap.sum_comp_single R (fun _ => X) T w]
  rfl

end BridgesTCOps

namespace StdChebIVPData

section BridgesTC

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

/-- Block `(l, j)` of `TC`, as an operator on one component. -/
noncomputable def TClj (d : StdChebIVPData ν L N) (l j : Fin L) :
    l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  (ContinuousLinearMap.proj l).comp
    (d.TC.comp (ContinuousLinearMap.single ℝ (fun _ : Fin L => l1Chebyshev ν) j))

theorem TClj_apply (d : StdChebIVPData ν L N) (l j : Fin L) (v : l1Chebyshev ν) :
    TClj d l j v = d.TC (Pi.single j v) l := rfl

theorem TCblock_single_toSeq (d : StdChebIVPData ν L N) (l j : Fin L) (mn : ℕ) (n : ℕ)
    (hn : n ≤ N) :
    l1Chebyshev.toSeq (d.TCblockFun (Pi.single j (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) l)
      (↑n : ℤ) = (TCcolQ N d.A_col l j mn ⟨n, Nat.lt_succ_of_le hn⟩ : ℝ) := by
  rw [d.TCblockFun_toSeq_nat]
  show d.approxInverse.actionFinite (fun j' => FCseq
    ((Pi.single j (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) : XCheb ν L) j')) l n = _
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn,
    Finset.sum_eq_single j (fun j' _ hj' => Finset.sum_eq_zero fun k _ => by
        rw [Pi.single_eq_of_ne hj', FCseq_eq_zero_of_nat 0 (fun n => l1Chebyshev.toSeq_zero _),
          mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
  rw [Pi.single_eq_same, TCcolQ]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FCseq_single_nat]
  rfl

theorem TCblock_single_negSucc_toSeq (d : StdChebIVPData ν L N) (l j : Fin L) (m' : ℕ)
    (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (d.TCblockFun (Pi.single j (l1Chebyshev.single (Int.negSucc m') 1)) l)
      (↑n : ℤ) = 0 := by
  rw [d.TCblockFun_toSeq_nat]
  show d.approxInverse.actionFinite (fun j' => FCseq
    ((Pi.single j (l1Chebyshev.single (Int.negSucc m') 1) : XCheb ν L) j')) l n = _
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
  refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun k _ => ?_
  rw [FCseq_eq_zero_of_nat _ (fun n => toSeq_pi_single_negSucc_nat j j' m' n), mul_zero]

theorem TCblock_single_norm_le (d : StdChebIVPData ν L N) (l j : Fin L) (m : ℤ) :
    ‖d.TCblockFun (Pi.single j (l1Chebyshev.single m 1)) l‖ ≤
      (TCblockGen N d.A_col d.ν_q l j : ℝ) * (ν : ℝ) ^ m.natAbs := by
  have hνq := ν_q_pos d
  rw [lpOneAlg.norm_eq_natFinSum_of_finSupp
    (d.TCblockFun (Pi.single j (l1Chebyshev.single m 1)) l) N
    (fun m => rfl)
    (fun n hn => by
      show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n)
        (d.TCblockSeq (Pi.single j (l1Chebyshev.single m 1)) l n)‖ = 0
      rw [d.TCblockSeq_tail _ _ n hn, FiberTrivialization.equiv_zero, norm_zero])]
  cases m with
  | ofNat mn =>
    have hterm : ∀ n : Fin (N + 1),
        ‖(d.TCblockFun (Pi.single j (l1Chebyshev.single (Int.ofNat mn) 1)) l)
          ((↑(n : ℕ)) : ℤ)‖ = ((|TCcolQ N d.A_col l j mn n| * d.ν_q ^ (n : ℕ) : ℚ) : ℝ) := by
      intro n
      rw [l1Chebyshev.norm_fiber]
      rw [show l1Chebyshev.toSeq
          (d.TCblockFun (Pi.single j (l1Chebyshev.single (Int.ofNat mn) 1)) l)
          (↑(n : ℕ) : ℤ) = ((TCcolQ N d.A_col l j mn ⟨(n : ℕ), n.isLt⟩ : ℚ) : ℝ) from
        TCblock_single_toSeq d l j mn (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
      rw [d.hν, Fin.eta]
      push_cast
      simp
    rw [Finset.sum_congr rfl fun n _ => hterm n]
    have h := TCcolNormQ_le N d.A_col hνq l j mn
    have h' : ((TCcolNormQ N d.A_col d.ν_q l j mn : ℚ) : ℝ) ≤
        ((TCblockGen N d.A_col d.ν_q l j * d.ν_q ^ mn : ℚ) : ℝ) := by exact_mod_cast h
    rw [TCcolNormQ] at h'
    push_cast at h' ⊢
    refine h'.trans (le_of_eq ?_)
    rw [d.hν]
    rfl
  | negSucc m' =>
    rw [Finset.sum_eq_zero fun n _ => by
      rw [l1Chebyshev.norm_fiber, TCblock_single_negSucc_toSeq d l j m' (n : ℕ)
        (Nat.lt_succ_iff.mp n.isLt), abs_zero, zero_mul]]
    exact mul_nonneg (by exact_mod_cast TCblockGen_nonneg N d.A_col hνq l j)
      (pow_nonneg ν.2.le _)

theorem TClj_col_le (d : StdChebIVPData ν L N) (l j : Fin L) (m : ℤ) :
    ‖TClj d l j (l1Chebyshev.single m 1)‖ ≤
      ((TCblockGen N d.A_col d.ν_q l j + if l = j then d.ν_q / ((N : ℚ) + 1) else 0 : ℚ) : ℝ)
        * (ν : ℝ) ^ m.natAbs := by
  rw [TClj_apply]
  change ‖d.TCblockFun (Pi.single j (l1Chebyshev.single m 1)) l +
    TCtailElem N ((Pi.single j (l1Chebyshev.single m 1) : XCheb ν L) l)‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  have hb := TCblock_single_norm_le d l j m
  have ht := TCtailElem_norm_le_tail N ((Pi.single j (l1Chebyshev.single m 1) : XCheb ν L) l)
  have hpow : (0 : ℝ) ≤ (ν : ℝ) ^ m.natAbs := pow_nonneg ν.2.le _
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same, ite_eq_left rfl]
    rw [Pi.single_eq_same, l1Chebyshev.norm_single, abs_one, one_mul] at ht
    push_cast
    rw [← d.hν, add_mul]
    exact add_le_add hb ht
  · rw [Pi.single_eq_of_ne hl, ite_eq_right hl]
    rw [Pi.single_eq_of_ne hl, norm_zero, mul_zero] at ht
    simp only [add_zero]
    linarith

/-- Generic `TC` operator bound from the generated block constants. -/
theorem TC_norm_le_gen (d : StdChebIVPData ν L N) (w : XCheb ν L) :
    ‖d.TC w‖ ≤ (TCnormGen N d.A_col d.ν_q : ℝ) * ‖w‖ := by
  have hνq := ν_q_pos d
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by exact_mod_cast TCnormGen_nonneg N d.A_col hνq)
    (norm_nonneg w))).mpr fun l => ?_
  rw [clm_apply_eq_sum d.TC w l]
  refine (norm_sum_le _ _).trans ?_
  have hc0 : ∀ j, (0 : ℝ) ≤ ((TCblockGen N d.A_col d.ν_q l j +
      if l = j then d.ν_q / ((N : ℚ) + 1) else 0 : ℚ) : ℝ) := fun j => by
    have : 0 ≤ TCblockGen N d.A_col d.ν_q l j +
        (if l = j then d.ν_q / ((N : ℚ) + 1) else 0) :=
      add_nonneg (TCblockGen_nonneg N d.A_col hνq l j) (by split_ifs <;> positivity)
    exact_mod_cast this
  have hj : ∀ j, ‖d.TC (Pi.single j (w j)) l‖ ≤ ((TCblockGen N d.A_col d.ν_q l j +
      if l = j then d.ν_q / ((N : ℚ) + 1) else 0 : ℚ) : ℝ) * ‖w‖ := fun j => by
    rw [← TClj_apply]
    exact (l1Chebyshev.norm_le_of_cols (TClj d l j) (TClj_col_le d l j) (w j)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (hc0 j))
  refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
  have hsup : (∑ j : Fin L, (TCblockGen N d.A_col d.ν_q l j +
      if l = j then d.ν_q / ((N : ℚ) + 1) else 0)) ≤ TCnormGen N d.A_col d.ν_q :=
    Finset.le_sup' (fun l : Fin L =>
      ∑ j : Fin L, (TCblockGen N d.A_col d.ν_q l j + if l = j then d.ν_q / ((N : ℚ) + 1) else 0))
      (Finset.mem_univ l)
  have h2 := (Rat.cast_le (K := ℝ)).mpr hsup
  rw [Rat.cast_sum] at h2
  exact h2

/-- `‖S(ā_i)‖` is the exact rational `SnormQ`. -/
theorem norm_symmetrize_abar_eq (d : StdChebIVPData ν L N) (i : Fin L) :
    ‖l1Chebyshev.symmetrize (d.abar i)‖ = (SnormQ N d.abar_Q d.ν_q i : ℝ) := by
  have hS : ∀ k : ℤ, l1Chebyshev.toSeq (l1Chebyshev.symmetrize (d.abar i)) k =
      ((d.abar_Q i).getD k.natAbs 0 : ℝ) := fun k => by
    rw [l1Chebyshev.symmetrize_toSeq, d.abar_toSeq_eq]
  rw [lpOneAlg.norm_eq_bilatFinSum _ N
    (fun n hn => by
      rw [l1Chebyshev.norm_fiber, hS, abar_Q_getD_eq_zero d i _ (by simpa using hn)]
      simp)
    (fun n hn => by
      rw [l1Chebyshev.norm_fiber, hS, abar_Q_getD_eq_zero d i _ (by
        simp [Int.natAbs_negSucc]; omega)]
      simp)]
  unfold SnormQ
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [l1Chebyshev.norm_fiber, hS, d.hν]
    simp
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [l1Chebyshev.norm_fiber, hS, d.hν,
      show (Int.negSucc (n : ℕ)).natAbs = (n : ℕ) + 1 from rfl]

/-- `Z₂` from ℚ checks with two override slots: `C` (≥ the generated `TC` constant) and `B`
(≥ twice the syntactic derivative-Lipschitz constant at the radii `R + 2 r₀`, where `R`
overrides the exact `‖S(ā)‖`). -/
theorem Z₂_le_of_Q (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    {R : Fin L → ℚ} (hR : ∀ i, SnormQ N d.abar_Q d.ν_q i ≤ R i)
    {r₀ C B Z₂ : ℚ} (hr₀ : 0 ≤ r₀)
    (hC : TCnormGen N d.A_col d.ν_q ≤ C)
    (hB : ∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l) (fun i => R i + 2 * r₀) ≤ B)
    (hZ₂ : C * B ≤ Z₂) :
    ∀ c ∈ Metric.closedBall d.abar (r₀ : ℝ),
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ (Z₂ : ℝ) * (r₀ : ℝ) := by
  intro c hc
  have hνq := ν_q_pos d
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast (TCnormGen_nonneg N d.A_col hνq).trans hC
  have hr : (0 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have hRi : ∀ i, ‖l1Chebyshev.symmetrize (d.abar i)‖ ≤ (R i : ℝ) := fun i => by
    rw [norm_symmetrize_abar_eq]; exact_mod_cast hR i
  have hball : ∀ c ∈ Metric.closedBall d.abar (r₀ : ℝ), ∀ i,
      max ‖l1Chebyshev.symmetrize (c i)‖ ‖l1Chebyshev.symmetrize (d.abar i)‖ ≤
        (R i : ℝ) + 2 * (r₀ : ℝ) := fun c hc i => by
    have hd : ‖c - d.abar‖ ≤ (r₀ : ℝ) := by rw [← dist_eq_norm]; exact hc
    have hci : ‖c i - d.abar i‖ ≤ ‖c - d.abar‖ := norm_le_pi_norm (c - d.abar) i
    have hsub : l1Chebyshev.symmetrize (c i) - l1Chebyshev.symmetrize (d.abar i) =
        l1Chebyshev.symmetrize (c i - d.abar i) := by
      simp only [← l1Chebyshev.symmetrize_CLM_apply, map_sub]
    have h2 := l1Chebyshev.symmetrize_norm_le (c i - d.abar i)
    have h3 := norm_le_insert' (l1Chebyshev.symmetrize (c i))
      (l1Chebyshev.symmetrize (d.abar i))
    rw [hsub] at h3
    have := hRi i
    refine max_le ?_ ?_ <;> nlinarith
  have hB' : ∀ c ∈ Metric.closedBall d.abar (r₀ : ℝ), ∀ l,
      2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
        (fun i => max ‖l1Chebyshev.symmetrize (c i)‖ ‖l1Chebyshev.symmetrize (d.abar i)‖)
        ≤ (B : ℝ) := fun c hc l => by
    have hm := CompPoly.Chebyshev.derivativeLipschitzBound_mono (f l)
      (fun i => le_max_of_le_left (norm_nonneg _)) (hball c hc)
    have hq : ((2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
        (fun i => R i + 2 * r₀) : ℚ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB l
    push_cast [CompPoly.Chebyshev.derivativeLipschitzBound_ratCast] at hq
    linarith
  have h := d.Z₂_le_of_compPoly_max f p hC0 hr
    (fun w => (TC_norm_le_gen d w).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (norm_nonneg w))) hB' c hc
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hr)
  exact_mod_cast hZ₂

end BridgesTC

end StdChebIVPData

/-! ### Z₁: the ε-leakage columns (generic in `L`) -/

section QLayerZ1

variable {L : ℕ}

/-- Exact Jacobian column `mn` of input component `j` (all output components, rows `≤ N`),
precomputed once per column. -/
def jacColQ (N : ℕ) (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (j : Fin L) (mn : ℕ) :
    Array (Array ℚ) :=
  Array.ofFn fun j' : Fin L => Array.ofFn fun k : Fin (N + 1) =>
    compPolyDFQ f arrs j' j (k : ℕ) mn

/-- Row `n` of column `mn` of block `(l, j)` of `composedApprox − DG(ā)`, from a precomputed
Jacobian column `jc`. -/
def DcolAux (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (jc : Array (Array ℚ)) (n : Fin (N + 1)) : ℚ :=
  ((if l = j ∧ (n : ℕ) = mn then 1 else 0) -
    (if h : mn ≤ N then
      blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j n
        ⟨mn, Nat.lt_succ_of_le h⟩ else 0)) -
    ∑ j' : Fin L, ∑ k : Fin (N + 1), (A_col l j' (k : ℕ)).getD n 0 *
      (jc.getD j' #[]).getD k 0

def colNormAux (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L)
    (mn : ℕ) (jc : Array (Array ℚ)) : ℚ :=
  ∑ n : Fin (N + 1), |DcolAux N A_col DF_col l j mn jc n| * ν_q ^ (n : ℕ)

/-- Exact ℚ weighted finite-row norm of column `mn` of block `(l, j)` of the `Z₁` operator, at
the stored data of a bundle (rows: `StdChebIVPData.Tlj_single_toSeq`; used in
`StdChebIVPData.Tlj_col_le`). -/
def chebColNormQ (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ)
    (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) : ℚ :=
  colNormAux N A_col DF_col ν_q l j mn (jacColQ N f abar_Q j mn)

/-- Far-column cutoff: beyond it only the row-0 alternating functional survives. -/
def Mfar (N : ℕ) (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) : ℕ :=
  N + 1 + Finset.univ.sup fun q : Fin L × Fin L =>
    ((f q.1).pderiv q.2).laurentRadius (fun i => (arrs i).size)

/-- The common norm of every far column of block `(l, j)`. The factor `2` is `|−2 · (−1)^mn|`,
the coefficient of the row-0 boundary functional in a far Jacobian column (`compPolyDFQ_far`). -/
def rowA0Q (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L) : ℚ :=
  2 * ∑ n : Fin (N + 1), |(A_col l j 0).getD n 0| * ν_q ^ (n : ℕ)

/-- Generated leakage constant of block `(l, j)`. -/
def epsBlockGen (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ)
    (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) : ℚ :=
  max (Finset.univ.sup' Finset.univ_nonempty fun mn : Fin (Mfar N f abar_Q + 1) =>
      chebColNormQ N A_col DF_col abar_Q ν_q f l j mn / ν_q ^ (mn : ℕ))
    (rowA0Q N A_col ν_q l j / ν_q ^ (Mfar N f abar_Q + 1))

/-- Generated leakage constant `ε = max_l Σ_j ε_{lj}`. -/
def epsGen [NeZero L] (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (f : Fin L → CompPoly L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l : Fin L =>
    ∑ j : Fin L, epsBlockGen N A_col DF_col abar_Q ν_q f l j

theorem DcolAux_jac (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) :
    DcolAux N A_col DF_col l j mn (jacColQ N f arrs j mn) n =
      ((if l = j ∧ (n : ℕ) = mn then 1 else 0) -
        (if h : mn ≤ N then
          blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ))
            l j n ⟨mn, Nat.lt_succ_of_le h⟩ else 0)) -
        ∑ j' : Fin L, ∑ k : Fin (N + 1), (A_col l j' (k : ℕ)).getD n 0 *
          compPolyDFQ f arrs j' j (k : ℕ) mn := by
  unfold DcolAux jacColQ
  simp only [getD_ofFn_fin]

/-- Beyond `Mfar`, the exact Jacobian column is the row-0 boundary functional only. -/
theorem compPolyDFQ_far (N : ℕ) (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ)
    {mn : ℕ} (hmn : Mfar N f arrs < mn) (j' j : Fin L) (k : ℕ) (hk : k ≤ N) :
    compPolyDFQ f arrs j' j k mn = if k = 0 ∧ j' = j then -2 * (-1 : ℚ) ^ mn else 0 := by
  have hR : ((f j').pderiv j).laurentRadius (fun i => (arrs i).size) ≤
      Finset.univ.sup fun q : Fin L × Fin L =>
        ((f q.1).pderiv q.2).laurentRadius (fun i => (arrs i).size) :=
    Finset.le_sup (f := fun q : Fin L × Fin L =>
      ((f q.1).pderiv q.2).laurentRadius (fun i => (arrs i).size)) (Finset.mem_univ (j', j))
  unfold Mfar at hmn
  cases k with
  | zero =>
      simp only [compPolyDFQ, true_and]
      by_cases h : j' = j
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_right (by omega)]
      · rw [ite_eq_right h, ite_eq_right h]
  | succ k =>
      simp only [compPolyDFQ, compPolyDphiQ, show ¬ (k + 1 = 0) by omega, false_and,
        ite_false, show ¬ (mn = 0) by omega]
      rw [ite_eq_right (fun h => by omega),
        CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by omega),
        CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by omega),
        CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by omega),
        CompPoly.evalChebCoeff_eq_zero_of_radius_lt _ _ _ (by omega)]
      ring

theorem chebColNormQ_far (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L)
    {mn : ℕ} (hmn : Mfar N f abar_Q < mn) :
    chebColNormQ N A_col DF_col abar_Q ν_q f l j mn = rowA0Q N A_col ν_q l j := by
  have hN : N < mn := by unfold Mfar at hmn; omega
  unfold chebColNormQ colNormAux rowA0Q
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [DcolAux_jac, ite_eq_right (fun h => by have := n.isLt; omega), dite_eq_right (by omega)]
  have hsum : ∑ j' : Fin L, ∑ k : Fin (N + 1), (A_col l j' (k : ℕ)).getD n 0 *
      compPolyDFQ f abar_Q j' j (k : ℕ) mn =
      (A_col l j 0).getD n 0 * (-2 * (-1 : ℚ) ^ mn) := by
    simp_rw [fun (j' : Fin L) (k : Fin (N + 1)) =>
      compPolyDFQ_far N f abar_Q hmn j' j (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)]
    rw [Finset.sum_eq_single j (fun j' _ hj' => Finset.sum_eq_zero fun k _ => by
        rw [ite_eq_right (fun h => hj' h.2), mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    rw [Finset.sum_eq_single (0 : Fin (N + 1)) (fun k _ hk => by
        rw [ite_eq_right (fun h => hk (Fin.ext h.1)), mul_zero])
      (fun h => absurd (Finset.mem_univ 0) h)]
    simp
  rw [hsum]
  rw [show (0 : ℚ) - 0 - (A_col l j 0).getD n 0 * (-2 * (-1 : ℚ) ^ mn) =
      2 * (-1 : ℚ) ^ mn * (A_col l j 0).getD n 0 by ring]
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    show |(2 : ℚ)| = 2 from by norm_num]
  ring

theorem epsBlockGen_nonneg (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) {ν_q : ℚ} (hν : 0 < ν_q) (f : Fin L → CompPoly L)
    (l j : Fin L) : 0 ≤ epsBlockGen N A_col DF_col abar_Q ν_q f l j :=
  le_max_of_le_right (div_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hν.le _)))
    (pow_nonneg hν.le _))

theorem chebColNormQ_le_eps (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) {ν_q : ℚ} (hν : 1 ≤ ν_q) (f : Fin L → CompPoly L)
    (l j : Fin L) (mn : ℕ) :
    chebColNormQ N A_col DF_col abar_Q ν_q f l j mn ≤
      epsBlockGen N A_col DF_col abar_Q ν_q f l j * ν_q ^ mn := by
  have hν0 : 0 < ν_q := lt_of_lt_of_le one_pos hν
  rcases le_or_gt mn (Mfar N f abar_Q) with hmn | hmn
  · have h := Finset.le_sup' (fun mn : Fin (Mfar N f abar_Q + 1) =>
      chebColNormQ N A_col DF_col abar_Q ν_q f l j mn / ν_q ^ (mn : ℕ))
      (Finset.mem_univ ⟨mn, Nat.lt_succ_of_le hmn⟩)
    exact (div_le_iff₀ (pow_pos hν0 _)).mp (h.trans (le_max_left _ _))
  · rw [chebColNormQ_far N A_col DF_col abar_Q ν_q f l j hmn]
    have h := (div_le_iff₀ (pow_pos hν0 _)).mp
      (le_max_right _ _ : rowA0Q N A_col ν_q l j / ν_q ^ (Mfar N f abar_Q + 1) ≤
        epsBlockGen N A_col DF_col abar_Q ν_q f l j)
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν (by omega))
      (epsBlockGen_nonneg N A_col DF_col abar_Q hν0 f l j))

end QLayerZ1

namespace StdChebIVPData

section BridgesZ1

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

theorem composed_toSeq_nat (d : StdChebIVPData ν L N) (h : XCheb ν L) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (d.composedApproxCLM h l) (↑n : ℤ)
      = l1Chebyshev.toSeq (h l) (↑n : ℤ)
        - (defectOfBlockDiagOp d.approxInverse d.approxDeriv).actionFinite
            (toCoeffCheb h) l n :=
  composedApproxCheb_toSeq_natCast _ h l n

theorem composed_toSeq_neg (d : StdChebIVPData ν L N) (h : XCheb ν L) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (d.composedApproxCLM h l) (Int.negSucc m)
      = l1Chebyshev.toSeq (h l) (Int.negSucc m) :=
  composedApproxCheb_toSeq_negSucc _ h l m

theorem fderiv_toSeq (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (h : XCheb ν L) (l : Fin L) (k : ℤ) :
    l1Chebyshev.toSeq ((fderiv ℝ (d.G (banachField f) p) d.abar h) l) k
      = l1Chebyshev.toSeq (d.TAfun h l) k
        + (l1Chebyshev.toSeq (d.TCblockFun (compPolyDerivative f d.abar h) l) k
          + l1Chebyshev.toSeq (TCtailElem N (compPolyDerivative f d.abar h l)) k) := by
  rw [d.fderiv_G_of_compPoly f p]
  show l1Chebyshev.toSeq (d.TAfun h l
    + (d.TCblockFun (compPolyDerivative f d.abar h) l
      + TCtailElem N (compPolyDerivative f d.abar h l))) k = _
  rw [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_add]

/-- `hneg`: negative modes pass through on both sides. -/
theorem Z₁_hneg (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (h : XCheb ν L) (l : Fin L) (m : ℕ) :
    (((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h) l) (Int.negSucc m)
      = 0 := by
  refine (LinearEquiv.map_eq_zero_iff
    (FiberTrivialization.equiv (E := ScaledRealZ ν) (Int.negSucc m)).symm).mp ?_
  show l1Chebyshev.toSeq
    (d.composedApproxCLM h l - (fderiv ℝ (d.G (banachField f) p) d.abar h) l)
      (Int.negSucc m) = 0
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_neg, fderiv_toSeq]
  rw [show l1Chebyshev.toSeq (d.TAfun h l) (Int.negSucc m)
      = l1Chebyshev.toSeq (h l) (Int.negSucc m) from d.TAfun_toSeq_neg h l m,
    d.TCblockFun_toSeq_neg, TCtailElem_toSeq_neg]
  ring

/-- `htail`: beyond mode `N` the difference is `−shiftDiv(Dφ h)`. -/
theorem Z₁_htail (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (h : XCheb ν L) (l : Fin L) (m : ℕ) (hm : N < m) :
    ‖(((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h) l) (↑m : ℤ)‖
      = ‖(chebyshevShiftDiv (compPolyDerivative f d.abar h l)) (↑m : ℤ)‖ := by
  have hval : l1Chebyshev.toSeq
      (((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h) l) (↑m : ℤ)
      = -(l1Chebyshev.toSeq (chebyshevShiftDiv (compPolyDerivative f d.abar h l)) (↑m : ℤ)) := by
    show l1Chebyshev.toSeq
      (d.composedApproxCLM h l - (fderiv ℝ (d.G (banachField f) p) d.abar h) l) (↑m : ℤ) = _
    rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat, fderiv_toSeq]
    rw [show (defectOfBlockDiagOp d.approxInverse d.approxDeriv).actionFinite
        (toCoeffCheb h) l m = 0 from SystemBlockDiagData.actionFinite_tail _ _ _ _ hm]
    rw [d.TAfun_toSeq_nat, d.TA_action_tail_eq h l m hm,
      d.TCblockFun_toSeq_nat,
      show d.TCblockSeq (compPolyDerivative f d.abar h) l m = 0 from
        d.TCblockSeq_tail _ l m hm,
      TCtailElem_toSeq_nat, ite_eq_left hm]
    ring
  rw [l1Chebyshev.norm_fiber, l1Chebyshev.norm_fiber, hval, abs_neg]

/-- `hDφ`: the derivative bound at the override radii `R ≥ ‖S(ā)‖`. -/
theorem Z₁_hDφ (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    {R : Fin L → ℚ} (hR : ∀ i, SnormQ N d.abar_Q d.ν_q i ≤ R i) {K : ℚ}
    (hK : ∀ l, CompPoly.Chebyshev.derivativeBound (f l) R ≤ K)
    (h : XCheb ν L) (l : Fin L) :
    ‖compPolyDerivative f d.abar h l‖ ≤ (K : ℝ) * ‖h‖ := by
  have hRi : ∀ i, ‖l1Chebyshev.symmetrize (d.abar i)‖ ≤ (R i : ℝ) := fun i => by
    rw [norm_symmetrize_abar_eq]; exact_mod_cast hR i
  refine (CompPoly.Chebyshev.norm_derivative_apply_le (f l) d.abar (fun i => (R i : ℝ))
    hRi h).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg h))
  rw [← CompPoly.Chebyshev.derivativeBound_ratCast]
  exact_mod_cast hK l

/-- Block `(l, j)` of the `Z₁` operator on one component. -/
noncomputable def Tlj (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (l j : Fin L) : l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  (ContinuousLinearMap.proj l).comp
    ((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin L => l1Chebyshev ν) j))

theorem defect_actionFinite_single (d : StdChebIVPData ν L N) (l j : Fin L) (mn n : ℕ)
    (hn : n ≤ N) :
    (defectOfBlockDiagOp d.approxInverse d.approxDeriv).actionFinite
        (toCoeffCheb (Pi.single j (l1Chebyshev.single (ν := ν) ((mn : ℕ) : ℤ) 1))) l n
      = if h : mn ≤ N then
          ((blockDefectMatQ (fun l m k => d.A_col l m (k : ℕ))
            (fun m j k => d.DF_col m j (k : ℕ)) l j ⟨n, Nat.lt_succ_of_le hn⟩
              ⟨mn, Nat.lt_succ_of_le h⟩ : ℚ) : ℝ) else 0 := by
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
  have hc : ∀ (j' : Fin L) (k : Fin (N + 1)),
      toCoeffCheb (Pi.single j (l1Chebyshev.single (ν := ν) ((mn : ℕ) : ℤ) 1)) j' (k : ℕ) =
        if j' = j ∧ (k : ℕ) = mn then 1 else 0 := fun j' k => by
    show l1Chebyshev.toSeq _ _ = _
    rw [toSeq_pi_single_nat]
    simp only [Nat.cast_inj]
  simp_rw [hc]
  rw [Finset.sum_eq_single j (fun j' _ hj' => Finset.sum_eq_zero fun k _ => by
      rw [ite_eq_right (fun h => hj' h.1), mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp only [true_and]
  split_ifs with hmn
  · rw [Finset.sum_eq_single (⟨mn, Nat.lt_succ_of_le hmn⟩ : Fin (N + 1))
      (fun k _ hk => by rw [ite_eq_right (fun h => hk (Fin.ext h)), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, mul_one]
    have := blockDefectMatQ_correct
      (fun l m => d.A_finBlock l m) (fun m j => d.DF_finBlock m j)
      (fun l m (k : Fin (N + 1)) => d.A_col l m (k : ℕ))
      (fun m j (k : Fin (N + 1)) => d.DF_col m j (k : ℕ))
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) l j ⟨n, Nat.lt_succ_of_le hn⟩
        ⟨mn, Nat.lt_succ_of_le hmn⟩
    exact this
  · exact Finset.sum_eq_zero fun k _ => by
      rw [ite_eq_right (by have := k.isLt; omega), mul_zero]

theorem Tlj_single_toSeq (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (l j : Fin L) (mn n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (Tlj d f p l j (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) (↑n : ℤ)
      = (DcolAux N d.A_col d.DF_col l j mn (jacColQ N f d.abar_Q j mn)
          ⟨n, Nat.lt_succ_of_le hn⟩ : ℝ) := by
  change l1Chebyshev.toSeq
    (d.composedApproxCLM (Pi.single j (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) l -
      fderiv ℝ (d.G (banachField f) p) d.abar
        (Pi.single j (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) l) (n : ℤ) = _
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat,
    d.fderiv_G_single_fin_eq_cast_of_compPoly f p l j ⟨n, Nat.lt_succ_of_le hn⟩ mn,
    defect_actionFinite_single d l j mn n hn, toSeq_pi_single_nat, DcolAux_jac]
  push_cast [apply_dite (fun q : ℚ => (q : ℝ))]
  congr 2
  simp only [Nat.cast_inj, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero]

theorem Tlj_single_negSucc_toSeq (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (l j : Fin L) (m' n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (Tlj d f p l j (l1Chebyshev.single (Int.negSucc m') 1)) (↑n : ℤ) = 0 := by
  set h : XCheb ν L := Pi.single j (l1Chebyshev.single (Int.negSucc m') 1) with hh
  have hz : ∀ j' (k : ℕ), l1Chebyshev.toSeq (h j') k = 0 := fun j' k =>
    toSeq_pi_single_negSucc_nat j j' m' k
  change l1Chebyshev.toSeq (d.composedApproxCLM h l -
      fderiv ℝ (d.G (banachField f) p) d.abar h l) (n : ℤ) = _
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat,
    d.fderiv_G_fin_toSeq_of_compPoly f p d.abar h l n hn,
    SystemBlockDiagData.actionFinite_finite _ _ _ _ hn, hz]
  have hD : ∀ j', compPolyDerivative f d.abar h j' = 0 := fun j' =>
    CompPoly.Chebyshev.derivative_single_negSucc (f j') d.abar j m' 1
  simp only [hD, show ∀ j' (k : ℕ), toCoeffCheb h j' k = 0 from fun j' k => hz j' k,
    FAseq_eq_zero_of_nat _ (hz _), FCseq_eq_zero_of_nat (0 : l1Chebyshev ν)
      (fun n => l1Chebyshev.toSeq_zero _), mul_zero, add_zero, Finset.sum_const_zero,
    sub_zero]

theorem Tlj_col_le (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    (l j : Fin L) (m : ℤ) :
    ∑ n : Fin (N + 1), ‖(Tlj d f p l j (l1Chebyshev.single m 1)) ((n : ℕ) : ℤ)‖ ≤
      (epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j : ℝ) * (ν : ℝ) ^ m.natAbs := by
  have hνq := ν_q_pos d
  cases m with
  | ofNat mn =>
    have hterm : ∀ n : Fin (N + 1),
        ‖(Tlj d f p l j (l1Chebyshev.single (Int.ofNat mn) 1)) ((↑(n : ℕ)) : ℤ)‖
          = ((|DcolAux N d.A_col d.DF_col l j mn (jacColQ N f d.abar_Q j mn) n| *
              d.ν_q ^ (n : ℕ) : ℚ) : ℝ) := by
      intro n
      rw [l1Chebyshev.norm_fiber]
      rw [show l1Chebyshev.toSeq (Tlj d f p l j (l1Chebyshev.single (Int.ofNat mn) 1))
          (↑(n : ℕ) : ℤ) = ((DcolAux N d.A_col d.DF_col l j mn (jacColQ N f d.abar_Q j mn)
            ⟨(n : ℕ), n.isLt⟩ : ℚ) : ℝ) from
        Tlj_single_toSeq d f p l j mn (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
      rw [d.hν, Fin.eta]
      push_cast
      simp
    rw [Finset.sum_congr rfl fun n _ => hterm n]
    have h := chebColNormQ_le_eps N d.A_col d.DF_col d.abar_Q (one_le_ν_q d) f l j mn
    have h' : ((chebColNormQ N d.A_col d.DF_col d.abar_Q d.ν_q f l j mn : ℚ) : ℝ) ≤
        ((epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j * d.ν_q ^ mn : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [chebColNormQ, colNormAux] at h'
    push_cast at h' ⊢
    refine h'.trans (le_of_eq ?_)
    rw [d.hν]
    rfl
  | negSucc m' =>
    rw [Finset.sum_eq_zero fun n _ => by
      rw [l1Chebyshev.norm_fiber, Tlj_single_negSucc_toSeq d f p l j m' (n : ℕ)
        (Nat.lt_succ_iff.mp n.isLt), abs_zero, zero_mul]]
    exact mul_nonneg (by exact_mod_cast epsBlockGen_nonneg N d.A_col d.DF_col d.abar_Q hνq f l j)
      (pow_nonneg ν.2.le _)

/-- `hfin_le`: the ε-leakage, generic in `L`. -/
theorem Z₁_hfin (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    {ε : ℚ} (hε : epsGen N d.A_col d.DF_col d.abar_Q d.ν_q f ≤ ε)
    (h : XCheb ν L) (l : Fin L) :
    ∑ k : Fin (N + 1),
        ‖(((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h) l)
          (↑(k : ℕ) : ℤ)‖ ≤ (ε : ℝ) * ‖h‖ := by
  have hνq := ν_q_pos d
  rw [clm_apply_eq_sum _ h l]
  have hj : ∀ j, (∑ k : Fin (N + 1),
      ‖((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar)
        (Pi.single j (h j)) l) (↑(k : ℕ) : ℤ)‖) ≤
      (epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j : ℝ) * ‖h‖ := fun j => by
    refine (l1Chebyshev.finsum_norm_le_of_cols (Tlj d f p l j) N (Tlj_col_le d f p l j)
      (h j)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm h j)
      (by exact_mod_cast epsBlockGen_nonneg N d.A_col d.DF_col d.abar_Q hνq f l j)
  refine (Finset.sum_le_sum fun k _ => l1Chebyshev.norm_fiber_sum_le _ _ _).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg h)
  have hsup : (∑ j : Fin L, epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j) ≤ ε :=
    (Finset.le_sup' (fun l : Fin L =>
      ∑ j : Fin L, epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j)
      (Finset.mem_univ l)).trans hε
  have h2 := (Rat.cast_le (K := ℝ)).mpr hsup
  rw [Rat.cast_sum] at h2
  exact h2

/-- `Z₁` from ℚ checks with override slots `R` (≥ ‖S(ā)‖), `K`, `ε`. -/
theorem Z₁_le_of_Q (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)
    {R : Fin L → ℚ} (hR : ∀ i, SnormQ N d.abar_Q d.ν_q i ≤ R i) {K ε Z₁ : ℚ}
    (hK : ∀ l, CompPoly.Chebyshev.derivativeBound (f l) R ≤ K)
    (hε : epsGen N d.A_col d.DF_col d.abar_Q d.ν_q f ≤ ε)
    (hZ₁ : ε + d.ν_q / ((N : ℚ) + 1) * K ≤ Z₁) :
    ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (Z₁ : ℝ) := by
  have hνq := ν_q_pos d
  have hR0 : ∀ i, 0 ≤ R i := fun i => (show 0 ≤ SnormQ N d.abar_Q d.ν_q i from
    add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hνq.le _))
      (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hνq.le _))).trans (hR i)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (CompPoly.Chebyshev.derivativeBound_nonneg (f 0) R hR0).trans (hK 0)
  have hε0 : (0 : ℝ) ≤ (ε : ℝ) := by
    have : 0 ≤ epsGen N d.A_col d.DF_col d.abar_Q d.ν_q f :=
      (Finset.sum_nonneg fun j _ => epsBlockGen_nonneg N d.A_col d.DF_col d.abar_Q hνq f 0 j).trans
        (Finset.le_sup' (fun l : Fin L =>
          ∑ j : Fin L, epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j) (Finset.mem_univ 0))
    exact_mod_cast this.trans hε
  refine chebyshev_Z₁_le_relaxed N d.composedApproxCLM (d.G (banachField f) p) d.abar
    (fun h l => compPolyDerivative f d.abar h l) (Z₁_hneg d f p) hε0 (Z₁_hfin d f p hε)
    (Z₁_htail d f p) hK0 (Z₁_hDφ d f hR hK) ?_
  rw [d.hν]
  exact_mod_cast hZ₁

/-- `Z₁` from ℚ checks with the semi-major tail factor `(ν⁻¹ + ν)/(2(N+1))` of
`chebyshev_Z₁_le_semiMajor` in place of `ν/(N+1)`: the sharper sibling of `Z₁_le_of_Q`, with
the same override slots `R` (≥ ‖S(ā)‖), `K`, `ε`. -/
theorem Z₁_le_semiMajor_of_Q (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) {R : Fin L → ℚ} (hR : ∀ i, SnormQ N d.abar_Q d.ν_q i ≤ R i) {K ε Z₁ : ℚ}
    (hK : ∀ l, CompPoly.Chebyshev.derivativeBound (f l) R ≤ K)
    (hε : epsGen N d.A_col d.DF_col d.abar_Q d.ν_q f ≤ ε)
    (hZ₁ : ε + (d.ν_q⁻¹ + d.ν_q) / (2 * ((N : ℚ) + 1)) * K ≤ Z₁) :
    ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (Z₁ : ℝ) := by
  have hνq := ν_q_pos d
  have hR0 : ∀ i, 0 ≤ R i := fun i => (show 0 ≤ SnormQ N d.abar_Q d.ν_q i from
    add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hνq.le _))
      (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hνq.le _))).trans (hR i)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (CompPoly.Chebyshev.derivativeBound_nonneg (f 0) R hR0).trans (hK 0)
  have hε0 : (0 : ℝ) ≤ (ε : ℝ) := by
    have : 0 ≤ epsGen N d.A_col d.DF_col d.abar_Q d.ν_q f :=
      (Finset.sum_nonneg fun j _ => epsBlockGen_nonneg N d.A_col d.DF_col d.abar_Q hνq f 0 j).trans
        (Finset.le_sup' (fun l : Fin L =>
          ∑ j : Fin L, epsBlockGen N d.A_col d.DF_col d.abar_Q d.ν_q f l j) (Finset.mem_univ 0))
    exact_mod_cast this.trans hε
  refine chebyshev_Z₁_le_semiMajor N d.composedApproxCLM (d.G (banachField f) p) d.abar
    (fun h l => compPolyDerivative f d.abar h l) (Z₁_hneg d f p) hε0 (Z₁_hfin d f p hε)
    (Z₁_htail d f p) hK0 (Z₁_hDφ d f hR hK) ?_
  rw [d.hν]
  exact_mod_cast hZ₁

end BridgesZ1

end StdChebIVPData

/-! ### The family face -/

section Face

/-- The numbers a certificate supplies beyond its bundle: the five radii-polynomial
numbers plus the five override slots (each `≥` its generated majorant, `_of_le` pattern). -/
structure ChebCertQ (L : ℕ) where
  Y₀ : ℚ
  Z₀ : ℚ
  Z₁ : ℚ
  Z₂ : ℚ
  r₀ : ℚ
  /-- override: radii `R i ≥ ‖S(ā_i)‖` (exact `SnormQ`). -/
  R : Fin L → ℚ
  /-- override: `K ≥ max_l derivativeBound (f l) R`. -/
  K : ℚ
  /-- override: `ε ≥ epsGen` (generated ε-leakage). -/
  ε : ℚ
  /-- override: `C ≥ TCnormGen` (generated `‖TC‖` constant). -/
  C : ℚ
  /-- override: `B ≥ 2 · max_l derivativeLipschitzBound (f l) (R + 2 r₀)`. -/
  B : ℚ

variable {L : ℕ} [NeZero L]

/-- All ℚ-decidable obligations, on the raw `StdChebIVPData` fields (ν-free: one
`decide +kernel`). The first conjunct is the exact family-neutral defect clause
(`DefectExact`). The literals are recipe constants of the library lemmas the conjuncts feed:
* `ν_q / (N + 1)` is the tail factor of `chebyshev_Z₁_le_relaxed` (the `Z₁` total);
* the `2` in `2 * derivativeLipschitzBound` is the symmetrization of the raw displacement
  (`norm_compPolyDerivative_sub_le`);
* the radii `C.R i + 2 * C.r₀` bound `‖S(cᵢ)‖` on the ball from `‖S(āᵢ)‖ ≤ C.R i` and
  `‖S(cᵢ − āᵢ)‖ ≤ 2 ‖cᵢ − āᵢ‖ ≤ 2 r₀` (`l1Chebyshev.symmetrize_norm_le`);
* the last conjunct is the radii polynomial `Z₂ r₀² − (1 − Z₀ − Z₁) r₀ + Y₀ < 0`
  (`generalRadiiPolynomial_ratCast`). -/
abbrev ChebCertQ.Checks (C : ChebCertQ L) (N : ℕ)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) : Prop :=
  finiteBlockMatrixNormQ L N (defectCols A_col DF_col) ν_q ≤ C.Z₀ ∧
    (∀ l, Y₀Q N A_col abar_Q ν_q f p_q l ≤ C.Y₀) ∧
    (∀ i, SnormQ N abar_Q ν_q i ≤ C.R i) ∧
    (∀ l, CompPoly.Chebyshev.derivativeBound (f l) C.R ≤ C.K) ∧
    epsGen N A_col DF_col abar_Q ν_q f ≤ C.ε ∧
    C.ε + ν_q / ((N : ℚ) + 1) * C.K ≤ C.Z₁ ∧
    TCnormGen N A_col ν_q ≤ C.C ∧
    (∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
      (fun i => C.R i + 2 * C.r₀) ≤ C.B) ∧
    C.C * C.B ≤ C.Z₂ ∧
    0 < C.r₀ ∧
    C.Z₂ * C.r₀ ^ 2 - (1 - C.Z₀ - C.Z₁) * C.r₀ + C.Y₀ < 0

namespace StdChebIVPData

section FaceBundle

variable {ν : PosReal} {N : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- Face with `Y₀`, `Z₀` from ℚ checks and `Z₁`, `Z₂` as explicit operator bounds; `hradii` is
the radii polynomial `Z₂ r₀² − (1 − Z₀ − Z₁) r₀ + Y₀ < 0` in exact arithmetic
(`generalRadiiPolynomial_ratCast`). -/
theorem certified_of_Y₀Z₀ (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) {Y₀ Z₀ Z₁ Z₂ r₀ : ℚ}
    (hZ₀ : finiteBlockMatrixNormQ L N (defectCols d.A_col d.DF_col) d.ν_q ≤ Z₀)
    (hY₀ : ∀ l, Y₀Q N d.A_col d.abar_Q d.ν_q f p_q l ≤ Y₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (Z₁ : ℝ))
    (hZ₂ : ∀ c ∈ Metric.closedBall d.abar (r₀ : ℝ),
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ (Z₂ : ℝ) * (r₀ : ℝ))
    (hr₀ : 0 < r₀) (hradii : Z₂ * r₀ ^ 2 - (1 - Z₀ - Z₁) * r₀ + Y₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall d.abar (r₀ : ℝ), d.G (banachField f) p xTilde = 0 :=
  d.existsUnique_of_compPoly f p (Z₂_val := (Z₂ : ℝ)) (by exact_mod_cast hr₀)
    (Y₀_le_of_Q d f p p_q hp hY₀) (defect_finBlockNorm_le_of_Q d hZ₀) hZ₁ hZ₂
    (generalRadiiPolynomial_neg_of_Q_const _ _ _ _ _ hradii)

/-- **Family face.** Existence and uniqueness of the zero of the preconditioned
Chebyshev IVP map for any `StdChebIVPData` bundle and `CompPoly` system, from ONE
ℚ-decidable conjunction (`decide +kernel`) plus the rational boundary-value bridge `hp`. -/
theorem certified_of_checks (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) (C : ChebCertQ L)
    (h : C.Checks N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ∃! xTilde ∈ Metric.closedBall d.abar (C.r₀ : ℝ), d.G (banachField f) p xTilde = 0 := by
  obtain ⟨hZ₀, hY₀, hR, hK, hε, hZ₁, hC, hB, hZ₂, hr₀, hrad⟩ := h
  exact certified_of_Y₀Z₀ d f p p_q hp hZ₀ hY₀ (Z₁_le_of_Q d f p hR hK hε hZ₁)
    (Z₂_le_of_Q d f p hR hr₀.le hC hB hZ₂) hr₀ hrad

end FaceBundle

end StdChebIVPData

end Face

/-! ### Kernel-scale checker

Four cost cuts, each with a generic soundness lemma, so that the kernel (`decide +kernel`)
closes certificates with a few dozen modes:

* `evalFast`: the Laurent interpreter with the convolution window clipped to the
  intersection of both factors' supports (`evalFast_eq`: equal to `evalLaurentCoeffSeq` on
  support-bounded inputs). The library interpreter sums over `laurentModes`, a
  `Finset.image` whose kernel reduction deduplicates `2R+1` integers per product node.
* `colNormS`: the `Z₁` leakage column as `A · w`, where `w` = (stored `DF` column) − (exact
  Jacobian column), summed over the support of `w` only (`colNormS_eq`: equal to
  `chebColNormQ`). Columns inside the stored block cancel to `w = 0` when `DF` is the exact
  Jacobian; columns beyond it keep only the Jacobian's nonzero rows.
* `TCnormF`: the `TC` column rows in closed form (two entries of `A` per row instead of an
  `N + 1`-term sum against the sparse `FCe`; `TCnormF_eq`: equal to `TCnormGen`).
* `ChecksK`: the `Z₀` conjunct of `Checks` replaced by a `DefectBy` slot (exact columns rounded
  onto a grid, or grid accumulators), the `ε` conjunct by per-block certificate data
  `E l j` (one comparison per column and one far-envelope comparison per block), and every
  conjunct stated separately so a certificate closes each by its own `decide +kernel`
  (`checks_of_checksK`: `ChecksK → Checks`; `Z₁_le_of_checksK`: the same `Z₁` operator
  bound `Z₁_le_of_Q` produces). -/

section KernelQ

variable {L : ℕ}

/-- Integer maximum through the core `Int.decLe` instance (kernel-reducible). -/
def zmax (a b : ℤ) : ℤ := @ite _ (a ≤ b) (Int.decLe a b) b a

/-- Integer minimum through the core `Int.decLe` instance (kernel-reducible). -/
def zmin (a b : ℤ) : ℤ := @ite _ (a ≤ b) (Int.decLe a b) a b

/-- Sum of `g` over the integer interval `[lo, hi]`, as a list fold. -/
def zsum (lo hi : ℤ) (g : ℤ → ℚ) : ℚ :=
  ((List.range (hi + 1 - lo).toNat).map fun i : ℕ => g (lo + i)).sum

theorem list_range_map_sum (n : ℕ) (F : ℕ → ℚ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem zsum_eq (lo hi : ℤ) (g : ℤ → ℚ) : zsum lo hi g = ∑ k ∈ Finset.Icc lo hi, g k := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map, zsum, list_range_map_sum]
  rfl

/-- The Laurent interpreter with the product window clipped to both supports. -/
def evalFast : CompPoly L → (Fin L → ℕ) → (Fin L → ℤ → ℚ) → ℤ → ℚ
  | .C r, _, _, n => if n = 0 then r else 0
  | .X i, _, seqs, n => seqs i n
  | .add p q, radii, seqs, n => evalFast p radii seqs n + evalFast q radii seqs n
  | .sub p q, radii, seqs, n => evalFast p radii seqs n - evalFast q radii seqs n
  | .mul p q, radii, seqs, n =>
      zsum (zmax (-(q.laurentRadius radii : ℤ)) (n - p.laurentRadius radii))
        (zmin (q.laurentRadius radii : ℤ) (n + p.laurentRadius radii))
        fun k => evalFast p radii seqs (n - k) * evalFast q radii seqs k
  | .neg p, radii, seqs, n => -(evalFast p radii seqs n)
  | .smul r p, radii, seqs, n => r * evalFast p radii seqs n

/-- Soundness of the clipped interpreter on support-bounded inputs. -/
theorem evalFast_eq (p : CompPoly L) (radii : Fin L → ℕ) (seqs : Fin L → ℤ → ℚ)
    (hs : ∀ i n, radii i < n.natAbs → seqs i n = 0) (n : ℤ) :
    evalFast p radii seqs n = p.evalLaurentCoeffSeq radii seqs n := by
  induction p generalizing n with
  | C r => rfl
  | X i => rfl
  | add p q ihp ihq => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
  | sub p q ihp ihq => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
  | mul p q ihp ihq =>
      simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
      rw [zsum_eq]
      refine Finset.sum_subset (fun k hk => ?_) (fun k hk hnk => ?_)
      · rw [Finset.mem_Icc] at hk
        rw [CompPoly.mem_laurentModes_iff]
        unfold zmax zmin at hk
        split_ifs at hk <;> omega
      · rw [CompPoly.mem_laurentModes_iff] at hk
        rw [Finset.mem_Icc] at hnk
        have hp : p.laurentRadius radii < (n - k).natAbs := by
          unfold zmax zmin at hnk
          split_ifs at hnk <;> omega
        rw [CompPoly.evalLaurentCoeffSeq_eq_zero_of_radius_lt p radii seqs hs _ hp, zero_mul]
  | neg p ih => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ih]
  | smul r p ih => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ih]

/-- `evalChebCoeff` through the clipped interpreter. -/
def evalChebFast (p : CompPoly L) (arrs : Fin L → Array ℚ) : ℤ → ℚ :=
  evalFast p (fun i => (arrs i).size) (fun i n => (arrs i).getD n.natAbs 0)

theorem evalChebFast_eq (p : CompPoly L) (arrs : Fin L → Array ℚ) (n : ℤ) :
    evalChebFast p arrs n = p.evalChebCoeff arrs n :=
  evalFast_eq p _ _ (fun i k hk => by
    simp [Array.getD, show ¬k.natAbs < (arrs i).size by omega]) n

/-- `compPolyDphiQ` through the clipped interpreter. -/
def dphiFast (p : CompPoly L) (m : Fin L) (arrs : Fin L → Array ℚ) (k : ℕ) (n : ℤ) : ℚ :=
  if k = 0 then evalChebFast (p.pderiv m) arrs n
  else evalChebFast (p.pderiv m) arrs (n - k) + evalChebFast (p.pderiv m) arrs (n + k)

/-- `compPolyDFQ` through the clipped interpreter. -/
def dfFast (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (l m : Fin L) (row col : ℕ) : ℚ :=
  match row with
  | 0 => if l = m then (if col = 0 then -1 else -2 * (-1 : ℚ) ^ col) else 0
  | k + 1 => (if l = m ∧ k + 1 = col then 2 * ((k : ℚ) + 1) else 0) +
      dphiFast (f l) m arrs col (↑(k + 2) : ℤ) - dphiFast (f l) m arrs col (k : ℤ)

theorem dfFast_eq (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (l m : Fin L)
    (row col : ℕ) : dfFast f arrs l m row col = compPolyDFQ f arrs l m row col := by
  cases row with
  | zero => rfl
  | succ k => simp only [dfFast, compPolyDFQ, dphiFast, compPolyDphiQ, evalChebFast_eq]

/-- Residual column `w = (stored DF column, inside the block) − (exact Jacobian column)`
of input component `j`, mode `mn`, at output `(j', k)`. -/
def wQ (N : ℕ) (DF_col : Fin L → Fin L → ℕ → Array ℚ) (f : Fin L → CompPoly L)
    (arrs : Fin L → Array ℚ) (j : Fin L) (mn : ℕ) (x : Fin L × Fin (N + 1)) : ℚ :=
  (if mn ≤ N then (DF_col x.1 j mn).getD x.2 0 else 0) - dfFast f arrs x.1 j x.2 mn

/-- Support of the residual column. -/
def wSupp (N : ℕ) (DF_col : Fin L → Fin L → ℕ → Array ℚ) (f : Fin L → CompPoly L)
    (arrs : Fin L → Array ℚ) (j : Fin L) (mn : ℕ) : Finset (Fin L × Fin (N + 1)) :=
  Finset.univ.filter fun x => wQ N DF_col f arrs j mn x ≠ 0

/-- Row `n` of leakage column `mn` of block `(l, j)`, as `A · w` over the support of `w`. -/
def DcolS (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (arrs : Fin L → Array ℚ)
    (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) (n : Fin (N + 1)) : ℚ :=
  ∑ x ∈ wSupp N DF_col f arrs j mn, (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x

/-- Sparse weighted norm of leakage column `mn` of block `(l, j)`. -/
def colNormS (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (arrs : Fin L → Array ℚ)
    (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) : ℚ :=
  ∑ n : Fin (N + 1), |DcolS N A_col DF_col arrs f l j mn n| * ν_q ^ (n : ℕ)

/-- The sparse row is the exact leakage row `DcolAux` (generic in `L`, `N`, the data). -/
theorem DcolS_eq (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (arrs : Fin L → Array ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) :
    DcolS N A_col DF_col arrs f l j mn n =
      DcolAux N A_col DF_col l j mn (jacColQ N f arrs j mn) n := by
  rw [DcolAux_jac]
  unfold DcolS wSupp
  rw [Finset.sum_filter]
  have h1 : ∀ x : Fin L × Fin (N + 1),
      (if wQ N DF_col f arrs j mn x ≠ 0 then
        (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x else 0) =
        (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x := fun x => by
    split_ifs with h
    · rfl
    · rw [not_not.mp h, mul_zero]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Fintype.sum_prod_type]
  simp only [wQ, dfFast_eq, mul_sub, Finset.sum_sub_distrib]
  congr 1
  by_cases hmn : mn ≤ N
  · rw [dite_eq_left hmn]
    simp only [ite_eq_left hmn]
    unfold blockDefectMatQ
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply, matOfCols]
    by_cases hlj : l = j
    · subst hlj
      simp only [ite_true, true_and, Matrix.one_apply, Fin.ext_iff]
      ring
    · simp only [hlj, ite_false, false_and, Matrix.zero_apply]
      ring
  · rw [dite_eq_right hmn, ite_eq_right (fun h : l = j ∧ (n : ℕ) = mn => hmn (h.2 ▸ Nat.lt_succ_iff.mp n.isLt))]
    simp only [ite_eq_right hmn, mul_zero, Finset.sum_const_zero, sub_zero]

theorem colNormS_eq (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (arrs : Fin L → Array ℚ) (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) :
    colNormS N A_col DF_col arrs ν_q f l j mn = chebColNormQ N A_col DF_col arrs ν_q f l j mn := by
  unfold colNormS chebColNormQ colNormAux
  simp only [DcolS_eq]

/-- Soundness of the per-block certificate data: column checks up to `Mfar`, the far
envelope, and the row sums give the generated leakage bound `epsGen ≤ ε` the face consumes. -/
theorem epsGen_le_of_cols [NeZero L] (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) {ν_q : ℚ} (hν : 0 < ν_q) (f : Fin L → CompPoly L)
    (E : Fin L → Fin L → ℚ) {ε : ℚ}
    (hcol : ∀ l j, ∀ mn < Mfar N f abar_Q + 1,
      chebColNormQ N A_col DF_col abar_Q ν_q f l j mn ≤ E l j * ν_q ^ mn)
    (hfar : ∀ l j, rowA0Q N A_col ν_q l j ≤ E l j * ν_q ^ (Mfar N f abar_Q + 1))
    (hE : ∀ l, ∑ j, E l j ≤ ε) :
    epsGen N A_col DF_col abar_Q ν_q f ≤ ε := by
  unfold epsGen
  refine Finset.sup'_le _ _ fun l _ => (Finset.sum_le_sum fun j _ => ?_).trans (hE l)
  unfold epsBlockGen
  refine max_le (Finset.sup'_le _ _ fun mn _ => ?_) ?_
  · exact (div_le_iff₀ (pow_pos hν _)).mpr (hcol l j mn mn.isLt)
  · exact (div_le_iff₀ (pow_pos hν _)).mpr (hfar l j)

/-- Closed form of a `TC` column row: `FCe mn` has at most two nonzero entries
(`k = mn − 1` with coefficient `1`, `k = mn + 1` with coefficient `−1`). -/
def TCcolF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) : ℚ :=
  (if 2 ≤ mn ∧ mn ≤ N + 1 then (A_col l j (mn - 1)).getD n 0 else 0) -
    (if mn < N then (A_col l j (mn + 1)).getD n 0 else 0)

theorem TCcolQ_eq_F (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) : TCcolQ N A_col l j mn n = TCcolF N A_col l j mn n := by
  set a : ℕ → ℚ := fun k => (A_col l j k).getD n 0 with ha
  have key : ∀ c : ℕ, (∑ i ∈ Finset.range N, if i = c then a (i + 1) else 0) =
      if c < N then a (c + 1) else 0 := fun c => by
    rw [Finset.sum_ite_eq' (Finset.range N) c (fun i => a (i + 1))]
    simp only [Finset.mem_range]
  unfold TCcolQ TCcolF
  rw [Fin.sum_univ_eq_sum_range (fun k => (A_col l j k).getD n 0 * FCe mn k) (N + 1),
    Finset.sum_range_succ']
  simp only [FCe, mul_zero, add_zero, mul_sub, mul_ite, mul_one, Finset.sum_sub_distrib]
  change (∑ i ∈ Finset.range N, if i + 2 = mn then a (i + 1) else 0) -
      (∑ i ∈ Finset.range N, if i = mn then a (i + 1) else 0) = _
  rw [key mn]
  congr 1
  by_cases h2 : 2 ≤ mn
  · obtain ⟨c, rfl⟩ : ∃ c, mn = c + 2 := ⟨mn - 2, by omega⟩
    simp only [add_left_inj, key c]
    by_cases hc : c < N
    · rw [ite_eq_left hc, ite_eq_left ⟨h2, by omega⟩]
      rfl
    · rw [ite_eq_right hc, ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

/-- `TCcolNormQ` through the closed-form rows. -/
def TCcolNormF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L)
    (mn : ℕ) : ℚ :=
  ∑ n : Fin (N + 1), |TCcolF N A_col l j mn n| * ν_q ^ (n : ℕ)

/-- `TCblockGen` through the closed-form rows. -/
def TCblockF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun mn : Fin (N + 2) =>
    TCcolNormF N A_col ν_q l j mn / ν_q ^ (mn : ℕ)

/-- `TCnormGen` through the closed-form rows. -/
def TCnormF [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l : Fin L =>
    ∑ j : Fin L, (TCblockF N A_col ν_q l j + if l = j then ν_q / ((N : ℚ) + 1) else 0)

theorem TCnormF_eq [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) :
    TCnormF N A_col ν_q = TCnormGen N A_col ν_q := by
  unfold TCnormF TCblockF TCcolNormF TCnormGen TCblockGen TCcolNormQ
  simp only [TCcolQ_eq_F]

/-- Splitting a bounded `∀` into two ranges (per-range `decide +kernel` lemmas). -/
theorem ball_lt_add {P : ℕ → Prop} {a b : ℕ} (h₁ : ∀ m < a, P m) (h₂ : ∀ t < b, P (a + t)) :
    ∀ m < a + b, P m := fun m hm => by
  rcases lt_or_ge m a with h | h
  · exact h₁ m h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    exact h₂ t (by omega)

end KernelQ

section KernelFace

variable {L : ℕ} [NeZero L]

/-- Kernel-scale obligations: `Checks` with the `Z₀` conjunct at a `DefectBy` slot `s` with grid
denominator `S` (sound for the exact clause by `defectBy_sound`) and the `ε` conjunct replaced by
per-block certificate data `E` (column checks through `colNormS`, far envelope, row sums). Every
conjunct is ν-free and ℚ-decidable; a certificate may close each by its own `decide +kernel`.
The literals are those of `Checks`: `ν_q / (N + 1)` is the tail factor of
`chebyshev_Z₁_le_relaxed`; the `2` in `2 * derivativeLipschitzBound` is the symmetrization of the
raw displacement (`norm_compPolyDerivative_sub_le`); the radii `C.R i + 2 * C.r₀` bound `‖S(cᵢ)‖`
on the ball (`l1Chebyshev.symmetrize_norm_le`); the last conjunct is the radii polynomial
(`generalRadiiPolynomial_ratCast`); `Mfar N f abar_Q + 1` is the number of columns checked
individually (`chebColNormQ_far` beyond it). -/
abbrev ChebCertQ.ChecksK (C : ChebCertQ L) (s : Z₀Slot) (S : ℕ) (E : Fin L → Fin L → ℚ) (N : ℕ)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) : Prop :=
  DefectBy L N A_col DF_col ν_q s S C.Z₀ ∧
    (∀ l, Y₀Q N A_col abar_Q ν_q f p_q l ≤ C.Y₀) ∧
    (∀ i, SnormQ N abar_Q ν_q i ≤ C.R i) ∧
    (∀ l, CompPoly.Chebyshev.derivativeBound (f l) C.R ≤ C.K) ∧
    (∀ l j, ∀ mn < Mfar N f abar_Q + 1,
      colNormS N A_col DF_col abar_Q ν_q f l j mn ≤ E l j * ν_q ^ mn) ∧
    (∀ l j, rowA0Q N A_col ν_q l j ≤ E l j * ν_q ^ (Mfar N f abar_Q + 1)) ∧
    (∀ l, ∑ j, E l j ≤ C.ε) ∧
    C.ε + ν_q / ((N : ℚ) + 1) * C.K ≤ C.Z₁ ∧
    TCnormF N A_col ν_q ≤ C.C ∧
    (∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
      (fun i => C.R i + 2 * C.r₀) ≤ C.B) ∧
    C.C * C.B ≤ C.Z₂ ∧
    0 < C.r₀ ∧
    C.Z₂ * C.r₀ ^ 2 - (1 - C.Z₀ - C.Z₁) * C.r₀ + C.Y₀ < 0

/-- **Soundness of the kernel-scale checker**: `ChecksK → Checks`. -/
theorem checks_of_checksK (C : ChebCertQ L) (E : Fin L → Fin L → ℚ) {N : ℕ}
    {A_col DF_col : Fin L → Fin L → ℕ → Array ℚ} {abar_Q : Fin L → Array ℚ} {ν_q : ℚ}
    (hν : 0 < ν_q) {f : Fin L → CompPoly L} {p_q : Fin L → ℚ} (s : Z₀Slot) (S : ℕ)
    (h : C.ChecksK s S E N A_col DF_col abar_Q ν_q f p_q) :
    C.Checks N A_col DF_col abar_Q ν_q f p_q := by
  obtain ⟨hZ₀, hY₀, hR, hK, hcol, hfar, hE, hZ₁, hC, hB, hZ₂, hr₀, hrad⟩ := h
  refine ⟨defectBy_sound s S hZ₀, hY₀, hR, hK, epsGen_le_of_cols N A_col DF_col abar_Q hν f E
    (fun l j mn hmn => ?_) hfar hE, hZ₁, TCnormF_eq N A_col ν_q ▸ hC, hB, hZ₂, hr₀, hrad⟩
  rw [← colNormS_eq]
  exact hcol l j mn hmn

namespace StdChebIVPData

section KernelFaceBundle

variable {ν : PosReal} {N : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- The `Z₁` operator bound from the kernel-scale checks (the bound `Z₁_le_of_Q` produces). -/
theorem Z₁_le_of_checksK (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (C : ChebCertQ L) (E : Fin L → Fin L → ℚ)
    (s : Z₀Slot) (S : ℕ) (h : C.ChecksK s S E N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (C.Z₁ : ℝ) := by
  obtain ⟨-, -, hR, hK, hε, hZ₁, -⟩ := checks_of_checksK C E (ν_q_pos d) s S h
  exact Z₁_le_of_Q d f p hR hK hε hZ₁

/-- The semi-major `Z₁` operator bound from the kernel-scale checks: the `R`, `K` and `ε`
obligations of `ChecksK` fed to `Z₁_le_semiMajor_of_Q`, with the semi-major total `hZ₁` in place
of the `ChecksK` conjunct. The derivative bound does not involve the boundary value, so no
`p = p_q` cast is assumed. -/
theorem Z₁_le_semiMajor_of_checksK (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (C : ChebCertQ L) (E : Fin L → Fin L → ℚ)
    (s : Z₀Slot) (S : ℕ) (h : C.ChecksK s S E N d.A_col d.DF_col d.abar_Q d.ν_q f p_q)
    {Z₁ : ℚ} (hZ₁ : C.ε + (d.ν_q⁻¹ + d.ν_q) / (2 * ((N : ℚ) + 1)) * C.K ≤ Z₁) :
    ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (Z₁ : ℝ) := by
  obtain ⟨-, -, hR, hK, hε, -⟩ := checks_of_checksK C E (ν_q_pos d) s S h
  exact Z₁_le_semiMajor_of_Q d f p hR hK hε hZ₁

/-- **Family face, kernel scale.** Existence and uniqueness from the kernel-scale obligations. -/
theorem certified_of_checksK (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) (C : ChebCertQ L)
    (E : Fin L → Fin L → ℚ) (s : Z₀Slot) (S : ℕ)
    (h : C.ChecksK s S E N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ∃! xTilde ∈ Metric.closedBall d.abar (C.r₀ : ℝ), d.G (banachField f) p xTilde = 0 :=
  certified_of_checks d f p p_q hp C (checks_of_checksK C E (ν_q_pos d) s S h)

end KernelFaceBundle

end StdChebIVPData

end KernelFace

end ChebyshevIVP
