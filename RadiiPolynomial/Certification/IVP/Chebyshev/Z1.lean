import RadiiPolynomial.Certification.IVP.Chebyshev.Y0Z0
import RadiiPolynomial.Certification.IVP.Chebyshev.Common

/-!
# Chebyshev certification adapter: `Z₁`

The leakage columns `jacColQ`, `DcolAux`, `colNormAux`, `chebColNormQ`, `Mfar`, `rowA0Q`,
`epsBlockGen`, `epsGen`; the hypotheses `d.Z₁_hneg`, `d.Z₁_htail`, `d.Z₁_hDφ`, `d.Z₁_hfin` of
`chebyshev_Z₁_le_relaxed`, and `d.Z₁_le_of_Q`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

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
  have hsplit : ((d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h) l =
      ∑ j, (d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar)
        (Pi.single j (h j)) l := by
    rw [← Finset.sum_apply,
      ← ContinuousLinearMap.sum_comp_single ℝ (fun _ => l1Chebyshev ν)
        (d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar) h]
    rfl
  rw [hsplit]
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


end BridgesZ1

end StdChebIVPData

end ChebyshevIVP
