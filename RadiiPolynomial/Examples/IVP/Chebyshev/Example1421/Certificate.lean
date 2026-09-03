import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Lambda
import RadiiPolynomial.Certification
import RadiiPolynomial.Tactic.FinMatrixBound

/-!
# Example 14.2.1 — Certificate (complete)

Full machine-checked verification of the Chebyshev logistic twin at ν = 2,
N = 40 (`main_existsUnique`). All four bounds:

- `Y₀_le` — ‖G(ā)‖ ≤ 10⁻²¹: support ⊆ modes 0..2N+2, the exact-ℚ folded
  convolution `FQ` mirrors F(ā) row by row, `finsum_bound` at 100 bits;
- `Z₀_le` — the 41×41 block defect ‖I − A·DF‖ ≤ 10⁻¹⁶ by a single
  `native_decide` in exact ℚ (dyadic entries, denominators 2⁹⁰/2¹²⁰);
- `Z₁_le` — ε + ν/(N+1)·K ≤ 0.2533 via `chebyshev_Z₁_le_relaxed`: negatives
  pass through, the tail is −shiftDiv(Dφ h), and the ε-leakage (7/2000) is
  certified column-by-column in exact ℚ (`DcolQ`/`colNormQ` + the
  `l1Chebyshev.finsum_norm_le_of_cols` column-norm bound) — columns ≤ N cancel
  exactly against the stored Jacobian, the leaked Dφ couplings N < m ≤ 2N+2
  peak at ≈ 0.0034, and beyond 2N+2 only row 0's alternating functional
  survives; K = 5.12 from `‖S(ā)‖ ≤ 39/50` (native_decide);
- `Z₂_le` — 14·r₀ from DG(c) − DG(ā) = TC∘(DΦ(c) − DΦ(ā)), the difference of
  derivatives being `h ↦ 2·S((c−ā)ₗ)·S(hₗ)` (≤ 8‖c−ā‖‖h‖), and the sharp
  full-column bound ‖TC‖ ≤ 7/4 (block columns exact in ℚ ≤ 279/164, tail
  tsum ≤ ν/(N+1) = 2/41);

plus `radii_neg` (the radii polynomial at r = 10⁻⁶) and
`margin_clears_gate` — the native margin (≈ 74.7%) clears the bordered↔U
transport threshold (κ−1)/κ = 5/8 at κ = 8/3, so the certificate transports
(`tmp/kappa_transport/Transport.lean` §7 `twin_transports`).
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap RadiiPolynomial ChebyshevIVP Example1421

noncomputable section

namespace Example1421.Cert

/-! ## Z₀ — defect bound via exact ℚ matrix arithmetic -/

private def defectBlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  Array.ofFn fun (i : Fin (N + 1)) =>
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j i k

private lemma Array.getD_ofFn_fin {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

private lemma defectBlockCol_correct (l j : Fin L) (i k : Fin (N + 1)) :
    data.defect.finBlock l j i k = ((defectBlockCols l j k).getD (i : ℕ) 0 : ℝ) := by
  rw [defectBlockCols, Array.getD_ofFn_fin]
  have := blockDefectMatQ_correct
    (fun l m => data.A_finBlock l m) (fun m j => data.DF_finBlock m j)
    (fun l m (k : Fin (N + 1)) => A_col l m (k : ℕ))
    (fun m j (k : Fin (N + 1)) => DF_col m j (k : ℕ))
    (fun l m j i => by simp [ChebyshevIVP.StdChebIVPData.A_finBlock, data])
    (fun m j k i => by simp [ChebyshevIVP.StdChebIVPData.DF_finBlock, data])
    l j i k
  show ((if l = j then 1 else 0) - ∑ m, data.A_finBlock l m * data.DF_finBlock m j) i k = _
  exact this

/-! ## ℚ mirror of F(ā)

The folded convolution of the stored dyadic coefficients, run in exact ℚ.
`FQ` mirrors `chebyshevIvpCoeffs phi p₀ ā` row by row (bridge: `F_abar_eq`). -/

/-- Stored coefficient, zero-extended beyond the array. -/
def qbar (k : ℕ) : ℚ := abar_0.getD k 0

lemma abar_0_size : abar_0.size = N + 1 := by native_decide

lemma qbar_eq_zero {k : ℕ} (hk : N < k) : qbar k = 0 := by
  unfold qbar
  simp only [Array.getD]
  rw [dif_neg (by rw [abar_0_size]; omega)]

/-- ℚ fold: `(S ā · S ā)_m` for `m ≥ 0` (symmetric-extension convolution),
indexed by `j ∈ range (2N+1)` via `i = j − N` to stay computable. -/
def foldQ (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (2 * N + 1),
    qbar ((m : ℤ) - ((j : ℤ) - N)).natAbs * qbar ((j : ℤ) - N).natAbs

/-- ℚ mirror of `toSeq (phi ā) m` for `m ≥ 0`. -/
def phiQ (m : ℕ) : ℚ := foldQ m - qbar m

/-- ℚ mirror of `chebyshevIvpCoeffs phi p₀ ā`. -/
def FQ : ℕ → ℚ
  | 0 => 1/2 - qbar 0 - 2 * ∑ j ∈ Finset.range N, (-1 : ℚ) ^ (j + 1) * qbar (j + 1)
  | (k + 1) => 2 * ((k : ℚ) + 1) * qbar (k + 1) + phiQ (k + 2) - phiQ k

lemma phiQ_eq_zero {m : ℕ} (hm : 2 * N < m) : phiQ m = 0 := by
  have hfold : foldQ m = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hNz : ((N : ℤ)) = 40 := rfl
    have hNn : N = 40 := rfl
    rw [qbar_eq_zero (k := ((m : ℤ) - ((j : ℤ) - N)).natAbs) (by omega), zero_mul]
  rw [phiQ, hfold, qbar_eq_zero (by omega), sub_zero]

lemma FQ_eq_zero {n : ℕ} (hn : 2 * N + 1 < n) : FQ n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show 2 * ((k : ℚ) + 1) * qbar (k + 1) + phiQ (k + 2) - phiQ k = 0
  rw [qbar_eq_zero (by omega), phiQ_eq_zero (by omega), phiQ_eq_zero (by omega)]
  ring

/-! ### Bridges: ā and φ(ā) in terms of the ℚ mirror -/

private lemma abar_toSeq_nat (l : Fin L) (k : ℕ) :
    l1Chebyshev.toSeq (ChebyshevIVP.StdChebIVPData.abar data l) (↑k : ℤ) = (qbar k : ℝ) :=
  data.abar_toSeq_eq l k

private lemma Sabar_toSeq (l : Fin L) (i : ℤ) :
    l1Chebyshev.toSeq (S (ChebyshevIVP.StdChebIVPData.abar data l)) i
      = (qbar i.natAbs : ℝ) := by
  rw [S_apply, Ssym_toSeq, abar_toSeq_nat]

/-- The index window `{j − N : j ∈ range (2N+1)}`, as a computable stand-in
for `Icc (−N) N`. -/
private def suppWindow : Finset ℤ :=
  Finset.image (fun j : ℕ => (j : ℤ) - N) (Finset.range (2 * N + 1))

private lemma Sabar_support (l : Fin L) (i : ℤ) (hi : i ∉ suppWindow) :
    l1Chebyshev.toSeq (S (ChebyshevIVP.StdChebIVPData.abar data l)) i = 0 := by
  have hNz : ((N : ℤ)) = 40 := rfl
  have hNn : N = 40 := rfl
  rw [Sabar_toSeq, qbar_eq_zero (show N < i.natAbs from by
    by_contra habs
    exact hi (Finset.mem_image.mpr ⟨(i + N).toNat,
      Finset.mem_range.mpr (by omega), by omega⟩))]
  norm_num

private lemma phi_abar_toSeq_nat (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (phi (ChebyshevIVP.StdChebIVPData.abar data) l) (↑n : ℤ)
      = (phiQ n : ℝ) := by
  show l1Chebyshev.toSeq (S (ChebyshevIVP.StdChebIVPData.abar data l)
    * S (ChebyshevIVP.StdChebIVPData.abar data l)
    - S (ChebyshevIVP.StdChebIVPData.abar data l)) (↑n : ℤ) = _
  rw [l1Chebyshev.toSeq_sub,
    l1Chebyshev.toSeq_mul_eq_finsum _ _ (↑n : ℤ) suppWindow (Sabar_support l),
    Sabar_toSeq]
  rw [show suppWindow
      = Finset.image (fun j : ℕ => (j : ℤ) - N) (Finset.range (2 * N + 1)) from rfl]
  rw [Finset.sum_image (fun x _ y _ h => by omega)]
  rw [Finset.sum_congr rfl fun j _ => by rw [Sabar_toSeq, Sabar_toSeq]]
  rw [phiQ, foldQ]
  push_cast
  simp

/-- The hvec bridge: the real F(ā) rows are the ℚ mirror, cast. -/
private lemma F_abar_eq (l : Fin L) (n : ℕ) :
    chebyshevIvpCoeffs phi p₀ (ChebyshevIVP.StdChebIVPData.abar data) l n = (FQ n : ℝ) := by
  cases n with
  | zero =>
    show p₀ l - l1Chebyshev.toSeq (ChebyshevIVP.StdChebIVPData.abar data l) 0
        - 2 * ∑' (j : ℕ), (-1 : ℝ) ^ (j + 1)
          * l1Chebyshev.toSeq (ChebyshevIVP.StdChebIVPData.abar data l) (↑(j + 1) : ℤ) = _
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
      rw [abar_toSeq_nat, qbar_eq_zero (by simp [Finset.mem_range] at hj; omega)]
      norm_num)]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, abar_toSeq_nat]
    rw [Finset.sum_congr rfl fun j _ => by rw [abar_toSeq_nat]]
    show 1/2 - _ - _ = _
    rw [show FQ 0 = 1/2 - qbar 0
      - 2 * ∑ j ∈ Finset.range N, (-1 : ℚ) ^ (j + 1) * qbar (j + 1) from rfl]
    push_cast
    ring
  | succ k =>
    show 2 * ((k : ℝ) + 1)
        * l1Chebyshev.toSeq (ChebyshevIVP.StdChebIVPData.abar data l) (↑(k + 1) : ℤ)
        + l1Chebyshev.toSeq (phi (ChebyshevIVP.StdChebIVPData.abar data) l) (↑(k + 2) : ℤ)
        - l1Chebyshev.toSeq (phi (ChebyshevIVP.StdChebIVPData.abar data) l) (↑k : ℤ) = _
    rw [abar_toSeq_nat, phi_abar_toSeq_nat, phi_abar_toSeq_nat]
    rw [show FQ (k + 1) = 2 * ((k : ℚ) + 1) * qbar (k + 1) + phiQ (k + 2) - phiQ k from rfl]
    push_cast
    ring

/-! ## Y₀ — defect of the approximate solution -/

private def ABlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ := A_col l j (k : ℕ)

private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun _l n => FQ n)
    (fun _l n => 1 / (2 * (n : ℚ))) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) (cfg : LeanCert.DyadicConfig)
    (hprec : cfg.precision ≤ 0) :
    (|data.approxInverse.action
        (chebyshevIvpCoeffs phi p₀ (ChebyshevIVP.StdChebIVPData.abar data)) l n|
      * (ν_val : ℝ) ^ n : ℝ) ∈ Y₀_eval l n cfg :=
  systemBlockDiagActionEval_correct data.approxInverse
    (chebyshevIvpCoeffs phi p₀ (ChebyshevIVP.StdChebIVPData.abar data))
    (fun _l n => FQ n) ABlockCols (fun _l n => 1 / (2 * (n : ℚ))) ν_q
    (fun l j k i => data.A_finBlock_eq l j i k)
    (fun l n => F_abar_eq l n)
    (fun _l n hn => by
      rw [data.htail_diag_inv _ n hn]
      push_cast
      ring)
    ν_val_eq_q l n cfg hprec

/-- Y₀ obligation: `‖G(ā)‖ ≤ 10⁻²¹`. The support of `G(ā)` is contained in
modes `0..2N+2`; the finite sum is certified against the exact-ℚ fold. -/
lemma Y₀_le :
    ‖data.G phi p₀ (ChebyshevIVP.StdChebIVPData.abar data)‖ ≤ (Y₀_bound : ℝ) := by
  have hb : (0 : ℝ) ≤ (Y₀_bound : ℝ) := by norm_num [Y₀_bound]
  refine (pi_norm_le_iff_of_nonneg hb).mpr fun l => ?_
  rw [ChebyshevIVP.lpOneAlg.norm_eq_natFinSum_of_finSupp
    (data.G phi p₀ (ChebyshevIVP.StdChebIVPData.abar data) l) (2 * N + 2)
    (fun m => rfl)
    (fun n hn => by
      show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν_val) (↑n)
        (data.approxInverse.action
          (chebyshevIvpCoeffs phi p₀ (ChebyshevIVP.StdChebIVPData.abar data)) l n)‖ = 0
      rw [SystemBlockDiagData.action_tail _ _ _ _ (show N < n from by omega),
        F_abar_eq, FQ_eq_zero (show 2 * N + 1 < n from by omega)]
      simp [lpAlgRingData.ofReal_zero])]
  rw [Finset.sum_congr rfl fun (n : Fin (2 * N + 2 + 1)) _ => show
      ‖(data.G phi p₀ (ChebyshevIVP.StdChebIVPData.abar data) l) (↑(n : ℕ) : ℤ)‖
        = |data.approxInverse.action
            (chebyshevIvpCoeffs phi p₀ (ChebyshevIVP.StdChebIVPData.abar data)) l (n : ℕ)|
          * (ν_val : ℝ) ^ (n : ℕ) from by
    show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν_val) (↑(n : ℕ)) _‖ = _
    rw [ScaledRealZ.norm_lpAlgRingData_ofReal]
    simp]
  have hl : l = 0 := Subsingleton.elim l 0
  subst hl
  simp only [N]
  unfold Y₀_bound
  finsum_bound using (Y₀_eval 0) (fun k _ => Y₀_eval_correct 0 k _ (by norm_num)) 100

lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val data.defect.finBlock ≤ (Z₀_bound : ℝ) := by
  finmatrix_bound
    (finiteBlockMatrixNorm_le_of_Q_le _ defectBlockCols ν_q
      (fun l j k i => defectBlockCol_correct l j i k) ν_val_eq_q)

/-- Z₀ obligation of `chebyshev_system_theorem`, discharged. -/
lemma Z₀_le :
    ‖ContinuousLinearMap.id ℝ (XCheb ν_val L) - data.composedApproxCLM‖ ≤ (Z₀_bound : ℝ) :=
  data.Z₀_le Z₀_finBlockNorm_le

/-! ## Z₁ — the leakage bound

`‖composedApprox − DG(ā)‖ ≤ Z₁ = ε + ν/(N+1)·K` via `chebyshev_Z₁_le_relaxed`:
- negatives: both sides pass through (difference 0);
- tail (m > N): difference = −`chebyshevShiftDiv (Dφ(ā) h)`;
- finite modes: the ε-leakage, certified column-by-column in exact ℚ through
  the `l1Chebyshev.finsum_norm_le_of_cols` column-norm bound. Columns `m ≤ N`
  cancel exactly (the stored Jacobian IS the derivative), `N < m ≤ 2N+2`
  are the leaked Dφ couplings (worst ≈ 0.0034), `m > 2N+2` leaves only the
  row-0 alternating functional (geometric decay);
- `K` from `norm_Dphi_le` with `‖S(ā)‖ ≤ 39/50` (native_decide).
-/

local notation "ābar" => ChebyshevIVP.StdChebIVPData.abar data

/-! ### The Fin-1 collapse -/

private def ι : l1Chebyshev ν_val →L[ℝ] XCheb ν_val L :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ _

private lemma ι_eq (h : XCheb ν_val L) : ι (h 0) = h :=
  funext fun l => by rw [Subsingleton.elim l 0]; rfl

/-- The Z₁ operator, collapsed to a scalar-component CLM. -/
private def Trow : l1Chebyshev ν_val →L[ℝ] l1Chebyshev ν_val :=
  (ContinuousLinearMap.proj 0).comp
    (((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar)).comp ι)

private lemma Trow_eq (h : XCheb ν_val L) (l : Fin L) :
    ((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar) h) l = Trow (h l) := by
  rw [Subsingleton.elim l 0]
  conv_lhs => rw [← ι_eq h]
  rfl

/-! ### Pointwise values of the two sides -/

private lemma fiber_eq_zero {k : ℤ} (x : ScaledRealZ ν_val k)
    (hx : lpAlgRingData.toReal k x = 0) : x = 0 := by
  rw [← lpAlgRingData.ofReal_toReal k x, hx, lpAlgRingData.ofReal_zero]

private lemma composed_toSeq_nat (h : XCheb ν_val L) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (data.composedApproxCLM h l) (↑n : ℤ)
      = l1Chebyshev.toSeq (h l) (↑n : ℤ)
        - (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
            (toCoeffCheb h) l n := by
  show l1Chebyshev.toSeq ((h - defectCheb_apply _ h) l) (↑n : ℤ) = _
  show l1Chebyshev.toSeq (h l - defectCheb_apply _ h l) (↑n : ℤ) = _
  rw [l1Chebyshev.toSeq_sub]
  have hd : l1Chebyshev.toSeq (defectCheb_apply
      (defectOfBlockDiagOp data.approxInverse data.approxDeriv) h l) (↑n : ℤ)
      = (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
          (toCoeffCheb h) l n := by
    show lpAlgRingData.toReal (↑n : ℤ) (lpAlgRingData.ofReal (E := ScaledRealZ ν_val) (↑n)
      ((defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
        (toCoeffCheb h) l n)) = _
    rw [lpAlgRingData.toReal_ofReal]
  rw [hd]

private lemma composed_toSeq_neg (h : XCheb ν_val L) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (data.composedApproxCLM h l) (Int.negSucc m)
      = l1Chebyshev.toSeq (h l) (Int.negSucc m) := by
  show l1Chebyshev.toSeq ((h - defectCheb_apply _ h) l) (Int.negSucc m) = _
  show l1Chebyshev.toSeq (h l - defectCheb_apply _ h l) (Int.negSucc m) = _
  rw [l1Chebyshev.toSeq_sub]
  rw [show l1Chebyshev.toSeq (defectCheb_apply
      (defectOfBlockDiagOp data.approxInverse data.approxDeriv) h l) (Int.negSucc m)
    = 0 from lpAlgRingData.toReal_zero _]
  ring

/-- The derivative side, unfolded through the Λ-decomposition. -/
private lemma fderiv_toSeq (h : XCheb ν_val L) (l : Fin L) (k : ℤ) :
    l1Chebyshev.toSeq ((fderiv ℝ (data.G phi p₀) ābar h) l) k
      = l1Chebyshev.toSeq (data.TAfun h l) k
        + (l1Chebyshev.toSeq (data.TCblockFun (fun j => Dphi ābar h j) l) k
          + l1Chebyshev.toSeq (TCtailElem N (Dphi ābar h l)) k) := by
  rw [fderiv_G]
  show l1Chebyshev.toSeq (data.TA h l + data.TC (DPhiCLM ābar h) l) k = _
  rw [DPhiCLM_apply]
  show l1Chebyshev.toSeq (data.TAfun h l
    + (data.TCblockFun (fun j => Dphi ābar h j) l + TCtailElem N (Dphi ābar h l))) k = _
  rw [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_add]

/-! ### hneg: negatives pass through on both sides -/

private lemma Z₁_hneg (h : XCheb ν_val L) (l : Fin L) (m : ℕ) :
    (((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar) h) l) (Int.negSucc m)
      = 0 := by
  refine fiber_eq_zero _ ?_
  show l1Chebyshev.toSeq
    ((data.composedApproxCLM h - fderiv ℝ (data.G phi p₀) ābar h) l) (Int.negSucc m) = 0
  show l1Chebyshev.toSeq
    (data.composedApproxCLM h l - (fderiv ℝ (data.G phi p₀) ābar h) l) (Int.negSucc m) = 0
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_neg, fderiv_toSeq]
  rw [show l1Chebyshev.toSeq (data.TAfun h l) (Int.negSucc m)
      = l1Chebyshev.toSeq (h l) (Int.negSucc m) from data.TAfun_toSeq_neg h l m,
    data.TCblockFun_toSeq_neg, TCtailElem_toSeq_neg]
  ring

/-! ### htail: the difference is −shiftDiv(Dφ h) beyond mode N -/

private lemma Z₁_htail (h : XCheb ν_val L) (l : Fin L) (m : ℕ) (hm : N < m) :
    ‖(((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar) h) l) (↑m : ℤ)‖
      = ‖(chebyshevShiftDiv (Dphi ābar h l)) (↑m : ℤ)‖ := by
  have hval : l1Chebyshev.toSeq
      (((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar) h) l) (↑m : ℤ)
      = -(l1Chebyshev.toSeq (chebyshevShiftDiv (Dphi ābar h l)) (↑m : ℤ)) := by
    show l1Chebyshev.toSeq
      (data.composedApproxCLM h l - (fderiv ℝ (data.G phi p₀) ābar h) l) (↑m : ℤ) = _
    rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat, fderiv_toSeq]
    rw [show (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
        (toCoeffCheb h) l m = 0 from SystemBlockDiagData.actionFinite_tail _ _ _ _ hm]
    rw [data.TAfun_toSeq_nat, data.TA_action_tail_eq h l m hm,
      data.TCblockFun_toSeq_nat,
      show data.TCblockSeq (fun j => Dphi ābar h j) l m = 0 from data.TCblockSeq_tail _ l m hm,
      TCtailElem_toSeq_nat, if_pos hm]
    ring
  rw [l1Chebyshev.norm_fiber, l1Chebyshev.norm_fiber, hval, abs_neg]

/-! ### hDφ: the K bound with the certified ‖S(ā)‖ -/

/-- ℚ value of `‖S(ā)‖` (bilateral finite support `|k| ≤ N`). -/
private def SnormQ : ℚ :=
  (∑ n ∈ Finset.range (N + 1), |qbar n| * ν_q ^ n)
    + ∑ n ∈ Finset.range N, |qbar (n + 1)| * ν_q ^ (n + 1)

lemma Sabar_norm_le (l : Fin L) : ‖S (ābar l)‖ ≤ ((39/50 : ℚ) : ℝ) := by
  have hbilat := lpOneAlg.norm_eq_bilatFinSum (S (ābar l)) N
    (fun n hn => by
      rw [l1Chebyshev.norm_fiber, Sabar_toSeq,
        qbar_eq_zero (show N < ((n : ℕ) : ℤ).natAbs from by simpa using hn)]
      norm_num)
    (fun n hn => by
      rw [l1Chebyshev.norm_fiber, Sabar_toSeq,
        qbar_eq_zero (show N < (Int.negSucc n).natAbs from by
          simp [Int.natAbs_negSucc]
          omega)]
      norm_num)
  rw [hbilat]
  have hterm1 : ∀ n : Fin (N + 1), ‖(S (ābar l)) (↑(n : ℕ) : ℤ)‖
      = ((|qbar (n : ℕ)| * ν_q ^ (n : ℕ) : ℚ) : ℝ) := by
    intro n
    rw [l1Chebyshev.norm_fiber, Sabar_toSeq, ν_val_eq_q]
    push_cast
    simp
  have hterm2 : ∀ n : Fin N, ‖(S (ābar l)) (Int.negSucc (n : ℕ))‖
      = ((|qbar ((n : ℕ) + 1)| * ν_q ^ ((n : ℕ) + 1) : ℚ) : ℝ) := by
    intro n
    rw [l1Chebyshev.norm_fiber, Sabar_toSeq, ν_val_eq_q]
    rw [show (Int.negSucc (n : ℕ)).natAbs = (n : ℕ) + 1 from rfl]
    push_cast
    simp
  rw [Finset.sum_congr rfl fun n _ => hterm1 n,
    Finset.sum_congr rfl fun n _ => hterm2 n]
  have hcast : (∑ n : Fin (N + 1), ((|qbar (n : ℕ)| * ν_q ^ (n : ℕ) : ℚ) : ℝ))
      + ∑ n : Fin N, ((|qbar ((n : ℕ) + 1)| * ν_q ^ ((n : ℕ) + 1) : ℚ) : ℝ)
      = ((SnormQ : ℚ) : ℝ) := by
    rw [SnormQ]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun x => |(qbar x : ℝ)| * (2 : ℝ) ^ x) (N + 1),
      Fin.sum_univ_eq_sum_range (fun x => |(qbar (x + 1) : ℝ)| * (2 : ℝ) ^ (x + 1)) N]
  rw [hcast]
  exact_mod_cast (show SnormQ ≤ 39/50 from by native_decide)

private lemma Z₁_hDφ (h : XCheb ν_val L) (l : Fin L) :
    ‖Dphi ābar h l‖ ≤ ((K_bound : ℚ) : ℝ) * ‖h‖ := by
  refine (norm_Dphi_le ābar h l).trans ?_
  have hS := Sabar_norm_le l
  have h2 : (2 * ‖S (ābar l)‖ + 1) * (2 * ‖h‖)
      ≤ (2 * ((39/50 : ℚ) : ℝ) + 1) * (2 * ‖h‖) := by
    have : (0 : ℝ) ≤ 2 * ‖h‖ := by positivity
    nlinarith
  refine h2.trans (le_of_eq ?_)
  rw [show ((K_bound : ℚ) : ℝ) = (2 * ((39/50 : ℚ) : ℝ) + 1) * 2 from by
    norm_num [K_bound]]
  ring

/-! ### hfin_le: the ε-leakage, column by column in exact ℚ -/

private def AQ (n k : ℕ) : ℚ := (A_col 0 0 k).getD n 0

/-- Column `mn` of the linear-in-`a` rows on the basis vector `e_mn`. -/
private def FAcolQ (mn : ℕ) : ℕ → ℚ
  | 0 => if mn = 0 then -1 else -2 * (-1 : ℚ) ^ mn
  | (k + 1) => if k + 1 = mn then 2 * ((k : ℚ) + 1) else 0

/-- `∂c_j/∂a_mn` — the Dφ(ā) coupling of stored mode `mn` into fold mode `j`. -/
private def wQ (mn j : ℕ) : ℚ :=
  2 * (if mn = 0 then qbar j else qbar ((j : ℤ) - mn).natAbs + qbar (j + mn))
    - (if j = mn then 1 else 0)

private def FCcolQ (mn : ℕ) : ℕ → ℚ
  | 0 => 0
  | (k + 1) => wQ mn (k + 2) - wQ mn k

private def defQ (n k : Fin (N + 1)) : ℚ :=
  blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) 0 0 n k

/-- Column `mn` of `composedApprox − DG(ā)` at the block rows, in exact ℚ. -/
private def DcolQ (mn : ℕ) (n : Fin (N + 1)) : ℚ :=
  ((if (n : ℕ) = mn then 1 else 0) - (if h : mn ≤ N then defQ n ⟨mn, by omega⟩ else 0))
    - ∑ k : Fin (N + 1), AQ (n : ℕ) (k : ℕ) * (FAcolQ mn (k : ℕ) + FCcolQ mn (k : ℕ))

private def colNormQ (mn : ℕ) : ℚ := ∑ n : Fin (N + 1), |DcolQ mn n| * ν_q ^ (n : ℕ)

/-- The near columns (`mn ≤ 2N+2`), certified numerically: columns `mn ≤ N`
cancel exactly, the leaked columns stay under ε. -/
private lemma colNormQ_le_small : ∀ mn : ℕ, mn < 2 * N + 3 →
    colNormQ mn ≤ eps_bound * ν_q ^ mn := by native_decide

private def rowA0Q : ℚ := 2 * ∑ n : Fin (N + 1), |AQ (n : ℕ) 0| * ν_q ^ (n : ℕ)

private lemma rowA0Q_le : rowA0Q ≤ eps_bound * ν_q ^ (2 * N + 3) := by native_decide

/-- Beyond `2N+2` only the row-0 alternating functional survives. -/
private lemma colNormQ_far {mn : ℕ} (hmn : 2 * N + 2 < mn) : colNormQ mn = rowA0Q := by
  have hNn : N = 40 := rfl
  have hw : ∀ j : ℕ, j ≤ N + 2 → wQ mn j = 0 := by
    intro j hj
    rw [wQ, if_neg (by omega), if_neg (by omega)]
    rw [qbar_eq_zero (show N < ((j : ℤ) - mn).natAbs from by omega),
      qbar_eq_zero (show N < j + mn from by omega)]
    ring
  have hcol : ∀ n : Fin (N + 1), DcolQ mn n = 2 * (-1 : ℚ) ^ mn * AQ (n : ℕ) 0 := by
    intro n
    rw [DcolQ, if_neg (by omega), dif_neg (by omega)]
    rw [Finset.sum_eq_single (0 : Fin (N + 1))
      (fun k _ hk => ?_) (fun habs => absurd (Finset.mem_univ _) habs)]
    · rw [show FAcolQ mn ((0 : Fin (N + 1)) : ℕ) = -2 * (-1 : ℚ) ^ mn from by
        show FAcolQ mn 0 = _
        rw [show FAcolQ mn 0 = if mn = 0 then -1 else -2 * (-1 : ℚ) ^ mn from rfl,
          if_neg (by omega)]]
      rw [show FCcolQ mn ((0 : Fin (N + 1)) : ℕ) = 0 from rfl]
      simp only [Fin.val_zero]
      ring
    · -- k ≠ 0: FAcolQ and FCcolQ both vanish
      have hk1 : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
      have hk0 : (k : ℕ) ≠ 0 := fun habs => hk (Fin.ext habs)
      obtain ⟨kv, hkv⟩ : ∃ kv, (k : ℕ) = kv + 1 := ⟨(k : ℕ) - 1, by omega⟩
      rw [hkv]
      rw [show FAcolQ mn (kv + 1) = if kv + 1 = mn then 2 * ((kv : ℚ) + 1) else 0 from rfl,
        if_neg (by omega),
        show FCcolQ mn (kv + 1) = wQ mn (kv + 2) - wQ mn kv from rfl,
        hw (kv + 2) (by omega), hw kv (by omega)]
      ring
  rw [colNormQ, Finset.sum_congr rfl fun n _ => by rw [hcol n]]
  rw [rowA0Q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    show |(2 : ℚ)| = 2 from by norm_num]
  ring

/-- ℚ certification of every column. -/
private lemma colNormQ_le (mn : ℕ) : colNormQ mn ≤ eps_bound * ν_q ^ mn := by
  rcases lt_or_ge mn (2 * N + 3) with hmn | hmn
  · exact colNormQ_le_small mn hmn
  · rw [colNormQ_far (by omega)]
    refine rowA0Q_le.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num [eps_bound])
    exact pow_le_pow_right₀ (by norm_num [ν_q]) (by omega)

/-! ### The analytic column bridge -/

private lemma toCoeff_single (mn : ℕ) (j : Fin L) (k' : ℕ) :
    toCoeffCheb (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) j k' = if k' = mn then 1 else 0 := by
  show l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑k' : ℤ) = _
  rw [l1Chebyshev.toSeq_single]
  by_cases h : k' = mn
  · rw [if_pos (by exact_mod_cast h), if_pos h]
  · rw [if_neg (fun hc => h (by exact_mod_cast hc)), if_neg h]

private lemma defect_actionFinite_single_le {mn : ℕ} (hmn : mn ≤ N) (n : ℕ) (hn : n ≤ N) :
    (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
        (toCoeffCheb (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1))) 0 n
      = ((defQ ⟨n, by omega⟩ ⟨mn, by omega⟩ : ℚ) : ℝ) := by
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn, Fin.sum_univ_one]
  rw [Finset.sum_eq_single (⟨mn, by omega⟩ : Fin (N + 1)) (fun k _ hk => ?_)
    (fun habs => absurd (Finset.mem_univ _) habs)]
  · rw [toCoeff_single, if_pos rfl, mul_one]
    have hbr := defectBlockCol_correct 0 0 ⟨n, by omega⟩ ⟨mn, by omega⟩
    rw [defectBlockCols, Array.getD_ofFn_fin] at hbr
    exact hbr
  · rw [toCoeff_single, if_neg (fun habs => hk (Fin.ext habs)), mul_zero]

private lemma defect_actionFinite_single_gt {mn : ℕ} (hmn : N < mn) (n : ℕ) (hn : n ≤ N) :
    (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
        (toCoeffCheb (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1))) 0 n = 0 := by
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [toCoeff_single, if_neg (show ¬((k : ℕ) = mn) from by
    have := k.isLt
    omega), mul_zero]

private lemma FAseq_single (mn k : ℕ) :
    FAseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) k = (FAcolQ mn k : ℝ) := by
  cases k with
  | zero =>
    rw [show FAseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0
        = -(l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0)
          - 2 * ∑' j : ℕ, (-1 : ℝ) ^ (j + 1)
            * l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑(j + 1) : ℤ) from rfl]
    cases mn with
    | zero =>
      have h0 : l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν_val) ((0 : ℕ) : ℤ) 1) 0 = 1 := by
        rw [l1Chebyshev.toSeq_single, if_pos (by norm_num)]
      have hz : ∀ j : ℕ, (-1 : ℝ) ^ (j + 1)
          * l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν_val) ((0 : ℕ) : ℤ) 1)
              (↑(j + 1) : ℤ) = 0 := by
        intro j
        rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
        ring
      rw [h0, tsum_congr hz, tsum_zero]
      rw [show FAcolQ 0 0 = -1 from rfl]
      norm_num
    | succ m' =>
      have h0 : l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν_val) ((m' + 1 : ℕ) : ℤ) 1)
          0 = 0 := by
        rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
      have htsum : ∑' j : ℕ, (-1 : ℝ) ^ (j + 1)
          * l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν_val) ((m' + 1 : ℕ) : ℤ) 1)
              (↑(j + 1) : ℤ)
          = (-1 : ℝ) ^ (m' + 1) := by
        rw [tsum_eq_single m' (fun j hj => by
          rw [l1Chebyshev.toSeq_single, if_neg (fun hc => hj (by omega))]
          ring)]
        rw [l1Chebyshev.toSeq_single, if_pos rfl, mul_one]
      rw [h0, htsum]
      rw [show FAcolQ (m' + 1) 0
          = if m' + 1 = 0 then -1 else -2 * (-1 : ℚ) ^ (m' + 1) from rfl,
        if_neg (Nat.succ_ne_zero m')]
      push_cast
      ring
  | succ k' =>
    rw [show FAseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (k' + 1)
        = 2 * ((k' : ℝ) + 1)
          * l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑(k' + 1) : ℤ) from rfl]
    rw [l1Chebyshev.toSeq_single]
    rw [show FAcolQ mn (k' + 1)
        = if k' + 1 = mn then 2 * ((k' : ℚ) + 1) else 0 from rfl]
    by_cases h : k' + 1 = mn
    · rw [if_pos (by exact_mod_cast h), if_pos h]
      push_cast
      ring
    · rw [if_neg (fun hc => h (by exact_mod_cast hc)), if_neg h]
      push_cast
      ring

private lemma S_single_toSeq (mn : ℕ) (i : ℤ) :
    l1Chebyshev.toSeq (S (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) i
      = if i.natAbs = mn then 1 else 0 := by
  rw [S_apply, Ssym_toSeq, l1Chebyshev.toSeq_single]
  by_cases h : i.natAbs = mn
  · rw [if_pos (by exact_mod_cast h), if_pos h]
  · rw [if_neg (fun hc => h (by exact_mod_cast hc)), if_neg h]

private lemma conv_single_toSeq (mn j : ℕ) :
    l1Chebyshev.toSeq (S (ābar 0) * S (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) (↑j : ℤ)
      = (if mn = 0 then (qbar j : ℝ)
         else (qbar ((j : ℤ) - mn).natAbs : ℝ) + (qbar (j + mn) : ℝ)) := by
  cases mn with
  | zero =>
    rw [l1Chebyshev.toSeq_mul_eq_finsum _ _ _ ({(0 : ℤ)} : Finset ℤ) (fun i hi => by
      rw [S_single_toSeq, if_neg (fun hc => hi (by
        simp only [Finset.mem_singleton]
        omega))])]
    rw [Finset.sum_singleton, S_single_toSeq,
      if_pos (show ((0 : ℤ)).natAbs = 0 from rfl), mul_one, Sabar_toSeq,
      if_pos (rfl : (0 : ℕ) = 0)]
    congr 1
  | succ m' =>
    rw [l1Chebyshev.toSeq_mul_eq_finsum _ _ _
      ({((m' + 1 : ℕ) : ℤ), -((m' + 1 : ℕ) : ℤ)} : Finset ℤ) (fun i hi => by
      rw [S_single_toSeq, if_neg (fun hc => hi (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega))])]
    rw [Finset.sum_pair (by omega)]
    rw [S_single_toSeq, if_pos (show (((m' + 1 : ℕ) : ℤ)).natAbs = m' + 1 from by omega),
      S_single_toSeq, if_pos (show (-((m' + 1 : ℕ) : ℤ)).natAbs = m' + 1 from by omega),
      mul_one, mul_one, Sabar_toSeq, Sabar_toSeq]
    rw [if_neg (Nat.succ_ne_zero m')]
    congr 2

private lemma Dphi_single_toSeq (mn j : ℕ) :
    l1Chebyshev.toSeq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (↑j : ℤ)
      = (wQ mn j : ℝ) := by
  show l1Chebyshev.toSeq ((2 : ℝ) • (S (ābar 0) * S (l1Chebyshev.single ((mn : ℕ) : ℤ) 1))
      - S (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) (↑j : ℤ) = _
  rw [l1Chebyshev.toSeq_sub, l1Chebyshev.toSeq_smul, conv_single_toSeq, S_single_toSeq]
  rw [show ((↑j : ℤ)).natAbs = j from by omega]
  rw [wQ]
  push_cast [apply_ite (fun q : ℚ => (q : ℝ))]
  ring

private lemma FCseq_Dphi_single (mn k : ℕ) :
    FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) k = (FCcolQ mn k : ℝ) := by
  cases k with
  | zero =>
    rw [show FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) 0 = 0 from rfl,
      show FCcolQ mn 0 = 0 from rfl]
    norm_num
  | succ k' =>
    rw [show FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (k' + 1)
        = l1Chebyshev.toSeq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0)
            (↑(k' + 2) : ℤ)
          - l1Chebyshev.toSeq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0)
            (↑k' : ℤ) from rfl]
    rw [Dphi_single_toSeq, Dphi_single_toSeq,
      show FCcolQ mn (k' + 1) = wQ mn (k' + 2) - wQ mn k' from rfl]
    push_cast
    ring

/-- The full analytic column bridge at block rows. -/
private lemma Trow_single_toSeq (mn : ℕ) (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (Trow (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) (↑n : ℤ)
      = (DcolQ mn ⟨n, by omega⟩ : ℝ) := by
  show l1Chebyshev.toSeq
    (((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar)
      (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1))) 0) (↑n : ℤ) = _
  show l1Chebyshev.toSeq
    (data.composedApproxCLM (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0
      - (fderiv ℝ (data.G phi p₀) ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1))) 0)
    (↑n : ℤ) = _
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat, fderiv_toSeq]
  -- the four pieces
  rw [show l1Chebyshev.toSeq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0) (↑n : ℤ)
      = (if n = mn then (1 : ℝ) else 0) from by
    show l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑n : ℤ) = _
    rw [l1Chebyshev.toSeq_single]
    by_cases h : n = mn
    · rw [if_pos (by exact_mod_cast h), if_pos h]
    · rw [if_neg (fun hc => h (by exact_mod_cast hc)), if_neg h]]
  rw [data.TAfun_toSeq_nat, SystemBlockDiagData.action_finite _ _ _ _ hn, Fin.sum_univ_one]
  rw [data.TCblockFun_toSeq_nat]
  rw [show data.TCblockSeq (fun j => Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) j) 0 n
      = ∑ k : Fin (N + 1),
          data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
            * FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (k : ℕ) from by
    show data.approxInverse.actionFinite
      (fun j => FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) j)) 0 n = _
    rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn, Fin.sum_univ_one]]
  rw [TCtailElem_toSeq_nat, if_neg (not_lt.mpr hn), add_zero]
  have hA : ∀ k : Fin (N + 1),
      data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
        = ((AQ n (k : ℕ) : ℚ) : ℝ) := fun k =>
    data.A_finBlock_eq 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
  have hFA : ∀ k : Fin (N + 1),
      FAseq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0) (k : ℕ)
        = ((FAcolQ mn (k : ℕ) : ℚ) : ℝ) := fun k => FAseq_single mn (k : ℕ)
  have hFC : ∀ k : Fin (N + 1),
      FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (k : ℕ)
        = ((FCcolQ mn (k : ℕ) : ℚ) : ℝ) := fun k => FCseq_Dphi_single mn (k : ℕ)
  have hsumFA : (∑ k : Fin (N + 1),
      data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
        * FAseq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0) (k : ℕ))
      = ∑ k : Fin (N + 1), ((AQ n (k : ℕ) : ℚ) : ℝ) * ((FAcolQ mn (k : ℕ) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [hA k, hFA k]
  have hsumFC : (∑ k : Fin (N + 1),
      data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
        * FCseq (Dphi ābar (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (k : ℕ))
      = ∑ k : Fin (N + 1), ((AQ n (k : ℕ) : ℚ) : ℝ) * ((FCcolQ mn (k : ℕ) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [hA k, hFC k]
  rw [hsumFA, hsumFC]
  -- assemble against DcolQ
  rw [DcolQ]
  push_cast [apply_dite (fun q : ℚ => (q : ℝ)), apply_ite (fun q : ℚ => (q : ℝ))]
  rw [show (∑ k : Fin (N + 1),
      ((AQ n (k : ℕ) : ℝ)) * ((FAcolQ mn (k : ℕ) : ℝ) + (FCcolQ mn (k : ℕ) : ℝ)))
      = (∑ k : Fin (N + 1), (AQ n (k : ℕ) : ℝ) * (FAcolQ mn (k : ℕ) : ℝ))
        + ∑ k : Fin (N + 1), (AQ n (k : ℕ) : ℝ) * (FCcolQ mn (k : ℕ) : ℝ) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring]
  by_cases hmn : mn ≤ N
  · rw [defect_actionFinite_single_le hmn n hn, dif_pos hmn]
  · rw [defect_actionFinite_single_gt (by omega) n hn, dif_neg hmn]

private lemma toSeq_zeroE (k : ℤ) : l1Chebyshev.toSeq (0 : l1Chebyshev ν_val) k = 0 := by
  have h := l1Chebyshev.toSeq_smul 0 (0 : l1Chebyshev ν_val) k
  rw [zero_smul] at h
  rw [h, zero_mul]

/-- Negative columns vanish: the nonlinearity reads only non-negative modes. -/
private lemma Trow_negSucc_toSeq (m' : ℕ) (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (Trow (l1Chebyshev.single (Int.negSucc m') 1)) (↑n : ℤ) = 0 := by
  have hSe : S (l1Chebyshev.single (ν := ν_val) (Int.negSucc m') 1) = 0 := by
    apply lpOneAlg.ext_toRealSeq
    funext i
    show l1Chebyshev.toSeq (S (l1Chebyshev.single (Int.negSucc m') 1)) i
      = lpOneAlg.toRealSeq (0 : l1Chebyshev ν_val) i
    rw [S_apply, Ssym_toSeq, l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
    exact (toSeq_zeroE i).symm
  have hDzero : Dphi ābar (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0 = 0 := by
    show (2 : ℝ) • (S (ābar 0) * S (l1Chebyshev.single (Int.negSucc m') 1))
      - S (l1Chebyshev.single (Int.negSucc m') 1) = 0
    rw [hSe, mul_zero, smul_zero, sub_zero]
  have hFC : ∀ k : ℕ,
      FCseq (Dphi ābar (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0) k = 0 := by
    intro k
    rw [hDzero]
    cases k with
    | zero => rfl
    | succ k' =>
      show l1Chebyshev.toSeq (0 : l1Chebyshev ν_val) (↑(k' + 2) : ℤ)
        - l1Chebyshev.toSeq (0 : l1Chebyshev ν_val) (↑k' : ℤ) = 0
      rw [toSeq_zeroE, toSeq_zeroE, sub_zero]
  have hFA : ∀ k : ℕ, FAseq (ι (l1Chebyshev.single (Int.negSucc m') 1) 0) k = 0 := by
    intro k
    cases k with
    | zero =>
      show -(l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) 0)
        - 2 * ∑' j : ℕ, (-1 : ℝ) ^ (j + 1)
          * l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑(j + 1) : ℤ) = 0
      rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
      rw [tsum_congr (fun j : ℕ => show (-1 : ℝ) ^ (j + 1)
          * l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν_val) (Int.negSucc m') 1)
              (↑(j + 1) : ℤ) = 0 from by
        rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
        ring), tsum_zero]
      ring
    | succ k' =>
      show 2 * ((k' : ℝ) + 1)
        * l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑(k' + 1) : ℤ) = 0
      rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
      ring
  show l1Chebyshev.toSeq
    (data.composedApproxCLM (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0
      - (fderiv ℝ (data.G phi p₀) ābar (ι (l1Chebyshev.single (Int.negSucc m') 1))) 0)
    (↑n : ℤ) = 0
  rw [l1Chebyshev.toSeq_sub, composed_toSeq_nat, fderiv_toSeq]
  rw [show l1Chebyshev.toSeq (ι (l1Chebyshev.single (Int.negSucc m') 1) 0) (↑n : ℤ) = 0 from by
    show l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑n : ℤ) = _
    rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]]
  rw [show (defectOfBlockDiagOp data.approxInverse data.approxDeriv).actionFinite
      (toCoeffCheb (ι (l1Chebyshev.single (Int.negSucc m') 1))) 0 n = 0 from by
    rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [show toCoeffCheb (ι (l1Chebyshev.single (Int.negSucc m') 1)) j (k : ℕ) = 0 from by
      show l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑(k : ℕ) : ℤ) = _
      rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)], mul_zero]]
  rw [data.TAfun_toSeq_nat, SystemBlockDiagData.action_finite _ _ _ _ hn, Fin.sum_univ_one]
  have hsA : (∑ k : Fin (N + 1),
      data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
        * FAseq (ι (l1Chebyshev.single (Int.negSucc m') 1) 0) (k : ℕ)) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hFA (k : ℕ), mul_zero]
  rw [hsA]
  rw [data.TCblockFun_toSeq_nat]
  have hsC : data.TCblockSeq
      (fun j => Dphi ābar (ι (l1Chebyshev.single (Int.negSucc m') 1)) j) 0 n = 0 := by
    show data.approxInverse.actionFinite
      (fun j => FCseq (Dphi ābar (ι (l1Chebyshev.single (Int.negSucc m') 1)) j)) 0 n = _
    rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [Subsingleton.elim j (0 : Fin L), hFC (k : ℕ), mul_zero]
  rw [hsC]
  rw [TCtailElem_toSeq_nat, if_neg (not_lt.mpr hn)]
  ring

/-- The per-column bound feeding the column-norm lemma. -/
private lemma Trow_col_le (m : ℤ) :
    ∑ n : Fin (N + 1), ‖(Trow (l1Chebyshev.single m 1)) ((↑(n : ℕ)) : ℤ)‖
      ≤ ((eps_bound : ℚ) : ℝ) * (ν_val : ℝ) ^ m.natAbs := by
  cases m with
  | ofNat mn =>
    have hterm : ∀ n : Fin (N + 1),
        ‖(Trow (l1Chebyshev.single (Int.ofNat mn) 1)) ((↑(n : ℕ)) : ℤ)‖
          = ((|DcolQ mn n| * ν_q ^ (n : ℕ) : ℚ) : ℝ) := by
      intro n
      rw [l1Chebyshev.norm_fiber]
      rw [show l1Chebyshev.toSeq (Trow (l1Chebyshev.single (Int.ofNat mn) 1)) (↑(n : ℕ) : ℤ)
          = ((DcolQ mn ⟨(n : ℕ), n.isLt⟩ : ℚ) : ℝ) from
        Trow_single_toSeq mn (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
      rw [ν_val_eq_q, Fin.eta]
      push_cast
      rw [show ((↑(n : ℕ) : ℤ)).natAbs = (n : ℕ) from by omega]
    rw [Finset.sum_congr rfl fun n _ => hterm n]
    have hsum : (∑ n : Fin (N + 1), ((|DcolQ mn n| * ν_q ^ (n : ℕ) : ℚ) : ℝ))
        = ((colNormQ mn : ℚ) : ℝ) := by
      rw [colNormQ]
      push_cast
      rfl
    rw [hsum]
    have hcast : ((colNormQ mn : ℚ) : ℝ) ≤ ((eps_bound * ν_q ^ mn : ℚ) : ℝ) := by
      exact_mod_cast colNormQ_le mn
    refine hcast.trans (le_of_eq ?_)
    rw [ν_val_eq_q]
    push_cast
    rw [show ((Int.ofNat mn)).natAbs = mn from rfl]
  | negSucc m' =>
    have hterm : ∀ n : Fin (N + 1),
        ‖(Trow (l1Chebyshev.single (Int.negSucc m') 1)) ((↑(n : ℕ)) : ℤ)‖ = 0 := by
      intro n
      rw [l1Chebyshev.norm_fiber, Trow_negSucc_toSeq m' (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
      norm_num
    rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_const, smul_zero]
    exact mul_nonneg (by norm_num [eps_bound]) (pow_nonneg ν_val.2.le _)

private lemma Z₁_hfin (h : XCheb ν_val L) (l : Fin L) :
    ∑ k : Fin (N + 1),
        ‖(((data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar) h) l)
          (↑(k : ℕ) : ℤ)‖
      ≤ ((eps_bound : ℚ) : ℝ) * ‖h‖ := by
  rw [Trow_eq h l]
  refine (l1Chebyshev.finsum_norm_le_of_cols Trow N Trow_col_le (h l)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm h l) (by norm_num [eps_bound])

/-- **Z₁ obligation**: `‖composedApprox − DG(ā)‖ ≤ Z₁ = ε + ν/(N+1)·K`. -/
lemma Z₁_le :
    ‖data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar‖ ≤ ((Z₁_bound : ℚ) : ℝ) := by
  refine chebyshev_Z₁_le_relaxed N data.composedApproxCLM (data.G phi p₀) ābar
    (fun h l => Dphi ābar h l) Z₁_hneg (by norm_num [eps_bound]) Z₁_hfin Z₁_htail
    (by norm_num [K_bound]) Z₁_hDφ ?_
  rw [show ((ν_val : ℝ)) = 2 from rfl]
  norm_num [eps_bound, K_bound, Z₁_bound, N]

/-- **Semi-major Z₁ bound**: `‖composedApprox − DG(ā)‖ ≤ ε + (ν⁻¹+ν)/(2(N+1))·K ≤ 0.16`,
via `chebyshev_Z₁_le_semiMajor` with the same four obligations as `Z₁_le`
(0.0035 + (1.25/41)·5.12 = 0.1596…). Additive: `Z₁_le` and `Z₁_bound` are unchanged. -/
theorem Z₁_le_semiMajor :
    ‖data.composedApproxCLM - fderiv ℝ (data.G phi p₀) ābar‖
      ≤ ((Z₁_semiMajor_bound : ℚ) : ℝ) := by
  refine chebyshev_Z₁_le_semiMajor N data.composedApproxCLM (data.G phi p₀) ābar
    (fun h l => Dphi ābar h l) Z₁_hneg (by norm_num [eps_bound]) Z₁_hfin Z₁_htail
    (by norm_num [K_bound]) Z₁_hDφ ?_
  rw [show ((ν_val : ℝ)) = 2 from rfl]
  norm_num [eps_bound, K_bound, Z₁_semiMajor_bound, N]

/-! ## Z₂ — Lipschitz bound on DG via the sharp ‖TC‖ ≤ 7/4

`DG(c) − DG(ā) = TC ∘ (DΦ(c) − DΦ(ā))` and the difference of derivatives is
`h ↦ 2·S((c−ā)ₗ)·S(hₗ)`, of norm ≤ 8‖c−ā‖‖h‖. The block part of TC is
certified columnwise in ℚ (≤ 2/5), the tail carries `ν/2 + 1/(2ν) = 5/4`. -/

/-- Column `mn` of the raw `c`-rows (`c_{k+2} − c_k`) on the basis vector. -/
private def FCe (mn : ℕ) : ℕ → ℚ
  | 0 => 0
  | (k + 1) => (if k + 2 = mn then 1 else 0) - (if k = mn then 1 else 0)

private def TCcolQ (mn : ℕ) (n : Fin (N + 1)) : ℚ :=
  ∑ k : Fin (N + 1), AQ (n : ℕ) (k : ℕ) * FCe mn (k : ℕ)

private def TCcolNormQ (mn : ℕ) : ℚ := ∑ n : Fin (N + 1), |TCcolQ mn n| * ν_q ^ (n : ℕ)

/-- The full TC column budget: `7/4 − ν/(N+1) = 7/4 − 2/41 = 279/164`.
The worst block column (`mn = 0`, ≈ 1.6471) fits under it. -/
private lemma TCcolNormQ_le_small : ∀ mn : ℕ, mn < N + 2 →
    TCcolNormQ mn ≤ (279/164) * ν_q ^ mn := by native_decide

private lemma TCcolNormQ_le (mn : ℕ) : TCcolNormQ mn ≤ (279/164) * ν_q ^ mn := by
  rcases lt_or_ge mn (N + 2) with hmn | hmn
  · exact TCcolNormQ_le_small mn hmn
  · have hz : TCcolNormQ mn = 0 := by
      rw [TCcolNormQ]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [show TCcolQ mn n = 0 from Finset.sum_eq_zero fun k _ => ?_, abs_zero, zero_mul]
      have hk1 : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
      rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
      · rw [hk, show FCe mn 0 = 0 from rfl, mul_zero]
      · obtain ⟨kv, hkv⟩ : ∃ kv, (k : ℕ) = kv + 1 := ⟨(k : ℕ) - 1, by omega⟩
        rw [hkv, show FCe mn (kv + 1)
            = (if kv + 2 = mn then 1 else 0) - (if kv = mn then 1 else 0) from rfl,
          if_neg (by omega), if_neg (by omega)]
        ring
    rw [hz]
    positivity

/-- The block part of TC, collapsed to a scalar-component CLM. -/
private def TCrow : l1Chebyshev ν_val →L[ℝ] l1Chebyshev ν_val :=
  (ContinuousLinearMap.proj 0).comp (data.TCblock.comp ι)

private lemma FCseq_single (mn k : ℕ) :
    FCseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) k = (FCe mn k : ℝ) := by
  cases k with
  | zero =>
    rw [show FCseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0 = 0 from rfl,
      show FCe mn 0 = 0 from rfl]
    norm_num
  | succ k' =>
    rw [show FCseq (ν := ν_val) (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (k' + 1)
        = l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑(k' + 2) : ℤ)
          - l1Chebyshev.toSeq (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) (↑k' : ℤ) from rfl,
      show FCe mn (k' + 1)
        = (if k' + 2 = mn then 1 else 0) - (if k' = mn then 1 else 0) from rfl]
    rw [l1Chebyshev.toSeq_single, l1Chebyshev.toSeq_single]
    push_cast [apply_ite (fun q : ℚ => (q : ℝ))]
    by_cases h1 : k' + 2 = mn
    · rw [if_pos h1, if_pos (by exact_mod_cast h1)]
      by_cases h2 : k' = mn
      · rw [if_pos h2, if_pos (by exact_mod_cast h2)]
      · rw [if_neg h2, if_neg (fun hc => h2 (by exact_mod_cast hc))]
    · rw [if_neg h1, if_neg (fun hc => h1 (by exact_mod_cast hc))]
      by_cases h2 : k' = mn
      · rw [if_pos h2, if_pos (by exact_mod_cast h2)]
      · rw [if_neg h2, if_neg (fun hc => h2 (by exact_mod_cast hc))]

private lemma TCrow_single_toSeq (mn : ℕ) (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (TCrow (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) (↑n : ℤ)
      = (TCcolQ mn ⟨n, Nat.lt_succ_of_le hn⟩ : ℝ) := by
  show l1Chebyshev.toSeq (data.TCblockFun (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) (↑n : ℤ) = _
  rw [data.TCblockFun_toSeq_nat]
  rw [show data.TCblockSeq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0 n
      = ∑ k : Fin (N + 1),
          data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
            * FCseq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0) (k : ℕ) from by
    show data.approxInverse.actionFinite
      (fun j => FCseq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) j)) 0 n = _
    rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn, Fin.sum_univ_one]]
  have hA : ∀ k : Fin (N + 1),
      data.approxInverse.finBlock 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
        = ((AQ n (k : ℕ) : ℚ) : ℝ) := fun k =>
    data.A_finBlock_eq 0 0 ⟨n, Nat.lt_succ_of_le hn⟩ k
  have hF : ∀ k : Fin (N + 1),
      FCseq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1) 0) (k : ℕ)
        = ((FCe mn (k : ℕ) : ℚ) : ℝ) := fun k => FCseq_single mn (k : ℕ)
  rw [Finset.sum_congr rfl fun k _ => by rw [hA k, hF k]]
  rw [TCcolQ]
  push_cast
  rfl

private lemma TCrow_negSucc_toSeq (m' : ℕ) (n : ℕ) (hn : n ≤ N) :
    l1Chebyshev.toSeq (TCrow (l1Chebyshev.single (Int.negSucc m') 1)) (↑n : ℤ) = 0 := by
  have hF : ∀ k : ℕ, FCseq (ι (l1Chebyshev.single (Int.negSucc m') 1) 0) k = 0 := by
    intro k
    cases k with
    | zero => rfl
    | succ k' =>
      show l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑(k' + 2) : ℤ)
        - l1Chebyshev.toSeq (l1Chebyshev.single (Int.negSucc m') 1) (↑k' : ℤ) = 0
      rw [l1Chebyshev.toSeq_single, if_neg (fun hc => by omega),
        l1Chebyshev.toSeq_single, if_neg (fun hc => by omega)]
      ring
  show l1Chebyshev.toSeq (data.TCblockFun (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0) (↑n : ℤ) = 0
  rw [data.TCblockFun_toSeq_nat]
  show data.approxInverse.actionFinite
    (fun j => FCseq (ι (l1Chebyshev.single (Int.negSucc m') 1) j)) 0 n = 0
  rw [SystemBlockDiagData.actionFinite_finite _ _ _ _ hn]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Subsingleton.elim j (0 : Fin L), hF (k : ℕ), mul_zero]

/-- Exact block-column norm (finite support, evaluated in ℚ). -/
private lemma TCblock_col_norm (mn : ℕ) :
    ‖data.TCblockFun (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0‖ = ((TCcolNormQ mn : ℚ) : ℝ) := by
  rw [ChebyshevIVP.lpOneAlg.norm_eq_natFinSum_of_finSupp
    (data.TCblockFun (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) N
    (fun m => rfl)
    (fun n hn => by
      show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν_val) (↑n)
        (data.TCblockSeq (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0 n)‖ = 0
      rw [data.TCblockSeq_tail _ _ n hn, lpAlgRingData.ofReal_zero, norm_zero])]
  have hterm : ∀ n : Fin (N + 1),
      ‖(data.TCblockFun (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0) ((↑(n : ℕ)) : ℤ)‖
        = ((|TCcolQ mn n| * ν_q ^ (n : ℕ) : ℚ) : ℝ) := by
    intro n
    rw [l1Chebyshev.norm_fiber]
    rw [show l1Chebyshev.toSeq (data.TCblockFun (ι (l1Chebyshev.single ((mn : ℕ) : ℤ) 1)) 0)
        (↑(n : ℕ) : ℤ) = ((TCcolQ mn ⟨(n : ℕ), n.isLt⟩ : ℚ) : ℝ) from
      TCrow_single_toSeq mn (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
    rw [ν_val_eq_q, Fin.eta]
    push_cast
    rw [show ((↑(n : ℕ) : ℤ)).natAbs = (n : ℕ) from by omega]
  rw [Finset.sum_congr rfl fun n _ => hterm n, TCcolNormQ]
  push_cast
  rfl

private lemma TCblock_col_neg (m' : ℕ) :
    ‖data.TCblockFun (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0‖ = 0 := by
  rw [ChebyshevIVP.lpOneAlg.norm_eq_natFinSum_of_finSupp
    (data.TCblockFun (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0) N
    (fun m => rfl)
    (fun n hn => by
      show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν_val) (↑n)
        (data.TCblockSeq (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0 n)‖ = 0
      rw [data.TCblockSeq_tail _ _ n hn, lpAlgRingData.ofReal_zero, norm_zero])]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [l1Chebyshev.norm_fiber,
    show l1Chebyshev.toSeq (data.TCblockFun (ι (l1Chebyshev.single (Int.negSucc m') 1)) 0)
      (↑(n : ℕ) : ℤ) = 0 from
    TCrow_negSucc_toSeq m' (n : ℕ) (Nat.lt_succ_iff.mp n.isLt)]
  norm_num

/-- The tail part of a column is dominated by the shift-div tail tsum. -/
private lemma TCtailElem_norm_le_tail (v : l1Chebyshev ν_val) :
    ‖TCtailElem N v‖ ≤ (ν_val : ℝ) / ((N : ℝ) + 1) * ‖v‖ := by
  set g : ℤ → ℝ := fun k => ‖(TCtailElem N v) k‖ with hg_def
  have hg_summ : Summable g := lpOneAlg.summable_norm (TCtailElem N v)
  have h_nat : Summable (fun n : ℕ => g ↑n) :=
    hg_summ.comp_injective fun n m h => by simpa using h
  have h_neg : Summable (fun n : ℕ => g (-(↑n + 1))) :=
    hg_summ.comp_injective fun n m h => by simpa using h
  have h_norm : ‖TCtailElem N v‖ = ∑' k : ℤ, g k := lpOneAlg.norm_eq_tsum _
  have h_decomp : ∑' k : ℤ, g k = (∑' n : ℕ, g ↑n) + ∑' n : ℕ, g (-(↑n + 1)) :=
    tsum_of_nat_of_neg_add_one h_nat h_neg
  have hneg0 : (∑' n : ℕ, g (-(↑n + 1))) = 0 := by
    rw [tsum_congr (fun n : ℕ => show g (-(↑n + 1)) = 0 from by
      show ‖(TCtailElem N v) (-(↑n + 1 : ℤ))‖ = 0
      rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega]
      show ‖(0 : ScaledRealZ ν_val _)‖ = 0
      exact norm_zero), tsum_zero]
  have h_split : ∑' n : ℕ, g ↑n
      = (∑ i ∈ Finset.range (N + 1), g ↑i) + ∑' n : ℕ, g ↑(n + (N + 1)) :=
    (h_nat.sum_add_tsum_nat_add (N + 1)).symm
  have hfin0 : ∑ i ∈ Finset.range (N + 1), g ↑i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiN : i ≤ N := by simp [Finset.mem_range] at hi; omega
    show ‖(TCtailElem N v) (↑i : ℤ)‖ = 0
    show ‖(if N < i then chebyshevShiftDiv v (↑i : ℤ) else 0)‖ = 0
    rw [if_neg (not_lt.mpr hiN)]
    exact norm_zero
  have htail_eq : (∑' n : ℕ, g ↑(n + (N + 1)))
      = ∑' n : ℕ, ‖(chebyshevShiftDiv v) (↑(n + (N + 1)) : ℤ)‖ :=
    tsum_congr fun n => by
      show ‖(TCtailElem N v) (↑(n + (N + 1)) : ℤ)‖ = _
      show ‖(if N < n + (N + 1) then chebyshevShiftDiv v (↑(n + (N + 1)) : ℤ) else 0)‖ = _
      rw [if_pos (by omega)]
  rw [h_norm, h_decomp, hneg0, add_zero, h_split, hfin0, zero_add, htail_eq]
  exact chebyshevShiftDiv_tailTsum_le_div v N

/-- The full TC operator, collapsed to a scalar-component CLM. -/
private def TCall : l1Chebyshev ν_val →L[ℝ] l1Chebyshev ν_val :=
  (ContinuousLinearMap.proj 0).comp (data.TC.comp ι)

/-- Per-column bound for the FULL TC: block (exact, ℚ) + tail (`ν/(N+1)`). -/
private lemma TCall_col_le (m : ℤ) :
    ‖TCall (l1Chebyshev.single m 1)‖ ≤ (7/4 : ℝ) * (ν_val : ℝ) ^ m.natAbs := by
  have hsplit : TCall (l1Chebyshev.single m 1)
      = data.TCblockFun (ι (l1Chebyshev.single m 1)) 0 + TCtailElem N (l1Chebyshev.single m 1) := rfl
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have htail := TCtailElem_norm_le_tail (l1Chebyshev.single m 1)
  rw [l1Chebyshev.norm_single, abs_one, one_mul] at htail
  have hNν : (ν_val : ℝ) / ((N : ℝ) + 1) = 2/41 := by
    rw [show ((ν_val : ℝ)) = 2 from rfl]
    norm_num [N]
  rw [hNν] at htail
  have hpow : (0 : ℝ) ≤ (ν_val : ℝ) ^ m.natAbs := pow_nonneg ν_val.2.le _
  cases m with
  | ofNat mn =>
    rw [show ‖data.TCblockFun (ι (l1Chebyshev.single (Int.ofNat mn) 1)) 0‖
        = ((TCcolNormQ mn : ℚ) : ℝ) from TCblock_col_norm mn]
    have hb : ((TCcolNormQ mn : ℚ) : ℝ) ≤ (((279/164) * ν_q ^ mn : ℚ) : ℝ) := by
      exact_mod_cast TCcolNormQ_le mn
    have hb' : ((TCcolNormQ mn : ℚ) : ℝ) ≤ (279/164 : ℝ) * (ν_val : ℝ) ^ mn := by
      refine hb.trans (le_of_eq ?_)
      rw [ν_val_eq_q]
      push_cast
      ring
    rw [show ((Int.ofNat mn)).natAbs = mn from rfl] at htail ⊢
    nlinarith [pow_nonneg ν_val.2.le mn]
  | negSucc m' =>
    rw [TCblock_col_neg m']
    have : (2/41 : ℝ) * (ν_val : ℝ) ^ (Int.negSucc m').natAbs
        ≤ (7/4 : ℝ) * (ν_val : ℝ) ^ (Int.negSucc m').natAbs := by
      nlinarith [pow_nonneg ν_val.2.le (Int.negSucc m').natAbs]
    linarith [htail]

/-- Sharp operator bound: `‖TC w‖ ≤ 7/4 · ‖w‖`. -/
private lemma TC_norm_le (w : XCheb ν_val L) : ‖data.TC w‖ ≤ (7/4 : ℝ) * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg w))).mpr
    fun l => ?_
  rw [Subsingleton.elim l (0 : Fin L)]
  rw [show (data.TC w) 0 = TCall (w 0) from by rw [show TCall (w 0) = (data.TC (ι (w 0))) 0 from rfl, ι_eq]]
  exact (l1Chebyshev.norm_le_of_cols TCall TCall_col_le (w 0)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm w 0) (by norm_num))

/-- **Z₂ obligation**: the Lipschitz bound on DG over the certificate ball. -/
lemma Z₂_le : ∀ c ∈ Metric.closedBall ābar ((r_minus : ℚ) : ℝ),
    ‖fderiv ℝ (data.G phi p₀) c - fderiv ℝ (data.G phi p₀) ābar‖
      ≤ ((Z₂_bound : ℚ) : ℝ) * ((r_minus : ℚ) : ℝ) := by
  intro c hc
  have hcball : ‖c - ābar‖ ≤ ((r_minus : ℚ) : ℝ) := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hc
  rw [fderiv_G, fderiv_G]
  have hdiff : (data.TA + data.TC.comp (DPhiCLM c)) - (data.TA + data.TC.comp (DPhiCLM ābar))
      = data.TC.comp (DPhiCLM c - DPhiCLM ābar) := by
    rw [ContinuousLinearMap.comp_sub]
    abel
  rw [hdiff]
  have hrnn : (0 : ℝ) ≤ ((r_minus : ℚ) : ℝ) := by norm_num [r_minus]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num [Z₂_bound]) hrnn) fun h => ?_
  show ‖data.TC ((DPhiCLM c - DPhiCLM ābar) h)‖ ≤ _
  have hw : ∀ l : Fin L, ((DPhiCLM c - DPhiCLM ābar) h) l
      = (2 : ℝ) • (S ((c - ābar) l) * S (h l)) := by
    intro l
    show DPhiCLM c h l - DPhiCLM ābar h l = _
    rw [show DPhiCLM c h l = Dphi c h l from congr_fun (DPhiCLM_apply c h) l,
      show DPhiCLM ābar h l = Dphi ābar h l from congr_fun (DPhiCLM_apply ābar h) l]
    show ((2 : ℝ) • (S (c l) * S (h l)) - S (h l))
      - ((2 : ℝ) • (S (ābar l) * S (h l)) - S (h l)) = _
    rw [sub_sub_sub_cancel_right, ← smul_sub, ← sub_mul, ← map_sub]
    rfl
  have hwnorm : ‖(DPhiCLM c - DPhiCLM ābar) h‖
      ≤ 8 * ‖c - ābar‖ * ‖h‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
    rw [hw l, norm_smul, Real.norm_ofNat]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by norm_num)) ?_
    have h1 : ‖S ((c - ābar) l)‖ ≤ 2 * ‖c - ābar‖ :=
      (norm_Ssym_le _).trans (by
        have := norm_le_pi_norm (c - ābar) l
        linarith)
    have h2 : ‖S (h l)‖ ≤ 2 * ‖h‖ :=
      (norm_Ssym_le _).trans (by
        have := norm_le_pi_norm h l
        linarith)
    nlinarith [norm_nonneg (S ((c - ābar) l)), norm_nonneg (S (h l)),
      norm_nonneg (c - ābar), norm_nonneg h]
  refine le_trans (TC_norm_le _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hwnorm (by norm_num)) ?_
  rw [show ((Z₂_bound : ℚ) : ℝ) = 14 from by norm_num [Z₂_bound]]
  nlinarith [norm_nonneg h, hcball, hrnn, mul_le_mul_of_nonneg_right hcball
    (norm_nonneg h)]

/-- The radii polynomial is negative at the certified radius r = 10⁻⁶. -/
lemma radii_neg :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 := by
  norm_num [generalRadiiPolynomial, Y₀_bound, Z₀_bound, Z₁_bound, Z₂_bound, r_minus]

/-- **The transport gate accepts.** The native margin at r = 10⁻⁶ exceeds
(κ−1)/κ = 5/8 for the bordered↔U price κ = 8/3 at ν = 2: by
`transport_radii_polynomial_of_margin`, the completed certificate transports
to bordered Chebyshev storage with no bound re-verified there. -/
lemma margin_clears_gate :
    (8/3 : ℝ) * 1 * generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ)
      + ((8/3 : ℝ) * 1 - 1) * (r_minus : ℝ) < 0 := by
  norm_num [generalRadiiPolynomial, Y₀_bound, Z₀_bound, Z₁_bound, Z₂_bound, r_minus]

/-! ## The main theorem -/

/-- **Example 14.2.1**: the composed Chebyshev map for `u̇ = u(u−1)`, `u(−1) = ½`
has a unique zero within `10⁻⁶` of the numerical Chebyshev candidate, at
`ν = 2`, `N = 40`. The book's own twin of Example 8.1, machine-checked. -/
theorem main_existsUnique :
    ∃! xTilde ∈ Metric.closedBall (ChebyshevIVP.StdChebIVPData.abar data)
        ((r_minus : ℚ) : ℝ),
      data.G phi p₀ xTilde = 0 :=
  data.existsUnique phi p₀ G_diff (by norm_num [r_minus]) Y₀_le Z₀_le Z₁_le Z₂_le radii_neg

end Example1421.Cert
