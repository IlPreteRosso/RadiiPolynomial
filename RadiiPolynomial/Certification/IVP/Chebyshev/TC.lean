import RadiiPolynomial.Certification.IVP.Chebyshev.Y0Z0
import RadiiPolynomial.Certification.IVP.Chebyshev.Common

/-!
# Chebyshev certification adapter: `Z₂`

The `TC` column norms `TCcolQ`, `TCcolNormQ`, `TCblockGen`, `TCnormGen`; the operator bound
`d.TC_norm_le_gen` and `d.Z₂_le_of_Q`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

/-! ### Z₂: the `TC` column norms (generic in `L`, `N`) -/

section QLayerTC

variable {L : ℕ}

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
  have hsplit : d.TC w l = ∑ j, d.TC (Pi.single j (w j)) l := by
    rw [← Finset.sum_apply,
      ← ContinuousLinearMap.sum_comp_single ℝ (fun _ => l1Chebyshev ν) d.TC w]
    rfl
  rw [hsplit]
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

end ChebyshevIVP
