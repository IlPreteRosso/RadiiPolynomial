import RadiiPolynomial.Certification.IVP.Chebyshev.QLayer
import RadiiPolynomial.Certification.Rational.Grid

/-!
# Chebyshev certification adapter: `Y₀`, `Z₀` and `‖S(ā)‖`

Bridges on a bundle `d : StdChebIVPData ν L N`: `d.defect_finBlockNorm_le_of_Q` (exact block
norm of the family-neutral `defectCols`), `d.Z₀_sound` (any `DefectBy` slot), `d.Y₀_le_of_Q`,
and the exact `‖S(āᵢ)‖` (`d.norm_symmetrize_abar_eq`) that both `Z₂` and `Z₁` consume; with the
stored-data facts `d.ν_q_pos`, `d.one_le_ν_q` and `d.abar_Q_getD_eq_zero`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

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
  rw [ScaledRealZ.norm_equiv_apply,
    d.approxInverse.action_eq_blockActionQ (fun l j k => d.A_col l j k.val)
      (fun _ n => (2 * (n : ℚ))⁻¹) (fun l j k i => rfl)
      (fun l n hn => by rw [d.htail_diag_inv l n hn]; push_cast; simp only [one_div])
      _ _ hF l n, d.hν]
  simp

/-! #### `‖S(ā)‖` -/

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

end Bridges

end StdChebIVPData

end ChebyshevIVP
