import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic

/-!
# Symmetric bilateral storage: `IsSymmetric`, `symmetrize`, `natEmbed`

`l1Chebyshev.IsSymmetric a` (`a₋ₖ = aₖ`); `symmetrize` (`(symmetrize a)_k = a_{|k|}`, symmetric
output, `‖·‖ ≤ 2‖a‖`, fixed on symmetric elements, `symmetrize_CLM`,
`mul_symmetrize_single_toSeq`); `natEmbed : l1Weighted ν →L[ℝ] l1Chebyshev ν`, the ℕ-supported
isometry. `Fact (1 ≤ ν)` only where the product enters.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

/-- Symmetric bilateral sequences `a_{-k} = a_k`: the physical T-series inside
`l1Chebyshev ν`. -/
def l1Chebyshev.IsSymmetric (a : l1Chebyshev ν) : Prop :=
  ∀ k : ℤ, lpOneAlg.toRealSeq a (-k) = lpOneAlg.toRealSeq a k

/-! #### Symmetrization: the section `l1Bordered`-style storage → symmetric bilateral

`symmetrize a = (a_{|k|})_k`: symmetric output, reads only non-negative input
modes. Promoted from Example 14.2.1 (2026-08-25), where it is the correct way
to write a physical Chebyshev nonlinearity on the bilateral carrier. -/

namespace l1Chebyshev

private lemma summable_nonneg_fibers (a : l1Chebyshev ν) :
    Summable (fun n : ℕ => |toSeq a (n : ℤ)| * (ν : ℝ) ^ n) := by
  refine (summable_norm_natCast a).congr fun n => ?_
  rw [norm_fiber]
  simp

private lemma summable_shift_fibers (a : l1Chebyshev ν) :
    Summable (fun n : ℕ => |toSeq a (((n + 1 : ℕ)) : ℤ)| * (ν : ℝ) ^ (n + 1)) :=
  (summable_nonneg_fibers a).comp_injective (fun n m h => by simpa using h)

private lemma symmetrizeSeq_norm (a : l1Chebyshev ν) (k : ℤ) :
    ‖FiberTrivialization.equiv (E := ScaledRealZ ν) k (toSeq a (k.natAbs : ℤ))‖
      = |toSeq a (k.natAbs : ℤ)| * (ν : ℝ) ^ k.natAbs := by
  simp

private lemma symmetrize_memℓp (a : l1Chebyshev ν) :
    Memℓp (fun k : ℤ => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (toSeq a (k.natAbs : ℤ))) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · refine (summable_nonneg_fibers a).congr fun n => ?_
    rw [symmetrizeSeq_norm]
    simp
  · refine (summable_shift_fibers a).congr fun n => ?_
    rw [symmetrizeSeq_norm]
    have h1 : ((-(n + 1) : ℤ)).natAbs = n + 1 := by omega
    rw [h1]

/-- Symmetrization `(symmetrize a)_k = a_{|k|}`: symmetric output, reads only
non-negative input modes. `‖symmetrize a‖ ≤ 2‖a‖` (`symmetrize_norm_le`). -/
def symmetrize (a : l1Chebyshev ν) : l1Chebyshev ν :=
  ⟨⟨fun k => FiberTrivialization.equiv (E := ScaledRealZ ν) k (toSeq a (k.natAbs : ℤ)),
    symmetrize_memℓp a⟩⟩

@[simp] lemma symmetrize_toSeq (a : l1Chebyshev ν) (k : ℤ) :
    toSeq (symmetrize a) k = toSeq a (k.natAbs : ℤ) :=
  FiberTrivialization.equiv_symm_apply_equiv k _

lemma symmetrize_add (a b : l1Chebyshev ν) :
    symmetrize (a + b) = symmetrize a + symmetrize b := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  show toSeq _ k = toSeq _ k
  rw [symmetrize_toSeq, toSeq_add, toSeq_add, symmetrize_toSeq, symmetrize_toSeq]

lemma symmetrize_smul (r : ℝ) (a : l1Chebyshev ν) :
    symmetrize (r • a) = r • symmetrize a := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  show toSeq _ k = toSeq _ k
  rw [symmetrize_toSeq, toSeq_smul, toSeq_smul, symmetrize_toSeq]

/-- `‖symmetrize a‖ ≤ 2‖a‖`: each non-zero output mode charges its source
mode twice (once per sign), mode 0 once. -/
lemma symmetrize_norm_le (a : l1Chebyshev ν) : ‖symmetrize a‖ ≤ 2 * ‖a‖ := by
  have hfib : ∀ k : ℤ,
      ‖(symmetrize a) k‖ = |toSeq a (k.natAbs : ℤ)| * (ν : ℝ) ^ k.natAbs := by
    intro k
    rw [norm_fiber, symmetrize_toSeq]
  have hs1 : Summable (fun n : ℕ => ‖(symmetrize a) (n : ℤ)‖) := by
    refine (summable_nonneg_fibers a).congr fun n => ?_
    rw [hfib]
    simp
  have hs2 : Summable (fun n : ℕ => ‖(symmetrize a) (-(n + 1) : ℤ)‖) := by
    refine (summable_shift_fibers a).congr fun n => ?_
    rw [hfib]
    have h1 : ((-(n + 1) : ℤ)).natAbs = n + 1 := by omega
    rw [h1]
  have hnorm : ‖symmetrize a‖ = (∑' n : ℕ, ‖(symmetrize a) (n : ℤ)‖)
      + ∑' n : ℕ, ‖(symmetrize a) (-(n + 1) : ℤ)‖ :=
    lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg _
  have hinj₁ : Function.Injective ((↑) : ℕ → ℤ) := fun n m h => by exact_mod_cast h
  have hleg1 : (∑' n : ℕ, ‖(symmetrize a) (n : ℤ)‖) ≤ ‖a‖ := by
    rw [lpOneAlg.norm_eq_tsum]
    refine hs1.tsum_le_tsum_of_inj ((↑) : ℕ → ℤ) hinj₁ (fun k _ => norm_nonneg _)
      (fun n => le_of_eq ?_) (lpOneAlg.summable_norm a)
    rw [hfib, norm_fiber]
    simp
  have hinj₂ : Function.Injective (fun n : ℕ => ((n : ℤ) + 1)) :=
    fun n m h => by simpa using h
  have hleg2 : (∑' n : ℕ, ‖(symmetrize a) (-(n + 1) : ℤ)‖) ≤ ‖a‖ := by
    rw [lpOneAlg.norm_eq_tsum]
    refine hs2.tsum_le_tsum_of_inj (fun n : ℕ => ((n : ℤ) + 1)) hinj₂
      (fun k _ => norm_nonneg _) (fun n => le_of_eq ?_) (lpOneAlg.summable_norm a)
    rw [hfib, norm_fiber]
    have h1 : ((-(n + 1) : ℤ)).natAbs = n + 1 := by omega
    have h2 : (((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [h1, h2]
    have h3 : (((n + 1 : ℕ) : ℤ)) = ((n : ℤ) + 1) := by push_cast; ring
    rw [h3]
  linarith [hnorm, hleg1, hleg2]

/-- The symmetrization as a CLM (`symmetrize_CLM_norm_le : ‖·‖ ≤ 2`). -/
def symmetrize_CLM : l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  LinearMap.mkContinuous
    { toFun := symmetrize
      map_add' := symmetrize_add
      map_smul' := symmetrize_smul }
    2 (fun a => by
      show ‖symmetrize a‖ ≤ 2 * ‖a‖
      exact symmetrize_norm_le a)

@[simp] lemma symmetrize_CLM_apply (a : l1Chebyshev ν) :
    symmetrize_CLM a = symmetrize a := rfl


/-- The symmetrized element is symmetric. -/
lemma symmetrize_isSymmetric (a : l1Chebyshev ν) : (symmetrize a).IsSymmetric := by
  intro k
  show toSeq (symmetrize a) (-k) = toSeq (symmetrize a) k
  rw [symmetrize_toSeq, symmetrize_toSeq, Int.natAbs_neg]

/-- Symmetric elements are fixed by symmetrization. -/
lemma symmetrize_eq_self_of_isSymmetric (a : l1Chebyshev ν) (ha : a.IsSymmetric) :
    symmetrize a = a := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  show toSeq (symmetrize a) k = toSeq a k
  rw [symmetrize_toSeq]
  rcases Int.natAbs_eq k with h | h
  · rw [← h]
  · rw [show ((k.natAbs : ℤ)) = -k from by omega]
    exact ha k

/-- Symmetrization annihilates strictly negative singles. -/
lemma symmetrize_single_negSucc (m : ℕ) (x : ℝ) :
    symmetrize (single (ν := ν) (Int.negSucc m) x) = 0 := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  show toSeq (symmetrize (single (ν := ν) (Int.negSucc m) x)) k
    = toSeq (0 : l1Chebyshev ν) k
  rw [symmetrize_toSeq, toSeq_single, toSeq_zero, ite_eq_right (by omega)]

private theorem symmetrize_single_toSeq (k : ℕ) (n : ℤ) :
    l1Chebyshev.toSeq (l1Chebyshev.symmetrize
      (l1Chebyshev.single (ν := ν) (k : ℤ) 1)) n =
      if n.natAbs = k then 1 else 0 := by
  rw [l1Chebyshev.symmetrize_toSeq, l1Chebyshev.toSeq_single]
  by_cases h : n.natAbs = k
  · rw [ite_eq_left (by exact_mod_cast h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (by exact_mod_cast hc)), ite_eq_right h]

/-- The stored zero mode is single; a positive mode has both Laurent directions. -/
theorem mul_symmetrize_single_toSeq [Fact (1 ≤ (ν : ℝ))] (c : l1Chebyshev ν) (k : ℕ) (n : ℤ) :
    l1Chebyshev.toSeq
      (c * l1Chebyshev.symmetrize (l1Chebyshev.single (k : ℤ) 1)) n =
      if k = 0 then l1Chebyshev.toSeq c n
      else l1Chebyshev.toSeq c (n - k) + l1Chebyshev.toSeq c (n + k) := by
  cases k with
  | zero =>
      rw [l1Chebyshev.toSeq_mul_eq_finsum _ _ _ ({(0 : ℤ)} : Finset ℤ)
        (fun i hi => by
          rw [symmetrize_single_toSeq, ite_eq_right (fun hc => hi (by
            simp only [Finset.mem_singleton]
            omega))])]
      rw [Finset.sum_singleton, symmetrize_single_toSeq]
      simp
  | succ k =>
      rw [l1Chebyshev.toSeq_mul_eq_finsum _ _ _
        ({((k + 1 : ℕ) : ℤ), -((k + 1 : ℕ) : ℤ)} : Finset ℤ)
        (fun i hi => by
          rw [symmetrize_single_toSeq, ite_eq_right (fun hc => hi (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega))])]
      rw [Finset.sum_pair (by omega)]
      rw [symmetrize_single_toSeq, ite_eq_left (show (((k + 1 : ℕ) : ℤ)).natAbs = k + 1
        from by omega), symmetrize_single_toSeq,
        ite_eq_left (show (-((k + 1 : ℕ) : ℤ)).natAbs = k + 1 from by omega)]
      simp only [mul_one, Nat.succ_ne_zero, ite_false, sub_neg_eq_add]

end l1Chebyshev

/-! ### The ℕ-supported embedding -/

namespace l1Chebyshev

section NatEmbed

/-- The ℕ-supported coefficient family has finite bilateral weighted norm. -/
private theorem natEmbed_memℓp (a : l1Weighted ν) :
    Memℓp (fun k : ℤ => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (if 0 ≤ k then l1Weighted.toSeq a k.toNat else 0)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · refine (l1Weighted.summable_weighted a).congr fun n => ?_
    rw [ScaledRealZ.norm_equiv_apply, ite_eq_left (by omega), Int.toNat_natCast,
      Int.natAbs_natCast]
  · refine summable_zero.congr fun n => ?_
    rw [ScaledRealZ.norm_equiv_apply, ite_eq_right (by omega), abs_zero, zero_mul]

/-- The ℕ-supported embedding as an element (`natEmbed` is its linear map). -/
private def natEmbedFun (a : l1Weighted ν) : l1Chebyshev ν :=
  ⟨⟨fun k => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (if 0 ≤ k then l1Weighted.toSeq a k.toNat else 0), natEmbed_memℓp a⟩⟩

/-- Coefficients of `natEmbedFun`. -/
private theorem natEmbedFun_toSeq (a : l1Weighted ν) (k : ℤ) :
    toSeq (natEmbedFun a) k = if 0 ≤ k then l1Weighted.toSeq a k.toNat else 0 :=
  FiberTrivialization.equiv_symm_apply_equiv k _

/-- `natEmbedFun` preserves the norm. -/
private theorem norm_natEmbedFun (a : l1Weighted ν) : ‖natEmbedFun a‖ = ‖a‖ := by
  rw [lpOneAlg.norm_eq_tsum_natCast_of_neg _ fun n => by
      rw [← norm_eq_zero, norm_fiber, natEmbedFun_toSeq, ite_eq_right (by omega), abs_zero,
        zero_mul],
    l1Weighted.norm_eq_tsum]
  exact tsum_congr fun n => by
    rw [norm_fiber_natCast, natEmbedFun_toSeq, ite_eq_left (by omega), Int.toNat_natCast]

/-- **The ℕ-supported embedding** `ℓ¹_ν(ℕ) → ℓ¹_ν(ℤ)`: `(natEmbed a)_k = a_k` for `k ≥ 0`
and `0` for `k < 0`. It is an isometry for every `ν : PosReal` (`norm_natEmbed`), because the
bilateral weight `ν^{|k|}` restricts to `νⁿ` on the nonnegative modes. Built by
`LinearMap.mkContinuous` on the coefficient map. -/
def natEmbed : l1Weighted ν →L[ℝ] l1Chebyshev ν :=
  LinearMap.mkContinuous
    { toFun := natEmbedFun
      map_add' := fun a b => lpOneAlg.ext_toRealSeq (funext fun k => by
        show toSeq (natEmbedFun (a + b)) k = toSeq (natEmbedFun a + natEmbedFun b) k
        rw [toSeq_add, natEmbedFun_toSeq, natEmbedFun_toSeq, natEmbedFun_toSeq]
        split_ifs <;> simp)
      map_smul' := fun r a => lpOneAlg.ext_toRealSeq (funext fun k => by
        show toSeq (natEmbedFun (r • a)) k = toSeq (r • natEmbedFun a) k
        rw [toSeq_smul, natEmbedFun_toSeq, natEmbedFun_toSeq]
        split_ifs <;> simp) }
    1 (fun a => (norm_natEmbedFun a).trans_le (one_mul _).ge)

/-- Coefficients of the ℕ-supported embedding. -/
theorem natEmbed_toSeq (a : l1Weighted ν) (k : ℤ) :
    toSeq (natEmbed a) k = if 0 ≤ k then l1Weighted.toSeq a k.toNat else 0 :=
  natEmbedFun_toSeq a k

/-- The ℕ-supported embedding at a nonnegative mode. -/
@[simp] theorem natEmbed_toSeq_natCast (a : l1Weighted ν) (n : ℕ) :
    toSeq (natEmbed a) (n : ℤ) = l1Weighted.toSeq a n := by
  rw [natEmbed_toSeq, ite_eq_left (by omega), Int.toNat_natCast]

/-- The ℕ-supported embedding vanishes at the negative modes. -/
@[simp] theorem natEmbed_toSeq_negSucc (a : l1Weighted ν) (n : ℕ) :
    toSeq (natEmbed a) (Int.negSucc n) = 0 := by
  rw [natEmbed_toSeq, ite_eq_right (by omega)]

/-- The ℕ-supported embedding is an isometry, for every `ν : PosReal`. -/
@[simp] theorem norm_natEmbed (a : l1Weighted ν) : ‖natEmbed a‖ = ‖a‖ :=
  norm_natEmbedFun a


end NatEmbed

end l1Chebyshev

end RadiiPolynomial

end
