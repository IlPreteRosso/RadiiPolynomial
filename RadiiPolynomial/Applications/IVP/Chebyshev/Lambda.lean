import RadiiPolynomial.Applications.IVP.Chebyshev.Standard

/-!
# Λ-decomposition of the composed Chebyshev IVP map

`G φ p a = constG p + TA a + TC (φ a)`: the composed map is affine in
`(a, φ(a))` for any coefficient-level nonlinearity `φ`.

- `constG p` — the constant rows (`p` preconditioned by the block of A);
- `TA` — the linear-in-`a` part: pass-through negatives, preconditioned block
  rows of the boundary functional and derivative diagonal, identity tail;
- `TC = TCblock + TCtail` — the linear-in-`c` part: preconditioned block rows
  of `c_{k+2} − c_k`, and the Chebyshev integration tail `chebyshevShiftDiv`
  on modes `> N`.

All three are CLMs. Crude norm constants suffice for differentiability;
`TCtail` carries the sharp `ν/2 + 1/(2ν)` constant reused by Z₂ bounds.

The equation-generic rows (`FAseq`, `FCseq`, `constFseq`) and the tail
operator `TCtail` live at the `ChebyshevIVP` level; everything that needs the
numerical data lives in the `StdChebIVPData` namespace, parameterized by
`d : StdChebIVPData ν L N`.

Outputs: `StdChebIVPData.hasFDerivAt_G`, `StdChebIVPData.differentiable_G`,
`StdChebIVPData.fderiv_G` (+ the pointwise `toSeq` bridges used by Z₁/Z₂
obligations at the example level).
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap RadiiPolynomial

noncomputable section

namespace ChebyshevIVP

/-! ## The affine rows of F -/

section Rows

variable {ν : PosReal} {L N : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- The linear-in-`a` rows of F (Eq. 14.11): row 0 is the boundary functional
`−a₀ − 2∑ (−1)^{n+1} a_{n+1}`, row k+1 the derivative diagonal `2(k+1)·a_{k+1}`. -/
def FAseq (v : l1Chebyshev ν) : ℕ → ℝ
  | 0 => -(l1Chebyshev.toSeq v 0) -
      2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)
  | (k + 1) => 2 * ((k : ℝ) + 1) * l1Chebyshev.toSeq v (↑(k + 1) : ℤ)

/-- The linear-in-`c` rows of F: row 0 is zero, row k+1 is `c_{k+2} − c_k`. -/
def FCseq (c : l1Chebyshev ν) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => l1Chebyshev.toSeq c (↑(k + 2) : ℤ) - l1Chebyshev.toSeq c (↑k : ℤ)

/-- The constant rows of F: the boundary value `p l` in row 0. -/
def constFseq (p : Fin L → ℝ) : Fin L → ℕ → ℝ := fun l n => if n = 0 then p l else 0

/-- Row-wise decomposition of the Chebyshev IVP coefficients into constant,
linear-in-`a`, and linear-in-`c` parts. -/
lemma ivpCoeffs_decomp (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (a : XCheb ν L) (l : Fin L) (n : ℕ) :
    chebyshevIvpCoeffs φ p a l n
      = constFseq p l n + FAseq (a l) n + FCseq (φ a l) n := by
  cases n with
  | zero =>
    simp only [chebyshevIvpCoeffs, constFseq, FAseq, FCseq, reduceIte]
    ring
  | succ k =>
    simp only [chebyshevIvpCoeffs, constFseq, FAseq, FCseq,
      if_neg (Nat.succ_ne_zero k)]
    ring

/-! Linearity of the rows. -/

lemma FAseq_add (v w : l1Chebyshev ν) (n : ℕ) :
    FAseq (v + w) n = FAseq v n + FAseq w n := by
  cases n with
  | zero =>
    have hv := summable_alternating_toSeq v
    have hw := summable_alternating_toSeq w
    simp only [FAseq, l1Chebyshev.toSeq_add]
    rw [show ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) *
          (l1Chebyshev.toSeq v (↑(n + 1) : ℤ) + l1Chebyshev.toSeq w (↑(n + 1) : ℤ))
        = ∑' n : ℕ, ((-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)
          + (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq w (↑(n + 1) : ℤ)) from
      tsum_congr fun n => by ring]
    rw [hv.tsum_add hw]
    ring
  | succ k =>
    simp only [FAseq, l1Chebyshev.toSeq_add]
    ring

lemma FAseq_smul (r : ℝ) (v : l1Chebyshev ν) (n : ℕ) :
    FAseq (r • v) n = r * FAseq v n := by
  cases n with
  | zero =>
    simp only [FAseq, l1Chebyshev.toSeq_smul]
    rw [show ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (r * l1Chebyshev.toSeq v (↑(n + 1) : ℤ))
        = ∑' n : ℕ, r * ((-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)) from
      tsum_congr fun n => by ring]
    rw [tsum_mul_left]
    ring
  | succ k =>
    simp only [FAseq, l1Chebyshev.toSeq_smul]
    ring

lemma FCseq_add (v w : l1Chebyshev ν) (n : ℕ) :
    FCseq (v + w) n = FCseq v n + FCseq w n := by
  cases n with
  | zero => simp [FCseq]
  | succ k => simp only [FCseq, l1Chebyshev.toSeq_add]; ring

lemma FCseq_smul (r : ℝ) (v : l1Chebyshev ν) (n : ℕ) :
    FCseq (r • v) n = r * FCseq v n := by
  cases n with
  | zero => simp [FCseq]
  | succ k => simp only [FCseq, l1Chebyshev.toSeq_smul]; ring

/-! Crude size bounds on the rows. -/

private lemma one_le_pow_nu (m : ℕ) : (1 : ℝ) ≤ (ν : ℝ) ^ m :=
  one_le_pow₀ (Fact.out : (1 : ℝ) ≤ (ν : ℝ))

lemma abs_toSeq_le_norm (v : l1Chebyshev ν) (k : ℤ) :
    |l1Chebyshev.toSeq v k| ≤ ‖v‖ := by
  refine le_trans ?_ (lpOneAlg.norm_apply_le_norm v k)
  rw [l1Chebyshev.norm_fiber]
  exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow_nu _)

private lemma summable_abs_shift (v : l1Chebyshev ν) :
    Summable (fun n : ℕ => |l1Chebyshev.toSeq v (↑(n + 1) : ℤ)|) := by
  have h1 : Summable (fun n : ℕ => ‖v ((↑(n + 1) : ℤ))‖) :=
    (lpOneAlg.summable_norm v).comp_injective fun n m h => by simpa using h
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_) h1
  rw [l1Chebyshev.norm_fiber]
  exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow_nu _)

lemma tsum_abs_shift_le_norm (v : l1Chebyshev ν) :
    ∑' n : ℕ, |l1Chebyshev.toSeq v (↑(n + 1) : ℤ)| ≤ ‖v‖ := by
  have h1 : Summable (fun n : ℕ => ‖v ((↑(n + 1) : ℤ))‖) :=
    (lpOneAlg.summable_norm v).comp_injective fun n m h => by simpa using h
  have hsummand : ∀ n : ℕ, |l1Chebyshev.toSeq v (↑(n + 1) : ℤ)| ≤ ‖v ((↑(n + 1) : ℤ))‖ := by
    intro n
    rw [l1Chebyshev.norm_fiber]
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow_nu _)
  refine (Summable.tsum_le_tsum hsummand (summable_abs_shift v) h1).trans ?_
  rw [lpOneAlg.norm_eq_tsum]
  exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm v)
    (fun _ => norm_nonneg _) fun n m h => by simpa using h

lemma FAseq_abs_le (v : l1Chebyshev ν) (k : ℕ) (hk : k ≤ N) :
    |FAseq v k| ≤ (2 * (N : ℝ) + 3) * ‖v‖ := by
  have hnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  cases k with
  | zero =>
    have h0 : |l1Chebyshev.toSeq v 0| ≤ ‖v‖ := abs_toSeq_le_norm v 0
    have habs : Summable (fun n : ℕ =>
        ‖(-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)‖) := by
      refine (summable_abs_shift v).congr fun n => ?_
      simp [Real.norm_eq_abs]
    have htsum : |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)|
        ≤ ‖v‖ := by
      refine le_trans ?_ (tsum_abs_shift_le_norm v)
      rw [show ∑' n : ℕ, |l1Chebyshev.toSeq v (↑(n + 1) : ℤ)|
          = ∑' n : ℕ, ‖(-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)‖ from
        tsum_congr fun n => by simp [Real.norm_eq_abs]]
      exact norm_tsum_le_tsum_norm habs
    have hval : FAseq v 0 = -(l1Chebyshev.toSeq v 0) -
        2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ) := rfl
    rw [hval]
    set T := ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq v (↑(n + 1) : ℤ)
    have htri : |(-(l1Chebyshev.toSeq v 0)) - 2 * T|
        ≤ |l1Chebyshev.toSeq v 0| + 2 * |T| := by
      have h := abs_add_le (-(l1Chebyshev.toSeq v 0)) (-(2 * T))
      rw [abs_neg, abs_neg, abs_mul] at h
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2] at h
      rw [sub_eq_add_neg]
      exact h
    nlinarith [h0, htsum, htri, abs_nonneg T]
  | succ m =>
    have hval : FAseq v (m + 1)
        = 2 * ((m : ℝ) + 1) * l1Chebyshev.toSeq v (↑(m + 1) : ℤ) := rfl
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1))]
    have hm : (m : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
    have habs : |l1Chebyshev.toSeq v (↑(m + 1) : ℤ)| ≤ ‖v‖ := abs_toSeq_le_norm v _
    nlinarith [abs_nonneg (l1Chebyshev.toSeq v (↑(m + 1) : ℤ))]

lemma FCseq_abs_le (c : l1Chebyshev ν) (k : ℕ) :
    |FCseq c k| ≤ 2 * ‖c‖ := by
  cases k with
  | zero =>
    have hval : FCseq c 0 = 0 := rfl
    rw [hval, abs_zero]
    positivity
  | succ m =>
    have hval : FCseq c (m + 1)
        = l1Chebyshev.toSeq c (↑(m + 2) : ℤ) - l1Chebyshev.toSeq c (↑m : ℤ) := rfl
    rw [hval]
    have h1 := abs_toSeq_le_norm c (↑(m + 2) : ℤ)
    have h2 := abs_toSeq_le_norm c (↑m : ℤ)
    have htri : |l1Chebyshev.toSeq c (↑(m + 2) : ℤ) - l1Chebyshev.toSeq c (↑m : ℤ)|
        ≤ |l1Chebyshev.toSeq c (↑(m + 2) : ℤ)| + |l1Chebyshev.toSeq c (↑m : ℤ)| := by
      have h := abs_add_le (l1Chebyshev.toSeq c (↑(m + 2) : ℤ))
        (-(l1Chebyshev.toSeq c (↑m : ℤ)))
      rw [abs_neg] at h
      rw [sub_eq_add_neg]
      exact h
    linarith

end Rows

/-! ## TCtail — the Chebyshev integration tail

Needs only `(ν, N)`, not the numerical data bundle: on tail modes `> N` the
preconditioned `c`-part is exactly the `chebyshevShiftDiv` fiber. The cutoff
`N` is an explicit argument (it is not determined by the types). -/

section TCtail

variable {ν : PosReal} {L : ℕ} (N : ℕ) [Fact (1 ≤ (ν : ℝ))]

/-- Raw ℤ-sequence of `TCtail`: the `chebyshevShiftDiv` fibers on modes `> N`,
zero elsewhere. -/
def TCtailSeq (v : l1Chebyshev ν) : ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => if N < n then chebyshevShiftDiv v (↑n : ℤ) else 0
  | (Int.negSucc _) => 0

private lemma TCtailSeq_le (v : l1Chebyshev ν) (k : ℤ) :
    ‖TCtailSeq N v k‖ ≤ ‖chebyshevShiftDiv v k‖ := by
  cases k with
  | ofNat n =>
    show ‖if N < n then chebyshevShiftDiv v (↑n : ℤ) else 0‖ ≤ _
    split
    · exact le_refl _
    · rw [norm_zero]; exact norm_nonneg _
  | negSucc m =>
    show ‖(0 : ScaledRealZ ν _)‖ ≤ _
    rw [norm_zero]; exact norm_nonneg _

private lemma TCtail_memℓp (v : l1Chebyshev ν) : Memℓp (TCtailSeq N v) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (TCtailSeq_le N v)
    (lpOneAlg.summable_norm (chebyshevShiftDiv v))

/-- One component of the tail operator. -/
def TCtailElem (v : l1Chebyshev ν) : l1Chebyshev ν :=
  ⟨⟨TCtailSeq N v, TCtail_memℓp N v⟩⟩

lemma TCtailElem_toSeq_nat (v : l1Chebyshev ν) (n : ℕ) :
    l1Chebyshev.toSeq (TCtailElem N v) (↑n : ℤ)
      = if N < n then l1Chebyshev.toSeq (chebyshevShiftDiv v) (↑n : ℤ) else 0 := by
  show lpAlgRingData.toReal (↑n : ℤ) (TCtailSeq N v (↑n : ℤ)) = _
  show lpAlgRingData.toReal (↑n : ℤ)
    (if N < n then chebyshevShiftDiv v (↑n : ℤ) else 0) = _
  split
  · rfl
  · exact lpAlgRingData.toReal_zero _

lemma TCtailElem_toSeq_neg (v : l1Chebyshev ν) (m : ℕ) :
    l1Chebyshev.toSeq (TCtailElem N v) (Int.negSucc m) = 0 := by
  show lpAlgRingData.toReal _ (TCtailSeq N v (Int.negSucc m)) = _
  exact lpAlgRingData.toReal_zero _

/-- Sharp norm bound for the tail component, from
`chebyshevShiftDiv_norm_le'`. -/
lemma TCtailElem_norm_le (v : l1Chebyshev ν) :
    ‖TCtailElem N v‖ ≤ ((ν : ℝ) / 2 + 1 / (2 * (ν : ℝ))) * ‖v‖ := by
  refine le_trans ?_ (chebyshevShiftDiv_norm_le' v)
  rw [lpOneAlg.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  exact Summable.tsum_le_tsum (TCtailSeq_le N v)
    (lpOneAlg.summable_norm (TCtailElem N v))
    (lpOneAlg.summable_norm (chebyshevShiftDiv v))

private lemma TCtailElem_add (v w : l1Chebyshev ν) :
    TCtailElem N (v + w) = TCtailElem N v + TCtailElem N w := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  rw [show lpOneAlg.toRealSeq (TCtailElem N v + TCtailElem N w) k
      = lpOneAlg.toRealSeq (TCtailElem N v) k + lpOneAlg.toRealSeq (TCtailElem N w) k from
    congr_fun (lpOneAlg.toRealSeq_add _ _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (TCtailElem N (v + w)) (↑n : ℤ)
      = l1Chebyshev.toSeq (TCtailElem N v) (↑n : ℤ)
        + l1Chebyshev.toSeq (TCtailElem N w) (↑n : ℤ)
    rw [TCtailElem_toSeq_nat, TCtailElem_toSeq_nat, TCtailElem_toSeq_nat,
      chebyshevShiftDiv_add]
    split
    · exact l1Chebyshev.toSeq_add _ _ _
    · ring
  | negSucc m =>
    show l1Chebyshev.toSeq (TCtailElem N (v + w)) (Int.negSucc m)
      = l1Chebyshev.toSeq (TCtailElem N v) (Int.negSucc m)
        + l1Chebyshev.toSeq (TCtailElem N w) (Int.negSucc m)
    rw [TCtailElem_toSeq_neg, TCtailElem_toSeq_neg, TCtailElem_toSeq_neg]
    ring

private lemma TCtailElem_smul (r : ℝ) (v : l1Chebyshev ν) :
    TCtailElem N (r • v) = r • TCtailElem N v := by
  apply lpOneAlg.ext_toRealSeq
  funext k
  rw [show lpOneAlg.toRealSeq (r • TCtailElem N v) k
      = r * lpOneAlg.toRealSeq (TCtailElem N v) k from
    congr_fun (lpOneAlg.toRealSeq_smul r _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (TCtailElem N (r • v)) (↑n : ℤ)
      = r * l1Chebyshev.toSeq (TCtailElem N v) (↑n : ℤ)
    rw [TCtailElem_toSeq_nat, TCtailElem_toSeq_nat, chebyshevShiftDiv_smul]
    split
    · exact l1Chebyshev.toSeq_smul r (chebyshevShiftDiv v) _
    · ring
  | negSucc m =>
    show l1Chebyshev.toSeq (TCtailElem N (r • v)) (Int.negSucc m)
      = r * l1Chebyshev.toSeq (TCtailElem N v) (Int.negSucc m)
    rw [TCtailElem_toSeq_neg, TCtailElem_toSeq_neg]
    ring

/-- The tail operator, componentwise. -/
def TCtailFun (c : XCheb ν L) : XCheb ν L := fun l => TCtailElem N (c l)

private lemma TCtailFun_norm_le (c : XCheb ν L) :
    ‖TCtailFun N c‖ ≤ ((ν : ℝ) / 2 + 1 / (2 * (ν : ℝ))) * ‖c‖ := by
  have hν0 : (0 : ℝ) < (ν : ℝ) := ν.2
  have hpos : (0 : ℝ) ≤ (ν : ℝ) / 2 + 1 / (2 * (ν : ℝ)) :=
    add_nonneg (div_nonneg ν.2.le (by norm_num))
      (div_nonneg (by norm_num) (by nlinarith))
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpos (norm_nonneg c))).mpr fun l => ?_
  exact (TCtailElem_norm_le N (c l)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm c l) hpos)

/-- The Chebyshev integration tail of TC as a CLM (sharp constant `ν/2 + 1/(2ν)`). -/
def TCtail : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous
    { toFun := TCtailFun N
      map_add' := fun a b => funext fun l => TCtailElem_add N (a l) (b l)
      map_smul' := fun r c => funext fun l => TCtailElem_smul N r (c l) }
    ((ν : ℝ) / 2 + 1 / (2 * (ν : ℝ)))
    fun c => by
      show ‖TCtailFun N c‖ ≤ _
      exact TCtailFun_norm_le N c

@[simp] lemma TCtail_apply (c : XCheb ν L) : TCtail N c = TCtailFun N c := rfl

end TCtail

/-! ## Data-dependent operators -/

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

namespace StdChebIVPData

variable (d : StdChebIVPData ν L N)

/-! ### Norm-assembly helpers -/

/-- Crude weighted row bound for the preconditioned finite block. -/
private lemma blockRow_abs_le (coeffs : SystemCoeff L) {C : ℝ}
    (hcoeffs : ∀ j : Fin L, ∀ k : ℕ, k ≤ N → |coeffs j k| ≤ C)
    (l : Fin L) (n : Fin (N + 1)) :
    |∑ j : Fin L, ∑ k : Fin (N + 1),
        d.approxInverse.finBlock l j n k * coeffs j (k : ℕ)|
      ≤ (∑ j : Fin L, ∑ k : Fin (N + 1), |d.approxInverse.finBlock l j n k|) * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hcoeffs j k (Fin.is_le k)) (abs_nonneg _)

/-- The crude weighted block constant, per output component. -/
def MAl (l : Fin L) : ℝ :=
  ∑ n : Fin (N + 1),
    (∑ j : Fin L, ∑ k : Fin (N + 1), |d.approxInverse.finBlock l j n k|)
      * (ν : ℝ) ^ (n : ℕ)

lemma MAl_nonneg (l : Fin L) : 0 ≤ d.MAl l :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _) (pow_nonneg ν.2.le _)

/-- The crude weighted block constant: the max of `MAl` over output
components. -/
def MA : ℝ := Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ d.MAl

lemma MAl_le_MA (l : Fin L) : d.MAl l ≤ d.MA :=
  Finset.le_sup' d.MAl (Finset.mem_univ l)

lemma MA_nonneg : 0 ≤ d.MA :=
  le_trans (d.MAl_nonneg 0) (d.MAl_le_MA 0)

/-- Weighted finite-row sums of the preconditioned block, crude bound. -/
private lemma finRows_weighted_le (coeffs : SystemCoeff L) {C : ℝ} (hC : 0 ≤ C)
    (hcoeffs : ∀ j : Fin L, ∀ k : ℕ, k ≤ N → |coeffs j k| ≤ C) (l : Fin L) :
    ∑ n : Fin (N + 1),
        |∑ j : Fin L, ∑ k : Fin (N + 1),
          d.approxInverse.finBlock l j n k * coeffs j (k : ℕ)|
          * (ν : ℝ) ^ (n : ℕ)
      ≤ d.MA * C := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (d.MAl_le_MA l) hC)
  rw [MAl, Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [show (∑ j : Fin L, ∑ k : Fin (N + 1), |d.approxInverse.finBlock l j n k|)
      * (ν : ℝ) ^ (n : ℕ) * C
    = ((∑ j : Fin L, ∑ k : Fin (N + 1), |d.approxInverse.finBlock l j n k|) * C)
      * (ν : ℝ) ^ (n : ℕ) from by ring]
  exact mul_le_mul_of_nonneg_right (d.blockRow_abs_le coeffs hcoeffs l n)
    (pow_nonneg ν.2.le _)

/-! ### constG -/

/-- Preconditioned constant rows. -/
def constGseq (p : Fin L → ℝ) : Fin L → ℕ → ℝ :=
  d.approxInverse.action (constFseq p)

lemma constGseq_tail (p : Fin L → ℝ) (l : Fin L) (n : ℕ) (hn : N < n) :
    d.constGseq p l n = 0 := by
  show d.approxInverse.action (constFseq p) l n = 0
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn]
  simp [constFseq, show n ≠ 0 from by omega]

private lemma constG_memℓp (p : Fin L → ℝ) (l : Fin L) :
    Memℓp (embedNatToInt (ν := ν) (d.constGseq p l) : ∀ k : ℤ, ScaledRealZ ν k) 1 :=
  embedNatToInt_memℓp_of_finSupp _ N fun n hn => d.constGseq_tail p l n hn

/-- The constant part of G. -/
def constG (p : Fin L → ℝ) : XCheb ν L := fun l =>
  ⟨⟨embedNatToInt (d.constGseq p l), d.constG_memℓp p l⟩⟩

lemma constG_toSeq_nat (p : Fin L → ℝ) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (d.constG p l) (↑n : ℤ) = d.constGseq p l n := by
  show lpAlgRingData.toReal (↑n : ℤ)
    (embedNatToInt (d.constGseq p l) (↑n : ℤ)) = _
  rw [embedNatToInt_natCast, lpAlgRingData.toReal_ofReal]

lemma constG_toSeq_neg (p : Fin L → ℝ) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (d.constG p l) (Int.negSucc m) = 0 := by
  show lpAlgRingData.toReal _
    (embedNatToInt (d.constGseq p l) (Int.negSucc m)) = _
  rw [embedNatToInt_negSucc]
  exact lpAlgRingData.toReal_zero _

/-! ### TA — the linear-in-`a` part -/

/-- Raw ℤ-sequence of `TA`: pass-through negatives, preconditioned FA rows,
identity tail (after `1/(2n) · 2n` cancellation). -/
def TAseq (a : XCheb ν L) (l : Fin L) : ∀ k : ℤ, ScaledRealZ ν k :=
  embedWithPassThrough (d.approxInverse.action (fun j => FAseq (a j)) l) (a l)

/-- On tail modes the preconditioned FA row is the identity. -/
lemma TA_action_tail_eq (a : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    d.approxInverse.action (fun j => FAseq (a j)) l n
      = l1Chebyshev.toSeq (a l) (↑n : ℤ) := by
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn, d.htail_diag_inv l n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show 1 / (2 * ((↑(m + 1) : ℕ) : ℝ))
      * (2 * ((m : ℝ) + 1) * l1Chebyshev.toSeq (a l) (↑(m + 1) : ℤ)) = _
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

lemma TAseq_tail_eq (a : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    d.TAseq a l (↑n : ℤ) = (a l) (↑n : ℤ) := by
  show lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n)
    (d.approxInverse.action (fun j => FAseq (a j)) l n) = _
  rw [d.TA_action_tail_eq a l n hn]
  exact lpAlgRingData.ofReal_toReal _ _

lemma TAseq_neg (a : XCheb ν L) (l : Fin L) (m : ℕ) :
    d.TAseq a l (Int.negSucc m) = (a l) (Int.negSucc m) := rfl

private lemma TAseq_memℓp (a : XCheb ν L) (l : Fin L) : Memℓp (d.TAseq a l) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · have hbase : Summable (fun n : ℕ => ‖(a l) (↑n : ℤ)‖) :=
      (lpOneAlg.summable_norm (a l)).comp_injective fun n m h => by simpa using h
    refine Summable.of_norm_bounded_eventually_nat hbase
      (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩)
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [d.TAseq_tail_eq a l n (by omega)]
  · have hbase : Summable (fun n : ℕ => ‖(a l) (Int.negSucc n)‖) :=
      (lpOneAlg.summable_norm (a l)).comp_injective fun n m h => by simpa using h
    refine hbase.congr fun n => ?_
    show ‖(a l) (Int.negSucc n)‖ = ‖d.TAseq a l (-(↑n + 1 : ℤ))‖
    rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega, d.TAseq_neg]

/-- The linear-in-`a` part of G, as a raw map. -/
def TAfun (a : XCheb ν L) : XCheb ν L := fun l => ⟨⟨d.TAseq a l, d.TAseq_memℓp a l⟩⟩

lemma TAfun_toSeq_nat (a : XCheb ν L) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (d.TAfun a l) (↑n : ℤ)
      = d.approxInverse.action (fun j => FAseq (a j)) l n := by
  show lpAlgRingData.toReal (↑n : ℤ) (d.TAseq a l (↑n : ℤ)) = _
  show lpAlgRingData.toReal (↑n : ℤ) (lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n)
    (d.approxInverse.action (fun j => FAseq (a j)) l n)) = _
  rw [lpAlgRingData.toReal_ofReal]

lemma TAfun_toSeq_neg (a : XCheb ν L) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (d.TAfun a l) (Int.negSucc m)
      = l1Chebyshev.toSeq (a l) (Int.negSucc m) := rfl

private lemma TAfun_add (a b : XCheb ν L) :
    d.TAfun (a + b) = d.TAfun a + d.TAfun b := by
  funext l
  apply lpOneAlg.ext_toRealSeq
  funext k
  show lpOneAlg.toRealSeq (d.TAfun (a + b) l) k
    = lpOneAlg.toRealSeq (d.TAfun a l + d.TAfun b l) k
  rw [show lpOneAlg.toRealSeq (d.TAfun a l + d.TAfun b l) k
      = lpOneAlg.toRealSeq (d.TAfun a l) k + lpOneAlg.toRealSeq (d.TAfun b l) k from
    congr_fun (lpOneAlg.toRealSeq_add _ _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (d.TAfun (a + b) l) (↑n : ℤ)
      = l1Chebyshev.toSeq (d.TAfun a l) (↑n : ℤ)
        + l1Chebyshev.toSeq (d.TAfun b l) (↑n : ℤ)
    rw [d.TAfun_toSeq_nat, d.TAfun_toSeq_nat, d.TAfun_toSeq_nat]
    rw [show (fun j => FAseq ((a + b) j)) = fun j n => FAseq (a j) n + FAseq (b j) n from
      funext fun j => funext fun n => FAseq_add (a j) (b j) n]
    exact congr_fun (congr_fun (SystemBlockDiagData.action_add d.approxInverse
      (fun j => FAseq (a j)) (fun j => FAseq (b j))) l) n
  | negSucc m =>
    show l1Chebyshev.toSeq (d.TAfun (a + b) l) (Int.negSucc m)
      = l1Chebyshev.toSeq (d.TAfun a l) (Int.negSucc m)
        + l1Chebyshev.toSeq (d.TAfun b l) (Int.negSucc m)
    rw [d.TAfun_toSeq_neg, d.TAfun_toSeq_neg, d.TAfun_toSeq_neg]
    exact l1Chebyshev.toSeq_add (a l) (b l) (Int.negSucc m)

private lemma TAfun_smul (r : ℝ) (a : XCheb ν L) :
    d.TAfun (r • a) = r • d.TAfun a := by
  funext l
  apply lpOneAlg.ext_toRealSeq
  funext k
  show lpOneAlg.toRealSeq (d.TAfun (r • a) l) k = lpOneAlg.toRealSeq (r • d.TAfun a l) k
  rw [show lpOneAlg.toRealSeq (r • d.TAfun a l) k
      = r * lpOneAlg.toRealSeq (d.TAfun a l) k from
    congr_fun (lpOneAlg.toRealSeq_smul r _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (d.TAfun (r • a) l) (↑n : ℤ)
      = r * l1Chebyshev.toSeq (d.TAfun a l) (↑n : ℤ)
    rw [d.TAfun_toSeq_nat, d.TAfun_toSeq_nat]
    rw [show (fun j => FAseq ((r • a) j)) = fun j n => r * FAseq (a j) n from
      funext fun j => funext fun n => FAseq_smul r (a j) n]
    exact congr_fun (congr_fun (SystemBlockDiagData.action_smul d.approxInverse r
      (fun j => FAseq (a j))) l) n
  | negSucc m =>
    show l1Chebyshev.toSeq (d.TAfun (r • a) l) (Int.negSucc m)
      = r * l1Chebyshev.toSeq (d.TAfun a l) (Int.negSucc m)
    rw [d.TAfun_toSeq_neg, d.TAfun_toSeq_neg]
    exact l1Chebyshev.toSeq_smul r (a l) (Int.negSucc m)

private lemma TAfun_norm_le (a : XCheb ν L) :
    ‖d.TAfun a‖ ≤ (d.MA * (2 * (N : ℝ) + 3) + 2) * ‖a‖ := by
  have hC : (0 : ℝ) ≤ (2 * (N : ℝ) + 3) * ‖a‖ := by positivity
  have hCoef : (0 : ℝ) ≤ d.MA * (2 * (N : ℝ) + 3) + 2 :=
    add_nonneg (mul_nonneg d.MA_nonneg (by positivity)) (by norm_num)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCoef (norm_nonneg a))).mpr fun l => ?_
  have hfin : ∑ n : Fin (N + 1),
      |d.approxInverse.action (fun j => FAseq (a j)) l (n : ℕ)|
        * (ν : ℝ) ^ (n : ℕ)
      ≤ d.MA * ((2 * (N : ℝ) + 3) * ‖a‖) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      (d.finRows_weighted_le (fun j => FAseq (a j)) hC
        (fun j k hk => (FAseq_abs_le (a j) k hk).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm a j) (by positivity))) l)
    rw [SystemBlockDiagData.action_finite _ _ _ _ (Fin.is_le n)]
  refine le_trans (embedWithPassThrough_norm_le _ (a l) N (d.TAseq_memℓp a l) hfin
    (fun n hn => d.TA_action_tail_eq a l n hn)) ?_
  have hla : ‖a l‖ ≤ ‖a‖ := norm_le_pi_norm a l
  nlinarith [d.MA_nonneg, norm_nonneg a]

/-- The linear-in-`a` part of G, as a CLM. -/
def TA : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous
    { toFun := d.TAfun
      map_add' := d.TAfun_add
      map_smul' := d.TAfun_smul }
    (d.MA * (2 * (N : ℝ) + 3) + 2)
    fun a => by
      show ‖d.TAfun a‖ ≤ _
      exact d.TAfun_norm_le a

@[simp] lemma TA_apply (a : XCheb ν L) : d.TA a = d.TAfun a := rfl

/-! ### TCblock — preconditioned block rows of the `c`-part -/

/-- Finite (block) rows of the preconditioned `c`-part. -/
def TCblockSeq (c : XCheb ν L) (l : Fin L) : ℕ → ℝ :=
  d.approxInverse.actionFinite (fun j => FCseq (c j)) l

lemma TCblockSeq_tail (c : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    d.TCblockSeq c l n = 0 :=
  SystemBlockDiagData.actionFinite_tail _ _ _ _ hn

private lemma TCblock_memℓp (c : XCheb ν L) (l : Fin L) :
    Memℓp (embedNatToInt (ν := ν) (d.TCblockSeq c l) : ∀ k : ℤ, ScaledRealZ ν k) 1 :=
  embedNatToInt_memℓp_of_finSupp _ N fun n hn => d.TCblockSeq_tail c l n hn

/-- The preconditioned block part of TC, as a raw map. -/
def TCblockFun (c : XCheb ν L) : XCheb ν L := fun l =>
  ⟨⟨embedNatToInt (d.TCblockSeq c l), d.TCblock_memℓp c l⟩⟩

lemma TCblockFun_toSeq_nat (c : XCheb ν L) (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (d.TCblockFun c l) (↑n : ℤ) = d.TCblockSeq c l n := by
  show lpAlgRingData.toReal (↑n : ℤ)
    (embedNatToInt (d.TCblockSeq c l) (↑n : ℤ)) = _
  rw [embedNatToInt_natCast, lpAlgRingData.toReal_ofReal]

lemma TCblockFun_toSeq_neg (c : XCheb ν L) (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (d.TCblockFun c l) (Int.negSucc m) = 0 := by
  show lpAlgRingData.toReal _
    (embedNatToInt (d.TCblockSeq c l) (Int.negSucc m)) = _
  rw [embedNatToInt_negSucc]
  exact lpAlgRingData.toReal_zero _

private lemma TCblockFun_add (a b : XCheb ν L) :
    d.TCblockFun (a + b) = d.TCblockFun a + d.TCblockFun b := by
  funext l
  apply lpOneAlg.ext_toRealSeq
  funext k
  show lpOneAlg.toRealSeq (d.TCblockFun (a + b) l) k
    = lpOneAlg.toRealSeq (d.TCblockFun a l + d.TCblockFun b l) k
  rw [show lpOneAlg.toRealSeq (d.TCblockFun a l + d.TCblockFun b l) k
      = lpOneAlg.toRealSeq (d.TCblockFun a l) k
        + lpOneAlg.toRealSeq (d.TCblockFun b l) k from
    congr_fun (lpOneAlg.toRealSeq_add _ _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (d.TCblockFun (a + b) l) (↑n : ℤ)
      = l1Chebyshev.toSeq (d.TCblockFun a l) (↑n : ℤ)
        + l1Chebyshev.toSeq (d.TCblockFun b l) (↑n : ℤ)
    rw [d.TCblockFun_toSeq_nat, d.TCblockFun_toSeq_nat, d.TCblockFun_toSeq_nat]
    show d.approxInverse.actionFinite (fun j => FCseq ((a + b) j)) l n = _
    rw [show (fun j => FCseq ((a + b) j)) = fun j n => FCseq (a j) n + FCseq (b j) n from
      funext fun j => funext fun n => FCseq_add (a j) (b j) n]
    exact congr_fun (congr_fun (SystemBlockDiagData.actionFinite_add d.approxInverse
      (fun j => FCseq (a j)) (fun j => FCseq (b j))) l) n
  | negSucc m =>
    show l1Chebyshev.toSeq (d.TCblockFun (a + b) l) (Int.negSucc m)
      = l1Chebyshev.toSeq (d.TCblockFun a l) (Int.negSucc m)
        + l1Chebyshev.toSeq (d.TCblockFun b l) (Int.negSucc m)
    rw [d.TCblockFun_toSeq_neg, d.TCblockFun_toSeq_neg, d.TCblockFun_toSeq_neg]
    ring

private lemma TCblockFun_smul (r : ℝ) (c : XCheb ν L) :
    d.TCblockFun (r • c) = r • d.TCblockFun c := by
  funext l
  apply lpOneAlg.ext_toRealSeq
  funext k
  show lpOneAlg.toRealSeq (d.TCblockFun (r • c) l) k
    = lpOneAlg.toRealSeq (r • d.TCblockFun c l) k
  rw [show lpOneAlg.toRealSeq (r • d.TCblockFun c l) k
      = r * lpOneAlg.toRealSeq (d.TCblockFun c l) k from
    congr_fun (lpOneAlg.toRealSeq_smul r _) k]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (d.TCblockFun (r • c) l) (↑n : ℤ)
      = r * l1Chebyshev.toSeq (d.TCblockFun c l) (↑n : ℤ)
    rw [d.TCblockFun_toSeq_nat, d.TCblockFun_toSeq_nat]
    show d.approxInverse.actionFinite (fun j => FCseq ((r • c) j)) l n = _
    rw [show (fun j => FCseq ((r • c) j)) = fun j n => r * FCseq (c j) n from
      funext fun j => funext fun n => FCseq_smul r (c j) n]
    exact congr_fun (congr_fun (SystemBlockDiagData.actionFinite_smul d.approxInverse r
      (fun j => FCseq (c j))) l) n
  | negSucc m =>
    show l1Chebyshev.toSeq (d.TCblockFun (r • c) l) (Int.negSucc m)
      = r * l1Chebyshev.toSeq (d.TCblockFun c l) (Int.negSucc m)
    rw [d.TCblockFun_toSeq_neg, d.TCblockFun_toSeq_neg]
    ring

private lemma TCblockFun_norm_le (c : XCheb ν L) :
    ‖d.TCblockFun c‖ ≤ (d.MA * 2) * ‖c‖ := by
  have hCoef : (0 : ℝ) ≤ d.MA * 2 := mul_nonneg d.MA_nonneg (by norm_num)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCoef (norm_nonneg c))).mpr fun l => ?_
  have hfin : ∑ n : Fin (N + 1), |d.TCblockSeq c l (n : ℕ)| * (ν : ℝ) ^ (n : ℕ)
      ≤ d.MA * (2 * ‖c‖) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      (d.finRows_weighted_le (fun j => FCseq (c j)) (by positivity)
        (fun j k _ => (FCseq_abs_le (c j) k).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm c j) (by norm_num))) l)
    congr 1
    congr 1
    show d.approxInverse.actionFinite (fun j => FCseq (c j)) l (n : ℕ) = _
    rw [SystemBlockDiagData.actionFinite_finite d.approxInverse
      (fun j => FCseq (c j)) l (n : ℕ) (Fin.is_le n)]
  refine le_trans (embedNatToInt_norm_le _ N (d.TCblock_memℓp c l)
    (fun n hn => d.TCblockSeq_tail c l n hn) hfin) (le_of_eq (by ring))

/-- The preconditioned block part of TC as a CLM. -/
def TCblock : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous
    { toFun := d.TCblockFun
      map_add' := d.TCblockFun_add
      map_smul' := d.TCblockFun_smul }
    (d.MA * 2)
    fun c => by
      show ‖d.TCblockFun c‖ ≤ _
      exact d.TCblockFun_norm_le c

@[simp] lemma TCblock_apply (c : XCheb ν L) : d.TCblock c = d.TCblockFun c := rfl

/-- The linear-in-`c` part of G. -/
def TC : XCheb ν L →L[ℝ] XCheb ν L := d.TCblock + TCtail N

lemma TC_apply (c : XCheb ν L) : d.TC c = d.TCblockFun c + TCtailFun N c := rfl

/-! ### The decomposition and the derivative of G -/

/-- **The Λ-decomposition**: the composed Chebyshev IVP map is affine in
`(a, φ(a))`. -/
lemma G_decomp (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (a : XCheb ν L) :
    d.G φ p a = d.constG p + d.TA a + d.TC (fun l => φ a l) := by
  funext l
  apply lpOneAlg.ext_toRealSeq
  funext k
  have hsplit : lpOneAlg.toRealSeq ((d.constG p + d.TA a + d.TC (fun l => φ a l)) l) k
      = l1Chebyshev.toSeq (d.constG p l) k + l1Chebyshev.toSeq (d.TAfun a l) k
        + (l1Chebyshev.toSeq (d.TCblockFun (fun j => φ a j) l) k
          + l1Chebyshev.toSeq (TCtailFun N (fun j => φ a j) l) k) := by
    show l1Chebyshev.toSeq (d.constG p l + d.TAfun a l
      + (d.TCblockFun (fun j => φ a j) l + TCtailFun N (fun j => φ a j) l)) k = _
    rw [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_add]
  rw [hsplit]
  cases k with
  | ofNat n =>
    show l1Chebyshev.toSeq (d.G φ p a l) (↑n : ℤ) = _
    have hG : l1Chebyshev.toSeq (d.G φ p a l) (↑n : ℤ)
        = d.approxInverse.action (chebyshevIvpCoeffs φ p a) l n := by
      show lpAlgRingData.toReal (↑n : ℤ) (lpAlgRingData.ofReal (E := ScaledRealZ ν)
        (↑n) (d.approxInverse.action (chebyshevIvpCoeffs φ p a) l n)) = _
      rw [lpAlgRingData.toReal_ofReal]
    rw [hG]
    show _ = l1Chebyshev.toSeq (d.constG p l) (↑n : ℤ)
      + l1Chebyshev.toSeq (d.TAfun a l) (↑n : ℤ)
      + (l1Chebyshev.toSeq (d.TCblockFun (fun j => φ a j) l) (↑n : ℤ)
        + l1Chebyshev.toSeq (TCtailElem N (φ a l)) (↑n : ℤ))
    rw [d.constG_toSeq_nat, d.TAfun_toSeq_nat, d.TCblockFun_toSeq_nat,
      TCtailElem_toSeq_nat]
    rcases le_or_gt n N with hn | hn
    · -- block rows: split the finite sums
      rw [if_neg (not_lt.mpr hn)]
      rw [SystemBlockDiagData.action_finite _ _ _ _ hn,
        SystemBlockDiagData.action_finite _ _ _ _ hn]
      show _ = d.approxInverse.action (constFseq p) l n
        + _ + (d.approxInverse.actionFinite (fun j => FCseq (φ a j)) l n + 0)
      rw [SystemBlockDiagData.action_finite (b := constFseq p) _ _ _ hn,
        SystemBlockDiagData.actionFinite_finite _ _ _ _ hn, add_zero]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ivpCoeffs_decomp]
      show d.approxInverse.finBlock l j ⟨n, _⟩ k
          * (constFseq p j (k : ℕ) + FAseq (a j) (k : ℕ) + FCseq (φ a j) (k : ℕ)) = _
      ring
    · -- tail rows: 1/(2n) · (2n·aₙ + c_{n+1} − c_{n−1}) = aₙ + shiftDiv(c)ₙ
      rw [if_pos hn]
      rw [SystemBlockDiagData.action_tail _ _ _ _ hn, d.htail_diag_inv l n hn,
        d.constGseq_tail p l n hn, d.TA_action_tail_eq a l n hn,
        d.TCblockSeq_tail _ l n hn]
      have hshift : l1Chebyshev.toSeq (chebyshevShiftDiv (φ a l)) (↑n : ℤ)
          = (l1Chebyshev.toSeq (φ a l) ((↑n : ℤ) + 1)
            - l1Chebyshev.toSeq (φ a l) ((↑n : ℤ) - 1)) / (2 * (n : ℝ)) := by
        show lpOneAlg.toRealSeq (chebyshevShiftDiv (φ a l)) (↑n : ℤ) = _
        rw [chebyshevShiftDiv_toSeq, chebyshevShiftDiv_seq_pos _ n (by omega)]
      rw [hshift]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      show 1 / (2 * ((↑(m + 1) : ℕ) : ℝ))
          * (2 * ((m : ℝ) + 1) * l1Chebyshev.toSeq (a l) (↑(m + 1) : ℤ)
            + l1Chebyshev.toSeq (φ a l) (↑(m + 2) : ℤ)
            - l1Chebyshev.toSeq (φ a l) (↑m : ℤ)) = _
      have h1 : ((↑(m + 1 : ℕ) : ℤ)) + 1 = (↑(m + 2 : ℕ) : ℤ) := by push_cast; ring
      have h2 : ((↑(m + 1 : ℕ) : ℤ)) - 1 = (↑(m : ℕ) : ℤ) := by push_cast; ring
      rw [h1, h2]
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | negSucc m =>
    show l1Chebyshev.toSeq (d.G φ p a l) (Int.negSucc m) = _
    have hG : l1Chebyshev.toSeq (d.G φ p a l) (Int.negSucc m)
        = l1Chebyshev.toSeq (a l) (Int.negSucc m) := rfl
    rw [hG]
    show _ = l1Chebyshev.toSeq (d.constG p l) (Int.negSucc m)
      + l1Chebyshev.toSeq (d.TAfun a l) (Int.negSucc m)
      + (l1Chebyshev.toSeq (d.TCblockFun (fun j => φ a j) l) (Int.negSucc m)
        + l1Chebyshev.toSeq (TCtailElem N (φ a l)) (Int.negSucc m))
    rw [d.constG_toSeq_neg, d.TAfun_toSeq_neg, d.TCblockFun_toSeq_neg,
      TCtailElem_toSeq_neg]
    ring

/-- **The derivative of G**: `DG(a) = TA + TC ∘ DΦ`, for any CLM `DΦ` that is
the derivative at `a` of the (componentwise) nonlinearity. -/
lemma hasFDerivAt_G (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (a : XCheb ν L) (DΦ : XCheb ν L →L[ℝ] XCheb ν L)
    (hΦ : HasFDerivAt (fun x => (fun l => φ x l)) DΦ a) :
    HasFDerivAt (d.G φ p) (d.TA + d.TC.comp DΦ) a := by
  rw [show d.G φ p = fun x => d.constG p + d.TA x + d.TC (fun l => φ x l) from
    funext (d.G_decomp φ p)]
  have hc : HasFDerivAt (fun _ : XCheb ν L => d.constG p)
      (0 : XCheb ν L →L[ℝ] XCheb ν L) a := hasFDerivAt_const _ _
  have hta : HasFDerivAt (fun x : XCheb ν L => d.TA x) d.TA a := d.TA.hasFDerivAt
  have htc : HasFDerivAt (fun x : XCheb ν L => d.TC (fun l => φ x l))
      (d.TC.comp DΦ) a := d.TC.hasFDerivAt.comp a hΦ
  have h := (hc.add hta).add htc
  rw [show (0 : XCheb ν L →L[ℝ] XCheb ν L) + d.TA + d.TC.comp DΦ
      = d.TA + d.TC.comp DΦ from by rw [zero_add]] at h
  exact h

/-- Differentiability obligation of `StdChebIVPData.existsUnique`. -/
lemma differentiable_G (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (DΦ : XCheb ν L → (XCheb ν L →L[ℝ] XCheb ν L))
    (hDΦ : ∀ a, HasFDerivAt (fun x => (fun l => φ x l)) (DΦ a) a) :
    Differentiable ℝ (d.G φ p) :=
  fun a => (d.hasFDerivAt_G φ p a (DΦ a) (hDΦ a)).differentiableAt

lemma fderiv_G (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (DΦ : XCheb ν L → (XCheb ν L →L[ℝ] XCheb ν L))
    (hDΦ : ∀ a, HasFDerivAt (fun x => (fun l => φ x l)) (DΦ a) a)
    (a : XCheb ν L) :
    fderiv ℝ (d.G φ p) a = d.TA + d.TC.comp (DΦ a) :=
  (d.hasFDerivAt_G φ p a (DΦ a) (hDΦ a)).fderiv

end StdChebIVPData

end ChebyshevIVP

end
