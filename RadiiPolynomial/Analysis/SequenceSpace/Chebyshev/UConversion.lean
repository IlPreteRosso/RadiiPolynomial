import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic

/-!
# Chebyshev T→U conversion and U-integration

The two halves of the Chebyshev integration tail operator:

- `chebyshevToU : l1Chebyshev ν → l1Weighted ν`, `(chebyshevToU c)_m = (c_m - c_{m+2})/2`.
  Coefficient-level form of the basis conversion `T_m = (U_m - U_{m-2})/2` (DLMF 18.9.9):
  a Chebyshev-T series with coefficients `c` has U-expansion coefficients `chebyshevToU c`.
- `uIntegrate : l1Weighted ν → l1Chebyshev ν`, `(uIntegrate b)_k = b_{k-1}/k` for `k ≥ 1`,
  `0` otherwise. Coefficient-level form of `∫ U_{k-1} = T_k / k`.

The U-coefficient carrier is `l1Weighted ν` — the same type as the Taylor coefficient
space, reused as a module of U-coefficients (no algebra structure is used or wanted).

Norm bounds: `‖chebyshevToU c‖ ≤ ‖c‖` and `‖uIntegrate b‖ ≤ ν·‖b‖`, so the composition
is `≤ ν`-bounded; the factorization `chebyshevShiftDiv = -(uIntegrate ∘ chebyshevToU)`
and the resulting sharper bound `‖chebyshevShiftDiv c‖ ≤ (ν/2 + 1/(2ν))·‖c‖` live in
`Applications/IVP/Chebyshev/Operator.lean` (where `chebyshevShiftDiv` is defined).

Convention note: both maps use the repo's raw bilateral storage (no separate zero-mode
weighting for `T_0`/`U_0`). An asymmetric zero-mode convention only matters for a future
two-sided T↔U conversion and is deliberately deferred.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

/-! ### Fiber-norm and subseries helpers for `l1Chebyshev` at nonnegative modes -/

/-- Norm sums restricted to nonnegative modes are summable. -/
lemma summable_norm_natCast (c : l1Chebyshev ν) :
    Summable (fun n : ℕ => ‖c (↑n : ℤ)‖) :=
  (lpOneAlg.summable_norm c).comp_injective (fun n m h => by omega)

/-- Norm sums restricted to shifted nonnegative modes are summable. -/
private lemma summable_norm_natCast_add (c : l1Chebyshev ν) (s : ℤ) :
    Summable (fun n : ℕ => ‖c (↑n + s)‖) :=
  (lpOneAlg.summable_norm c).comp_injective (fun n m h => by omega)

/-- Fiber norm at a nonnegative mode: `‖c_m‖ = |c_m|·ν^m`. -/
lemma norm_fiber_natCast (c : l1Chebyshev ν) (m : ℕ) :
    ‖c (↑m : ℤ)‖ = |l1Chebyshev.toSeq c ↑m| * (ν : ℝ) ^ m := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight c (↑m : ℤ)]
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul, Real.norm_eq_abs,
    Int.natAbs_natCast]
  rfl

/-- Fiber norm at mode `m + 2`: `‖c_{m+2}‖ = |c_{m+2}|·ν^{m+2}`. -/
private lemma norm_fiber_natCast_add_two (c : l1Chebyshev ν) (m : ℕ) :
    ‖c ((↑m : ℤ) + 2)‖ = |l1Chebyshev.toSeq c (↑m + 2)| * (ν : ℝ) ^ (m + 2) := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑m : ℤ) + 2)]
  have h2 : ((↑m : ℤ) + 2).natAbs = m + 2 := by omega
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul, Real.norm_eq_abs, h2]
  rfl

/-! ### The T→U conversion -/

section ChebyshevToU

/-- The raw T→U conversion sequence: `(c_m - c_{m+2})/2`. -/
private def chebyshevToU_seq (c : l1Chebyshev ν) : ℕ → ℝ :=
  fun m => (l1Chebyshev.toSeq c ↑m - l1Chebyshev.toSeq c (↑m + 2)) / 2

-- Per-fiber bound with the exact weight transfer
-- `|c_{m+2}|·ν^m = ν⁻²·(|c_{m+2}|·ν^{m+2})` (needs only ν ≠ 0, not ν ≥ 1):
-- `|(c_m - c_{m+2})/2|·ν^m ≤ (1/2)·(‖c_m‖ + ν⁻²·‖c_{m+2}‖)`.
private lemma chebyshevToU_fiber_le (c : l1Chebyshev ν) (m : ℕ) :
    |chebyshevToU_seq c m| * (ν : ℝ) ^ m ≤
      1 / 2 * (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖) := by
  rw [norm_fiber_natCast, norm_fiber_natCast_add_two]
  simp only [chebyshevToU_seq]
  have htri : |l1Chebyshev.toSeq c ↑m - l1Chebyshev.toSeq c (↑m + 2)| ≤
      |l1Chebyshev.toSeq c ↑m| + |l1Chebyshev.toSeq c (↑m + 2)| := by
    have h := norm_sub_le (l1Chebyshev.toSeq c ↑m) (l1Chebyshev.toSeq c (↑m + 2))
    simpa only [Real.norm_eq_abs] using h
  have s1 : |l1Chebyshev.toSeq c ↑m - l1Chebyshev.toSeq c (↑m + 2)| * (ν : ℝ) ^ m ≤
      (|l1Chebyshev.toSeq c ↑m| + |l1Chebyshev.toSeq c (↑m + 2)|) * (ν : ℝ) ^ m :=
    mul_le_mul_of_nonneg_right htri (pow_nonneg ν.2.le m)
  rw [add_mul] at s1
  have hy : |l1Chebyshev.toSeq c (↑m + 2)| * (ν : ℝ) ^ m =
      ((ν : ℝ) ^ 2)⁻¹ * (|l1Chebyshev.toSeq c (↑m + 2)| * (ν : ℝ) ^ (m + 2)) := by
    have hν : (ν : ℝ) ≠ 0 := ν.2.ne'
    field_simp
    ring
  rw [abs_div, abs_two, div_mul_eq_mul_div]
  linarith

private lemma chebyshevToU_mem (c : l1Chebyshev ν) :
    l1Weighted.Mem ν (chebyshevToU_seq c) := by
  rw [l1Weighted.mem_iff]
  have h0 : Summable (fun m : ℕ => ‖c (↑m : ℤ)‖) := summable_norm_natCast c
  have h2 : Summable (fun m : ℕ => ‖c ((↑m : ℤ) + 2)‖) := summable_norm_natCast_add c 2
  have h2' : Summable (fun m : ℕ => ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖) := h2.mul_left _
  have hsum : Summable (fun m : ℕ =>
      1 / 2 * (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖)) := by
    simpa only [smul_eq_mul] using (h0.add h2').const_smul ((1 : ℝ) / 2)
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    (fun m => chebyshevToU_fiber_le c m) hsum

/-- The T→U basis conversion `(chebyshevToU c)_m = (c_m - c_{m+2})/2` on coefficient
sequences (DLMF 18.9.9: `T_m = (U_m - U_{m-2})/2`). Target carrier: `l1Weighted ν`,
reused as the module of U-coefficients. -/
def chebyshevToU (c : l1Chebyshev ν) : l1Weighted ν :=
  l1Weighted.mk (chebyshevToU_seq c) (chebyshevToU_mem c)

@[simp] lemma chebyshevToU_toSeq (c : l1Chebyshev ν) (m : ℕ) :
    l1Weighted.toSeq (chebyshevToU c) m =
      (l1Chebyshev.toSeq c ↑m - l1Chebyshev.toSeq c (↑m + 2)) / 2 := rfl

lemma chebyshevToU_add (c d : l1Chebyshev ν) :
    chebyshevToU (c + d) = chebyshevToU c + chebyshevToU d := by
  apply l1Weighted.ext; intro m
  simp only [chebyshevToU_toSeq, l1Weighted.add_toSeq, l1Chebyshev.toSeq_add]
  ring

lemma chebyshevToU_smul (r : ℝ) (c : l1Chebyshev ν) :
    chebyshevToU (r • c) = r • chebyshevToU c := by
  apply l1Weighted.ext; intro m
  have hs : ∀ k : ℤ, l1Chebyshev.toSeq (r • c) k = r * l1Chebyshev.toSeq c k :=
    fun k => congr_fun (lpOneAlg.toRealSeq_smul r c) k
  simp only [chebyshevToU_toSeq, l1Weighted.smul_toSeq, hs]
  ring

/-- Sharp norm bound for the T→U conversion on raw bilateral storage:
`‖chebyshevToU c‖ ≤ (1 + ν⁻²)/2 · ‖c‖`. The constant is attained on unit
columns `e_m`, `m ≥ 1`, so it is the operator norm. Holds for every `ν > 0`. -/
lemma chebyshevToU_norm_le_sharp (c : l1Chebyshev ν) :
    ‖chebyshevToU c‖ ≤ (1 + ((ν : ℝ) ^ 2)⁻¹) / 2 * ‖c‖ := by
  rw [l1Weighted.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  have h0 : Summable (fun m : ℕ => ‖c (↑m : ℤ)‖) := summable_norm_natCast c
  have h2 : Summable (fun m : ℕ => ‖c ((↑m : ℤ) + 2)‖) := summable_norm_natCast_add c 2
  have h2' : Summable (fun m : ℕ => ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖) := h2.mul_left _
  have hsb : Summable (fun m : ℕ =>
      1 / 2 * (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖)) := by
    simpa only [smul_eq_mul] using (h0.add h2').const_smul ((1 : ℝ) / 2)
  have hstep := Summable.tsum_le_tsum (fun m => chebyshevToU_fiber_le c m)
    (l1Weighted.summable_weighted (chebyshevToU c)) hsb
  refine hstep.trans ?_
  -- `∑ 1/2·(‖c_m‖ + ν⁻²‖c_{m+2}‖) = 1/2·(∑‖c_m‖ + ν⁻²∑‖c_{m+2}‖) ≤ 1/2·(1 + ν⁻²)·‖c‖`
  have e1 : ∑' m : ℕ, (1 / 2 * (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖)) =
      1 / 2 * ∑' m : ℕ, (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖) :=
    tsum_mul_left
  have e2 : ∑' m : ℕ, (‖c (↑m : ℤ)‖ + ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖) =
      (∑' m : ℕ, ‖c (↑m : ℤ)‖) + ∑' m : ℕ, ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖ :=
    h0.tsum_add h2'
  have e3 : ∑' m : ℕ, ((ν : ℝ) ^ 2)⁻¹ * ‖c ((↑m : ℤ) + 2)‖ =
      ((ν : ℝ) ^ 2)⁻¹ * ∑' m : ℕ, ‖c ((↑m : ℤ) + 2)‖ := tsum_mul_left
  have hsub0 : (∑' m : ℕ, ‖c (↑m : ℤ)‖) ≤ ∑' k : ℤ, ‖c k‖ :=
    tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm c) (fun _ => norm_nonneg _)
      (fun n m h => by omega)
  have hsub2 : (∑' m : ℕ, ‖c ((↑m : ℤ) + 2)‖) ≤ ∑' k : ℤ, ‖c k‖ :=
    tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm c) (fun _ => norm_nonneg _)
      (fun n m h => by omega)
  have hs2' : ((ν : ℝ) ^ 2)⁻¹ * (∑' m : ℕ, ‖c ((↑m : ℤ) + 2)‖) ≤
      ((ν : ℝ) ^ 2)⁻¹ * ∑' k : ℤ, ‖c k‖ :=
    mul_le_mul_of_nonneg_left hsub2 (by positivity)
  have egoal : (1 + ((ν : ℝ) ^ 2)⁻¹) / 2 * (∑' k : ℤ, ‖c k‖) =
      1 / 2 * ((∑' k : ℤ, ‖c k‖) + ((ν : ℝ) ^ 2)⁻¹ * ∑' k : ℤ, ‖c k‖) := by ring
  rw [e1, e2, e3, egoal]
  linarith

/-- Weaker convenient form: for `ν ≥ 1` the T→U conversion is `1`-bounded. -/
lemma chebyshevToU_norm_le [Fact (1 ≤ (ν : ℝ))] (c : l1Chebyshev ν) :
    ‖chebyshevToU c‖ ≤ ‖c‖ := by
  refine (chebyshevToU_norm_le_sharp c).trans ?_
  have hν : (1 : ℝ) ≤ (ν : ℝ) := Fact.out
  have h1 : (1 : ℝ) ≤ (ν : ℝ) ^ 2 := one_le_pow₀ hν
  have h2 : ((ν : ℝ) ^ 2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr h1
  exact mul_le_of_le_one_left (norm_nonneg c) (by linarith)

/-- The T→U conversion as a CLM with operator norm `(1 + ν⁻²)/2` (in particular ≤ 1
for `ν ≥ 1`). -/
noncomputable def chebyshevToU_CLM : l1Chebyshev ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := chebyshevToU
      map_add' := chebyshevToU_add
      map_smul' := fun r c => by simp [chebyshevToU_smul] }
    ((1 + ((ν : ℝ) ^ 2)⁻¹) / 2)
    (fun c => chebyshevToU_norm_le_sharp c)

@[simp] lemma chebyshevToU_CLM_apply (c : l1Chebyshev ν) :
    chebyshevToU_CLM c = chebyshevToU c := rfl

end ChebyshevToU

/-! ### U-integration -/

section UIntegrate

/-- The raw U-integration sequence: `b_{k-1}/k` at modes `k ≥ 1`, `0` at modes `k ≤ 0`
(from `∫ U_{k-1} = T_k / k`). -/
private def uIntegrate_seq (b : l1Weighted ν) : ℤ → ℝ
  | Int.ofNat 0 => 0
  | Int.ofNat (n + 1) => l1Weighted.toSeq b n / (↑n + 1)
  | Int.negSucc _ => 0

@[simp] private lemma uIntegrate_seq_zero (b : l1Weighted ν) :
    uIntegrate_seq b 0 = 0 := rfl

@[simp] private lemma uIntegrate_seq_negSucc (b : l1Weighted ν) (n : ℕ) :
    uIntegrate_seq b (Int.negSucc n) = 0 := rfl

@[simp] private lemma uIntegrate_seq_succ (b : l1Weighted ν) (n : ℕ) :
    uIntegrate_seq b (↑(n + 1) : ℤ) = l1Weighted.toSeq b n / (↑n + 1) := rfl

-- Fiber norm at mode `n+1`: `|b_n/(n+1)|·ν^{n+1}`.
private lemma uIntegrate_fiber_eq (b : l1Weighted ν) (n : ℕ) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
        (uIntegrate_seq b (↑(n + 1) : ℤ))‖ =
      |l1Weighted.toSeq b n| / (↑n + 1) * (ν : ℝ) ^ (n + 1) := by
  rw [ScaledRealZ.norm_lpAlgRingData_ofReal, uIntegrate_seq_succ]
  have h1 : ((↑(n + 1) : ℤ)).natAbs = n + 1 := by omega
  rw [h1, abs_div, abs_of_pos (show (0 : ℝ) < ↑n + 1 by positivity)]

-- Fiber bound: `|b_n/(n+1)|·ν^{n+1} ≤ ν·(|b_n|·ν^n)` — the `1/k ≤ 1` estimate.
private lemma uIntegrate_fiber_le (b : l1Weighted ν) (n : ℕ) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
        (uIntegrate_seq b (↑(n + 1) : ℤ))‖ ≤
      (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n) := by
  rw [uIntegrate_fiber_eq]
  have hd : |l1Weighted.toSeq b n| / (↑n + 1) ≤ |l1Weighted.toSeq b n| :=
    div_le_self (abs_nonneg _) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hstep : |l1Weighted.toSeq b n| / (↑n + 1) * (ν : ℝ) ^ (n + 1) ≤
      |l1Weighted.toSeq b n| * (ν : ℝ) ^ (n + 1) :=
    mul_le_mul_of_nonneg_right hd (pow_nonneg ν.2.le _)
  refine hstep.trans (le_of_eq ?_)
  rw [pow_succ]; ring

private lemma uIntegrate_memℓp (b : l1Weighted ν) :
    Memℓp (fun k : ℤ => lpAlgRingData.ofReal (E := ScaledRealZ ν) k
      (uIntegrate_seq b k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hinj : Function.Injective (fun n : ℕ => (↑(n + 1) : ℤ)) := by
    intro n m h; simp only at h; omega
  have hvanish : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ => (↑(n + 1) : ℤ)) →
      ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) k (uIntegrate_seq b k)‖ = 0 := by
    intro k hk
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        have h0 : uIntegrate_seq b (Int.ofNat 0) = 0 := uIntegrate_seq_zero b
        rw [h0, lpAlgRingData.ofReal_zero, norm_zero]
      | succ n => exact absurd ⟨n, by simp⟩ hk
    | negSucc n =>
      rw [uIntegrate_seq_negSucc, lpAlgRingData.ofReal_zero, norm_zero]
  rw [← Function.Injective.summable_iff hinj hvanish]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((l1Weighted.summable_weighted b).mul_left (ν : ℝ))
  simp only [Function.comp_apply]
  exact uIntegrate_fiber_le b n

/-- U-integration `(uIntegrate b)_k = b_{k-1}/k` for `k ≥ 1`, `0` for `k ≤ 0`:
the coefficient-level form of `∫ U_{k-1} = T_k/k`, mapping U-coefficients back
into the Chebyshev-T space. -/
def uIntegrate (b : l1Weighted ν) : l1Chebyshev ν :=
  ⟨⟨fun k => lpAlgRingData.ofReal (E := ScaledRealZ ν) k (uIntegrate_seq b k),
    uIntegrate_memℓp b⟩⟩

-- Internal bridge (private RHS — for in-file use; external files use the
-- per-mode simp lemmas below).
lemma uIntegrate_toSeq (b : l1Weighted ν) (k : ℤ) :
    lpOneAlg.toRealSeq (uIntegrate b) k = uIntegrate_seq b k := by
  simp [uIntegrate, lpOneAlg.toRealSeq, lpAlgRingData.toReal_ofReal]

@[simp] lemma uIntegrate_toSeq_zero (b : l1Weighted ν) :
    lpOneAlg.toRealSeq (uIntegrate b) 0 = 0 := by
  rw [uIntegrate_toSeq]; rfl

@[simp] lemma uIntegrate_toSeq_negSucc (b : l1Weighted ν) (n : ℕ) :
    lpOneAlg.toRealSeq (uIntegrate b) (Int.negSucc n) = 0 := by
  rw [uIntegrate_toSeq]; rfl

@[simp] lemma uIntegrate_toSeq_succ (b : l1Weighted ν) (n : ℕ) :
    lpOneAlg.toRealSeq (uIntegrate b) (↑(n + 1) : ℤ) =
      l1Weighted.toSeq b n / (↑n + 1) := by
  rw [uIntegrate_toSeq]; rfl

lemma uIntegrate_add (b d : l1Weighted ν) :
    uIntegrate (b + d) = uIntegrate b + uIntegrate d := by
  apply lpOneAlg.ext_toRealSeq; funext k
  simp only [uIntegrate_toSeq, lpOneAlg.toRealSeq_add, Pi.add_apply]
  cases k with
  | ofNat n => cases n with
    | zero => simp
    | succ n => simp [uIntegrate_seq]; ring
  | negSucc n => simp

lemma uIntegrate_smul (r : ℝ) (b : l1Weighted ν) :
    uIntegrate (r • b) = r • uIntegrate b := by
  apply lpOneAlg.ext_toRealSeq
  rw [lpOneAlg.toRealSeq_smul]; funext k
  simp only [Pi.smul_apply, smul_eq_mul, uIntegrate_toSeq]
  cases k with
  | ofNat n => cases n with
    | zero => simp
    | succ n => simp [uIntegrate_seq]; ring
  | negSucc n => simp

/-! #### Norm bound: `‖uIntegrate b‖ ≤ ν·‖b‖` (exact: attained on `b = e_0`). -/

-- Element-level restatements of the fiber facts (the element applied at a mode is
-- definitionally `ofReal` of the raw sequence).
private lemma uIntegrate_elem_zero (b : l1Weighted ν) :
    (uIntegrate b) (Int.ofNat 0) = 0 := by
  show lpAlgRingData.ofReal (E := ScaledRealZ ν) _ (uIntegrate_seq b _) = 0
  rw [show uIntegrate_seq b (Int.ofNat 0) = 0 from rfl, lpAlgRingData.ofReal_zero]

private lemma uIntegrate_elem_negSucc (b : l1Weighted ν) (n : ℕ) :
    (uIntegrate b) (Int.negSucc n) = 0 := by
  show lpAlgRingData.ofReal (E := ScaledRealZ ν) _ (uIntegrate_seq b _) = 0
  rw [uIntegrate_seq_negSucc, lpAlgRingData.ofReal_zero]

private lemma uIntegrate_elem_succ_le (b : l1Weighted ν) (n : ℕ) :
    ‖(uIntegrate b) (↑(n + 1) : ℤ)‖ ≤
      (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n) := by
  show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
      (uIntegrate_seq b (↑(n + 1) : ℤ))‖ ≤ _
  exact uIntegrate_fiber_le b n

private lemma uIntegrate_norm_support (b : l1Weighted ν) :
    Function.support (fun k : ℤ => ‖(uIntegrate b) k‖) ⊆
      Set.range (fun n : ℕ => (↑(n + 1) : ℤ)) := by
  intro k hk
  simp only [Function.mem_support] at hk
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact absurd (by rw [uIntegrate_elem_zero, norm_zero]) hk
    | succ n => exact ⟨n, by simp⟩
  | negSucc n => exact absurd (by rw [uIntegrate_elem_negSucc, norm_zero]) hk

lemma uIntegrate_norm_le (b : l1Weighted ν) : ‖uIntegrate b‖ ≤ (ν : ℝ) * ‖b‖ := by
  rw [lpOneAlg.norm_eq_tsum]
  have hinj : Function.Injective (fun n : ℕ => (↑(n + 1) : ℤ)) := by
    intro n m h; simp only at h; omega
  -- Reindex the bilateral sum onto the positive modes carrying the support.
  have hre : (∑' n : ℕ, ‖(uIntegrate b) (↑(n + 1) : ℤ)‖) =
      ∑' k : ℤ, ‖(uIntegrate b) k‖ :=
    hinj.tsum_eq (uIntegrate_norm_support b)
  rw [← hre]
  have hsA : Summable (fun n : ℕ => ‖(uIntegrate b) (↑(n + 1) : ℤ)‖) :=
    (lpOneAlg.summable_norm (uIntegrate b)).comp_injective hinj
  have hsB : Summable (fun n : ℕ => (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n)) :=
    (l1Weighted.summable_weighted b).mul_left _
  refine (Summable.tsum_le_tsum (fun n => uIntegrate_elem_succ_le b n) hsA hsB).trans
    (le_of_eq ?_)
  rw [l1Weighted.norm_eq_tsum]
  exact tsum_mul_left

/-- U-integration as a CLM with operator norm ≤ ν (exact: attained on `e_0`). -/
noncomputable def uIntegrate_CLM : l1Weighted ν →L[ℝ] l1Chebyshev ν :=
  LinearMap.mkContinuous
    { toFun := uIntegrate
      map_add' := uIntegrate_add
      map_smul' := fun r b => by simp [uIntegrate_smul] }
    (ν : ℝ)
    (fun b => uIntegrate_norm_le b)

@[simp] lemma uIntegrate_CLM_apply (b : l1Weighted ν) :
    uIntegrate_CLM b = uIntegrate b := rfl

end UIntegrate

/-! ### The U→T conversion (inverse direction)

`chebyshevFromU b`, mode `k ≥ 0`: `2·Σ_{j≥0} b_{k+2j}` — the telescoping inverse of
`chebyshevToU` (`(c_m - c_{m+2})/2`). An infinite-band operator: it is bounded only for
`ν > 1` (the band sums a `ν⁻²`-geometric series), which is why this section takes
`Fact (1 < ν)` — the quantitative face of "basis transport degenerates as ν → 1". -/

section ChebyshevFromU

variable [Fact (1 < (ν : ℝ))]

private lemma one_lt_nu : (1 : ℝ) < (ν : ℝ) := Fact.out
private lemma one_le_nu : (1 : ℝ) ≤ (ν : ℝ) := (one_lt_nu (ν := ν)).le

omit [Fact (1 < (ν : ℝ))] in
lemma invsq_nonneg : (0 : ℝ) ≤ ((ν : ℝ) ^ 2)⁻¹ := by positivity

lemma one_lt_nusq : (1 : ℝ) < (ν : ℝ) ^ 2 := by
  nlinarith [one_lt_nu (ν := ν)]

lemma invsq_lt_one : ((ν : ℝ) ^ 2)⁻¹ < 1 :=
  (inv_lt_one₀ (pow_pos ν.2 2)).mpr (one_lt_nusq (ν := ν))

/-- Abs-summability along a shifted even-spaced ℕ subsequence of `l1Weighted` coefficients. -/
lemma summable_abs_toSeq_shift (b : l1Weighted ν) (s : ℕ) :
    Summable (fun j : ℕ => |l1Weighted.toSeq b (s + 2 * j)|) := by
  have habs : Summable (fun n : ℕ => |l1Weighted.toSeq b n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (l1Weighted.summable_weighted b)
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (one_le_nu (ν := ν)))
  exact habs.comp_injective (fun x y h => by omega)

lemma summable_toSeq_shift (b : l1Weighted ν) (s : ℕ) :
    Summable (fun j : ℕ => l1Weighted.toSeq b (s + 2 * j)) :=
  (summable_abs_toSeq_shift b s).of_abs

/-- The raw U→T conversion sequence: `2·Σ_j b_{k+2j}` on modes `k ≥ 0`, `0` below. -/
private def chebyshevFromU_seq (b : l1Weighted ν) : ℤ → ℝ
  | Int.ofNat n => 2 * ∑' j : ℕ, l1Weighted.toSeq b (n + 2 * j)
  | Int.negSucc _ => 0

omit [Fact (1 < (ν : ℝ))] in
@[simp] private lemma chebyshevFromU_seq_ofNat (b : l1Weighted ν) (n : ℕ) :
    chebyshevFromU_seq b (↑n : ℤ) = 2 * ∑' j : ℕ, l1Weighted.toSeq b (n + 2 * j) := rfl

omit [Fact (1 < (ν : ℝ))] in
@[simp] private lemma chebyshevFromU_seq_negSucc (b : l1Weighted ν) (n : ℕ) :
    chebyshevFromU_seq b (Int.negSucc n) = 0 := rfl

-- Row bound for the double family: `Σ_k |b_{k+2j}|·ν^k ≤ ((ν²)⁻¹)^j·‖b‖`
-- via the exact per-term transfer `|b_{k+2j}|·ν^k = ((ν²)⁻¹)^j·(|b_{k+2j}|·ν^{k+2j})`.
omit [Fact (1 < (ν : ℝ))] in
lemma fromU_row_le (b : l1Weighted ν) (j : ℕ) :
    (∑' k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) ≤
      (((ν : ℝ) ^ 2)⁻¹) ^ j * ‖b‖ := by
  have hterm : ∀ k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k =
      (((ν : ℝ) ^ 2)⁻¹) ^ j *
        (|l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ (k + 2 * j)) := by
    intro k
    have hpow : (ν : ℝ) ^ (k + 2 * j) = (ν : ℝ) ^ k * ((ν : ℝ) ^ 2) ^ j := by
      rw [← pow_mul, ← pow_add]
    have hcp : (((ν : ℝ) ^ 2)⁻¹) ^ j * ((ν : ℝ) ^ 2) ^ j = 1 := by
      have hc : ((ν : ℝ) ^ 2)⁻¹ * (ν : ℝ) ^ 2 = 1 :=
        inv_mul_cancel₀ (pow_pos ν.2 2).ne'
      rw [← mul_pow, hc, one_pow]
    rw [hpow]
    linear_combination (-(|l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k)) * hcp
  rw [tsum_congr hterm, tsum_mul_left]
  have hsub : (∑' k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ (k + 2 * j)) ≤
      ∑' n : ℕ, |l1Weighted.toSeq b n| * (ν : ℝ) ^ n :=
    tsum_comp_le_tsum_of_inj (l1Weighted.summable_weighted b)
      (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)) (fun x y h => by omega)
  rw [l1Weighted.norm_eq_tsum]
  exact mul_le_mul_of_nonneg_left hsub (by positivity)

/-- The double family `(j, k) ↦ |b_{k+2j}|·ν^k` is summable on `ℕ × ℕ`:
rows are shifted subseries, row sums are geometrically dominated. -/
lemma fromU_prod_summable (b : l1Weighted ν) :
    Summable (fun p : ℕ × ℕ =>
      |l1Weighted.toSeq b (p.2 + 2 * p.1)| * (ν : ℝ) ^ p.2) := by
  refine (summable_prod_of_nonneg
    (fun p => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))).mpr ⟨?_, ?_⟩
  · intro j
    have hrow : Summable (fun k : ℕ =>
        |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ (k + 2 * j)) :=
      (l1Weighted.summable_weighted b).comp_injective
        (by intro x y h; simp only at h; omega)
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)) (fun k => ?_) hrow
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_le_nu (ν := ν)) (by omega)) (abs_nonneg _)
  · refine Summable.of_nonneg_of_le
      (fun j => tsum_nonneg fun k => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
      (fun j => fromU_row_le b j)
      ((summable_geometric_of_lt_one (invsq_nonneg (ν := ν))
        (invsq_lt_one (ν := ν))).mul_right ‖b‖)

/-- Marginal in the other order: `k ↦ Σ_j |b_{k+2j}|·ν^k` is summable. -/
lemma fromU_marginal_summable (b : l1Weighted ν) :
    Summable (fun k : ℕ => ∑' j : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) := by
  have hswap : Summable (fun q : ℕ × ℕ =>
      |l1Weighted.toSeq b (q.1 + 2 * q.2)| * (ν : ℝ) ^ q.1) :=
    (fromU_prod_summable b).prod_symm
  exact ((summable_prod_of_nonneg
    (fun q => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))).mp hswap).2

-- Fiber bound at mode `n`: `|2·Σ_j b_{n+2j}|·ν^n ≤ 2·Σ_j |b_{n+2j}|·ν^n`.
private lemma chebyshevFromU_fiber_le (b : l1Weighted ν) (n : ℕ) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n : ℤ) (chebyshevFromU_seq b (↑n : ℤ))‖ ≤
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)| * (ν : ℝ) ^ n := by
  rw [ScaledRealZ.norm_lpAlgRingData_ofReal, chebyshevFromU_seq_ofNat]
  have hna : ((↑n : ℤ)).natAbs = n := by omega
  rw [hna]
  have hs : Summable (fun j : ℕ => ‖l1Weighted.toSeq b (n + 2 * j)‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_toSeq_shift b n
  have hAbs : |∑' j : ℕ, l1Weighted.toSeq b (n + 2 * j)| ≤
      ∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
  have hmr : (∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)| * (ν : ℝ) ^ n) =
      (∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)|) * (ν : ℝ) ^ n := tsum_mul_right
  rw [abs_mul, abs_two, hmr]
  have h1 : |∑' j : ℕ, l1Weighted.toSeq b (n + 2 * j)| * (ν : ℝ) ^ n ≤
      (∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)|) * (ν : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hAbs (pow_nonneg ν.2.le n)
  linarith

private lemma chebyshevFromU_memℓp (b : l1Weighted ν) :
    Memℓp (fun k : ℤ => lpAlgRingData.ofReal (E := ScaledRealZ ν) k
      (chebyshevFromU_seq b k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hinj : Function.Injective (fun n : ℕ => (↑n : ℤ)) := by
    intro n m h; simp only at h; omega
  have hvanish : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ => (↑n : ℤ)) →
      ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) k (chebyshevFromU_seq b k)‖ = 0 := by
    intro k hk
    cases k with
    | ofNat n => exact absurd ⟨n, by simp⟩ hk
    | negSucc n => rw [chebyshevFromU_seq_negSucc, lpAlgRingData.ofReal_zero, norm_zero]
  rw [← Function.Injective.summable_iff hinj hvanish]
  have hmarg : Summable (fun k : ℕ =>
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) :=
    (fromU_marginal_summable b).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmarg
  simp only [Function.comp_apply]
  exact chebyshevFromU_fiber_le b n

/-- The U→T basis conversion: `(chebyshevFromU b)_k = 2·Σ_{j≥0} b_{k+2j}` for `k ≥ 0`,
`0` for `k < 0` — the telescoping inverse of `chebyshevToU`. Bounded only for `ν > 1`. -/
def chebyshevFromU (b : l1Weighted ν) : l1Chebyshev ν :=
  ⟨⟨fun k => lpAlgRingData.ofReal (E := ScaledRealZ ν) k (chebyshevFromU_seq b k),
    chebyshevFromU_memℓp b⟩⟩

-- Internal bridge (private RHS); external files use the per-mode lemmas below.
lemma chebyshevFromU_toSeq (b : l1Weighted ν) (k : ℤ) :
    lpOneAlg.toRealSeq (chebyshevFromU b) k = chebyshevFromU_seq b k := by
  simp [chebyshevFromU, lpOneAlg.toRealSeq, lpAlgRingData.toReal_ofReal]

@[simp] lemma chebyshevFromU_toSeq_natCast (b : l1Weighted ν) (n : ℕ) :
    lpOneAlg.toRealSeq (chebyshevFromU b) (↑n : ℤ) =
      2 * ∑' j : ℕ, l1Weighted.toSeq b (n + 2 * j) := by
  rw [chebyshevFromU_toSeq]; rfl

@[simp] lemma chebyshevFromU_toSeq_negSucc (b : l1Weighted ν) (n : ℕ) :
    lpOneAlg.toRealSeq (chebyshevFromU b) (Int.negSucc n) = 0 := by
  rw [chebyshevFromU_toSeq]; rfl

lemma chebyshevFromU_add (b d : l1Weighted ν) :
    chebyshevFromU (b + d) = chebyshevFromU b + chebyshevFromU d := by
  apply lpOneAlg.ext_toRealSeq; funext k
  rw [lpOneAlg.toRealSeq_add, Pi.add_apply]
  cases k with
  | ofNat n =>
    rw [show ((Int.ofNat n) : ℤ) = (↑n : ℤ) from rfl]
    rw [chebyshevFromU_toSeq_natCast, chebyshevFromU_toSeq_natCast,
      chebyshevFromU_toSeq_natCast]
    have hcong : (∑' j : ℕ, l1Weighted.toSeq (b + d) (n + 2 * j)) =
        ∑' j : ℕ, (l1Weighted.toSeq b (n + 2 * j) + l1Weighted.toSeq d (n + 2 * j)) :=
      tsum_congr fun j => l1Weighted.add_toSeq b d (n + 2 * j)
    rw [hcong, (summable_toSeq_shift b n).tsum_add (summable_toSeq_shift d n)]
    ring
  | negSucc n =>
    rw [chebyshevFromU_toSeq_negSucc, chebyshevFromU_toSeq_negSucc,
      chebyshevFromU_toSeq_negSucc]
    ring

lemma chebyshevFromU_smul (r : ℝ) (b : l1Weighted ν) :
    chebyshevFromU (r • b) = r • chebyshevFromU b := by
  apply lpOneAlg.ext_toRealSeq
  rw [lpOneAlg.toRealSeq_smul]; funext k
  rw [Pi.smul_apply, smul_eq_mul]
  cases k with
  | ofNat n =>
    rw [show ((Int.ofNat n) : ℤ) = (↑n : ℤ) from rfl]
    rw [chebyshevFromU_toSeq_natCast, chebyshevFromU_toSeq_natCast]
    have hcong : (∑' j : ℕ, l1Weighted.toSeq (r • b) (n + 2 * j)) =
        ∑' j : ℕ, r * l1Weighted.toSeq b (n + 2 * j) :=
      tsum_congr fun j => l1Weighted.smul_toSeq r b (n + 2 * j)
    rw [hcong, tsum_mul_left]
    ring
  | negSucc n =>
    rw [chebyshevFromU_toSeq_negSucc, chebyshevFromU_toSeq_negSucc]
    ring

/-! #### Round-trip identities -/

/-- U-side round trip: `chebyshevToU (chebyshevFromU b) = b`, exact on all of
`l1Weighted ν`. Together with `chebyshevFromU_chebyshevToU_toSeq` this certifies that
`chebyshevToU` and `chebyshevFromU` are mutually inverse basis conversions. -/
theorem chebyshevToU_chebyshevFromU (b : l1Weighted ν) :
    chebyshevToU (chebyshevFromU b) = b := by
  apply l1Weighted.ext; intro m
  rw [chebyshevToU_toSeq]
  have hm : l1Chebyshev.toSeq (chebyshevFromU b) (↑m : ℤ) =
      2 * ∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j) := chebyshevFromU_toSeq_natCast b m
  have hm2 : l1Chebyshev.toSeq (chebyshevFromU b) ((↑m : ℤ) + 2) =
      2 * ∑' j : ℕ, l1Weighted.toSeq b ((m + 2) + 2 * j) := by
    rw [show ((↑m : ℤ) + 2) = (↑(m + 2) : ℤ) from by omega]
    exact chebyshevFromU_toSeq_natCast b (m + 2)
  rw [hm, hm2]
  -- Telescoping: `Σ_j b_{m+2j} = b_m + Σ_j b_{(m+2)+2j}`.
  have hkey : (∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j)) =
      l1Weighted.toSeq b m + ∑' j : ℕ, l1Weighted.toSeq b ((m + 2) + 2 * j) := by
    have hshift : (∑' j : ℕ, l1Weighted.toSeq b (m + 2 * (j + 1))) =
        ∑' j : ℕ, l1Weighted.toSeq b ((m + 2) + 2 * j) :=
      tsum_congr fun j => by
        rw [show m + 2 * (j + 1) = (m + 2) + 2 * j from by omega]
    rw [(summable_toSeq_shift b m).tsum_eq_zero_add, hshift,
      show m + 2 * 0 = m from by omega]
  rw [hkey]
  ring

/-- Summability of `l1Chebyshev` coefficients along an even-spaced nonnegative
mode progression (uses ν ≥ 1 to compare with fiber norms). -/
private lemma summable_toRealSeq_even (c : l1Chebyshev ν) (n : ℕ) :
    Summable (fun j : ℕ => l1Chebyshev.toSeq c (↑(n + 2 * j) : ℤ)) := by
  have habs : Summable (fun j : ℕ => ‖c (↑(n + 2 * j) : ℤ)‖) :=
    (lpOneAlg.summable_norm c).comp_injective (by intro x y h; simp only at h; omega)
  refine Summable.of_norm (Summable.of_nonneg_of_le
    (fun j => norm_nonneg _) (fun j => ?_) habs)
  rw [Real.norm_eq_abs, norm_fiber_natCast]
  exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (one_le_nu (ν := ν)))

/-- T-side round trip on nonnegative modes: `(chebyshevFromU (chebyshevToU c))_n = c_n`
for `n ≥ 0`. (Negative modes are zeroed — see `chebyshevFromU_toSeq_negSucc`; the pair
of conversions is inverse on the nonnegative-mode part that carries the T-series.) -/
theorem chebyshevFromU_chebyshevToU_toSeq (c : l1Chebyshev ν) (n : ℕ) :
    lpOneAlg.toRealSeq (chebyshevFromU (chebyshevToU c)) (↑n : ℤ) =
      lpOneAlg.toRealSeq c (↑n : ℤ) := by
  rw [chebyshevFromU_toSeq_natCast]
  have hgoal : lpOneAlg.toRealSeq c (↑n : ℤ) = l1Chebyshev.toSeq c (↑n : ℤ) := rfl
  rw [hgoal]
  have hx : Summable (fun j : ℕ => l1Chebyshev.toSeq c (↑(n + 2 * j) : ℤ)) :=
    summable_toRealSeq_even c n
  have hx' : Summable (fun j : ℕ => l1Chebyshev.toSeq c (↑(n + 2 * (j + 1)) : ℤ)) :=
    hx.comp_injective (by intro x y h; simp only at h; omega)
  have hcong : (∑' j : ℕ, l1Weighted.toSeq (chebyshevToU c) (n + 2 * j)) =
      ∑' j : ℕ, (1 / 2) * (l1Chebyshev.toSeq c (↑(n + 2 * j) : ℤ) -
        l1Chebyshev.toSeq c (↑(n + 2 * (j + 1)) : ℤ)) := by
    refine tsum_congr fun j => ?_
    rw [chebyshevToU_toSeq,
      show ((↑(n + 2 * j) : ℤ) + 2) = (↑(n + 2 * (j + 1)) : ℤ) from by omega]
    ring
  rw [hcong, tsum_mul_left, hx.tsum_sub hx']
  have hza := hx.tsum_eq_zero_add
  have hX0 : l1Chebyshev.toSeq c (↑(n + 2 * 0) : ℤ) = l1Chebyshev.toSeq c (↑n : ℤ) := by
    norm_num
  rw [hza, hX0]
  ring

/-! #### Norm bound and the transport constant κ -/

private lemma chebyshevFromU_elem_negSucc (b : l1Weighted ν) (n : ℕ) :
    (chebyshevFromU b) (Int.negSucc n) = 0 := by
  show lpAlgRingData.ofReal (E := ScaledRealZ ν) _ (chebyshevFromU_seq b _) = 0
  rw [chebyshevFromU_seq_negSucc, lpAlgRingData.ofReal_zero]

private lemma chebyshevFromU_elem_natCast_le (b : l1Weighted ν) (n : ℕ) :
    ‖(chebyshevFromU b) (↑n : ℤ)‖ ≤
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)| * (ν : ℝ) ^ n := by
  show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n : ℤ)
      (chebyshevFromU_seq b (↑n : ℤ))‖ ≤ _
  exact chebyshevFromU_fiber_le b n

private lemma chebyshevFromU_norm_support (b : l1Weighted ν) :
    Function.support (fun k : ℤ => ‖(chebyshevFromU b) k‖) ⊆
      Set.range (fun n : ℕ => (↑n : ℤ)) := by
  intro k hk
  simp only [Function.mem_support] at hk
  cases k with
  | ofNat n => exact ⟨n, by simp⟩
  | negSucc n => exact absurd (by rw [chebyshevFromU_elem_negSucc, norm_zero]) hk

/-- Norm bound for the U→T conversion: `‖chebyshevFromU b‖ ≤ (2ν²/(ν²-1))·‖b‖`.
The constant is the operator norm (column ratios approach it as the mode grows), and
blows up as ν ↓ 1 — the quantitative degeneration of T↔U transport at ν = 1. -/
lemma chebyshevFromU_norm_le (b : l1Weighted ν) :
    ‖chebyshevFromU b‖ ≤ 2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) * ‖b‖ := by
  rw [lpOneAlg.norm_eq_tsum]
  have hinj : Function.Injective (fun n : ℕ => (↑n : ℤ)) := by
    intro n m h; simp only at h; omega
  have hre : (∑' n : ℕ, ‖(chebyshevFromU b) (↑n : ℤ)‖) =
      ∑' k : ℤ, ‖(chebyshevFromU b) k‖ :=
    hinj.tsum_eq (chebyshevFromU_norm_support b)
  rw [← hre]
  have hsA : Summable (fun n : ℕ => ‖(chebyshevFromU b) (↑n : ℤ)‖) :=
    (lpOneAlg.summable_norm (chebyshevFromU b)).comp_injective hinj
  have hsB : Summable (fun n : ℕ =>
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (n + 2 * j)| * (ν : ℝ) ^ n) :=
    (fromU_marginal_summable b).mul_left 2
  refine (Summable.tsum_le_tsum
    (fun n => chebyshevFromU_elem_natCast_le b n) hsA hsB).trans ?_
  rw [tsum_mul_left]
  -- interchange the double sum, then bound rows by the geometric series
  have hu : Summable (Function.uncurry fun j k : ℕ =>
      |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) := fromU_prod_summable b
  have hcomm : (∑' k : ℕ, ∑' j : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) =
      ∑' j : ℕ, ∑' k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k :=
    Summable.tsum_comm hu
  rw [hcomm]
  have hrows : Summable (fun j : ℕ =>
      ∑' k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) :=
    ((summable_prod_of_nonneg
      (fun p => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))).mp
      (fromU_prod_summable b)).2
  have hgeom : Summable (fun j : ℕ => (((ν : ℝ) ^ 2)⁻¹) ^ j * ‖b‖) :=
    (summable_geometric_of_lt_one (invsq_nonneg (ν := ν))
      (invsq_lt_one (ν := ν))).mul_right ‖b‖
  have hstep2 : (∑' j : ℕ, ∑' k : ℕ, |l1Weighted.toSeq b (k + 2 * j)| * (ν : ℝ) ^ k) ≤
      ∑' j : ℕ, (((ν : ℝ) ^ 2)⁻¹) ^ j * ‖b‖ :=
    Summable.tsum_le_tsum (fun j => fromU_row_le b j) hrows hgeom
  refine (mul_le_mul_of_nonneg_left hstep2 (by norm_num : (0 : ℝ) ≤ 2)).trans
    (le_of_eq ?_)
  have hgeo_eq : (∑' j : ℕ, (((ν : ℝ) ^ 2)⁻¹) ^ j * ‖b‖) =
      (1 - ((ν : ℝ) ^ 2)⁻¹)⁻¹ * ‖b‖ := by
    rw [tsum_mul_right,
      tsum_geometric_of_lt_one (invsq_nonneg (ν := ν)) (invsq_lt_one (ν := ν))]
  rw [hgeo_eq]
  have h1 : ((ν : ℝ) ^ 2) ≠ 0 := (pow_pos ν.2 2).ne'
  have h2 : ((ν : ℝ) ^ 2) - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_nusq (ν := ν)).ne'
  field_simp

/-- The U→T conversion as a CLM with operator norm `2ν²/(ν²-1)`. -/
noncomputable def chebyshevFromU_CLM : l1Weighted ν →L[ℝ] l1Chebyshev ν :=
  LinearMap.mkContinuous
    { toFun := chebyshevFromU
      map_add' := chebyshevFromU_add
      map_smul' := fun r b => by simp [chebyshevFromU_smul] }
    (2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1))
    (fun b => chebyshevFromU_norm_le b)

@[simp] lemma chebyshevFromU_CLM_apply (b : l1Weighted ν) :
    chebyshevFromU_CLM b = chebyshevFromU b := rfl

/-- **Transport conditioning of the certified T↔U pair**:
`‖chebyshevToU_CLM‖ · ‖chebyshevFromU_CLM‖ ≤ (ν² + 1)/(ν² - 1)`.

In closed form the right-hand side is `coth(log ν)` — kept rational in ν² here.
It diverges as ν ↓ 1 and decreases to 1 as ν grows: the conditioning number of the
certified basis transport. (The repo's symmetric bilateral storage adds a zero-mode
asymmetry to the *full* storage-level transport — `κ_repo = 1 + coth(log ν)` — which is
a separate, storage-dependent refinement, not formalized here.) -/
theorem chebyshevToU_CLM_norm_mul_chebyshevFromU_CLM_norm_le :
    ‖chebyshevToU_CLM (ν := ν)‖ * ‖chebyshevFromU_CLM (ν := ν)‖ ≤
      ((ν : ℝ) ^ 2 + 1) / ((ν : ℝ) ^ 2 - 1) := by
  have hden : (0 : ℝ) < (ν : ℝ) ^ 2 - 1 := by linarith [one_lt_nusq (ν := ν)]
  have h1 : ‖chebyshevToU_CLM (ν := ν)‖ ≤ (1 + ((ν : ℝ) ^ 2)⁻¹) / 2 :=
    LinearMap.mkContinuous_norm_le _ (by positivity) _
  have h2 : ‖chebyshevFromU_CLM (ν := ν)‖ ≤ 2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) :=
    LinearMap.mkContinuous_norm_le _
      (div_nonneg (by positivity) hden.le) _
  refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
  have hν2 : ((ν : ℝ) ^ 2) ≠ 0 := (pow_pos ν.2 2).ne'
  field_simp

/-- CLM-level U-side round trip: `chebyshevToU_CLM ∘ chebyshevFromU_CLM = id` —
the certified pair is a section–retraction of Banach spaces. -/
theorem chebyshevToU_CLM_comp_chebyshevFromU_CLM :
    (chebyshevToU_CLM (ν := ν)).comp (chebyshevFromU_CLM (ν := ν)) =
      ContinuousLinearMap.id ℝ (l1Weighted ν) :=
  ContinuousLinearMap.ext fun b => by simp [chebyshevToU_chebyshevFromU]

end ChebyshevFromU
end RadiiPolynomial
