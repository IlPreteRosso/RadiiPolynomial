import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic

/-!
# Chebyshev T→U conversion and U-integration on raw bilateral storage

- `chebyshevToU : l1Chebyshev ν → l1Weighted ν`, `(chebyshevToU c)_m = (c_m - c_{m+2})/2`
  (DLMF 18.9.9), bound `(1 + ν⁻²)/2` for every `ν > 0` (`chebyshevToU_norm_le_sharp`; its
  attainment is not proved).
- `uIntegrate : l1Weighted ν → l1Chebyshev ν`, `(uIntegrate b)_k = b_{k-1}/k` (`k ≥ 1`),
  `‖uIntegrate b‖ ≤ ν‖b‖`.


The U-carrier `l1Weighted ν` is used as a module only. `chebyshevShiftDiv = -(uIntegrate ∘
chebyshevToU)` lives in `Applications/IVP/Chebyshev/Operator.lean`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

variable {ν : PosReal}

/-! ### Fiber-norm and subseries helpers for `l1Chebyshev` at nonnegative modes

The public faces `summable_norm_natCast` and `norm_fiber_natCast` live in
`Chebyshev/Algebra.lean`. -/

/-- Norm sums restricted to shifted nonnegative modes are summable. -/
private lemma summable_norm_natCast_add (c : l1Chebyshev ν) (s : ℤ) :
    Summable (fun n : ℕ => ‖c (↑n + s)‖) :=
  (lpOneAlg.summable_norm c).comp_injective (fun n m h => by omega)

/-- Fiber norm at mode `m + 2`: `‖c_{m+2}‖ = |c_{m+2}|·ν^{m+2}`. -/
private lemma norm_fiber_natCast_add_two (c : l1Chebyshev ν) (m : ℕ) :
    ‖c ((↑m : ℤ) + 2)‖ = |l1Chebyshev.toSeq c (↑m + 2)| * (ν : ℝ) ^ (m + 2) := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑m : ℤ) + 2)]
  have h2 : ((↑m : ℤ) + 2).natAbs = m + 2 := by omega
  simp only [WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs, h2]
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
`‖chebyshevToU c‖ ≤ (1 + ν⁻²)/2 · ‖c‖`. The constant is attained on the unit
columns `e_m`, `m ≥ 2` (at `e_1` the ratio is `1/2`), so it is the operator norm; the
attainment is not proved here, only the bound. Holds for every `ν > 0`. -/
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


/-- The T→U conversion as a CLM with operator-norm bound `(1 + ν⁻²)/2`. -/
noncomputable def chebyshevToU_CLM : l1Chebyshev ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := chebyshevToU
      map_add' := chebyshevToU_add
      map_smul' := fun r c => by simp [chebyshevToU_smul] }
    ((1 + ((ν : ℝ) ^ 2)⁻¹) / 2)
    (fun c => chebyshevToU_norm_le_sharp c)


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
    ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
        (uIntegrate_seq b (↑(n + 1) : ℤ))‖ =
      |l1Weighted.toSeq b n| / (↑n + 1) * (ν : ℝ) ^ (n + 1) := by
  rw [ScaledRealZ.norm_equiv_apply, uIntegrate_seq_succ]
  have h1 : ((↑(n + 1) : ℤ)).natAbs = n + 1 := by omega
  rw [h1, abs_div, abs_of_pos (show (0 : ℝ) < ↑n + 1 by positivity)]

-- Fiber bound: `|b_n/(n+1)|·ν^{n+1} ≤ ν·(|b_n|·ν^n)` — the `1/k ≤ 1` estimate.
private lemma uIntegrate_fiber_le (b : l1Weighted ν) (n : ℕ) :
    ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
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
    Memℓp (fun k : ℤ => FiberTrivialization.equiv (E := ScaledRealZ ν) k
      (uIntegrate_seq b k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hinj : Function.Injective (fun n : ℕ => (↑(n + 1) : ℤ)) := by
    intro n m h; simp only at h; omega
  have hvanish : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ => (↑(n + 1) : ℤ)) →
      ‖FiberTrivialization.equiv (E := ScaledRealZ ν) k (uIntegrate_seq b k)‖ = 0 := by
    intro k hk
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        have h0 : uIntegrate_seq b (Int.ofNat 0) = 0 := uIntegrate_seq_zero b
        rw [h0, FiberTrivialization.equiv_zero, norm_zero]
      | succ n => exact absurd ⟨n, by simp⟩ hk
    | negSucc n =>
      rw [uIntegrate_seq_negSucc, FiberTrivialization.equiv_zero, norm_zero]
  rw [← Function.Injective.summable_iff hinj hvanish]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((l1Weighted.summable_weighted b).mul_left (ν : ℝ))
  simp only [Function.comp_apply]
  exact uIntegrate_fiber_le b n

/-- U-integration `(uIntegrate b)_k = b_{k-1}/k` for `k ≥ 1`, `0` for `k ≤ 0`:
the coefficient-level form of `∫ U_{k-1} = T_k/k`, mapping U-coefficients back
into the Chebyshev-T space. -/
def uIntegrate (b : l1Weighted ν) : l1Chebyshev ν :=
  ⟨⟨fun k => FiberTrivialization.equiv (E := ScaledRealZ ν) k (uIntegrate_seq b k),
    uIntegrate_memℓp b⟩⟩

-- Internal bridge (private, like its right-hand side); external files use the per-mode simp
-- lemmas below.
private lemma uIntegrate_toSeq (b : l1Weighted ν) (k : ℤ) :
    lpOneAlg.toRealSeq (uIntegrate b) k = uIntegrate_seq b k :=
  FiberTrivialization.equiv_symm_apply_equiv k _

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

/-! #### Norm bound: `‖uIntegrate b‖ ≤ ν·‖b‖` (attained on `b = e_0`; not proved here). -/

-- Element-level restatements of the fiber facts (the element applied at a mode is
-- definitionally `ofReal` of the raw sequence).
private lemma uIntegrate_elem_zero (b : l1Weighted ν) :
    (uIntegrate b) (Int.ofNat 0) = 0 := by
  show FiberTrivialization.equiv (E := ScaledRealZ ν) _ (uIntegrate_seq b _) = 0
  rw [show uIntegrate_seq b (Int.ofNat 0) = 0 from rfl, FiberTrivialization.equiv_zero]

private lemma uIntegrate_elem_negSucc (b : l1Weighted ν) (n : ℕ) :
    (uIntegrate b) (Int.negSucc n) = 0 := by
  show FiberTrivialization.equiv (E := ScaledRealZ ν) _ (uIntegrate_seq b _) = 0
  rw [uIntegrate_seq_negSucc, FiberTrivialization.equiv_zero]

private lemma uIntegrate_elem_succ_le (b : l1Weighted ν) (n : ℕ) :
    ‖(uIntegrate b) (↑(n + 1) : ℤ)‖ ≤
      (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n) := by
  show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑(n + 1) : ℤ)
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

/-- U-integration as a CLM with operator norm ≤ ν (attained on `e_0`; not proved here). -/
noncomputable def uIntegrate_CLM : l1Weighted ν →L[ℝ] l1Chebyshev ν :=
  LinearMap.mkContinuous
    { toFun := uIntegrate
      map_add' := uIntegrate_add
      map_smul' := fun r b => by simp [uIntegrate_smul] }
    (ν : ℝ)
    (fun b => uIntegrate_norm_le b)


end UIntegrate




end RadiiPolynomial
