import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Mul
import RadiiPolynomial.source.lpSpace.ScaledReal
import RadiiPolynomial.source.lpSpace.CauchyProduct
import RadiiPolynomial.source.lpSpace.NormHelpers
/-!
# Weighted sequence-space infrastructure

This file provides the concrete weighted spaces used by the system-level API:
- `lpWeighted ν p`
- `l1Weighted ν`
- norm/membership bridge lemmas (`norm_eq_tailTsum_of_fin_zero`, `tailTsum_le_norm_of_eq`, `norm_mk_le_of_pointwise`)
- single-index embedding (`single`, `single_CLM`)
- coefficient truncation (`trunc`, `trunc_CLM`)

Differentiability lemmas (`differentiable_mk_of_finSupp`, `fderiv_mk_of_finSupp_toSeq_tail`)
are in `lpWeightedDeriv.lean` to avoid pulling in `FDeriv` imports.
-/

open scoped BigOperators Topology NNReal ENNReal Matrix

noncomputable section

namespace RadiiPolynomial

/-- Weighted `ℓᵖ` space realized as `lp` with scaled fibers. -/
abbrev lpWeighted (ν : PosReal) (p : ℝ≥0∞) := lp (ScaledReal ν) p

/-- Weighted `ℓ¹` Banach algebra via `lpOneAlg`. Ring structure from `SubMulWeight`. -/
abbrev l1Weighted (ν : PosReal) := lpOneAlg ℕ (ScaledReal ν)

namespace lpWeighted

variable {ν : PosReal} {p : ℝ≥0∞}

instance instUniformSpace [Fact (1 ≤ p)] : UniformSpace (lpWeighted ν p) := by
  change UniformSpace (lp (ScaledReal ν) p)
  infer_instance

instance instCompleteSpace [Fact (1 ≤ p)] : CompleteSpace (lpWeighted ν p) := by
  change CompleteSpace (lp (ScaledReal ν) p)
  infer_instance

/-- Underlying real sequence. -/
def toSeq (a : lpWeighted ν p) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

/-- Extensionality through coefficients. -/
lemma ext {a b : lpWeighted ν p} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate for weighted `ℓᵖ`. -/
def Mem (ν : PosReal) (p : ℝ≥0∞) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) p

/-- Construct an element from a sequence with finite weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν p a) : lpWeighted ν p :=
  ⟨fun n => ScaledReal.ofReal (a n), ha⟩

@[simp] lemma toSeq_apply (a : lpWeighted ν p) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl

/-- Bridge: the `lp` coercion of `mk` gives `ScaledReal.ofReal ∘ f` at each index.
Useful for `simp_rw` when the goal has `↑(mk f hf) n` instead of `toSeq`. -/
@[simp] lemma mk_val_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) :
    (mk a ha).val n = ScaledReal.ofReal (a n) := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : lpWeighted ν p) n = 0 := rfl
@[simp] lemma neg_toSeq (a : lpWeighted ν p) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : lpWeighted ν p) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl

lemma norm_eq_tsum_rpow (hp : 0 < p.toReal) (a : lpWeighted ν p) :
    ‖a‖ = (∑' n, (|toSeq a n| * (ν : ℝ) ^ n) ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  simp only [one_div, toSeq_apply]
  rfl

lemma mem_iff_summable (hp : 0 < p.toReal) (a : ℕ → ℝ) (hp' : p ≠ ⊤) :
    Mem ν p a ↔ Summable (fun n => (|a n| * (ν : ℝ) ^ n) ^ p.toReal) := by
  simp only [Mem, Memℓp, ScaledReal.ofReal_apply, ne_eq]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  simp only [hp0, hp', ↓reduceIte, ScaledReal.norm_def, ScaledReal.toReal_apply]

end lpWeighted

namespace l1Weighted

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

/-- Access the underlying `lp` element. -/
def toLpWeighted (a : l1Weighted ν) : lpWeighted ν 1 := a.toLp

/-- Underlying real sequence. -/
def toSeq (a : l1Weighted ν) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

/-- Membership predicate for `l1Weighted`. -/
def Mem (ν : PosReal) (a : ℕ → ℝ) : Prop := lpWeighted.Mem ν 1 a

/-- Construct an `l1Weighted` element from a sequence with finite weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν a) : l1Weighted ν := ⟨lpWeighted.mk a ha⟩

/-- Extensionality through coefficients. -/
lemma ext {a b : l1Weighted ν} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lpOneAlg.ext h

@[simp] lemma toSeq_apply (a : l1Weighted ν) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl

@[simp] lemma mk_val_apply (a : ℕ → ℝ) (ha : Mem ν a) (n : ℕ) :
    (mk a ha).toLp.val n = ScaledReal.ofReal (a n) := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : l1Weighted ν) n = 0 := rfl
@[simp] lemma neg_toSeq (a : l1Weighted ν) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : l1Weighted ν) (n : ℕ) :
    toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : l1Weighted ν) (n : ℕ) :
    toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : l1Weighted ν) (n : ℕ) :
    toSeq (c • a) n = c * toSeq a n := by
  show ScaledReal.toReal ((c • a).toLp.val n) = c * ScaledReal.toReal (a.toLp.val n)
  rw [lpOneAlg.toLp_smul]; rfl

lemma mem_iff (a : ℕ → ℝ) :
    Mem ν a ↔ Summable (fun n => |a n| * (ν : ℝ) ^ n) := by
  have h := @lpWeighted.mem_iff_summable ν 1 (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
    ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h

lemma norm_eq_tsum (a : l1Weighted ν) :
    ‖a‖ = ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
  have h := lpWeighted.norm_eq_tsum_rpow (ν := ν) (p := (1 : ℝ≥0∞))
    (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a.toLp
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one] at h
  show ‖a.toLp‖ = _; exact h

lemma norm_eq_Icc_sum_of_support (a : l1Weighted ν) (M : ℕ)
    (hsupp : ∀ n, M < n → toSeq a n = 0) :
    ‖a‖ = ∑ n ∈ Finset.Icc 0 M, |toSeq a n| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  refine tsum_eq_sum ?_
  intro n hn
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  have h0 : toSeq a n = 0 := hsupp n (by omega)
  rw [h0, abs_zero, zero_mul]

/-- Direct summability of weighted terms for `a ∈ ℓ¹_ν`. -/
lemma summable_weighted (a : l1Weighted ν) :
    Summable (fun n => |toSeq a n| * (ν : ℝ) ^ n) :=
  (mem_iff (toSeq a)).mp a.toLp.2

section CoordinateCLM

/-- Coordinate evaluation `toSeq · n` as a CLM on `l1Weighted ν`.
`|toSeq a n| ≤ ν⁻ⁿ · ‖a‖` since `|a_n| · ν^n ≤ ‖a‖`. -/
noncomputable def toSeq_CLM (n : ℕ) : l1Weighted ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => toSeq a n
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp [smul_eq_mul] }
    ((ν : ℝ) ^ n)⁻¹
    (fun a => by
      have hle : |toSeq a n| * (ν : ℝ) ^ n ≤ ‖a‖ := by
        rw [norm_eq_tsum]
        exact (summable_weighted a).le_tsum n (fun k _ =>
          mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      exact (le_inv_mul_iff₀ (pow_pos ν.2 n)).mpr (by rwa [mul_comm]))

end CoordinateCLM

section NormSplitting

/-- Finite weighted prefix bound. -/
lemma finSum_weighted_toSeq_le_norm (a : l1Weighted ν) (N : ℕ) :
    ∑ k : Fin (N + 1), |toSeq a k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖a‖ := by
  have hsum := summable_weighted a
  have hrange :
      ∑ n ∈ Finset.range (N + 1), |toSeq a n| * (ν : ℝ) ^ n ≤
        ∑' n, |toSeq a n| * (ν : ℝ) ^ n :=
    hsum.sum_le_tsum (Finset.range (N + 1))
      (fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _))
  have hleft :
      ∑ k : Fin (N + 1), |toSeq a k| * (ν : ℝ) ^ (k : ℕ) =
        ∑ n ∈ Finset.range (N + 1), |toSeq a n| * (ν : ℝ) ^ n :=
    Fin.sum_univ_eq_sum_range (fun n => |toSeq a n| * (ν : ℝ) ^ n) (N + 1)
  exact (hleft.trans_le hrange).trans_eq (norm_eq_tsum a).symm

/-- Norm splitting: `‖a‖ = ∑_{n ∈ range k} f(n) + ∑' n, f(n+k)`. -/
lemma norm_eq_finRangeSum_add_tailTsum (a : l1Weighted ν) (k : ℕ) :
    ‖a‖ = ∑ n ∈ Finset.range k, |toSeq a n| * (ν : ℝ) ^ n +
      ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) := by
  rw [norm_eq_tsum]
  exact ((summable_weighted a).sum_add_tsum_nat_add k).symm

/-- If `toSeq a n = 0` for `n < k`, then `‖a‖` equals the tail tsum from index `k`. -/
lemma norm_eq_tailTsum_of_fin_zero (a : l1Weighted ν) (k : ℕ)
    (hfin : ∀ n, n < k → toSeq a n = 0) :
    ‖a‖ = ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) := by
  rw [norm_eq_finRangeSum_add_tailTsum a k]
  have h_zero : ∑ n ∈ Finset.range k, |toSeq a n| * (ν : ℝ) ^ n = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [hfin n (Finset.mem_range.mp hn)]; simp
  rw [h_zero, zero_add]

/-- If tail coefficients of `a` match `b` from index `k`, then `tail_tsum(a, k) ≤ ‖b‖`. -/
lemma tailTsum_le_norm_of_eq (a b : l1Weighted ν) (k : ℕ)
    (heq : ∀ n, k ≤ n → toSeq a n = toSeq b n) :
    ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) ≤ ‖b‖ := by
  have h_eq : ∀ n, |toSeq a (n + k)| = |toSeq b (n + k)| :=
    fun n => by rw [heq _ (by omega)]
  simp_rw [h_eq]
  rw [norm_eq_finRangeSum_add_tailTsum b k]
  linarith [Finset.sum_nonneg (fun n (_ : n ∈ Finset.range k) =>
    mul_nonneg (abs_nonneg (toSeq b n)) (pow_nonneg ν.coe_nonneg n))]

/-- If `a` kills modes below `k` and matches `b` on modes ≥ `k`, then `‖a‖ ≤ ‖b‖`. -/
lemma norm_le_of_fin_zero_tail_eq (a b : l1Weighted ν) (k : ℕ)
    (hfin : ∀ n, n < k → toSeq a n = 0)
    (htail : ∀ n, k ≤ n → toSeq a n = toSeq b n) :
    ‖a‖ ≤ ‖b‖ :=
  (norm_eq_tailTsum_of_fin_zero a k hfin).symm ▸ tailTsum_le_norm_of_eq a b k htail

/-- Pointwise-dominated norm bound: if `|f n| ≤ C * |toSeq a n|`,
then `‖mk f hf‖ ≤ C * ‖a‖`. -/
lemma norm_mk_le_of_pointwise (f : ℕ → ℝ) (hf : Mem ν f)
    (a : l1Weighted ν) (C : ℝ) (hle : ∀ n, |f n| ≤ C * |toSeq a n|) :
    ‖mk f hf‖ ≤ C * ‖a‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n =>
    calc |f n| * (ν : ℝ) ^ n
        ≤ C * |toSeq a n| * (ν : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (hle n) (pow_nonneg ν.coe_nonneg n)
      _ = C * (|toSeq a n| * (ν : ℝ) ^ n) := by ring)
    ((mem_iff f).mp hf) ((summable_weighted a).mul_left C)

end NormSplitting

section Membership

/-- Shifted weighted summability. -/
lemma summable_shifted_weighted (b : l1Weighted ν) :
    Summable (fun n => |toSeq b (n - 1)| * (ν : ℝ) ^ n) := by
  rw [← summable_nat_add_iff (k := 1)]
  exact (summable_weighted b).mul_left (ν : ℝ) |>.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    fun n => le_of_eq (by simp only [Nat.add_sub_cancel, pow_succ]; ring)

/-- Membership via eventual domination with shifted index. -/
lemma mem_of_eventually_le_add_shift (f : ℕ → ℝ) (a b : l1Weighted ν) (N : ℕ)
    (htail : ∀ n, N < n → |f n| ≤ |toSeq a n| + |toSeq b (n - 1)|) :
    Mem ν f := by
  rw [mem_iff]
  exact Summable.of_norm_bounded_eventually_nat
    (((summable_weighted a).add (summable_shifted_weighted b)).congr
      fun n => (add_mul ..).symm)
    (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => by
      simp only [Real.norm_eq_abs, abs_mul, abs_abs]
      have hν : (0 : ℝ) ≤ ↑ν ^ n := pow_nonneg (le_of_lt ν.2) n
      rw [abs_of_nonneg hν]
      exact mul_le_mul_of_nonneg_right (htail n (by omega)) hν⟩)

end Membership

section Single

/-- Sequence with value `x` at index `n` and zero elsewhere. -/
def single (n : ℕ) (x : ℝ) : l1Weighted ν :=
  mk (fun k => if k = n then x else 0) (by
    rw [mem_iff]
    have h : (fun k => |if k = n then x else 0| * (ν : ℝ) ^ k) =
        fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
      ext k; split_ifs with hk <;> simp [hk]
    rw [h]
    exact summable_of_ne_finset_zero (s := {n}) (fun k hk => by simp at hk; simp [hk]))

@[simp] lemma single_toSeq (idx n : ℕ) (x : ℝ) :
    toSeq (single (ν := ν) idx x) n = if n = idx then x else 0 := by
  simp only [single, mk_apply]

@[simp] lemma single_toSeq_self (n : ℕ) (x : ℝ) :
    toSeq (single n x : l1Weighted ν) n = x := by
  simp only [single_toSeq, ite_true]
lemma single_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) :
    toSeq (single n x : l1Weighted ν) k = 0 := by
  simp only [single_toSeq, if_neg h]

lemma norm_single (n : ℕ) (x : ℝ) :
    ‖(single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  have h : (fun k => |toSeq (single n x : l1Weighted ν) k| * (ν : ℝ) ^ k) =
      fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
    ext k; simp only [single_toSeq]; split_ifs with hk <;> simp [hk]
  rw [h, tsum_ite_eq]

/-- `single n` as a CLM. -/
noncomputable def single_CLM (n : ℕ) : ℝ →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := single n
      map_add' := fun x y => by
        apply ext; intro k; simp only [single_toSeq, add_toSeq]; split_ifs <;> simp
      map_smul' := fun r x => by
        apply ext; intro k
        simp only [single_toSeq, smul_toSeq, RingHom.id_apply]; split_ifs <;> simp }
    ((ν : ℝ) ^ n)
    (fun x => by show ‖single n x‖ ≤ _; rw [norm_single, Real.norm_eq_abs, mul_comm])

/-- `toSeq` distributes over finite sums. -/
@[simp] lemma toSeq_finset_sum {ι : Type*} (s : Finset ι) (g : ι → l1Weighted ν) (n : ℕ) :
    toSeq (∑ i ∈ s, g i) n = ∑ i ∈ s, toSeq (g i) n := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp only [Finset.sum_cons, add_toSeq, ih]

@[simp] lemma single_CLM_apply (n : ℕ) (x : ℝ) :
    (single_CLM (ν := ν) n) x = single n x := rfl

@[simp] lemma single_CLM_toSeq_self (n : ℕ) (x : ℝ) :
    toSeq (single_CLM (ν := ν) n x) n = x := single_toSeq_self n x

@[simp] lemma single_CLM_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) :
    toSeq (single_CLM (ν := ν) n x) k = 0 := single_toSeq_ne n k x h

end Single

section Truncation

/-- Coefficient truncation at order `N` in `ℓ¹_ν`. -/
def trunc (N : ℕ) (a : l1Weighted ν) : l1Weighted ν :=
  mk (fun n => if n ≤ N then toSeq a n else 0) (by
    rw [mem_iff]
    have h : (fun n => |(if n ≤ N then toSeq a n else 0 : ℝ)| * (ν : ℝ) ^ n) =
        fun n => if n ≤ N then |toSeq a n| * (ν : ℝ) ^ n else 0 := by
      ext n; split_ifs <;> simp
    rw [h]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) (fun n hn => by
      have hnot : ¬ n ≤ N := fun hle => hn (by simp [Finset.mem_Icc, hle])
      simp [hnot]))

lemma coeff_trunc (N : ℕ) (a : l1Weighted ν) (n : ℕ) :
    toSeq (trunc N a) n = if n ≤ N then toSeq a n else 0 := by
  simp [trunc]

private lemma trunc_add (N : ℕ) (a b : l1Weighted ν) :
    trunc N (a + b) = trunc N a + trunc N b := by
  apply ext; intro n; simp only [coeff_trunc, add_toSeq]; split_ifs <;> simp

private lemma trunc_smul (N : ℕ) (c : ℝ) (a : l1Weighted ν) :
    trunc N (c • a) = c • trunc N a := by
  apply ext; intro n; simp only [coeff_trunc, smul_toSeq]; split_ifs <;> simp

private lemma trunc_norm_le (N : ℕ) (a : l1Weighted ν) :
    ‖trunc N a‖ ≤ 1 * ‖a‖ := by
  rw [one_mul, norm_eq_tsum, norm_eq_tsum]
  exact ((mem_iff _).mp (trunc N a).toLp.2).tsum_le_tsum (fun n => by
    simp only [coeff_trunc]
    split_ifs <;> simp [mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)])
    ((mem_iff _).mp a.toLp.2)

/-- Truncation as a continuous linear map on `ℓ¹_ν`. -/
noncomputable def trunc_CLM (N : ℕ) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := trunc N
      map_add' := trunc_add N
      map_smul' := fun c a => by simp [trunc_smul] }
    1
    (trunc_norm_le N)

@[simp] lemma trunc_CLM_apply (N : ℕ) (a : l1Weighted ν) :
    trunc_CLM N a = trunc N a := rfl

end Truncation

section TailProjection

/-- Tail projection at order `N` in `ℓ¹_ν`: complement of `trunc`. -/
def tailProj (N : ℕ) (a : l1Weighted ν) : l1Weighted ν :=
  mk (fun n => if N < n then toSeq a n else 0) (by
    rw [mem_iff]
    have h : (fun n => |(if N < n then toSeq a n else 0 : ℝ)| * (ν : ℝ) ^ n) =
        fun n => if N < n then |toSeq a n| * (ν : ℝ) ^ n else 0 := by
      ext n; split_ifs <;> simp
    rw [h]
    exact (summable_weighted a).of_nonneg_of_le
      (fun n => by split_ifs <;>
        simp [mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)])
      (fun n => by split_ifs <;>
        simp [mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)]))

lemma coeff_tailProj (N : ℕ) (a : l1Weighted ν) (n : ℕ) :
    toSeq (tailProj N a) n = if N < n then toSeq a n else 0 := by
  simp [tailProj]

private lemma tailProj_add (N : ℕ) (a b : l1Weighted ν) :
    tailProj N (a + b) = tailProj N a + tailProj N b := by
  apply ext; intro n; simp only [coeff_tailProj, add_toSeq]; split_ifs <;> simp

private lemma tailProj_smul (N : ℕ) (c : ℝ) (a : l1Weighted ν) :
    tailProj N (c • a) = c • tailProj N a := by
  apply ext; intro n; simp only [coeff_tailProj, smul_toSeq]; split_ifs <;> simp

private lemma tailProj_norm_le (N : ℕ) (a : l1Weighted ν) :
    ‖tailProj N a‖ ≤ 1 * ‖a‖ := by
  rw [one_mul, norm_eq_tsum, norm_eq_tsum]
  exact ((mem_iff _).mp (tailProj N a).toLp.2).tsum_le_tsum (fun n => by
    simp only [coeff_tailProj]
    split_ifs <;> simp [mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)])
    ((mem_iff _).mp a.toLp.2)

/-- Tail projection as a continuous linear map on `ℓ¹_ν`. -/
noncomputable def tailProj_CLM (N : ℕ) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := tailProj N
      map_add' := tailProj_add N
      map_smul' := fun c a => by simp [tailProj_smul] }
    1
    (tailProj_norm_le N)

@[simp] lemma tailProj_CLM_apply (N : ℕ) (a : l1Weighted ν) :
    tailProj_CLM N a = tailProj N a := rfl

end TailProjection

/-! ### Banach Algebra API (from lpOneAlg + HasAntidiagonal) -/

section BanachAlgebra

/-- `toSeq` of l1Weighted multiplication = CauchyProduct of `toSeq`.
Bridge via `CauchyProduct.eq_addRingConvolution`. -/
@[simp] lemma toSeq_mul (a b : l1Weighted ν) (n : ℕ) :
    toSeq (a * b) n = CauchyProduct (toSeq a) (toSeq b) n := by
  have h := congr_fun (CauchyProduct.eq_addRingConvolution (toSeq a) (toSeq b)) n
  rw [h]; rfl

/-- `toSeq` of the multiplicative identity. -/
@[simp] lemma one_toSeq_eq (n : ℕ) :
    toSeq (1 : l1Weighted ν) n = if n = 0 then 1 else 0 := by
  show lpOneAlg.toRealSeq (1 : l1Weighted ν) n = _
  rw [lpOneAlg.toRealSeq_one_fun]
  simp [DiscreteConvolution.addDelta, Pi.single_apply]

@[simp] lemma one_toSeq_zero : toSeq (1 : l1Weighted ν) 0 = 1 := by
  rw [one_toSeq_eq]; simp
@[simp] lemma one_toSeq_succ (n : ℕ) : toSeq (1 : l1Weighted ν) (n + 1) = 0 := by
  rw [one_toSeq_eq]; simp

/-- `toSeq` of `c • a - 1` in terms of coefficient access. -/
lemma toSeq_smul_sub_one (c : ℝ) (a : l1Weighted ν) (n : ℕ) :
    toSeq (c • a - 1) n =
      c * toSeq a n - if n = 0 then 1 else 0 := by
  simp only [sub_toSeq, smul_toSeq, one_toSeq_eq]

/-- `toSeq` of `(k : ℕ) • a - 1` — converts ℕ smul to ℝ smul. -/
lemma toSeq_nsmul_sub_one (k : ℕ) (a : l1Weighted ν) (n : ℕ) :
    toSeq ((k : ℕ) • a - 1) n =
      (k : ℝ) * toSeq a n - if n = 0 then 1 else 0 := by
  rw [show (k : ℕ) • a = (k : ℝ) • a from by norm_cast]
  exact toSeq_smul_sub_one k a n

@[simp] lemma algebraMap_apply (r : ℝ) : algebraMap ℝ (l1Weighted ν) r = r • 1 := rfl

lemma norm_one_eq : ‖(1 : l1Weighted ν)‖ = 1 := by
  rw [norm_eq_tsum]
  have h : ∀ n, |toSeq (1 : l1Weighted ν) n| * (ν : ℝ) ^ n =
      if n = 0 then 1 else 0 := by
    intro n; rw [one_toSeq_eq]; split_ifs with hn <;> simp [hn]
  simp_rw [h]; exact tsum_ite_eq 0 1

lemma norm_algebraMap (r : ℝ) : ‖algebraMap ℝ (l1Weighted ν) r‖ = ‖r‖ := by
  simp only [algebraMap_apply, norm_smul, Real.norm_eq_abs, norm_one_eq, mul_one]

/-- Algebra ℚ instance via the chain ℚ →(algebraMap) ℝ →(algebraMap) l1Weighted.
Needed for `MvPolynomial.aeval` to target `l1Weighted ν`. -/
instance instAlgebraRat : Algebra ℚ (l1Weighted ν) :=
  RingHom.toAlgebra ((algebraMap ℝ (l1Weighted ν)).comp (algebraMap ℚ ℝ))

/-- ℚ-scalar action on l1Weighted agrees with ℝ-scalar action via cast. -/
@[simp] lemma ratSmul_eq (q : ℚ) (x : l1Weighted ν) :
    (q • x : l1Weighted ν) = ((q : ℝ) • x : l1Weighted ν) := by
  show algebraMap ℚ (l1Weighted ν) q * x = (q : ℝ) • x
  have : algebraMap ℚ (l1Weighted ν) q = (q : ℝ) • 1 := by
    show (algebraMap ℝ (l1Weighted ν)).comp (algebraMap ℚ ℝ) q = _
    simp [algebraMap_apply]
  rw [this, smul_mul_assoc]; simp

/-! ### Left multiplication CLM -/

noncomputable abbrev leftMul (a : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  letI : Algebra ℝ (l1Weighted ν) := lpOneAlg.instAlgebra
  letI : IsScalarTower ℝ (l1Weighted ν) (l1Weighted ν) := IsScalarTower.right
  letI : SMulCommClass ℝ (l1Weighted ν) (l1Weighted ν) := Algebra.to_smulCommClass
  ContinuousLinearMap.mul ℝ (l1Weighted ν) a

@[simp] lemma leftMul_apply (a h : l1Weighted ν) : leftMul a h = a * h := rfl

lemma norm_leftMul_le (a : l1Weighted ν) : ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le _ _ a

lemma leftMul_add (a b : l1Weighted ν) :
    leftMul (a + b) = leftMul a + leftMul b :=
  map_add (ContinuousLinearMap.mul ℝ (l1Weighted ν)) a b

lemma leftMul_sub (a b : l1Weighted ν) :
    leftMul (a - b) = leftMul a - leftMul b :=
  map_sub (ContinuousLinearMap.mul ℝ (l1Weighted ν)) a b

lemma leftMul_smul (c : ℝ) (a : l1Weighted ν) :
    leftMul (c • a) = c • leftMul a :=
  (ContinuousLinearMap.mul ℝ (l1Weighted ν)).map_smul c a

/-- Bridge: `a • .id = leftMul a`. Used by `derive_fderiv` automation. -/
lemma smul_id_eq_leftMul (a : l1Weighted ν) :
    a • ContinuousLinearMap.id ℝ (l1Weighted ν) = leftMul a := by
  ext h; simp [smul_eq_mul]

/-- Bridge: ℕ-smul inside `leftMul` → ℝ-smul. -/
lemma leftMul_nsmul (n : ℕ) (a : l1Weighted ν) :
    leftMul (n • a) = (↑n : ℝ) • leftMul a := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n a, leftMul_smul]

/-! ### CLM Operator Norm Bounds -/

/-- Operator norm bound: `‖π_N‖ ≤ 1`. -/
lemma norm_trunc_CLM_le (N : ℕ) : ‖trunc_CLM (ν := ν) N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Operator norm bound: `‖π_{N,∞}‖ ≤ 1`. -/
lemma norm_tailProj_CLM_le (N : ℕ) : ‖tailProj_CLM (ν := ν) N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end BanachAlgebra

end l1Weighted

end RadiiPolynomial
