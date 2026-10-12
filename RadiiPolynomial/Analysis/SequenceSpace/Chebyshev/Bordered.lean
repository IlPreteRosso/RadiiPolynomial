import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Symmetrize

/-!
# Bordered Chebyshev carrier and the storage-level T↔U transport

The repo's physical T-series `u = a₀ + 2·Σ_{k≥1} a_k T_k` lives in symmetric bilateral
storage; its norm counts every mode doubled except the zero mode. This file realizes that
storage as an honest one-sided weighted space and certifies its T↔U transport:

- `borderedWeight ν` — `1` at mode 0, `2ν^n` at modes `n ≥ 1`: the pushforward of the
  bilateral weight `ν^{|k|}` along the index cover `k ↦ |k|`, ramified at `0`.
- `l1Bordered ν` — the physical one-sided T-coefficient space.
- `nonnegRestrict : l1Chebyshev ν → l1Bordered ν` — restriction to the nonnegative modes,
  `2`-bounded (`nonnegRestrict_norm_le`) and isometric on symmetric storage
  (`nonnegRestrict_norm_of_isSymmetric`); its bundles `nonnegRestrictCLM` and
  `physicalBorderedEquiv` live in `Chebyshev/SymmetricSubalgebra.lean`.
- `borderedToU` / `borderedFromU` — a genuine two-sided Banach isomorphism
  (`borderedTU_equiv`) with `‖P‖ ≤ 1` and `‖P⁻¹‖ ≤ 2ν²/(ν²-1)`, so the transport
  conditioning is `κ_repo ≤ 2ν²/(ν²-1) = 1 + coth(log ν)`
  (`borderedToU_CLM_norm_mul_borderedFromU_CLM_norm_le`, on the bundle
  `norm_borderedTU_equiv_mul_norm_symm_le`). The `+1` over the clean pair's `coth(log ν)` is
  exactly the ramification of the cover at the zero mode.
- compatibility with the bilateral pair: `borderedToU ∘ nonnegRestrict = 2 • chebyshevToU`
  (`borderedToU_nonnegRestrict`) and `nonnegRestrict ∘ chebyshevFromU = 2 • borderedFromU`
  (`nonnegRestrict_chebyshevFromU`).

`l1Chebyshev.IsSymmetric`, `symmetrize` and `natEmbed` live in `Chebyshev/Symmetrize.lean`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### The bordered carrier: physical one-sided T-storage

`borderedWeight ν` is the pushforward of the bilateral weight `ν^{|k|}` along the
quotient `k ↦ |k|`: each unramified fiber `{±m}` contributes `2ν^m`, the ramified
fiber `{0}` contributes `1`. Restriction to the nonnegative modes maps the symmetric
subspace of `l1Chebyshev ν` (physical T-series `a₀ + 2Σ_{k≥1} a_k T_k`) isometrically onto
`l1Bordered ν` (`nonnegRestrict_norm_of_isSymmetric`; the bundled linear isometry equivalence is
`l1Chebyshev.physicalBorderedEquiv` in `Chebyshev/SymmetricSubalgebra.lean`), an honest one-sided
weighted space — the "bordering" datum as a weight.

On this carrier the T↔U transport `borderedToU`/`borderedFromU` is a genuine
two-sided Banach isomorphism with `‖P‖ ≤ 1` and `‖P⁻¹‖ ≤ 2ν²/(ν²-1)`, so
`κ_repo = ‖P‖·‖P⁻¹‖ ≤ 2ν²/(ν²-1) = 1 + coth(log ν)` — the `+1` over the clean
`κ = coth(log ν)` is exactly the ramification of the cover at the zero mode. -/

section BorderedWeight

/-- The bordered geometric weight: `1` at mode `0`, `2ν^n` at modes `n ≥ 1`. -/
def borderedWeight (ν : PosReal) : ℕ → ℝ :=
  fun n => if n = 0 then 1 else 2 * (ν : ℝ) ^ n

@[simp] lemma borderedWeight_zero (ν : PosReal) : borderedWeight ν 0 = 1 := rfl

@[simp] lemma borderedWeight_succ (ν : PosReal) (n : ℕ) :
    borderedWeight ν (n + 1) = 2 * (ν : ℝ) ^ (n + 1) := rfl

lemma borderedWeight_pos (ν : PosReal) (n : ℕ) : 0 < borderedWeight ν n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n => rw [borderedWeight_succ]; exact mul_pos two_pos (pow_pos ν.2 _)

/-- `ν^n ≤ borderedWeight ν n` — for every `ν > 0`. -/
lemma pow_le_borderedWeight (ν : PosReal) (n : ℕ) :
    (ν : ℝ) ^ n ≤ borderedWeight ν n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n =>
    rw [borderedWeight_succ]
    have h : (0 : ℝ) < (ν : ℝ) ^ (n + 1) := pow_pos ν.2 _
    linarith

/-- `borderedWeight ν n ≤ 2ν^n` — for every `ν > 0`. -/
lemma borderedWeight_le_two_mul (ν : PosReal) (n : ℕ) :
    borderedWeight ν n ≤ 2 * (ν : ℝ) ^ n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n => rw [borderedWeight_succ]

instance borderedWeight.instPosWeight (ν : PosReal) : PosWeight (borderedWeight ν) where
  weight_pos n := borderedWeight_pos ν n

/-- Submultiplicativity holds for every `ν > 0` (with slack `2 ≤ 4` in the interior). -/
instance borderedWeight.instSubMulWeightBase (ν : PosReal) :
    SubMulWeightBase (borderedWeight ν) where
  weight_pos n := borderedWeight_pos ν n
  weight_zero := borderedWeight_zero ν
  submul m n := by
    cases m with
    | zero => rw [Nat.zero_add, borderedWeight_zero, one_mul]
    | succ m =>
      cases n with
      | zero => rw [Nat.add_zero, borderedWeight_zero, mul_one]
      | succ n =>
        rw [show m + 1 + (n + 1) = (m + n + 1) + 1 from by omega, borderedWeight_succ,
          borderedWeight_succ, borderedWeight_succ]
        have h1 : (0 : ℝ) < (ν : ℝ) ^ (m + n + 1 + 1) := pow_pos ν.2 _
        have h2 : (ν : ℝ) ^ (m + 1) * (ν : ℝ) ^ (n + 1) = (ν : ℝ) ^ (m + n + 1 + 1) := by
          rw [← pow_add]; congr 1; omega
        nlinarith [h1, h2]

instance borderedWeight.instSubMulWeight (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    SubMulWeight (borderedWeight ν) where
  one_le n := by
    cases n with
    | zero => norm_num [borderedWeight]
    | succ n =>
      rw [borderedWeight_succ]
      have h : (1 : ℝ) ≤ (ν : ℝ) ^ (n + 1) := one_le_pow₀ Fact.out
      linarith

/-- `BorderedScaledReal ν n` is `ℝ` with norm `|x| · borderedWeight ν n`.

WARNING: the automatic `Ring` on `lpOneAlg ℕ (BorderedScaledReal ν)` is the plain
ℕ-Cauchy-product ring, NOT the physical Chebyshev product
`T_m·T_n = (T_{m+n} + T_{|m-n|})/2` (a folded/hypergroup convolution outside the
monoid-algebra frame). This carrier is used at the normed-space level only. -/
abbrev BorderedScaledReal (ν : PosReal) := WeightedScalar ℝ (borderedWeight ν)

/-- Physical one-sided T-coefficient space: `‖a‖ = |a₀| + 2Σ_{n≥1}|a_n|ν^n`. -/
abbrev l1Bordered (ν : PosReal) := lpOneAlg ℕ (BorderedScaledReal ν)

@[simp] theorem BorderedScaledReal.norm_lpAlgRingData_ofReal (ν : PosReal) (n : ℕ) (r : ℝ) :
    ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) n r‖ = |r| * borderedWeight ν n :=
  WeightedScalar.norm_ofReal r

variable {ν : PosReal}

/-- Fiber norm on the bordered carrier. -/
private lemma l1Bordered_norm_fiber (a : l1Bordered ν) (n : ℕ) :
    ‖a n‖ = |lpOneAlg.toRealSeq a n| * borderedWeight ν n := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight a n]
  simp only [BorderedScaledReal.norm_lpAlgRingData_ofReal, abs_one, one_mul,
    Real.norm_eq_abs]

end BorderedWeight

/-! #### Restriction of bilateral storage to the nonnegative modes -/

section SymmetricBridge

variable {ν : PosReal}

private lemma nonnegRestrict_fiber_le (a : l1Chebyshev ν) (n : ℕ) :
    |lpOneAlg.toRealSeq a (↑n : ℤ)| * borderedWeight ν n ≤ 2 * ‖a (↑n : ℤ)‖ := by
  rw [norm_fiber_natCast]
  have he : |l1Chebyshev.toSeq a (↑n : ℤ)| = |lpOneAlg.toRealSeq a (↑n : ℤ)| := rfl
  rw [he]
  refine (mul_le_mul_of_nonneg_left (borderedWeight_le_two_mul ν n) (abs_nonneg _)).trans
    (le_of_eq ?_)
  ring

private lemma nonnegRestrict_mem (a : l1Chebyshev ν) :
    Memℓp (fun n : ℕ => lpAlgRingData.ofReal (E := BorderedScaledReal ν) n
      (lpOneAlg.toRealSeq a (↑n : ℤ))) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_norm_natCast a).mul_left 2)
  rw [BorderedScaledReal.norm_lpAlgRingData_ofReal]
  exact nonnegRestrict_fiber_le a n

/-- Restriction of a bilateral sequence to its nonnegative modes, viewed in the
bordered carrier. On symmetric sequences this is an isometry
(`nonnegRestrict_norm_of_isSymmetric`). -/
def nonnegRestrict (a : l1Chebyshev ν) : l1Bordered ν :=
  ⟨⟨fun n => lpAlgRingData.ofReal (E := BorderedScaledReal ν) n
      (lpOneAlg.toRealSeq a (↑n : ℤ)),
    nonnegRestrict_mem a⟩⟩

@[simp] lemma nonnegRestrict_toSeq (a : l1Chebyshev ν) (n : ℕ) :
    lpOneAlg.toRealSeq (nonnegRestrict a) n = lpOneAlg.toRealSeq a (↑n : ℤ) := by
  simp [nonnegRestrict, lpOneAlg.toRealSeq, lpAlgRingData.toReal_ofReal]

/-- On symmetric sequences the bordered restriction is an isometry:
`‖nonnegRestrict a‖ = ‖a‖` — the bordered weight is exactly the pushforward of the
bilateral weight along `k ↦ |k|`. -/
theorem nonnegRestrict_norm_of_isSymmetric (a : l1Chebyshev ν)
    (ha : l1Chebyshev.IsSymmetric a) : ‖nonnegRestrict a‖ = ‖a‖ := by
  rw [lpOneAlg.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  have hpos : Summable (fun n : ℕ => ‖a (↑n : ℤ)‖) := summable_norm_natCast a
  have hsplit : (∑' k : ℤ, ‖a k‖) =
      (∑' n : ℕ, ‖a (↑n : ℤ)‖) + ∑' n : ℕ, ‖a (Int.negSucc n)‖ := by
    rw [← lpOneAlg.norm_eq_tsum]
    exact lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg a
  have hsym : ∀ n : ℕ, ‖a (Int.negSucc n)‖ = ‖a (↑(n + 1) : ℤ)‖ := by
    intro n
    have hval : lpOneAlg.toRealSeq a (Int.negSucc n) =
        lpOneAlg.toRealSeq a (↑(n + 1) : ℤ) := by
      have h := ha (↑(n + 1) : ℤ)
      rwa [show -(↑(n + 1) : ℤ) = Int.negSucc n from by omega] at h
    rw [lpOneAlg.norm_eq_abs_toReal_mul_weight a (Int.negSucc n),
      lpOneAlg.norm_eq_abs_toReal_mul_weight a (↑(n + 1) : ℤ), hval]
    simp only [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul]
    have hna : (Int.negSucc n).natAbs = ((↑(n + 1) : ℤ)).natAbs := by omega
    rw [hna]
  have hnegeq : (∑' n : ℕ, ‖a (Int.negSucc n)‖) = ∑' n : ℕ, ‖a (↑(n + 1) : ℤ)‖ :=
    tsum_congr hsym
  have hz : (∑' n : ℕ, ‖a (↑n : ℤ)‖) =
      ‖a ((0 : ℕ) : ℤ)‖ + ∑' n : ℕ, ‖a (↑(n + 1) : ℤ)‖ := hpos.tsum_eq_zero_add
  have hLfib : (∑' n : ℕ, ‖(nonnegRestrict a) n‖) =
      ∑' n : ℕ, |lpOneAlg.toRealSeq a (↑n : ℤ)| * borderedWeight ν n :=
    tsum_congr fun n => by rw [l1Bordered_norm_fiber, nonnegRestrict_toSeq]
  have sL : Summable (fun n : ℕ =>
      |lpOneAlg.toRealSeq a (↑n : ℤ)| * borderedWeight ν n) :=
    (lpOneAlg.summable_norm (nonnegRestrict a)).congr (fun n => by
      rw [l1Bordered_norm_fiber, nonnegRestrict_toSeq])
  have hzL : (∑' n : ℕ, |lpOneAlg.toRealSeq a (↑n : ℤ)| * borderedWeight ν n) =
      |lpOneAlg.toRealSeq a ((0 : ℕ) : ℤ)| * borderedWeight ν 0 +
        ∑' n : ℕ, |lpOneAlg.toRealSeq a (↑(n + 1) : ℤ)| * borderedWeight ν (n + 1) :=
    sL.tsum_eq_zero_add
  have hz0 : |lpOneAlg.toRealSeq a ((0 : ℕ) : ℤ)| * borderedWeight ν 0 =
      ‖a ((0 : ℕ) : ℤ)‖ := by
    rw [borderedWeight_zero, mul_one, norm_fiber_natCast]
    rw [pow_zero, mul_one]
    rfl
  have hterm : ∀ n : ℕ, |lpOneAlg.toRealSeq a (↑(n + 1) : ℤ)| * borderedWeight ν (n + 1) =
      2 * ‖a (↑(n + 1) : ℤ)‖ := by
    intro n
    rw [borderedWeight_succ, norm_fiber_natCast]
    have he : |l1Chebyshev.toSeq a (↑(n + 1) : ℤ)| =
        |lpOneAlg.toRealSeq a (↑(n + 1) : ℤ)| := rfl
    rw [he]
    ring
  have hw2 : (∑' n : ℕ, |lpOneAlg.toRealSeq a (↑(n + 1) : ℤ)| * borderedWeight ν (n + 1)) =
      2 * ∑' n : ℕ, ‖a (↑(n + 1) : ℤ)‖ := by
    rw [tsum_congr hterm, tsum_mul_left]
  linarith [hLfib, hzL, hz0, hw2, hsplit, hnegeq, hz]

/-- Restriction to the nonnegative modes is `2`-bounded on all of `l1Chebyshev ν`, for every
`ν`: each stored mode `n ≥ 1` carries the bordered weight `2νⁿ`. -/
theorem nonnegRestrict_norm_le (a : l1Chebyshev ν) : ‖nonnegRestrict a‖ ≤ 2 * ‖a‖ := by
  have hfib : ∀ n : ℕ, ‖(nonnegRestrict a) n‖ ≤ 2 * ‖a (n : ℤ)‖ := fun n => by
    rw [l1Bordered_norm_fiber, nonnegRestrict_toSeq]
    exact nonnegRestrict_fiber_le a n
  rw [lpOneAlg.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  refine (Summable.tsum_le_tsum hfib (lpOneAlg.summable_norm _)
    ((summable_norm_natCast a).mul_left 2)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm a)
    (fun _ => norm_nonneg _) Nat.cast_injective) zero_le_two

namespace l1Chebyshev

/-- Restriction after symmetrization is the plain restriction. -/
lemma nonnegRestrict_symmetrize (a : l1Chebyshev ν) :
    nonnegRestrict (symmetrize a) = nonnegRestrict a := by
  apply lpOneAlg.ext_toRealSeq
  funext n
  show lpOneAlg.toRealSeq (nonnegRestrict (symmetrize a)) n
    = lpOneAlg.toRealSeq (nonnegRestrict a) n
  rw [nonnegRestrict_toSeq, nonnegRestrict_toSeq]
  show toSeq (symmetrize a) (↑n : ℤ) = toSeq a (↑n : ℤ)
  rw [symmetrize_toSeq]
  simp

end l1Chebyshev

end SymmetricBridge

section BorderedTransport

variable {ν : PosReal}

/-! #### T→U on the bordered carrier: `(P a)_m = a_m - a_{m+2}`, `‖P‖ ≤ 1` -/

private lemma borderedToU_mem (a : l1Bordered ν) :
    l1Weighted.Mem ν (fun m => lpOneAlg.toRealSeq a m - lpOneAlg.toRealSeq a (m + 2)) := by
  rw [l1Weighted.mem_iff]
  have h0 : Summable (fun m : ℕ => ‖a m‖) := lpOneAlg.summable_norm a
  have h2 : Summable (fun m : ℕ => ‖a (m + 2)‖) :=
    h0.comp_injective (by intro x y h; simp only at h; omega)
  have h2' : Summable (fun m : ℕ => ((ν : ℝ) ^ 2)⁻¹ * ‖a (m + 2)‖) := h2.mul_left _
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)) (fun m => ?_) (h0.add h2')
  rw [l1Bordered_norm_fiber, l1Bordered_norm_fiber]
  have htri : |lpOneAlg.toRealSeq a m - lpOneAlg.toRealSeq a (m + 2)| ≤
      |lpOneAlg.toRealSeq a m| + |lpOneAlg.toRealSeq a (m + 2)| := by
    simpa only [Real.norm_eq_abs] using
      norm_sub_le (lpOneAlg.toRealSeq a m) (lpOneAlg.toRealSeq a (m + 2))
  have s1 : |lpOneAlg.toRealSeq a m - lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m ≤
      |lpOneAlg.toRealSeq a m| * (ν : ℝ) ^ m +
        |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m := by
    have := mul_le_mul_of_nonneg_right htri (pow_nonneg ν.2.le m)
    rw [add_mul] at this
    exact this
  have hA : |lpOneAlg.toRealSeq a m| * (ν : ℝ) ^ m ≤
      |lpOneAlg.toRealSeq a m| * borderedWeight ν m :=
    mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν m) (abs_nonneg _)
  have hy : |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m =
      ((ν : ℝ) ^ 2)⁻¹ * (|lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ (m + 2)) := by
    have hν : (ν : ℝ) ≠ 0 := ν.2.ne'
    field_simp
    ring
  have hB : ((ν : ℝ) ^ 2)⁻¹ * (|lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ (m + 2)) ≤
      ((ν : ℝ) ^ 2)⁻¹ * (|lpOneAlg.toRealSeq a (m + 2)| * borderedWeight ν (m + 2)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν (m + 2)) (abs_nonneg _))
      (by positivity)
  linarith

/-- The bordered T→U conversion `(borderedToU a)_m = a_m - a_{m+2}` (no `1/2`:
the bordered storage carries the doubling in its weight instead). -/
def borderedToU (a : l1Bordered ν) : l1Weighted ν :=
  l1Weighted.mk _ (borderedToU_mem a)

@[simp] lemma borderedToU_toSeq (a : l1Bordered ν) (m : ℕ) :
    l1Weighted.toSeq (borderedToU a) m =
      lpOneAlg.toRealSeq a m - lpOneAlg.toRealSeq a (m + 2) := rfl

lemma borderedToU_add (a b : l1Bordered ν) :
    borderedToU (a + b) = borderedToU a + borderedToU b := by
  apply l1Weighted.ext; intro m
  simp only [borderedToU_toSeq, l1Weighted.add_toSeq, lpOneAlg.toRealSeq_add, Pi.add_apply]
  ring

lemma borderedToU_smul (r : ℝ) (a : l1Bordered ν) :
    borderedToU (r • a) = r • borderedToU a := by
  apply l1Weighted.ext; intro m
  simp only [borderedToU_toSeq, l1Weighted.smul_toSeq, lpOneAlg.toRealSeq_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- `‖borderedToU a‖ ≤ ‖a‖`: on the bordered carrier the T→U conversion is
`1`-bounded (the zero-mode column attains the bound; that attainment is not proved here). -/
lemma borderedToU_norm_le [Fact (1 ≤ (ν : ℝ))] (a : l1Bordered ν) :
    ‖borderedToU a‖ ≤ ‖a‖ := by
  rw [l1Weighted.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  have sB : Summable (fun m : ℕ => |lpOneAlg.toRealSeq a m| * borderedWeight ν m) :=
    (lpOneAlg.summable_norm a).congr (fun m => l1Bordered_norm_fiber a m)
  have s1 : Summable (fun m : ℕ => |lpOneAlg.toRealSeq a m| * (ν : ℝ) ^ m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν m) (abs_nonneg _)) sB
  have s1' : Summable (fun m : ℕ => |lpOneAlg.toRealSeq a (m + 1)| * (ν : ℝ) ^ (m + 1)) :=
    s1.comp_injective (by intro x y h; simp only at h; omega)
  have s2' : Summable (fun m : ℕ => |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ (m + 2)) :=
    s1.comp_injective (by intro x y h; simp only at h; omega)
  have s2 : Summable (fun m : ℕ => |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
      (fun m => mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (Fact.out : (1 : ℝ) ≤ ν) (by omega)) (abs_nonneg _)) s2'
  have hstep : (∑' m : ℕ, |l1Weighted.toSeq (borderedToU a) m| * (ν : ℝ) ^ m) ≤
      ∑' m : ℕ, (|lpOneAlg.toRealSeq a m| * (ν : ℝ) ^ m +
        |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m) := by
    refine Summable.tsum_le_tsum (fun m => ?_)
      (l1Weighted.summable_weighted (borderedToU a)) (s1.add s2)
    simp only [borderedToU_toSeq]
    have htri : |lpOneAlg.toRealSeq a m - lpOneAlg.toRealSeq a (m + 2)| ≤
        |lpOneAlg.toRealSeq a m| + |lpOneAlg.toRealSeq a (m + 2)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (lpOneAlg.toRealSeq a m) (lpOneAlg.toRealSeq a (m + 2))
    have := mul_le_mul_of_nonneg_right htri (pow_nonneg ν.2.le m)
    rw [add_mul] at this
    exact this
  refine hstep.trans ?_
  rw [s1.tsum_add s2]
  have hnorm : (∑' m : ℕ, ‖a m‖) =
      ∑' m : ℕ, |lpOneAlg.toRealSeq a m| * borderedWeight ν m :=
    tsum_congr (fun m => l1Bordered_norm_fiber a m)
  rw [hnorm]
  -- decompose both sides at the zero mode and compare
  have hz1 : (∑' m : ℕ, |lpOneAlg.toRealSeq a m| * borderedWeight ν m) =
      |lpOneAlg.toRealSeq a 0| +
        ∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 1)| * borderedWeight ν (m + 1) := by
    rw [sB.tsum_eq_zero_add, borderedWeight_zero, mul_one]
  have hw : (∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 1)| * borderedWeight ν (m + 1)) =
      2 * ∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 1)| * (ν : ℝ) ^ (m + 1) := by
    rw [show (fun m : ℕ => |lpOneAlg.toRealSeq a (m + 1)| * borderedWeight ν (m + 1)) =
        fun m : ℕ => 2 * (|lpOneAlg.toRealSeq a (m + 1)| * (ν : ℝ) ^ (m + 1)) from
      funext fun m => by rw [borderedWeight_succ]; ring, tsum_mul_left]
  have hz2 : (∑' m : ℕ, |lpOneAlg.toRealSeq a m| * (ν : ℝ) ^ m) =
      |lpOneAlg.toRealSeq a 0| +
        ∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 1)| * (ν : ℝ) ^ (m + 1) := by
    rw [s1.tsum_eq_zero_add, pow_zero, mul_one]
  have hz3 : (∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 1)| * (ν : ℝ) ^ (m + 1)) =
      |lpOneAlg.toRealSeq a 1| * (ν : ℝ) ^ 1 +
        ∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ (m + 2) :=
    s1'.tsum_eq_zero_add
  have h23 : (∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ m) ≤
      ∑' m : ℕ, |lpOneAlg.toRealSeq a (m + 2)| * (ν : ℝ) ^ (m + 2) :=
    Summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (Fact.out : (1 : ℝ) ≤ ν) (by omega)) (abs_nonneg _)) s2 s2'
  have hpos1 : (0 : ℝ) ≤ |lpOneAlg.toRealSeq a 1| * (ν : ℝ) ^ 1 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)
  linarith

/-- The bordered T→U conversion as a CLM with operator norm ≤ 1. -/
noncomputable def borderedToU_CLM [Fact (1 ≤ (ν : ℝ))] :
    l1Bordered ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := borderedToU
      map_add' := borderedToU_add
      map_smul' := fun r a => by simp [borderedToU_smul] }
    1
    (fun a => by rw [one_mul]; exact borderedToU_norm_le a)

@[simp] lemma borderedToU_CLM_apply [Fact (1 ≤ (ν : ℝ))] (a : l1Bordered ν) :
    borderedToU_CLM a = borderedToU a := rfl

/-- Compatibility with the certified bilateral pair: on the bordered carrier the
conversion is exactly twice `chebyshevToU` (the `1/2` was absorbed by the storage
convention). Holds for every `a`, symmetric or not. -/
theorem borderedToU_nonnegRestrict (a : l1Chebyshev ν) :
    borderedToU (nonnegRestrict a) = (2 : ℝ) • chebyshevToU a := by
  apply l1Weighted.ext; intro m
  simp only [borderedToU_toSeq, nonnegRestrict_toSeq, l1Weighted.smul_toSeq,
    chebyshevToU_toSeq]
  rw [show ((↑(m + 2) : ℤ)) = (↑m : ℤ) + 2 from by omega]
  have he : ∀ k : ℤ, lpOneAlg.toRealSeq a k = l1Chebyshev.toSeq a k := fun _ => rfl
  rw [he, he]
  ring

/-! #### U→T on the bordered carrier: `(Q b)_m = Σ_j b_{m+2j}`, `‖Q‖ ≤ 2ν²/(ν²-1)` -/

variable [Fact (1 < (ν : ℝ))]

private lemma borderedFromU_fiber_le (b : l1Weighted ν) (m : ℕ) :
    ‖lpAlgRingData.ofReal (E := BorderedScaledReal ν) m
        (∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j))‖ ≤
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)| * (ν : ℝ) ^ m := by
  rw [BorderedScaledReal.norm_lpAlgRingData_ofReal]
  have hs : Summable (fun j : ℕ => ‖l1Weighted.toSeq b (m + 2 * j)‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_toSeq_shift b m
  have hAbs : |∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j)| ≤
      ∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
  have hmr : (∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)| * (ν : ℝ) ^ m) =
      (∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)|) * (ν : ℝ) ^ m := tsum_mul_right
  have hwb : borderedWeight ν m ≤ 2 * (ν : ℝ) ^ m := borderedWeight_le_two_mul ν m
  have h1 : |∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j)| * borderedWeight ν m ≤
      (∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)|) * (2 * (ν : ℝ) ^ m) :=
    mul_le_mul hAbs hwb (le_of_lt (borderedWeight_pos ν m))
      (tsum_nonneg fun j => abs_nonneg _)
  rw [hmr]
  linarith

private lemma borderedFromU_mem (b : l1Weighted ν) :
    Memℓp (fun m : ℕ => lpAlgRingData.ofReal (E := BorderedScaledReal ν) m
      (∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j))) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have hmarg : Summable (fun m : ℕ =>
      2 * ∑' j : ℕ, |l1Weighted.toSeq b (m + 2 * j)| * (ν : ℝ) ^ m) :=
    (fromU_marginal_summable b).mul_left 2
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => borderedFromU_fiber_le b m) hmarg

/-- The bordered U→T conversion `(borderedFromU b)_m = Σ_{j≥0} b_{m+2j}` (no `2`). -/
def borderedFromU (b : l1Weighted ν) : l1Bordered ν :=
  ⟨⟨fun m => lpAlgRingData.ofReal (E := BorderedScaledReal ν) m
      (∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j)),
    borderedFromU_mem b⟩⟩

@[simp] lemma borderedFromU_toSeq (b : l1Weighted ν) (m : ℕ) :
    lpOneAlg.toRealSeq (borderedFromU b) m =
      ∑' j : ℕ, l1Weighted.toSeq b (m + 2 * j) := by
  simp [borderedFromU, lpOneAlg.toRealSeq, lpAlgRingData.toReal_ofReal]

lemma borderedFromU_add (b d : l1Weighted ν) :
    borderedFromU (b + d) = borderedFromU b + borderedFromU d := by
  apply lpOneAlg.ext_toRealSeq; funext m
  rw [lpOneAlg.toRealSeq_add, Pi.add_apply, borderedFromU_toSeq, borderedFromU_toSeq,
    borderedFromU_toSeq]
  have hcong : (∑' j : ℕ, l1Weighted.toSeq (b + d) (m + 2 * j)) =
      ∑' j : ℕ, (l1Weighted.toSeq b (m + 2 * j) + l1Weighted.toSeq d (m + 2 * j)) :=
    tsum_congr fun j => l1Weighted.add_toSeq b d (m + 2 * j)
  rw [hcong, (summable_toSeq_shift b m).tsum_add (summable_toSeq_shift d m)]

lemma borderedFromU_smul (r : ℝ) (b : l1Weighted ν) :
    borderedFromU (r • b) = r • borderedFromU b := by
  apply lpOneAlg.ext_toRealSeq
  rw [lpOneAlg.toRealSeq_smul]; funext m
  rw [Pi.smul_apply, smul_eq_mul, borderedFromU_toSeq, borderedFromU_toSeq]
  have hcong : (∑' j : ℕ, l1Weighted.toSeq (r • b) (m + 2 * j)) =
      ∑' j : ℕ, r * l1Weighted.toSeq b (m + 2 * j) :=
    tsum_congr fun j => l1Weighted.smul_toSeq r b (m + 2 * j)
  rw [hcong, tsum_mul_left]

/-- **Compatibility of the two U→T conversions**: restricted to its nonnegative modes, the
bilateral `chebyshevFromU` is exactly twice the bordered `borderedFromU` (the `2` that the bordered
storage moved into its weight). Sibling of `borderedToU_nonnegRestrict`. -/
theorem nonnegRestrict_chebyshevFromU (b : l1Weighted ν) :
    nonnegRestrict (chebyshevFromU b) = (2 : ℝ) • borderedFromU b := by
  apply lpOneAlg.ext_toRealSeq; funext n
  rw [lpOneAlg.toRealSeq_smul, Pi.smul_apply, smul_eq_mul, nonnegRestrict_toSeq,
    chebyshevFromU_toSeq_natCast, borderedFromU_toSeq]

/-- `‖borderedFromU b‖ ≤ (2ν²/(ν²-1))·‖b‖`: the bilateral bound `chebyshevFromU_norm_le` read
through `nonnegRestrict_chebyshevFromU` and `nonnegRestrict_norm_le`. -/
lemma borderedFromU_norm_le (b : l1Weighted ν) :
    ‖borderedFromU b‖ ≤ 2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) * ‖b‖ := by
  have h := (nonnegRestrict_norm_le (chebyshevFromU b)).trans
    (mul_le_mul_of_nonneg_left (chebyshevFromU_norm_le b) zero_le_two)
  rw [nonnegRestrict_chebyshevFromU, norm_smul, Real.norm_two] at h
  linarith

/-! #### Round trips: a genuine Banach isomorphism -/

/-- U-side round trip on the bordered carrier: exact (the bilateral round trip
`chebyshevToU_chebyshevFromU` through `borderedToU_nonnegRestrict` and
`nonnegRestrict_chebyshevFromU`). -/
theorem borderedToU_borderedFromU (b : l1Weighted ν) :
    borderedToU (borderedFromU b) = b := by
  have h := borderedToU_nonnegRestrict (chebyshevFromU b)
  rw [nonnegRestrict_chebyshevFromU, borderedToU_smul, chebyshevToU_chebyshevFromU] at h
  exact smul_right_injective _ two_ne_zero h

/-- T-side round trip on the bordered carrier: exact (both spaces are one-sided,
so unlike `chebyshevFromU ∘ chebyshevToU` there is no truncation caveat). -/
theorem borderedFromU_borderedToU (a : l1Bordered ν) :
    borderedFromU (borderedToU a) = a := by
  apply lpOneAlg.ext_toRealSeq; funext m
  rw [borderedFromU_toSeq]
  have hxabs : Summable (fun n : ℕ => |lpOneAlg.toRealSeq a n|) := by
    have hone : ∀ n : ℕ, (1 : ℝ) ≤ borderedWeight ν n := fun n =>
      le_trans (one_le_pow₀ (Fact.out : (1 : ℝ) < ν).le) (pow_le_borderedWeight ν n)
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((lpOneAlg.summable_norm a).congr (fun n => l1Bordered_norm_fiber a n))
    exact le_mul_of_one_le_right (abs_nonneg _) (hone n)
  have hx : Summable (fun j : ℕ => lpOneAlg.toRealSeq a (m + 2 * j)) :=
    (hxabs.comp_injective (by intro x y h; simp only at h; omega)).of_abs
  have hx' : Summable (fun j : ℕ => lpOneAlg.toRealSeq a (m + 2 * (j + 1))) :=
    (hxabs.comp_injective (by intro x y h; simp only at h; omega)).of_abs
  have hcong : (∑' j : ℕ, l1Weighted.toSeq (borderedToU a) (m + 2 * j)) =
      ∑' j : ℕ, (lpOneAlg.toRealSeq a (m + 2 * j) -
        lpOneAlg.toRealSeq a (m + 2 * (j + 1))) := by
    refine tsum_congr fun j => ?_
    rw [borderedToU_toSeq, show m + 2 * j + 2 = m + 2 * (j + 1) from by omega]
  rw [hcong, hx.tsum_sub hx']
  have hza := hx.tsum_eq_zero_add
  rw [hza, show m + 2 * 0 = m from by omega]
  ring

/-- `Fact (1 ≤ ν)` from the section's `Fact (1 < ν)`; a local instance of this section only
(never a global instance). -/
private theorem fact_one_le_of_one_lt : Fact (1 ≤ (ν : ℝ)) := ⟨(Fact.out : (1 : ℝ) < ν).le⟩

attribute [local instance] fact_one_le_of_one_lt

/-- The bordered U→T conversion as a CLM. -/
noncomputable def borderedFromU_CLM : l1Weighted ν →L[ℝ] l1Bordered ν :=
  LinearMap.mkContinuous
    { toFun := borderedFromU
      map_add' := borderedFromU_add
      map_smul' := fun r b => by simp [borderedFromU_smul] }
    (2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1))
    (fun b => borderedFromU_norm_le b)

@[simp] lemma borderedFromU_CLM_apply (b : l1Weighted ν) :
    borderedFromU_CLM b = borderedFromU b := rfl

/-- The bordered T↔U transport as a continuous linear equivalence — the certified
conjugation between physical T-storage and U-coefficients, built from the two named CLMs. -/
noncomputable def borderedTU_equiv : l1Bordered ν ≃L[ℝ] l1Weighted ν :=
  ContinuousLinearEquiv.equivOfInverse borderedToU_CLM borderedFromU_CLM
    (fun a => by simp [borderedFromU_borderedToU])
    (fun b => by simp [borderedToU_borderedFromU])

@[simp] theorem borderedTU_equiv_apply (a : l1Bordered ν) :
    borderedTU_equiv a = borderedToU a := rfl

@[simp] theorem borderedTU_equiv_symm_apply (b : l1Weighted ν) :
    borderedTU_equiv.symm b = borderedFromU b := rfl

theorem coe_borderedTU_equiv :
    (borderedTU_equiv (ν := ν) : l1Bordered ν →L[ℝ] l1Weighted ν) = borderedToU_CLM := rfl

theorem coe_borderedTU_equiv_symm :
    ((borderedTU_equiv (ν := ν)).symm : l1Weighted ν →L[ℝ] l1Bordered ν) = borderedFromU_CLM :=
  rfl

/-- **κ_repo**: conditioning of the physical-storage T↔U transport,
`‖P‖·‖P⁻¹‖ ≤ 2ν²/(ν²-1) = 1 + coth(log ν)`.

Compare the clean pair (`chebyshevToU_CLM_norm_mul_chebyshevFromU_CLM_norm_le`,
bound `(ν²+1)/(ν²-1) = coth(log ν)`): the `+1` is exactly the ramification of the
index cover `k ↦ |k|` at the zero mode — the bordered weight is `1` there instead
of `2`, so the `e₀` column of `P` attains norm `1`, while the columns `e_n`, `n ≥ 2`,
cost `(1+ν⁻²)/2` and `e₁` costs `1/2`. Only the product bound is proved here; the column
norms are not. -/
theorem borderedToU_CLM_norm_mul_borderedFromU_CLM_norm_le :
    ‖borderedToU_CLM (ν := ν)‖ * ‖borderedFromU_CLM (ν := ν)‖ ≤
      2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) := by
  have hden : (0 : ℝ) < (ν : ℝ) ^ 2 - 1 := by linarith [one_lt_nusq (ν := ν)]
  have h1 : ‖borderedToU_CLM (ν := ν)‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have h2 : ‖borderedFromU_CLM (ν := ν)‖ ≤ 2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) :=
    LinearMap.mkContinuous_norm_le _ (div_nonneg (by positivity) hden.le) _
  have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  rwa [one_mul] at this

/-- κ_repo stated on the bundled equivalence `borderedTU_equiv`. -/
theorem norm_borderedTU_equiv_mul_norm_symm_le :
    ‖(borderedTU_equiv (ν := ν) : l1Bordered ν →L[ℝ] l1Weighted ν)‖ *
      ‖((borderedTU_equiv (ν := ν)).symm : l1Weighted ν →L[ℝ] l1Bordered ν)‖ ≤
      2 * (ν : ℝ) ^ 2 / ((ν : ℝ) ^ 2 - 1) := by
  rw [coe_borderedTU_equiv, coe_borderedTU_equiv_symm]
  exact borderedToU_CLM_norm_mul_borderedFromU_CLM_norm_le

end BorderedTransport

end RadiiPolynomial

end
