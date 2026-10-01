import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra

/-!
# The finite Galerkin carrier of the flip-fixed Chebyshev algebra

`FνN ν N` is the space of stored Chebyshev modes `0, …, N` with the weighted ℓ¹ norm
`‖x‖ = |x₀| + 2 Σ_{k=1}^{N} |x_k| ν^k` (`FνN.norm_eq`); the weight is `wt ν k`. It is a
distinct carrier (a `def`, not the Pi sup-norm space), finite dimensional
(`instFiniteDimensionalFνN`), and the identity map `amb` identifies it with
`Fin (N + 1) → ℝ` as a continuous linear equivalence.

The even zero padding `ιN : FνN ν N →ₗᵢ[ℝ] symmetricSubalgebra ν` is an isometry into the
flip-fixed algebra, and the Galerkin projection `πN` onto modes `0, …, N` is a contraction on it
(`norm_πN_le`), with `πN ∘ ιN = id` (`πN_ιN`). Products are taken in the algebra before
projecting: the Galerkin coefficients of `ιN x * ιN y` are the truncated convolution of the even
paddings (`πN_mul_ιN`, `truncConv`); a product of three paddings is the triple sum over
`k₁ + k₂ + k₃ = k` with `kᵢ ∈ [-N, N]` (`toSeq_mul_mul_ιN`). The kept-mode embedding `Jσ σ` along
`σ : Fin M ↪ Fin (N+1)` and its left inverse `Tσ σ` handle carriers that store only some modes.
-/

noncomputable section

open scoped BigOperators

namespace RadiiPolynomial

namespace Galerkin

/-! ### The finite weighted-ℓ¹ carrier -/

/-- The Chebyshev weight on stored modes: `1` at mode `0`, `2 ν^k` at mode `k ≥ 1`. -/
def wt (ν : PosReal) (k : ℕ) : ℝ := if k = 0 then 1 else 2 * (ν : ℝ) ^ k

theorem wt_pos (ν : PosReal) (k : ℕ) : 0 < wt ν k := by
  unfold wt
  split_ifs
  · exact one_pos
  · have := ν.2
    positivity

set_option linter.unusedVariables false in
/-- The finite weighted-ℓ¹ carrier on `Fin (N+1)`.  A `def`, not an `abbrev`: instance
search does not see through it, so the Pi sup-norm is never picked up. -/
def FνN (ν : PosReal) (N : ℕ) : Type := Fin (N + 1) → ℝ

namespace FνN

variable {ν : PosReal} {N : ℕ}

instance : AddCommGroup (FνN ν N) := inferInstanceAs (AddCommGroup (Fin (N + 1) → ℝ))
instance : Module ℝ (FνN ν N) := inferInstanceAs (Module ℝ (Fin (N + 1) → ℝ))

/-- Build a carrier element from its coefficients. -/
def mk (f : Fin (N + 1) → ℝ) : FνN ν N := f

@[simp] theorem mk_apply (f : Fin (N + 1) → ℝ) (k : Fin (N + 1)) :
    (mk f : FνN ν N) k = f k := rfl
@[simp] theorem zero_apply (k : Fin (N + 1)) : (0 : FνN ν N) k = 0 := rfl
@[simp] theorem add_apply (x y : FνN ν N) (k : Fin (N + 1)) : (x + y) k = x k + y k := rfl
@[simp] theorem neg_apply (x : FνN ν N) (k : Fin (N + 1)) : (-x) k = -x k := rfl
@[simp] theorem sub_apply (x y : FνN ν N) (k : Fin (N + 1)) : (x - y) k = x k - y k := rfl
@[simp] theorem smul_apply (c : ℝ) (x : FνN ν N) (k : Fin (N + 1)) :
    (c • x) k = c * x k := rfl

theorem ext {x y : FνN ν N} (h : ∀ k, x k = y k) : x = y := funext h

/-- The weighted ℓ¹ norm as a raw function. -/
def wnorm (x : FνN ν N) : ℝ := ∑ k : Fin (N + 1), |x k| * wt ν k

theorem wnorm_nonneg (x : FνN ν N) : 0 ≤ wnorm x :=
  Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (wt_pos ν k).le

/-- The weighted ℓ¹ norm as an additive group norm. -/
def addGroupNorm : AddGroupNorm (FνN ν N) where
  toFun := wnorm
  map_zero' := by simp [wnorm]
  add_le' x y := by
    unfold wnorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (wt_pos ν k).le
  neg' x := by simp [wnorm]
  eq_zero_of_map_eq_zero' x h := by
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg (x k)) (wt_pos ν k).le)).1 h
    refine ext fun k => ?_
    have hk := h0 k (Finset.mem_univ _)
    rcases mul_eq_zero.1 hk with h1 | h1
    · exact abs_eq_zero.1 h1
    · exact absurd h1 (wt_pos ν k).ne'

instance : NormedAddCommGroup (FνN ν N) := addGroupNorm.toNormedAddCommGroup

theorem norm_def (x : FνN ν N) : ‖x‖ = ∑ k : Fin (N + 1), |x k| * wt ν k := rfl

instance : NormedSpace ℝ (FνN ν N) where
  norm_smul_le c x := by
    rw [norm_def, norm_def, Real.norm_eq_abs, Finset.mul_sum]
    refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [smul_apply, abs_mul, mul_assoc]

/-- The norm formula `‖x‖ = |x₀| + 2 Σ_{k=1}^{N} |x_k| ν^k`. -/
theorem norm_eq (x : FνN ν N) :
    ‖x‖ = |x 0| + 2 * ∑ k : Fin N, |x k.succ| * (ν : ℝ) ^ ((k : ℕ) + 1) := by
  rw [norm_def, Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp [wt]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [wt, Fin.val_succ, Nat.add_one_ne_zero, if_false]
    ring

/-- The norm of a single stored mode: `‖c e_k‖ = |c| wt ν k`. -/
theorem norm_mk_single (k : Fin (N + 1)) (c : ℝ) :
    ‖(mk (Pi.single k c) : FνN ν N)‖ = |c| * wt ν k := by
  rw [norm_def, Finset.sum_eq_single k
    (fun j _ hj => by rw [mk_apply, Pi.single_eq_of_ne hj, abs_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ k) h), mk_apply, Pi.single_eq_same]

end FνN

/-- `FνN` is finite dimensional (same vector space as `Fin (N+1) → ℝ`). -/
instance instFiniteDimensionalFνN {ν : PosReal} {N : ℕ} : FiniteDimensional ℝ (FνN ν N) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin (N + 1) → ℝ))

/-! ### The even padding `ιN` and the projection `πN` -/

section Maps

open l1Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N : ℕ}

/-- The even zero-padded extension of stored modes: `m ↦ x_{|m|}` for `|m| ≤ N`, else `0`. -/
def evenLift (x : FνN ν N) (m : ℤ) : ℝ :=
  if h : m.natAbs ≤ N then x ⟨m.natAbs, Nat.lt_succ_of_le h⟩ else 0

omit [Fact (1 ≤ (ν : ℝ))] in
theorem evenLift_neg (x : FνN ν N) (m : ℤ) : evenLift x (-m) = evenLift x m := by
  simp only [evenLift, Int.natAbs_neg]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem evenLift_natCast_of_le (x : FνN ν N) {n : ℕ} (h : n ≤ N) :
    evenLift x (n : ℤ) = x ⟨n, Nat.lt_succ_of_le h⟩ := by
  simp only [evenLift, Int.natAbs_natCast, dif_pos h]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem evenLift_natCast_of_lt (x : FνN ν N) {n : ℕ} (h : N < n) :
    evenLift x (n : ℤ) = 0 := by
  simp only [evenLift, Int.natAbs_natCast, dif_neg (not_le.2 h)]

/-- Stored nonnegative modes, before the flip. -/
private def rawPad (x : FνN ν N) : l1Chebyshev ν :=
  ∑ k : Fin (N + 1), single ((k : ℕ) : ℤ) (x k)

private theorem rawPad_toSeq_natCast (x : FνN ν N) (n : ℕ) :
    toSeq (rawPad (ν := ν) x) (n : ℤ) = if h : n ≤ N then x ⟨n, Nat.lt_succ_of_le h⟩ else 0 := by
  have hs : toSeq (rawPad (ν := ν) x) (n : ℤ) =
      ∑ k : Fin (N + 1), toSeq (single (ν := ν) ((k : ℕ) : ℤ) (x k)) (n : ℤ) :=
    toSeq_finset_sum _ _ _
  rw [hs]
  simp only [toSeq_single, Nat.cast_inj]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_of_le h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hc
      exact hb (Fin.ext hc.symm)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro hc
    exact h (hc ▸ Nat.le_of_lt_succ k.2)

/-- The padded bilateral element (flip of the stored modes). -/
private def padSeq (x : FνN ν N) : l1Chebyshev ν := symmetrize (rawPad x)

private theorem padSeq_toSeq (x : FνN ν N) (m : ℤ) :
    toSeq (padSeq (ν := ν) x) m = evenLift x m := by
  rw [padSeq, symmetrize_toSeq, rawPad_toSeq_natCast]
  rfl

private theorem padSeq_isSymmetric (x : FνN ν N) : (padSeq (ν := ν) x).IsSymmetric :=
  symmetrize_isSymmetric _

/-- The norm of a symmetric element through its nonnegative modes. -/
theorem norm_eq_of_isSymmetric (a : l1Chebyshev ν) (ha : a.IsSymmetric) :
    ‖a‖ = |toSeq a 0| + 2 * ∑' k : ℕ, |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1) := by
  rw [← norm_symmetrize_eq, symmetrize_eq_self_of_isSymmetric a ha]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem summable_modes (a : l1Chebyshev ν) :
    Summable (fun k : ℕ => |toSeq a ((k + 1 : ℕ) : ℤ)| * (ν : ℝ) ^ (k + 1)) := by
  refine ((summable_norm_natCast a).comp_injective (add_left_injective 1)).congr fun k => ?_
  simp only [Function.comp_apply]
  rw [norm_fiber, Int.natAbs_natCast]

private theorem padSeq_norm (x : FνN ν N) : ‖padSeq (ν := ν) x‖ = ‖x‖ := by
  rw [norm_eq_of_isSymmetric _ (padSeq_isSymmetric x), FνN.norm_eq, padSeq_toSeq]
  have h0 : evenLift x 0 = x 0 := by simp [evenLift]
  rw [h0, tsum_eq_sum (s := Finset.range N)]
  · rw [← Fin.sum_univ_eq_sum_range (fun k => |toSeq (padSeq (ν := ν) x) ((k + 1 : ℕ) : ℤ)| *
      (ν : ℝ) ^ (k + 1)) N]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [padSeq_toSeq, evenLift_natCast_of_le x (by omega)]
    rfl
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [padSeq_toSeq, evenLift_natCast_of_lt x (by omega), abs_zero, zero_mul]

private theorem padSeq_add (x y : FνN ν N) :
    padSeq (ν := ν) (x + y) = padSeq x + padSeq y := by
  apply lpOneAlg.ext_toRealSeq
  funext m
  change toSeq _ m = toSeq _ m
  rw [toSeq_add, padSeq_toSeq, padSeq_toSeq, padSeq_toSeq]
  unfold evenLift
  split_ifs <;> simp

private theorem padSeq_smul (c : ℝ) (x : FνN ν N) :
    padSeq (ν := ν) (c • x) = c • padSeq x := by
  apply lpOneAlg.ext_toRealSeq
  funext m
  change toSeq _ m = toSeq _ m
  rw [toSeq_smul, padSeq_toSeq, padSeq_toSeq]
  unfold evenLift
  split_ifs <;> simp

/-- The even zero padding `FνN → symmetricSubalgebra`, an isometry. -/
def ιN : FνN ν N →ₗᵢ[ℝ] symmetricSubalgebra ν where
  toFun x := ⟨padSeq x, padSeq_isSymmetric x⟩
  map_add' x y := Subtype.ext (padSeq_add x y)
  map_smul' c x := Subtype.ext (padSeq_smul c x)
  norm_map' x := padSeq_norm x

/-- Coefficient formula for `ιN`. -/
@[simp] theorem ιN_toSeq (x : FνN ν N) (m : ℤ) :
    toSeq ((ιN x : symmetricSubalgebra ν) : l1Chebyshev ν) m = evenLift x m :=
  padSeq_toSeq x m

theorem norm_ιN (x : FνN ν N) : ‖(ιN x : symmetricSubalgebra ν)‖ = ‖x‖ :=
  (ιN (ν := ν)).norm_map x

private theorem proj_norm_le (a : symmetricSubalgebra ν) :
    ‖(FνN.mk (fun k : Fin (N + 1) => toSeq (a : l1Chebyshev ν) ((k : ℕ) : ℤ)) : FνN ν N)‖
      ≤ ‖a‖ := by
  change _ ≤ ‖(a : l1Chebyshev ν)‖
  rw [FνN.norm_eq, norm_eq_of_isSymmetric _ a.2]
  simp only [FνN.mk_apply, Fin.val_zero, Nat.cast_zero, Fin.val_succ]
  gcongr
  rw [Fin.sum_univ_eq_sum_range (fun k => |toSeq (a : l1Chebyshev ν) ((k + 1 : ℕ) : ℤ)| *
      (ν : ℝ) ^ (k + 1)) N]
  exact (summable_modes _).sum_le_tsum _ (fun k _ => mul_nonneg (abs_nonneg _)
    (pow_nonneg ν.2.le _))

/-- The Galerkin projection onto modes `0..N`, acting on the flip-fixed algebra.

Why the domain must be the flip-fixed subalgebra and not the bilateral carrier:
the target norm charges a positive mode `k` with weight `2 ν^k`.  On a symmetric element
that factor `2` is already paid in the source norm by the mirror mode `-k`
(`‖a‖ = |a₀| + 2 Σ_{k ≥ 1} |a_k| ν^k`), so the truncation is a contraction, `‖πN‖ ≤ 1`.
On the bilateral carrier a single `z^k` has norm `ν^k` but its truncation has norm
`2 ν^k`, so the same coefficient map would only be `2`-bounded
(compare `l1Chebyshev.nonnegRestrictCLM_norm_le`). -/
def πN : symmetricSubalgebra ν →L[ℝ] FνN ν N :=
  LinearMap.mkContinuous
    { toFun a := FνN.mk fun k => toSeq (a : l1Chebyshev ν) ((k : ℕ) : ℤ)
      map_add' a b := FνN.ext fun k => by simp
      map_smul' c a := FνN.ext fun k => by simp }
    1 (fun a => by rw [one_mul]; exact proj_norm_le a)

/-- Coefficient formula for `πN`. -/
@[simp] theorem πN_apply (a : symmetricSubalgebra ν) (k : Fin (N + 1)) :
    (πN a : FνN ν N) k = toSeq (a : l1Chebyshev ν) ((k : ℕ) : ℤ) := rfl

theorem norm_πN_le : ‖(πN : symmetricSubalgebra ν →L[ℝ] FνN ν N)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem πN_ιN (x : FνN ν N) : πN (ιN (ν := ν) x) = x := by
  refine FνN.ext fun k => ?_
  rw [πN_apply, ιN_toSeq, evenLift_natCast_of_le x (Nat.le_of_lt_succ k.2)]

end Maps

/-! ### The carrier product: truncated convolution -/

section Conv

open l1Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N : ℕ}

omit [Fact (1 ≤ (ν : ℝ))] in
theorem evenLift_eq_zero (x : FνN ν N) {m : ℤ} (hm : ¬ |m| ≤ (N : ℤ)) : evenLift x m = 0 := by
  rw [evenLift, dif_neg]
  rw [Int.abs_eq_natAbs] at hm
  omega

omit [Fact (1 ≤ (ν : ℝ))] in
theorem evenLift_eq_zero_of_not_mem (x : FνN ν N) {m : ℤ}
    (hm : m ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : evenLift x m = 0 := by
  refine evenLift_eq_zero x fun h => hm ?_
  rw [Finset.mem_Icc]
  exact abs_le.1 h

/-- The truncated bilateral convolution on the window `[-N, N]`, for any two sequences. -/
def truncConv (N : ℕ) (x y : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun k => |n - k| ≤ (N : ℤ)), x (n - k) * y k

/-- The product of two padded elements in the flip-fixed algebra, before any projection, as a
finite sum. -/
theorem toSeq_mul_ιN (x y : FνN ν N) (k : ℤ) :
    toSeq (((ιN x * ιN y : symmetricSubalgebra ν)) : l1Chebyshev ν) k =
      ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), evenLift x (k - i) * evenLift y i := by
  change toSeq ((ιN x : l1Chebyshev ν) * (ιN y : l1Chebyshev ν)) k = _
  rw [toSeq_mul_eq_finsum _ _ k (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun i hi => by
    rw [ιN_toSeq]; exact evenLift_eq_zero_of_not_mem y hi)]
  simp only [ιN_toSeq]

/-- The product of three padded elements in the flip-fixed algebra, before any projection, is the
triple sum over `k₁ + k₂ + k₃ = k` with `kᵢ ∈ [-N, N]` (no intermediate truncation). -/
protected theorem toSeq_mul_mul_ιN (x y z : FνN ν N) (k : ℤ) :
    toSeq (((ιN x * ιN y * ιN z : symmetricSubalgebra ν)) : l1Chebyshev ν) k =
      ∑ k₁ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ k₂ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ∑ k₃ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k₁ + k₂ + k₃ = k then evenLift x k₁ * evenLift y k₂ * evenLift z k₃ else 0 := by
  have hP : (ιN x * ιN y * ιN z : symmetricSubalgebra ν) = ιN z * ιN y * ιN x := by ring
  rw [hP]
  change toSeq (((ιN z * ιN y : symmetricSubalgebra ν) : l1Chebyshev ν) * (ιN x : l1Chebyshev ν)) k = _
  rw [toSeq_mul_eq_finsum _ _ k (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun i hi => by
    rw [ιN_toSeq]; exact evenLift_eq_zero_of_not_mem x hi)]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [toSeq_mul_ιN, ιN_toSeq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k₂ _ => ?_
  rw [Finset.sum_congr rfl (fun k₃ (_ : k₃ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) =>
    if_congr (show k₁ + k₂ + k₃ = k ↔ k - k₁ - k₂ = k₃ from by omega) rfl rfl),
    Finset.sum_ite_eq]
  split_ifs with hm
  · ring
  · rw [evenLift_eq_zero_of_not_mem z hm]
    ring

/-- The Galerkin coefficients of a product of paddings are the truncated convolution of the
even paddings. -/
theorem πN_mul_ιN (x y : FνN ν N) (k : Fin (N + 1)) :
    (πN (ιN x * ιN y : symmetricSubalgebra ν) : FνN ν N) k =
      truncConv N (evenLift x) (evenLift y) ((k : ℕ) : ℤ) := by
  rw [πN_apply, toSeq_mul_ιN, truncConv, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [evenLift_eq_zero x h, zero_mul]

end Conv

/-! ### Kept-mode embedding -/

section KeptModes

variable {ν : PosReal} {N M : ℕ}

/-- The kept-mode inclusion along `σ : Fin M ↪ Fin (N+1)`: mode `σ j` carries `x j`, every
other mode is `0`. -/
def Jσ (σ : Fin M ↪ Fin (N + 1)) : (Fin M → ℝ) →ₗ[ℝ] FνN ν N where
  toFun x := FνN.mk (Function.ExtendByZero.linearMap ℝ σ x)
  map_add' x y := by simp only [map_add]; rfl
  map_smul' c x := by simp only [map_smul]; rfl

/-- The kept-mode restriction `y ↦ y ∘ σ`, a left inverse of `Jσ σ`. -/
def Tσ (σ : Fin M ↪ Fin (N + 1)) : FνN ν N →ₗ[ℝ] (Fin M → ℝ) where
  toFun y j := y (σ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Jσ_apply_emb (σ : Fin M ↪ Fin (N + 1)) (x : Fin M → ℝ) (j : Fin M) :
    (Jσ (ν := ν) σ x : FνN ν N) (σ j) = x j :=
  σ.injective.extend_apply x 0 j

theorem Tσ_Jσ (σ : Fin M ↪ Fin (N + 1)) (x : Fin M → ℝ) : Tσ σ (Jσ (ν := ν) σ x) = x :=
  funext fun j => Jσ_apply_emb (ν := ν) σ x j

theorem norm_Jσ (σ : Fin M ↪ Fin (N + 1)) (x : Fin M → ℝ) :
    ‖(Jσ (ν := ν) σ x : FνN ν N)‖ = ∑ j, |x j| * wt ν (σ j) := by
  have hz : ∀ k ∈ (Finset.univ : Finset (Fin (N + 1))), k ∉ Finset.univ.map σ →
      |(Jσ (ν := ν) σ x : FνN ν N) k| * wt ν k = 0 := fun k _ hk => by
    rw [show (Jσ (ν := ν) σ x : FνN ν N) k = 0 from Function.extend_apply' x (0 : Fin (N + 1) → ℝ) k
      fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩), abs_zero, zero_mul]
  rw [FνN.norm_def, ← Finset.sum_subset (Finset.subset_univ _) hz, Finset.sum_map]
  simp only [Jσ_apply_emb]

theorem norm_Jσ_Tσ_le (σ : Fin M ↪ Fin (N + 1)) (y : FνN ν N) :
    ‖(Jσ σ (Tσ σ y) : FνN ν N)‖ ≤ ‖y‖ := by
  rw [norm_Jσ, FνN.norm_def]
  exact (le_of_eq (Finset.sum_map Finset.univ σ (fun k => |y k| * wt ν k)).symm).trans
    (Finset.sum_le_univ_sum_of_nonneg fun k => mul_nonneg (abs_nonneg _) (wt_pos ν k).le)

end KeptModes

/-! ### The identity equivalence `FνN ν N ≃L (Fin (N+1) → ℝ)` (two norms on one space) -/

section Amb

/-- The identity map `FνN ν N ≃ (Fin (N+1) → ℝ)` (two norms on one vector space). -/
def ambL (ν : PosReal) (N : ℕ) : FνN ν N ≃ₗ[ℝ] (Fin (N + 1) → ℝ) where
  toFun x := x
  invFun x := FνN.mk x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identity map `FνN ν N ≃L (Fin (N+1) → ℝ)`, continuous in both directions (finite
dimension). -/
def amb (ν : PosReal) (N : ℕ) : FνN ν N ≃L[ℝ] (Fin (N + 1) → ℝ) :=
  (ambL ν N).toContinuousLinearEquiv

end Amb

end Galerkin

end RadiiPolynomial

end
