import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.ScalarInstances
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The weighted Schur test and its kernel operator on `WeightedLp`

A kernel `K : I → J → 𝕜` acts from `WeightedLp J E p` to `WeightedLp I F p` by
`coeff (K x) i = ∑' j, K i j * coeff x j`. Its normalized entry is
`schurEntry v w K i j = ‖K i j‖ * v i / w j`, where the frame weights of the source and
target are `w` and `v`.

`RowSum v w K R` and `ColSum v w K C` assert summable normalized rows and columns bounded
by nonnegative constants `R` and `C`; `SchurBound` bundles both. For `1 ≤ p ≤ ∞`,
`schur_bound_of` proves absolute convergence of the coordinate series, membership of the image
and the bound `R^(1/q) * C^(1/p)` for a Hölder conjugate `q`. It needs the row hypothesis
only when `p ≠ 1`, and the column hypothesis only when `p ≠ ∞`.

`kernelCLMOf` bundles this coordinate operator using precisely those hypotheses;
`coeff_kernelCLMOf`, `hasSum_coeff_kernelCLMOf` and `norm_kernelCLMOf_le` give its
computation, convergent coordinate series and norm bound. `kernelCLM` takes both hypotheses,
with its coefficient formula and general norm bound. `SchurBound.ofFinsets` supplies the
finite-support sufficient conditions.

The proof uses `lp.holderL` on the factors `κ^(1/q)` and `κ^(1/p) * ‖x j‖`, then aggregates
over finite sets of rows using the column hypothesis. No multiplication on the state carrier or
operation on the index is assumed. The bounded diagonal and Laurent kernel/series identification are included for the Fourier consumer.
No endpoint-only column principle or test-vector specialization is exported.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

/-! ### Normalized entries and the two Schur hypotheses -/

section Kernel

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*}

/-- The normalized entry `‖K i j‖ v_i / w_j` of a kernel `K : I → J → 𝕜` between a source weight
`w` and a target weight `v` (the absolute kernel of `D_v K D_w⁻¹`). -/
def schurEntry (v : I → ℝ) (w : J → ℝ) (K : I → J → 𝕜) (i : I) (j : J) : ℝ :=
  ‖K i j‖ * v i / w j

theorem schurEntry_nonneg {v : I → ℝ} {w : J → ℝ} (hv : ∀ i, 0 ≤ v i) (hw : ∀ j, 0 ≤ w j)
    (K : I → J → 𝕜) (i : I) (j : J) : 0 ≤ schurEntry v w K i j :=
  div_nonneg (mul_nonneg (norm_nonneg _) (hv i)) (hw j)

theorem schurEntry_of_eq_zero {v : I → ℝ} {w : J → ℝ} {K : I → J → 𝕜} {i : I} {j : J}
    (h : K i j = 0) : schurEntry v w K i j = 0 := by
  rw [schurEntry, h, norm_zero, zero_mul, zero_div]

/-- The row hypothesis (ROW): every normalized row is summable, with sum at most `R ≥ 0`. -/
structure RowSum (v : I → ℝ) (w : J → ℝ) (K : I → J → 𝕜) (R : ℝ) : Prop where
  row_nonneg : 0 ≤ R
  row_summable : ∀ i, Summable fun j => schurEntry v w K i j
  row_le : ∀ i, ∑' j, schurEntry v w K i j ≤ R

/-- The column hypothesis (COL): every normalized column is summable, with sum at most `C ≥ 0`. -/
structure ColSum (v : I → ℝ) (w : J → ℝ) (K : I → J → 𝕜) (C : ℝ) : Prop where
  col_nonneg : 0 ≤ C
  col_summable : ∀ j, Summable fun i => schurEntry v w K i j
  col_le : ∀ j, ∑' i, schurEntry v w K i j ≤ C

/-- **The Schur hypotheses**: (ROW) with constant `R` and (COL) with constant `C`. -/
structure SchurBound (v : I → ℝ) (w : J → ℝ) (K : I → J → 𝕜) (R C : ℝ) : Prop
    extends RowSum v w K R, ColSum v w K C

variable {v : I → ℝ} {w : J → ℝ} {K : I → J → 𝕜} {R C : ℝ}

/-- A single normalized entry is below the column constant. -/
theorem ColSum.entry_le (h : ColSum v w K C) (hv : ∀ i, 0 ≤ v i) (hw : ∀ j, 0 ≤ w j) (i : I)
    (j : J) : schurEntry v w K i j ≤ C :=
  ((h.col_summable j).le_tsum i fun i' _ => schurEntry_nonneg hv hw K i' j).trans (h.col_le j)

end Kernel

/-! ### Exponent bookkeeping -/

section Exponent

variable {p : ℝ≥0∞}

/-- For Hölder conjugate exponents, `1 / q.toReal + 1 / p.toReal = 1` (`1 / ∞.toReal = 0`). -/
theorem one_div_toReal_add_one_div_toReal (q : ℝ≥0∞) [p.HolderConjugate q] :
    1 / q.toReal + 1 / p.toReal = 1 := by
  have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one q p)
  rwa [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero q p))
    (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero p q)), ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_one, ← one_div, ← one_div] at h

/-- `S^(1/q) S^(1/p) = S` for `S ≥ 0` and Hölder conjugate exponents. -/
theorem rpow_one_div_mul_rpow_one_div {S : ℝ} (hS : 0 ≤ S) (q : ℝ≥0∞) [p.HolderConjugate q] :
    S ^ (1 / q.toReal) * S ^ (1 / p.toReal) = S := by
  rw [← Real.rpow_add' hS (by rw [one_div_toReal_add_one_div_toReal]; exact one_ne_zero),
    one_div_toReal_add_one_div_toReal, Real.rpow_one]

/-- The factorization `κ^(1/q) (κ^(1/p) a) = κ a` of the Hölder step. -/
theorem rpow_one_div_mul_rpow_one_div_mul {κ : ℝ} (hκ : 0 ≤ κ) (q : ℝ≥0∞) [p.HolderConjugate q]
    (a : ℝ) : κ ^ (1 / q.toReal) * (κ ^ (1 / p.toReal) * a) = κ * a := by
  rw [← mul_assoc, rpow_one_div_mul_rpow_one_div hκ q]

/-- `0 ≤ S^(1/r)` whenever `S ≥ 0` is known for finite `r` (at `r = ∞` the power is `1`). -/
theorem rpow_one_div_nonneg {r : ℝ≥0∞} {S : ℝ} (h : r ≠ ∞ → 0 ≤ S) : 0 ≤ S ^ (1 / r.toReal) := by
  by_cases hr : r = ∞
  · rw [hr, ENNReal.toReal_top, div_zero, Real.rpow_zero]; exact zero_le_one
  · exact Real.rpow_nonneg (h hr) _

end Exponent

/-! ### The two Hölder factors (scalar families) -/

section Factors

variable {ι : Type*} {g : ι → ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- The row factor `g^(1/r)` of a nonnegative family lies in `ℓ^r`; summability of `g` is used
only for finite `r`. -/
theorem memℓp_rpow_one_div (hg0 : ∀ i, 0 ≤ g i) (hg : r ≠ ∞ → Summable g) :
    Memℓp (fun i => g i ^ (1 / r.toReal)) r := by
  by_cases hr : r = ∞
  · subst hr
    exact memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; simp⟩
  · refine memℓp_gen ((hg hr).congr fun i => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hg0 i) _), ← Real.rpow_mul (hg0 i),
      one_div_mul_cancel (exponent_toReal_pos hr).ne', Real.rpow_one]

/-- The row factor has norm at most `S^(1/r)` when `∑' g ≤ S` (for finite `r`). -/
theorem norm_rpow_one_div_le (hg0 : ∀ i, 0 ≤ g i) (hg : r ≠ ∞ → Summable g) {S : ℝ}
    (hS : r ≠ ∞ → 0 ≤ S) (hle : r ≠ ∞ → ∑' i, g i ≤ S) :
    ‖(⟨_, memℓp_rpow_one_div hg0 hg⟩ : lp (fun _ : ι => ℝ) r)‖ ≤ S ^ (1 / r.toReal) := by
  by_cases hr : r = ∞
  · subst hr
    refine lp.norm_le_of_forall_le (rpow_one_div_nonneg hS) fun i => ?_
    show ‖g i ^ (1 / (∞ : ℝ≥0∞).toReal)‖ ≤ S ^ (1 / (∞ : ℝ≥0∞).toReal)
    simp
  · have hr0 := exponent_toReal_pos hr
    refine lp.norm_le_of_tsum_le hr0 (Real.rpow_nonneg (hS hr) _) ?_
    rw [← Real.rpow_mul (hS hr), one_div_mul_cancel hr0.ne', Real.rpow_one]
    refine le_of_eq_of_le (tsum_congr fun i => ?_) (hle hr)
    show ‖g i ^ (1 / r.toReal)‖ ^ r.toReal = g i
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hg0 i) _), ← Real.rpow_mul (hg0 i),
      one_div_mul_cancel hr0.ne', Real.rpow_one]

/-- The column factor `g^(1/r) a` lies in `ℓ^r` for `a ∈ ℓ^r`, given an entry bound `g ≤ G`
for finite `r` (at `r = ∞` the factor is `a`). -/
theorem memℓp_rpow_one_div_mul (hg0 : ∀ i, 0 ≤ g i) {G : ℝ} (hG : r ≠ ∞ → ∀ i, g i ≤ G)
    {a : ι → ℝ} (ha : Memℓp a r) : Memℓp (fun i => g i ^ (1 / r.toReal) * a i) r := by
  by_cases hr : r = ∞
  · subst hr
    simpa using ha
  · refine (ha.norm.const_mul (G ^ (1 / r.toReal))).mono fun i => ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (hg0 i) _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hg0 i) (hG hr i) (by positivity)) (norm_nonneg _)

end Factors

/-! ### The estimate -/

section Estimate

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F]
  {p : ℝ≥0∞} {K : I → J → 𝕜} {R C : ℝ}

/-- The pointwise identity `κ_{ij} ‖x j‖ = v_i ‖K i j * coeff x j‖`. -/
theorem schurEntry_mul_norm (v : I → ℝ) (K : I → J → 𝕜) (x : WeightedLp J E p) (i : I) (j : J) :
    schurEntry v (FiberTrivialization.weight (E := E)) K i j * ‖x j‖ =
      v i * ‖K i j * coeff x j‖ := by
  rw [schurEntry, norm_apply_eq, norm_mul]
  have := FiberTrivialization.weight_ne_zero (E := E) j
  field_simp

/-- The multiplication family of the Hölder step. -/
private def schurMul (J : Type*) : J → ℝ →L[ℝ] ℝ →L[ℝ] ℝ := fun _ => ContinuousLinearMap.mul ℝ ℝ

private theorem norm_schurMul_le (J : Type*) (j : J) : ‖schurMul J j‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  rw [NNReal.coe_one]; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ

variable [Fact (1 ≤ p)]

/-- **Aggregation over the rows.** If `y_i k = κ_{ik}^(1/p) ‖x k‖`, then `i ↦ ‖y_i‖` lies in
`ℓ^p(I)` with norm at most `C^(1/p) ‖x‖`; the column hypothesis is used for finite `p` only. -/
theorem schur_aggregate
    (hcol : p ≠ ∞ → ColSum (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K C)
    (x : WeightedLp J E p) (y : I → lp (fun _ : J => ℝ) p)
    (hy : ∀ i j, y i j = schurEntry (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K i j ^ (1 / p.toReal) * ‖x j‖) :
    ∃ h : Memℓp (fun i => ‖y i‖) p,
      ‖(⟨_, h⟩ : lp (fun _ : I => ℝ) p)‖ ≤ C ^ (1 / p.toReal) * ‖x‖ := by
  have hκ0 := schurEntry_nonneg (fun i => FiberTrivialization.weight_nonneg (E := F) i)
    (fun j => FiberTrivialization.weight_nonneg (E := E) j) K
  rcases p.dichotomy with rfl | hp
  · have hle : ∀ i, ‖y i‖ ≤ ‖x‖ := fun i => lp.norm_le_of_forall_le (norm_nonneg x) fun j => by
      rw [hy]
      simpa using norm_apply_le_norm x j
    refine ⟨memℓp_infty_iff.2 ⟨‖x‖, by rintro _ ⟨i, rfl⟩; simpa using hle i⟩, ?_⟩
    refine lp.norm_le_of_forall_le
      (mul_nonneg (rpow_one_div_nonneg fun h => absurd rfl h) (norm_nonneg _)) fun i => ?_
    simpa using hle i
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    have hc := hcol fun h => by rw [h, ENNReal.toReal_top] at hp; linarith
    have hC0 := hc.col_nonneg
    have hxs : Summable fun j => ‖x j‖ ^ p.toReal := (lp.memℓp x).summable hp0
    have hrows : ∀ i, ‖‖y i‖‖ ^ p.toReal = ∑' j, schurEntry (FiberTrivialization.weight (E := F))
        (FiberTrivialization.weight (E := E)) K i j * ‖x j‖ ^ p.toReal := fun i => by
      rw [norm_norm, lp.norm_rpow_eq_tsum hp0]
      refine tsum_congr fun j => ?_
      rw [hy, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hκ0 i j) _) (norm_nonneg _)),
        Real.mul_rpow (Real.rpow_nonneg (hκ0 i j) _) (norm_nonneg _), ← Real.rpow_mul (hκ0 i j),
        one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hrs : ∀ i, Summable fun j => schurEntry (FiberTrivialization.weight (E := F))
        (FiberTrivialization.weight (E := E)) K i j * ‖x j‖ ^ p.toReal := fun i =>
      (hxs.mul_left C).of_nonneg_of_le
        (fun j => mul_nonneg (hκ0 i j) (Real.rpow_nonneg (norm_nonneg _) _)) fun j =>
        mul_le_mul_of_nonneg_right (hc.entry_le (fun i => FiberTrivialization.weight_nonneg i)
          (fun j => FiberTrivialization.weight_nonneg j) i j) (Real.rpow_nonneg (norm_nonneg _) _)
    have key : ∀ s : Finset I, ∑ i ∈ s, ‖‖y i‖‖ ^ p.toReal ≤ (C ^ (1 / p.toReal) * ‖x‖) ^ p.toReal :=
      fun s => by
        rw [Finset.sum_congr rfl fun i _ => hrows i, ← Summable.tsum_finsetSum fun i _ => hrs i,
          Real.mul_rpow (Real.rpow_nonneg hC0 _) (norm_nonneg _), ← Real.rpow_mul hC0,
          one_div_mul_cancel hp0.ne', Real.rpow_one, lp.norm_rpow_eq_tsum hp0 x, ← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun i _ => hrs i) (hxs.mul_left C)
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right ((Summable.sum_le_tsum s (fun i _ => hκ0 i j)
          (hc.col_summable j)).trans (hc.col_le j)) (by positivity)
    exact ⟨memℓp_gen' key, lp.norm_le_of_forall_sum_le hp0 (by positivity) key⟩

/-- **The weighted Schur test (engine), one proof for every `1 ≤ p ≤ ∞`.** For a Hölder conjugate
row exponent `q`, the row hypothesis where `p ≠ 1` (i.e. `q < ∞`) and the column hypothesis where
`p ≠ ∞`:

* every coordinate series `∑ j, K i j * coeff x j` converges absolutely, and
* the image `i ↦ θ_i (∑' j, K i j * coeff x j)` lies in `ℓ^p` with norm at most
  `R^(1/q) C^(1/p) ‖x‖`.

The unused constant at an endpoint enters as `S^(1/∞.toReal) = S^0 = 1`. -/
theorem schur_bound_of (q : ℝ≥0∞) [p.HolderConjugate q]
    (hrow : p ≠ 1 → RowSum (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K R)
    (hcol : p ≠ ∞ → ColSum (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K C)
    (x : WeightedLp J E p) :
    (∀ i, Summable fun j => ‖K i j * coeff x j‖) ∧
    ∃ h : Memℓp (fun i => FiberTrivialization.equiv (E := F) i (∑' j, K i j * coeff x j)) p,
      ‖(⟨_, h⟩ : WeightedLp I F p)‖ ≤ R ^ (1 / q.toReal) * C ^ (1 / p.toReal) * ‖x‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ → p ≠ 1 := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).1
  have hv := fun i => FiberTrivialization.weight_nonneg (E := F) i
  have hw := fun j => FiberTrivialization.weight_nonneg (E := E) j
  have hκ0 := schurEntry_nonneg hv hw K
  -- the two Hölder factors of row `i`
  let u : ∀ i, lp (fun _ : J => ℝ) q := fun i =>
    ⟨_, memℓp_rpow_one_div (hκ0 i) fun h => (hrow (hq h)).row_summable i⟩
  have hu : ∀ i, ‖u i‖ ≤ R ^ (1 / q.toReal) := fun i =>
    norm_rpow_one_div_le (hκ0 i) (fun h => (hrow (hq h)).row_summable i)
      (fun h => (hrow (hq h)).row_nonneg)
      fun h => (hrow (hq h)).row_le i
  let y : ∀ i, lp (fun _ : J => ℝ) p := fun i =>
    ⟨_, memℓp_rpow_one_div_mul (hκ0 i) (fun h j => (hcol h).entry_le hv hw i j)
      (lp.memℓp x).norm⟩
  -- the Hölder product, one step for every `p`
  let H : ∀ i, lp (fun _ : J => ℝ) 1 := fun i =>
    lp.holderL (p := q) (q := p) 1 (schurMul J) (norm_schurMul_le J) (u i) (y i)
  have hH : ∀ i j, H i j = schurEntry (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K i j * ‖x j‖ := fun i j =>
    rpow_one_div_mul_rpow_one_div_mul (hκ0 i j) q _
  have hHnn : ∀ i j, ‖H i j‖ = H i j := fun i j => Real.norm_of_nonneg <| by
    rw [hH]; exact mul_nonneg (hκ0 i j) (norm_nonneg _)
  have hHsum : ∀ i, Summable fun j => ‖H i j‖ := fun i => by
    simpa using (lp.memℓp (H i)).summable (by simp)
  have hHnorm : ∀ i, ‖H i‖ = ∑' j, ‖H i j‖ := fun i => by
    simpa using lp.norm_eq_tsum_rpow (by simp) (H i)
  have hHle : ∀ i, ‖H i‖ ≤ R ^ (1 / q.toReal) * ‖y i‖ := fun i =>
    ((ContinuousLinearMap.le_opNorm₂ _ _ _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (lp.norm_holderL_le 1 (schurMul J) (norm_schurMul_le J) |>.trans (by simp))
        (hu i) (lp.norm_nonneg' _) zero_le_one) (lp.norm_nonneg' _))).trans_eq (by ring)
  -- absolute convergence of every row
  have hsum : ∀ i, Summable fun j => ‖K i j * coeff x j‖ := fun i =>
    ((hHsum i).mul_left (FiberTrivialization.weight (E := F) i)⁻¹).congr fun j => by
      rw [hHnn, hH, schurEntry_mul_norm, ← mul_assoc,
        inv_mul_cancel₀ (FiberTrivialization.weight_ne_zero i), one_mul]
  -- the pointwise output bound
  have hout : ∀ i, ‖FiberTrivialization.equiv (E := F) i (∑' j, K i j * coeff x j)‖ ≤
      R ^ (1 / q.toReal) * ‖y i‖ := fun i => by
    refine le_trans ?_ (hHle i)
    rw [FiberTrivialization.norm_equiv_apply, hHnorm, mul_comm]
    refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hsum i))
      (FiberTrivialization.weight_nonneg i)).trans_eq ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [hHnn, hH, schurEntry_mul_norm]
  -- aggregation and assembly
  obtain ⟨hN, hNle⟩ := schur_aggregate hcol x y fun _ _ => rfl
  let N : lp (fun _ : I => ℝ) p := ⟨_, hN⟩
  have hA0 : 0 ≤ R ^ (1 / q.toReal) := rpow_one_div_nonneg fun h => (hrow (hq h)).row_nonneg
  refine ⟨hsum, (hN.const_mul _).mono hout, ?_⟩
  refine (lp.norm_mono exponent_ne_zero (y := R ^ (1 / q.toReal) • N)
    fun i => (hout i).trans_eq ?_).trans ?_
  · rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      Real.norm_of_nonneg (mul_nonneg hA0 (lp.norm_nonneg' _))]
  · rw [lp.norm_const_smul exponent_ne_zero, Real.norm_of_nonneg hA0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hNle hA0

end Estimate

/-! ### The kernel operators -/

section CLM

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {K : I → J → 𝕜} {R C : ℝ}
  (hrow : p ≠ 1 → RowSum (FiberTrivialization.weight (E := F))
    (FiberTrivialization.weight (E := E)) K R)
  (hcol : p ≠ ∞ → ColSum (FiberTrivialization.weight (E := F))
    (FiberTrivialization.weight (E := E)) K C)

include hrow hcol in
/-- Over a complete field every coordinate series of the kernel is summable. -/
theorem summable_kernel (x : WeightedLp J E p) (i : I) : Summable fun j => K i j * coeff x j :=
  ((schur_bound_of p.conjExponent hrow hcol x).1 i).of_norm

/-- The kernel operator as a linear map: `(K x)_i = ∑' j, K i j * coeff x j`. -/
def kernelLM : WeightedLp J E p →ₗ[𝕜] WeightedLp I F p where
  toFun x := ⟨_, (schur_bound_of p.conjExponent hrow hcol x).2.1⟩
  map_add' x y := ext_coeff <| funext fun i => (coeff_mk_equiv _ _ i).trans <| by
    simp only [coeff_add, Pi.add_apply, coeff_mk_equiv, mul_add]
    exact (summable_kernel hrow hcol x i).tsum_add (summable_kernel hrow hcol y i)
  map_smul' c x := ext_coeff <| funext fun i => (coeff_mk_equiv _ _ i).trans <| by
    simp only [coeff_smul, Pi.smul_apply, coeff_mk_equiv, smul_eq_mul, RingHom.id_apply]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => mul_left_comm _ _ _

/-- **The kernel operator** `WeightedLp J E p →L[𝕜] WeightedLp I F p`, from the Schur
hypotheses that the exponent uses (rows unless `p = 1`, columns unless `p = ∞`). The bundled
constant is the one of the canonical conjugate exponent; `norm_kernelCLMOf_le` states the bound
for any conjugate. -/
def kernelCLMOf : WeightedLp J E p →L[𝕜] WeightedLp I F p :=
  (kernelLM hrow hcol).mkContinuous (R ^ (1 / p.conjExponent.toReal) * C ^ (1 / p.toReal))
    fun x => (schur_bound_of p.conjExponent hrow hcol x).2.2

/-- The kernel operator in coordinates. -/
theorem coeff_kernelCLMOf (x : WeightedLp J E p) (i : I) :
    coeff (kernelCLMOf hrow hcol x) i = ∑' j, K i j * coeff x j :=
  coeff_mk_equiv _ _ i

theorem hasSum_coeff_kernelCLMOf (x : WeightedLp J E p) (i : I) :
    HasSum (fun j => K i j * coeff x j) (coeff (kernelCLMOf hrow hcol x) i) := by
  rw [coeff_kernelCLMOf]
  exact (summable_kernel hrow hcol x i).hasSum

end CLM

section CLMOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {K : I → J → 𝕜} {R C : ℝ}
  (hrow : p ≠ 1 → RowSum (FiberTrivialization.weight (E := F))
    (FiberTrivialization.weight (E := E)) K R)
  (hcol : p ≠ ∞ → ColSum (FiberTrivialization.weight (E := F))
    (FiberTrivialization.weight (E := E)) K C)

/-- `‖K‖ ≤ R^(1/q) C^(1/p)` for every Hölder conjugate `q`. -/
theorem norm_kernelCLMOf_le (q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖kernelCLMOf hrow hcol‖ ≤ R ^ (1 / q.toReal) * C ^ (1 / p.toReal) :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (rpow_one_div_nonneg fun h =>
        (hrow ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).1 h)).row_nonneg)
      (rpow_one_div_nonneg fun h => (hcol h).col_nonneg))
    fun x => (schur_bound_of q hrow hcol x).2.2

end CLMOpNorm

section KernelCLM

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜} {R C : ℝ}

/-- **The Schur operator** of a kernel with both Schur hypotheses, at every `1 ≤ p ≤ ∞`. -/
def kernelCLM {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (h : SchurBound (FiberTrivialization.weight (E := F)) (FiberTrivialization.weight (E := E)) K
      R C) :
    WeightedLp J E p →L[𝕜] WeightedLp I F p :=
  kernelCLMOf (fun _ => h.toRowSum) (fun _ => h.toColSum)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (h : SchurBound (FiberTrivialization.weight (E := F)) (FiberTrivialization.weight (E := E)) K R C)

/-- The Schur operator in coordinates: `coeff (K x) i = ∑' j, K i j * coeff x j`. -/
theorem kernelCLM_apply_coeff (x : WeightedLp J E p) (i : I) :
    coeff (kernelCLM h x) i = ∑' j, K i j * coeff x j :=
  coeff_kernelCLMOf _ _ x i

end KernelCLM

section KernelCLMOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {I J : Type*}
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜} {R C : ℝ}

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (h : SchurBound (FiberTrivialization.weight (E := F)) (FiberTrivialization.weight (E := E)) K R C)

/-- `‖K‖_{p → p} ≤ R^(1/q) C^(1/p)`. -/
theorem norm_kernelCLM_le (q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖kernelCLM (p := p) h‖ ≤ R ^ (1 / q.toReal) * C ^ (1 / p.toReal) :=
  norm_kernelCLMOf_le _ _ q

end KernelCLMOpNorm


/-! ### Finitely supported rows and columns (the certificate hook) -/

section Finsets

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*} {v : I → ℝ} {w : J → ℝ} {K : I → J → 𝕜}
  {R C : ℝ}

/-- **Banded kernels**: if the support of row `i` lies in the finite set `s i` and the support
of column `j` in `t j`, the two Schur hypotheses are finite sums. -/
theorem SchurBound.ofFinsets (s : I → Finset J) (t : J → Finset I)
    (hs : ∀ i j, K i j ≠ 0 → j ∈ s i) (ht : ∀ i j, K i j ≠ 0 → i ∈ t j) (hR0 : 0 ≤ R)
    (hC0 : 0 ≤ C) (hR : ∀ i, ∑ j ∈ s i, schurEntry v w K i j ≤ R)
    (hC : ∀ j, ∑ i ∈ t j, schurEntry v w K i j ≤ C) : SchurBound v w K R C :=
  have hs' : ∀ i, ∀ j ∉ s i, schurEntry v w K i j = 0 := fun i j hj =>
    schurEntry_of_eq_zero (not_not.1 (mt (hs i j) hj))
  have ht' : ∀ j, ∀ i ∉ t j, schurEntry v w K i j = 0 := fun j i hi =>
    schurEntry_of_eq_zero (not_not.1 (mt (ht i j) hi))
  { row_nonneg := hR0
    row_summable := fun i => summable_of_ne_finset_zero (hs' i)
    row_le := fun i => (tsum_eq_sum (hs' i)).trans_le (hR i)
    col_nonneg := hC0
    col_summable := fun j => summable_of_ne_finset_zero (ht' j)
    col_le := fun j => (tsum_eq_sum (ht' j)).trans_le (hC j) }

end Finsets

section DiagonalConstruction

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (d : M → 𝕜) (hd : BddAbove (Set.range fun n => ‖d n‖))

/-- The pointwise bounded diagonal. It needs no completeness because no series is formed. -/
def diagCLM : WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  let D := ⨆ n, ‖d n‖
  have hD : 0 ≤ D := Real.iSup_nonneg fun n => norm_nonneg (d n)
  have bound : ∀ x : WeightedLp M E p,
      ∃ h : Memℓp (fun n => d n • x n) p,
        ‖(⟨_, h⟩ : WeightedLp M E p)‖ ≤ D * ‖x‖ := fun x =>
    memℓp_norm_le_of_le_comp (Equiv.refl M) x _ hD fun n =>
      (norm_smul_le (d n) (x n)).trans
        (mul_le_mul_of_nonneg_right (le_ciSup hd n) (norm_nonneg (x n)))
  LinearMap.mkContinuous
    { toFun x := ⟨_, (bound x).1⟩
      map_add' x y := lp.ext <| funext fun n => by
        change d n • (x + y) n = d n • x n + d n • y n
        rw [lp.coeFn_add, Pi.add_apply, smul_add]
      map_smul' c x := lp.ext <| funext fun n => by
        change d n • (c • x) n = c • (d n • x n)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_comm] }
    D fun x => (bound x).2

/-- The diagonal acts in the scalar coordinates of the chosen frame. -/
theorem coeff_diagCLM (x : WeightedLp M E p) (n : M) :
    coeff (diagCLM d hd x) n = d n * coeff x n := by
  change (FiberTrivialization.equiv (E := E) n).symm (d n • x n) = _
  rw [map_smul]
  rfl

end DiagonalConstruction

section DiagonalOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [DecidableEq M]
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (d : M → 𝕜) (hd : BddAbove (Set.range fun n => ‖d n‖))

/-- Each diagonal entry is below the operator norm (tested on `single n 1`). -/
theorem norm_le_norm_diagCLM (n : M) : ‖d n‖ ≤ ‖diagCLM (E := E) (p := p) d hd‖ := by
  have h1 := norm_apply_le_norm (diagCLM (E := E) (p := p) d hd (single n 1)) n
  rw [norm_apply_eq, coeff_diagCLM, coeff_single_self, mul_one] at h1
  have h2 := (diagCLM (E := E) (p := p) d hd).le_opNorm (single n 1)
  rw [norm_single, norm_one, one_mul] at h2
  exact le_of_mul_le_mul_right (h1.trans h2) (FiberTrivialization.weight_pos n)

/-- The exact diagonal norm at every exponent. -/
theorem norm_diagCLM : ‖diagCLM (E := E) (p := p) d hd‖ = ⨆ n, ‖d n‖ := by
  refine le_antisymm ?_ (Real.iSup_le (norm_le_norm_diagCLM d hd) (norm_nonneg _))
  apply (diagCLM (E := E) (p := p) d hd).opNorm_le_bound
    (Real.iSup_nonneg fun n => norm_nonneg (d n))
  intro x
  exact (memℓp_norm_le_of_le_comp (Equiv.refl M) x (fun n => d n • x n)
    (Real.iSup_nonneg fun n => norm_nonneg (d n)) fun n =>
      (norm_smul_le (d n) (x n)).trans
        (mul_le_mul_of_nonneg_right (le_ciSup hd n) (norm_nonneg (x n)))).2

/-- `‖D_d‖ ≤ D` from a bound `‖d n‖ ≤ D`, `0 ≤ D`. -/
theorem norm_diagCLM_le {D : ℝ} (hD : ∀ n, ‖d n‖ ≤ D) (hD0 : 0 ≤ D) :
    ‖diagCLM (E := E) (p := p) d hd‖ ≤ D :=
  (norm_diagCLM d hd).trans_le (Real.iSup_le hD hD0)


end DiagonalOpNorm

section LaurentBound

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M]

/-- The Laurent (convolution) kernel `K n k = a (n - k)`. -/
def laurentKernel (a : M → 𝕜) : M → M → 𝕜 := fun n k => a (n - k)

/-- The moderate-weight entry bound `κ_{nk} ≤ C ‖a (n - k)‖ v (n - k)`. -/
theorem schurEntry_laurentKernel_le {w v : M → ℝ} {Cm : ℝ} (hw : ∀ m, 0 < w m)
    (hC : Moderate w v Cm) (a : M → 𝕜) (n k : M) :
    schurEntry w w (laurentKernel a) n k ≤ Cm * (‖a (n - k)‖ * v (n - k)) := by
  have hmod := hC k (n - k)
  rw [add_sub_cancel] at hmod
  rw [schurEntry, laurentKernel, mul_div_assoc]
  exact (mul_le_mul_of_nonneg_left ((div_le_iff₀ (hw k)).2 hmod) (norm_nonneg _)).trans_eq
    (by ring)

/-- **The Laurent kernel of an `ℓ¹_v` symbol on a moderate weight satisfies both Schur
hypotheses with `R = C = C_mod ‖a‖_{1,v}`** (rows and columns are both dominated by the symbol
after `l = n - k`). -/
theorem schurBound_laurent {w v : M → ℝ} {Cm : ℝ} (hw : ∀ m, 0 < w m) (hC : Moderate w v Cm)
    {a : M → 𝕜} (ha : MemL1v v a) :
    SchurBound w w (laurentKernel a) (Cm * normL1v v a) (Cm * normL1v v a) := by
  let g : M → ℝ := fun l => Cm * (‖a l‖ * v l)
  have hg : Summable g := ha.mul_left Cm
  have hg0 : ∀ l, 0 ≤ g l := fun l =>
    (mul_nonneg (norm_nonneg (a l)) (hC.mul_pos hw l).le).trans_eq (by ring)
  have hgt : ∑' l, g l = Cm * normL1v v a := tsum_mul_left
  have hκ0 := schurEntry_nonneg (fun m => (hw m).le) (fun m => (hw m).le) (laurentKernel a)
  have hle : ∀ n k, schurEntry w w (laurentKernel a) n k ≤ g (n - k) :=
    schurEntry_laurentKernel_le hw hC a
  have hrs : ∀ n, Summable fun k => g (n - k) := fun n => (Equiv.subLeft n).summable_iff.2 hg
  have hcs : ∀ k, Summable fun n => g (n - k) := fun k => (Equiv.subRight k).summable_iff.2 hg
  have hS0 : 0 ≤ Cm * normL1v v a := hgt ▸ tsum_nonneg hg0
  exact
    { row_nonneg := hS0
      row_summable := fun n => (hrs n).of_nonneg_of_le (hκ0 n) (hle n)
      row_le := fun n => ((Summable.tsum_le_tsum (hle n) ((hrs n).of_nonneg_of_le (hκ0 n) (hle n))
        (hrs n)).trans_eq ((Equiv.subLeft n).tsum_eq g)).trans_eq hgt
      col_nonneg := hS0
      col_summable := fun k => (hcs k).of_nonneg_of_le (fun n => hκ0 n k) fun n => hle n k
      col_le := fun k => ((Summable.tsum_le_tsum (fun n => hle n k)
        ((hcs k).of_nonneg_of_le (fun n => hκ0 n k) fun n => hle n k)
        (hcs k)).trans_eq ((Equiv.subRight k).tsum_eq g)).trans_eq hgt }


end LaurentBound

section LaurentComparison

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {M : Type*} [AddCommGroup M]
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {Cm : ℝ} {a : M → 𝕜}
  (ha : MemL1v v a) (hC : Moderate (FiberTrivialization.weight (E := E)) v Cm)

/-- **The Schur operator of the Laurent kernel is the symbol operator** of `WeightedLp/Module`. -/
theorem kernelCLM_laurent_eq_symbolSeries :
    kernelCLM (E := E) (F := E) (p := p) (schurBound_laurent FiberTrivialization.weight_pos hC ha) =
      symbolSeries a ha hC :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun n => by
    rw [kernelCLM_apply_coeff, coeff_symbolSeries]
    exact ((Equiv.subLeft n).tsum_eq fun k => laurentKernel a n k * coeff x k).symm.trans
      (tsum_congr fun l => by rw [Equiv.subLeft_apply, laurentKernel, sub_sub_cancel])


end LaurentComparison

end RadiiPolynomial.WeightedLp

end
