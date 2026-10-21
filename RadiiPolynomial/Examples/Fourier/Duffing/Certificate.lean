import RadiiPolynomial.Examples.Fourier.Duffing.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock
import RadiiPolynomial.Examples.Fourier.Duffing.Numbers
import RadiiPolynomial.Certification.RadiiPolynomialQ

/-!
# Book §10.1 Helmholtz–Duffing on `ℓ²_{6/5}`: the numerical closure

The concrete certificate at our own rational centre for the data `c = (1/10, 4, 1)`, `N = 10`,
`ν = 6/5` of book §10.1 (`ch10.tex:155–158`), and the endpoint: the raw Fourier map
`F_n(a) = (−n² + i n/10 + 4) aₙ − (a ⋆ a)ₙ − bₙ`, `b_{±1} = 1/2`, has a unique zero in the closed
ball of radius `1/200000` around the candidate `ā` in `ℓ²_{6/5}`; the zero is unique in the ball of
radius `1/25` and real (`conj ã₋ₙ = ãₙ`).

The candidate and the head matrix are the consumer-owned data of `Examples/Fourier/Duffing/Numbers.lean`
(generated). This file supplies
* the BRIDGES from the exact `ℚ` mirror to the complex objects of the frozen consumer
  `Examples/Fourier/Duffing/Algebra.lean` (`toC z = z.1 + z.2 i`; folds over `List.range` plus a shift, matched
  with the `Finset` heads by `List.sum_toFinset`);
* the four bound lemmas: `Y₀` through the exact finite residual `norm_sq_G_abar`, `Z₀` through the
  block Schur producer `norm_le_sqrt_of_block`, the composed leakage `H` through
  `norm_head_term_le_composed`, and `U` through `norm_comp_headReal_le_urow`; entry moduli are
  bounded by the rational majorant `‖z‖ ≤ |Re z| + |Im z|` (all UPPER);
* the certificate `cert`, the discharges of the endpoint's forcing and tail-sum sockets, the radii
  inequality at `r₀ = 1/200000` and `r₁ = 1/25`;
* the endpoints, the concrete instances of `duffing_existsUnique` and `duffing_existsUnique_real`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace FourierDuffing.Certificate

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  FourierDuffing FourierDuffing.Numbers

/-! ### A. Objects and bridges -/

section Objects

/-- The weight parameter `ν = 6/5`. -/
def ν₆₅ : PosReal := ⟨6 / 5, by norm_num⟩

/-- `ν = 6/5` satisfies `1 ≤ ν`. -/
instance fact_one_le_ν₆₅ : Fact (1 ≤ (ν₆₅ : ℝ)) := ⟨by show (1 : ℝ) ≤ 6 / 5; norm_num⟩

theorem coe_ν₆₅ : (ν₆₅ : ℝ) = 6 / 5 := rfl

/-- A rational complex pair as a complex number: `toC z = z.1 + z.2 i`. -/
def toC (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The raw centre coefficients. -/
def abarC (n : ℤ) : ℂ := toC (abarQ n)

/-- **The candidate** `ā = J_F (ā_n)` on the head `|n| ≤ 10`. -/
def abar : X₂ ℂ ν₆₅ := headOfRaw (headF 10) abarC

theorem abar_supp : ∀ k ∉ headF 10, coeff abar k = 0 := fun k hk => by
  rw [abar, coeff_headOfRaw, ite_eq_right hk]

/-- The raw head-matrix entries. -/
def MC (i j : ℤ) : ℂ := toC (MQ i j)

/-- **The head matrix** as a bounded operator (a finite matrix on `headF 10`). -/
def Mop : X₂ ℂ ν₆₅ →L[ℂ] X₂ ℂ ν₆₅ := finMatrixCLM (E := geomFiberZ ℂ ν₆₅) (p := 2) (headF 10) MC

/-- `P M = M` by construction (no computation). -/
theorem hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν₆₅) (p := 2) (headF 10) ∘L Mop = Mop :=
  headProj_comp_finMatrixCLM _ _

end Objects

section Bridges

/-! #### Complex arithmetic on `ℚ × ℚ` -/

@[simp] theorem toC_re (z : ℚ × ℚ) : (toC z).re = z.1 := by simp [toC]

@[simp] theorem toC_im (z : ℚ × ℚ) : (toC z).im = z.2 := by simp [toC]

theorem toC_zero : toC (0, 0) = 0 := Complex.ext (by simp) (by simp)

theorem toC_cadd (x y : ℚ × ℚ) : toC (cadd x y) = toC x + toC y :=
  Complex.ext (by simp [cadd]) (by simp [cadd])

theorem toC_csub (x y : ℚ × ℚ) : toC (csub x y) = toC x - toC y :=
  Complex.ext (by simp [csub]) (by simp [csub])

theorem toC_cmul (x y : ℚ × ℚ) : toC (cmul x y) = toC x * toC y :=
  Complex.ext (by simp [cmul]) (by simp [cmul])

theorem toC_cscale (t : ℚ) (x : ℚ × ℚ) : toC (cscale t x) = (t : ℂ) * toC x :=
  Complex.ext (by simp [cscale]) (by simp [cscale])

theorem toC_cinv (x : ℚ × ℚ) : toC (cinv x) = (toC x)⁻¹ :=
  Complex.ext (by simp [cinv, cnormSq, Complex.inv_re, Complex.normSq_apply])
    (by simp [cinv, cnormSq, Complex.inv_im, Complex.normSq_apply, neg_div])

theorem toC_cconj (x : ℚ × ℚ) : toC (cconj x) = starRingEnd ℂ (toC x) :=
  Complex.ext (by simp [cconj]) (by simp [cconj])

theorem qabs_eq (q : ℚ) : qabs q = |q| := by
  unfold qabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.1 h)).symm

/-- **The rational modulus majorant** `‖z‖ ≤ |Re z| + |Im z|` (UPPER). -/
theorem norm_le_reim (z : ℚ × ℚ) : ‖toC z‖ ≤ (reim z : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
  rw [toC_re, toC_im, reim, Rat.cast_add, qabs_eq, qabs_eq, Rat.cast_abs, Rat.cast_abs]

/-- **The exact squared modulus** `‖z‖² = re² + im²`. -/
theorem sq_norm_toC (z : ℚ × ℚ) : ‖toC z‖ ^ 2 = (cnormSq z : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, toC_re, toC_im, cnormSq]
  push_cast
  ring

theorem cast_nuQ : ((nuQ : ℚ) : ℝ) = 6 / 5 := by
  rw [nuQ]
  push_cast
  ring

/-- The normalized entry against its rational majorant. -/
theorem weighted_le_reim (z : ℚ × ℚ) (i j : ℤ) :
    ‖toC z‖ * (ν₆₅ : ℝ) ^ i.natAbs / (ν₆₅ : ℝ) ^ j.natAbs ≤
      ((reim z * nuQ ^ i.natAbs / nuQ ^ j.natAbs : ℚ) : ℝ) := by
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_pow, cast_nuQ, coe_ν₆₅]
  gcongr
  exact norm_le_reim z

/-! #### Folds over lists versus `Finset` sums -/

theorem toC_csum (l : List ℤ) (f : ℤ → ℚ × ℚ) :
    toC (csum l f) = (l.map fun k => toC (f k)).sum := by
  induction l with
  | nil => exact toC_zero
  | cons k l ih =>
    show toC (cadd (f k) (csum l f)) = _
    rw [toC_cadd, ih, List.map_cons, List.sum_cons]

theorem cast_qsum (l : List ℤ) (f : ℤ → ℚ) :
    ((qsum l f : ℚ) : ℝ) = (l.map fun k => (f k : ℝ)).sum := by
  induction l with
  | nil => simp [qsum]
  | cons k l ih =>
    show ((f k + qsum l f : ℚ) : ℝ) = _
    rw [Rat.cast_add, ih, List.map_cons, List.sum_cons]

theorem qsum_append (l₁ l₂ : List ℤ) (f : ℤ → ℚ) :
    qsum (l₁ ++ l₂) f = qsum l₁ f + qsum l₂ f := by
  induction l₁ with
  | nil => simp [qsum]
  | cons k l ih =>
    show f k + qsum (l ++ l₂) f = f k + qsum l f + qsum l₂ f
    rw [ih, add_assoc]

/-- A `Finset` sum over `s` is the list sum over a duplicate-free list with the same members. -/
theorem sum_eq_list {R : Type*} [AddCommMonoid R] {s : Finset ℤ} {l : List ℤ} (hl : l.Nodup)
    (hs : ∀ n, n ∈ s ↔ n ∈ l) (f : ℤ → R) : ∑ n ∈ s, f n = (l.map f).sum := by
  rw [show s = l.toFinset from Finset.ext fun n => by rw [hs, List.mem_toFinset],
    List.sum_toFinset _ hl]

/-! #### The index lists -/

theorem mem_headF10 {k : ℤ} : k ∈ headF 10 ↔ -10 ≤ k ∧ k ≤ 10 := by
  simp only [Finset.mem_Icc, Nat.cast_ofNat]

theorem mem_headF7 {k : ℤ} : k ∈ headF 7 ↔ -7 ≤ k ∧ k ≤ 7 := by
  simp only [Finset.mem_Icc, Nat.cast_ofNat]

theorem mem_idx {k : ℤ} : k ∈ idx ↔ -10 ≤ k ∧ k ≤ 10 := by
  simp only [idx, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k + 10).toNat, by omega, by omega⟩

theorem mem_idx41 {k : ℤ} : k ∈ idx41 ↔ -20 ≤ k ∧ k ≤ 20 := by
  simp only [idx41, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k + 20).toNat, by omega, by omega⟩

theorem mem_leakColsQ {k : ℤ} : k ∈ leakColsQ ↔ (-17 ≤ k ∧ k ≤ -11) ∨ (11 ≤ k ∧ k ≤ 17) := by
  simp only [leakColsQ, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨(k + 17).toNat, by omega, by omega⟩
    · exact Or.inr ⟨(k - 11).toNat, by omega, by omega⟩

theorem mem_leakRowsQ {k : ℤ} : k ∈ leakRowsQ ↔ (-10 ≤ k ∧ k ≤ -4) ∨ (4 ≤ k ∧ k ≤ 10) := by
  simp only [leakRowsQ, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨(k + 10).toNat, by omega, by omega⟩
    · exact Or.inr ⟨(k - 4).toNat, by omega, by omega⟩

theorem nodup_idx : idx.Nodup := by decide +kernel

theorem nodup_idx41 : idx41.Nodup := by decide +kernel

theorem nodup_leakColsQ : leakColsQ.Nodup := by decide +kernel

theorem nodup_leakRowsQ : leakRowsQ.Nodup := by decide +kernel

theorem idx_eq_chunks : idx = rowChunk 0 ++ rowChunk 1 ++ rowChunk 2 := by decide +kernel

theorem leakColsQ_eq_chunks : leakColsQ = leakColChunk 0 ++ leakColChunk 1 := by decide +kernel

theorem idx41_eq_chunks : idx41 = y0Chunk 0 ++ y0Chunk 1 ++ y0Chunk 2 := by decide +kernel

/-- **The index bridge** `∑_{k ∈ headF 10} f k = ∑_{j < 21} f (j − 10)` (as the list `idx`). -/
theorem sum_headF_eq_list {R : Type*} [AddCommMonoid R] (f : ℤ → R) :
    ∑ k ∈ headF 10, f k = (idx.map f).sum :=
  sum_eq_list nodup_idx (fun _ => by rw [mem_headF10, mem_idx]) f

/-- The band columns of the head `|n| ≤ 10` and the band `|b| ≤ 7`: `11 ≤ |k| ≤ 17`. -/
theorem mem_leakCols_iff (k : ℤ) : k ∈ leakCols (headF 10) (headF 7) ↔ k ∈ leakColsQ := by
  rw [mem_leakCols, mem_leakColsQ, mem_headF10]
  constructor
  · rintro ⟨hk, n, hn, hb⟩
    rw [mem_headF10] at hn
    rw [mem_headF7] at hb
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h
    · exact ⟨-10, mem_headF10.2 (by norm_num), mem_headF7.2 (by omega)⟩
    · exact ⟨10, mem_headF10.2 (by norm_num), mem_headF7.2 (by omega)⟩

/-- The boundary rows of the head `|n| ≤ 10` and the band `|b| ≤ 7`: `4 ≤ |n| ≤ 10`. -/
theorem mem_leakRows_iff (n : ℤ) : n ∈ leakRows (headF 10) (headF 7) ↔ n ∈ leakRowsQ := by
  rw [leakRows, Finset.mem_filter, mem_leakRowsQ, mem_headF10]
  constructor
  · rintro ⟨hn, b, hb, hnb⟩
    rw [mem_headF7] at hb
    rw [mem_headF10] at hnb
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h
    · exact ⟨7, mem_headF7.2 (by norm_num), by rw [mem_headF10]; omega⟩
    · exact ⟨-7, mem_headF7.2 (by norm_num), by rw [mem_headF10]; omega⟩

theorem leakCols_eq : leakCols (headF 10) (headF 7) = leakColsQ.toFinset :=
  Finset.ext fun k => by rw [List.mem_toFinset]; exact mem_leakCols_iff k

theorem leakRows_eq : leakRows (headF 10) (headF 7) = leakRowsQ.toFinset :=
  Finset.ext fun n => by rw [List.mem_toFinset]; exact mem_leakRows_iff n

/-- The residual support `F ∪ (F + F) = {|n| ≤ 20}` of the head `F = headF 10`. -/
theorem mem_support_iff (n : ℤ) :
    n ∈ headF 10 ∪ (headF 10).image₂ (· + ·) (headF 10) ↔ n ∈ idx41 := by
  rw [mem_idx41, Finset.mem_union, Finset.mem_image₂, mem_headF10]
  constructor
  · rintro (h | ⟨a, ha, b, hb, rfl⟩)
    · omega
    · rw [mem_headF10] at ha hb
      omega
  · intro h
    by_cases h' : -10 ≤ n ∧ n ≤ 10
    · exact Or.inl h'
    · right
      rcases le_or_gt n 0 with hn | hn
      · exact ⟨-10, mem_headF10.2 (by norm_num), n + 10, mem_headF10.2 (by omega), by ring⟩
      · exact ⟨10, mem_headF10.2 (by norm_num), n - 10, mem_headF10.2 (by omega), by ring⟩

/-! #### The chunk checks cover every row and column -/

theorem z0Row_le {i : ℤ} (hi : i ∈ idx) : z0RowQ i ≤ RzC := by
  rw [idx_eq_chunks, List.mem_append, List.mem_append] at hi
  rcases hi with (h | h) | h
  exacts [check_Z0_rows_0 i h, check_Z0_rows_1 i h, check_Z0_rows_2 i h]

theorem z0Col_le {j : ℤ} (hj : j ∈ idx) : z0ColQ j ≤ CzC := by
  rw [idx_eq_chunks, List.mem_append, List.mem_append] at hj
  rcases hj with (h | h) | h
  exacts [check_Z0_cols_0 j h, check_Z0_cols_1 j h, check_Z0_cols_2 j h]

theorem kmRow_le {i : ℤ} (hi : i ∈ idx) : kmRowQ i ≤ RmC := by
  rw [idx_eq_chunks, List.mem_append, List.mem_append] at hi
  rcases hi with (h | h) | h
  exacts [check_Z1_rows_0 i h, check_Z1_rows_1 i h, check_Z1_rows_2 i h]

theorem kmCol_le {k : ℤ} (hk : k ∈ leakColsQ) : kmColQ k ≤ CmC := by
  rw [leakColsQ_eq_chunks, List.mem_append] at hk
  rcases hk with h | h
  exacts [check_Z1_cols_0 k h, check_Z1_cols_1 k h]

/-! #### The data as complex objects -/

theorem abarQ_eq_zero {n : ℤ} (hn : n ∉ headF 10) : abarQ n = (0, 0) := by
  rw [abarQ, ite_eq_right fun h => hn (mem_headF10.2 h)]

theorem coeff_abar (n : ℤ) : coeff abar n = toC (abarQ n) := by
  rw [abar, coeff_headOfRaw]
  split_ifs with h
  · rfl
  · rw [abarQ_eq_zero h, toC_zero]

theorem MQ_eq_zero {i j : ℤ} (h : ¬(i ∈ headF 10 ∧ j ∈ headF 10)) : MQ i j = (0, 0) := by
  rw [MQ, ite_eq_right fun h' => h ⟨mem_headF10.2 h'.1, mem_headF10.2 h'.2⟩]

/-- **The matrix of `M`** is the mirror (every `i`, `j`; `0` off the head block on both sides). -/
theorem matrixOf_Mop (i j : ℤ) : matrixOf Mop i j = toC (MQ i j) := by
  rw [Mop, matrixOf_finMatrixCLM]
  split_ifs with h
  · rfl
  · rw [MQ_eq_zero h, toC_zero]

theorem duffing_eq_toC (n : ℤ) : duffing (1 / 10) 4 n = toC (muQ n) := by
  apply Complex.ext
  · simp [duffing, muQ, c₂Q, sq]
    ring
  · simp [duffing, muQ, c₁Q, sq]

theorem coeff_forcing_eq (n : ℤ) : coeff (forcing (ν := ν₆₅) 1) n = toC (forcQ n) := by
  rw [coeff_forcing, forcQ]
  split_ifs
  · exact Complex.ext (by simp [c₃Q]) (by simp)
  · exact toC_zero.symm

theorem convCoeff_abar (n : ℤ) : convCoeff abar abar n = toC (convQ n) := by
  rw [convCoeff_eq_sum (headF 10) abar_supp abar n, convQ, toC_csum, sum_headF_eq_list]
  simp only [coeff_abar, toC_cmul]

/-- The raw Fourier map at the candidate is the mirror residual. -/
theorem rawF_abar (j : ℤ) :
    rawF (duffing (1 / 10) 4) (forcing 1) abar j = toC (residQ j) := by
  rw [rawF, duffing_eq_toC, coeff_abar, convCoeff_abar, coeff_forcing_eq, residQ, toC_csub,
    toC_csub, toC_cmul]

/-- **The coefficients of `G ā`** are the mirror `GQ` (the coefficient identity `coeff_G`, with
the forcing support and the nonvanishing tail symbol). -/
theorem coeff_G_abar_eq (n : ℤ) :
    coeff (G (headF 10) (duffing (1 / 10) 4) (summable_sq_tailSymbol_duffing_headF control_hN) Mop
      (forcing 1) abar) n = toC (GQ n) := by
  have h := congrFun (coeff_G (headF 10) (duffing (1 / 10) 4)
    (summable_sq_tailSymbol_duffing_headF control_hN) Mop (forcing 1)
    (forcing_supp (by norm_num)) (duffing_ne_zero control_hN) abar) n
  rw [h, rawA, Mop, coeff_finMatrixCLM, GQ]
  by_cases hn : n ∈ headF 10
  · rw [ite_eq_left hn, ite_eq_left (mem_headF10.1 hn), tailSymbol_of_mem (Finset.mem_coe.2 hn), zero_mul,
      add_zero, toC_csum, ← sum_headF_eq_list]
    exact Finset.sum_congr rfl fun j hj => by
      rw [coeff_headOfRaw, ite_eq_left hj, rawF_abar, MC, toC_cmul]
  · rw [ite_eq_right hn, ite_eq_right fun h' => hn (mem_headF10.2 h'),
      tailSymbol_of_notMem fun h' => hn (Finset.mem_coe.1 h'), zero_add, rawF_abar,
      duffing_eq_toC, toC_cmul, toC_cinv]

/-- The Jacobian block `K_H` has the mirror matrix `DF` on the head block. -/
theorem matrixOf_Kh {n j : ℤ} (hn : n ∈ headF 10) (hj : j ∈ headF 10) :
    matrixOf (Kh (headF 10) (duffing (1 / 10) 4) (betaOf (headF 10) abar abar_supp)) n j =
      toC (DFQ n j) := by
  rw [Kh, matrixOf_sub, LamH, matrixOf_diagCLM, matrixOf_headProj_symbolAction_headProj,
    ite_eq_left (show n ∈ headF 10 ∧ j ∈ headF 10 from ⟨hn, hj⟩), DFQ, toC_csub, toC_cscale]
  simp only [rawSymbol_betaOf, coeff_abar, headSym]
  by_cases h : n = j
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left hn, duffing_eq_toC]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h, toC_zero]
    push_cast
    ring

/-- **The `Z₀` matrix** `P − M K_H` on the head block is the mirror `E = I − M DF`. -/
theorem matrixOf_Z0op_eq (i j : ℤ) (hi : i ∈ headF 10) (hj : j ∈ headF 10) :
    matrixOf (headProj (headF 10) - Mop ∘L Kh (headF 10) (duffing (1 / 10) 4)
      (betaOf (headF 10) abar abar_supp)) i j = toC (EQ i j) := by
  have h₂ : ∀ x, ∀ n ∉ headF 10,
      coeff (Kh (headF 10) (duffing (1 / 10) 4) (betaOf (headF 10) abar abar_supp) x) n = 0 :=
    fun x n hn => by
      rw [← headProj_comp_Kh (headF 10) (duffing (1 / 10) 4) (betaOf (headF 10) abar abar_supp),
        ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hn]
  rw [matrixOf_sub, matrixOf_headProj, matrixOf_comp_of_support Mop _ h₂, EQ, toC_csub, toC_csum,
    ← sum_headF_eq_list]
  congr 1
  · by_cases h : i = j
    · rw [ite_eq_left ⟨h, hi⟩, ite_eq_left h]
      exact Complex.ext (by simp) (by simp)
    · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h, toC_zero]
  · exact Finset.sum_congr rfl fun n hn => by rw [matrixOf_Mop, matrixOf_Kh hn hj, toC_cmul]

/-- **The band of `β = 2ā`**: `rawSymbol β l = 0` for `|l| > 7` (`check_support`). -/
theorem band_beta : ∀ l ∉ headF 7, rawSymbol (betaOf (headF 10) abar abar_supp) l = 0 :=
  fun l hl => by
    simp only [rawSymbol_betaOf, coeff_abar]
    by_cases h : l ∈ idx
    · have h7 : 7 < |l| := lt_abs.2 (by rw [mem_headF7] at hl; omega)
      rw [check_support l h h7, toC_zero, mul_zero]
    · rw [abarQ_eq_zero fun h' => h (mem_idx.2 (mem_headF10.1 h')), toC_zero, mul_zero]

/-- **The composed leakage kernel** is the mirror `K_M` (every `i`, `k`). -/
theorem composedLeakKernel_eq (i k : ℤ) :
    composedLeakKernel Mop (betaOf (headF 10) abar abar_supp) (headF 10) (headF 7) i k =
      toC (KMQ i k) := by
  rw [composedLeakKernel, KMQ, toC_csum, leakRows_eq, List.sum_toFinset _ nodup_leakRowsQ]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  rw [matrixOf_Mop, toC_cmul, toC_cscale]
  simp only [rawSymbol_betaOf, coeff_abar]
  push_cast
  ring

/-- **The symbol norm** `‖β‖ = ∑ 2 ‖ā_k‖ ν^{|k|} ≤ βc` (UPPER through `|Re| + |Im|`). -/
theorem norm_beta_le : ‖betaOf (headF 10) abar abar_supp‖ ≤ (betaQ : ℝ) := by
  rw [norm_symbol_eq, tsum_eq_sum (s := headF 10) fun l hl => by
      simp only [rawSymbol_betaOf, abar_supp l hl, mul_zero, norm_zero, zero_mul],
    betaQ, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [rawSymbol_betaOf]
  simp only [coeff_abar, norm_mul, Complex.norm_two, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    cast_nuQ, coe_ν₆₅]
  gcongr
  exact norm_le_reim _

/-- **Reality of the candidate** `R ā = ā` (`check_reality`). -/
theorem real_abar : conjRefl abar = abar :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjRefl, coeff_abar, coeff_abar]
    by_cases h : n ∈ idx
    · have hn : -n ∈ idx := mem_idx.2 (by have := mem_idx.1 h; omega)
      have e := check_reality (-n) hn
      rw [neg_neg] at e
      rw [e, toC_cconj]
    · have hn : -n ∉ headF 10 := fun h' => h (mem_idx.2 (by have := mem_headF10.1 h'; omega))
      rw [abarQ_eq_zero hn, abarQ_eq_zero fun h' => h (mem_idx.2 (mem_headF10.1 h')), toC_zero,
        map_zero]

end Bridges

/-! ### B. The bound lemmas, the certificate, the producer discharges and the radii -/

section Bounds

theorem RzC_nonneg : (0 : ℝ) ≤ RzC := by rw [RzC]; norm_num

theorem CzC_nonneg : (0 : ℝ) ≤ CzC := by rw [CzC]; norm_num

theorem RmC_nonneg : (0 : ℝ) ≤ RmC := by rw [RmC]; norm_num

theorem CmC_nonneg : (0 : ℝ) ≤ CmC := by rw [CmC]; norm_num

theorem UpartC_sum_nonneg : (0 : ℝ) ≤ ((UpartC 0 + UpartC 1 + UpartC 2 : ℚ) : ℝ) := by
  simp only [UpartC]
  norm_num

/-- **The `Y₀` bound**: `‖G ā‖ ≤ Y₀` through the exact finite residual (`norm_sq_G_abar`), the
coefficient bridge and the three chunk checks. -/
theorem Y0_le :
    ‖G (headF 10) (duffing (1 / 10) 4) (summable_sq_tailSymbol_duffing_headF control_hN) Mop
      (forcing 1) abar‖ ≤ (Y0c : ℝ) := by
  have hval : ‖G (headF 10) (duffing (1 / 10) 4) (summable_sq_tailSymbol_duffing_headF control_hN)
      Mop (forcing 1) abar‖ ^ 2 = ((y0PartQ 0 + y0PartQ 1 + y0PartQ 2 : ℚ) : ℝ) := by
    rw [norm_sq_G_abar (headF 10) (duffing (1 / 10) 4)
        (summable_sq_tailSymbol_duffing_headF control_hN) Mop (forcing 1) hPM abar_supp,
      sum_eq_list nodup_idx41 mem_support_iff, y0PartQ, y0PartQ, y0PartQ, ← qsum_append,
      ← qsum_append, ← idx41_eq_chunks, cast_qsum]
    congr 1
    refine List.map_congr_left fun n _ => ?_
    rw [coeff_G_abar_eq, sq_norm_toC, y0Term, Rat.cast_mul, Rat.cast_pow, cast_nuQ, coe_ν₆₅]
  have hle : ((y0PartQ 0 + y0PartQ 1 + y0PartQ 2 : ℚ) : ℝ) ≤ (Y0c : ℝ) ^ 2 := by
    exact_mod_cast (add_le_add (add_le_add check_Y0_part_0 check_Y0_part_1) check_Y0_part_2).trans
      check_Y0
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by rw [Y0c]; norm_num) two_ne_zero).1
    (hval.trans_le hle)

/-- **The `Z₀` bound** through the block Schur producer on `headF 10 × headF 10`. -/
theorem Z0_le : ‖headProj (headF 10) - Mop ∘L Kh (headF 10) (duffing (1 / 10) 4)
    (betaOf (headF 10) abar abar_supp)‖ ≤ (Z0c : ℝ) := by
  refine (norm_le_sqrt_of_block _ (block_one_sub_B0 (headF 10) (duffing (1 / 10) 4) Mop hPM _)
    RzC_nonneg CzC_nonneg ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (z0RowQ i : ℝ) ≤ RzC by
      exact_mod_cast z0Row_le (mem_idx.2 (mem_headF10.1 hi)))
    rw [z0RowQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [schurEntry, matrixOf_Z0op_eq i j hi hj, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim _ i j
  · intro j hj
    refine le_trans ?_ (show (z0ColQ j : ℝ) ≤ CzC by
      exact_mod_cast z0Col_le (mem_idx.2 (mem_headF10.1 hj)))
    rw [z0ColQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [schurEntry, matrixOf_Z0op_eq i j hi hj, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim _ i j
  · refine (Real.sqrt_le_sqrt (show (RzC : ℝ) * CzC ≤ (Z0c : ℝ) ^ 2 by
      exact_mod_cast check_Z0)).trans_eq (Real.sqrt_sq (by rw [Z0c]; norm_num))

/-- **The composed leakage bound `H`** (UPPER) through `norm_head_term_le_composed` on
`headF 10 × leakCols`, the band `headF 7` and the composed-kernel chunk checks. -/
theorem H_le : ‖Mop ∘L headProj (headF 10) ∘L symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ
    (betaOf (headF 10) abar abar_supp) ∘L tailProj (headF 10)‖ ≤ √((RmC : ℝ) * CmC) := by
  refine norm_head_term_le_composed Fourier.moderate_geomFiberZ (betaOf (headF 10) abar abar_supp)
    (headF 10) (headF 7) Mop band_beta hPM RmC_nonneg CmC_nonneg ?_ ?_
  · intro i hi
    refine le_trans ?_ (show (kmRowQ i : ℝ) ≤ RmC by
      exact_mod_cast kmRow_le (mem_idx.2 (mem_headF10.1 hi)))
    rw [kmRowQ, cast_qsum, ← List.sum_toFinset _ nodup_leakColsQ, ← leakCols_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [composedLeakKernel_eq, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim _ i k
  · intro k hk
    refine le_trans ?_ (show (kmColQ k : ℝ) ≤ CmC by
      exact_mod_cast kmCol_le ((mem_leakCols_iff k).1 hk))
    rw [kmColQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [composedLeakKernel_eq, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim _ i k

/-- **The `U_row` bound** (UPPER) through `norm_comp_headReal_le_urow`. -/
theorem U_le : ‖Mop ∘L headReal (headF 10)‖ ≤ √(((UpartC 0 + UpartC 1 + UpartC 2 : ℚ) : ℝ)) := by
  refine (norm_comp_headReal_le_urow (headF 10) Mop hPM).trans (Real.sqrt_le_sqrt ?_)
  have hsum : ((urowPartQ 0 + urowPartQ 1 + urowPartQ 2 : ℚ) : ℝ) =
      ∑ i ∈ headF 10, ((urowRowQ i : ℚ) : ℝ) ^ 2 := by
    rw [urowPartQ, urowPartQ, urowPartQ, ← qsum_append, ← qsum_append, ← idx_eq_chunks,
      cast_qsum, sum_headF_eq_list]
    simp only [Rat.cast_pow]
  refine le_trans ?_ (show ((urowPartQ 0 + urowPartQ 1 + urowPartQ 2 : ℚ) : ℝ) ≤
      ((UpartC 0 + UpartC 1 + UpartC 2 : ℚ) : ℝ) by
    exact_mod_cast add_le_add (add_le_add check_Z2_part_0 check_Z2_part_1) check_Z2_part_2)
  rw [hsum]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg ν₆₅.2.le _)) (pow_nonneg ν₆₅.2.le _)) ?_ 2
  rw [urowRowQ, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [matrixOf_Mop]
  exact weighted_le_reim _ i j

/-- **The certificate** of book §10.1 at `c = (1/10, 4, 1)`, `N = 10`, `ν = 6/5`. -/
def cert : Cert (1 / 10) 4 10 ν₆₅ where
  abar := abar
  M := Mop
  Z₀ := Z0c
  H := √((RmC : ℝ) * CmC)
  U := √(((UpartC 0 + UpartC 1 + UpartC 2 : ℚ) : ℝ))
  abar_supp := abar_supp
  hPM := hPM
  hZ₀ := Z0_le
  hH := H_le
  hU := U_le

/-- **The forcing socket** `supp (c₃ b) ⊆ headF 10` (`forcing_supp`, `1 ≤ 10`). -/
theorem hg_data : ∀ k ∉ headF 10, coeff (forcing (ν := ν₆₅) 1) k = 0 := forcing_supp (by norm_num)

/-- **The tail-sum socket** `∑' ‖d‖² ≤ T2 = 484/287469` (the T2 producer at `0 ≤ 4 < 121`). -/
theorem T2_le : ∑' k, ‖tailSymbol ((headF 10 : Finset ℤ) : Set ℤ) (duffing (1 / 10) 4) k‖ ^ 2 ≤
    ((484 / 287469 : ℚ) : ℝ) :=
  (tsum_sq_tailSymbol_duffing_le (c₁ := 1 / 10) control_hN (by norm_num)).trans (by norm_num)

/-- **The `Z₁` socket** in the endpoint's squared form (`check_Z1`, `norm_beta_le`,
`|μ₁₁|² = 1369021/100`). -/
theorem Z1_ok : cert.H ^ 2 + (‖betaOf (headF 10) cert.abar cert.abar_supp‖ /
    ‖duffing (1 / 10) 4 (((10 : ℕ) : ℤ) + 1)‖) ^ 2 ≤ (Z1c : ℝ) ^ 2 := by
  have hH : cert.H ^ 2 = (RmC : ℝ) * CmC := Real.sq_sqrt (mul_nonneg RmC_nonneg CmC_nonneg)
  have hμ : ‖duffing (1 / 10) 4 (((10 : ℕ) : ℤ) + 1)‖ ^ 2 = 1369021 / 100 := by
    rw [show (((10 : ℕ) : ℤ) + 1) = 11 by norm_num, sq_norm_duffing_control]
    norm_num
  have hβ : ‖betaOf (headF 10) cert.abar cert.abar_supp‖ ^ 2 ≤ (betaQ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) norm_beta_le 2
  have hc : ((RmC * CmC + betaQ ^ 2 * (100 / 1369021) : ℚ) : ℝ) ≤ ((Z1c ^ 2 : ℚ) : ℝ) :=
    Rat.cast_le.2 check_Z1
  push_cast at hc
  rw [hH, div_pow, hμ]
  have : ‖betaOf (headF 10) cert.abar cert.abar_supp‖ ^ 2 / (1369021 / 100) ≤
      (betaQ : ℝ) ^ 2 * (100 / 1369021) := by
    rw [div_eq_mul_inv, inv_div]
    exact mul_le_mul_of_nonneg_right hβ (by norm_num)
  linarith

/-- **The `Z₂` socket** in the endpoint's squared form (`check_Z2`). -/
theorem Z2_ok : 4 * (cert.U ^ 2 + ((484 / 287469 : ℚ) : ℝ)) ≤ (Z2c : ℝ) ^ 2 := by
  have hU : cert.U ^ 2 = ((UpartC 0 + UpartC 1 + UpartC 2 : ℚ) : ℝ) :=
    Real.sq_sqrt UpartC_sum_nonneg
  rw [hU, show ((484 / 287469 : ℚ) : ℝ) = (t2Q : ℝ) from rfl]
  exact_mod_cast check_Z2

/-- **The radii inequality at `r₀ = 1/200000`**. -/
theorem radii_r0 :
    generalRadiiPolynomial (Y0c : ℝ) cert.Z₀ (Z1c : ℝ) (fun _ => (Z2c : ℝ)) (1 / 200000) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r0 check_radii_r0
  rwa [show ((r0 : ℚ) : ℝ) = 1 / 200000 by rw [r0]; norm_num] at h

/-- **The radii inequality at `r₁ = 1/25`**. -/
theorem radii_r1 :
    generalRadiiPolynomial (Y0c : ℝ) cert.Z₀ (Z1c : ℝ) (fun _ => (Z2c : ℝ)) (1 / 25) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r1 check_radii_r1
  rwa [show ((r1 : ℚ) : ℝ) = 1 / 25 by rw [r1]; norm_num] at h

end Bounds

/-! ### C. The endpoints -/

section Endpoints

/-- **THE ENDPOINT** (book §10.1 at its data, on `ℓ²_{6/5}` at our centre): the raw Fourier map
`F_n(a) = (−n² + i n/10 + 4) aₙ − (a ⋆ a)ₙ − bₙ` has a unique zero in the closed ball of radius
`1/200000` around `ā`. -/
theorem duffing_l2_existsUnique :
    ∃! a, a ∈ Metric.closedBall abar (1 / 200000) ∧
      ∀ n : ℤ, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data Y0_le Z1_ok (by rw [Z1c]; norm_num) T2_le Z2_ok
    (by rw [Z2c]; norm_num) (by norm_num) radii_r0

/-- The same at the uniqueness radius `1/25`. -/
theorem duffing_l2_existsUnique_r1 :
    ∃! a, a ∈ Metric.closedBall abar (1 / 25) ∧
      ∀ n : ℤ, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data Y0_le Z1_ok (by rw [Z1c]; norm_num) T2_le Z2_ok
    (by rw [Z2c]; norm_num) (by norm_num) radii_r1

/-- **The enclosure**: the zero in the small ball is the only zero in the ball of radius `1/25`. -/
theorem duffing_l2_enclosure :
    ∃ a ∈ Metric.closedBall abar (1 / 200000),
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0) ∧
        ∀ z ∈ Metric.closedBall abar (1 / 25),
          (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = a := by
  obtain ⟨a, ⟨ha, hFa⟩, -⟩ := duffing_l2_existsUnique
  obtain ⟨b, -, hub⟩ := duffing_l2_existsUnique_r1
  have hab : a = b := hub a ⟨Metric.closedBall_subset_closedBall (by norm_num) ha, hFa⟩
  exact ⟨a, ha, hFa, fun z hz hFz => (hub z ⟨hz, hFz⟩).trans hab.symm⟩

/-- **The real endpoint**: the zero is real, `conj ã₋ₙ = ãₙ` (reality consumed from CF-5a.2). -/
theorem duffing_l2_real :
    ∃ a ∈ Metric.closedBall abar (1 / 200000),
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0) ∧ conjRefl a = a ∧
        ∀ z ∈ Metric.closedBall abar (1 / 200000),
          (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = a :=
  duffing_existsUnique_real control_hN cert hg_data Y0_le Z1_ok (by rw [Z1c]; norm_num) T2_le
    Z2_ok (by rw [Z2c]; norm_num) (by norm_num) radii_r0 real_abar


end Endpoints

end FourierDuffing.Certificate

end

