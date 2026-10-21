import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.GetD
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.Rational.Frac

/-!
# Rational grid helpers

Small facts about the `Array` encodings of rational certificate data (columns, coefficient
lists) that exact-arithmetic certificates read back into `Fin`-indexed matrices
(`getD_ofFn_fin` is in `Rational/Matrix`), and the kernel-facing checkers of the defect block
norm `‖I − A B‖` on stored columns.

- `defectColF` / `roundCols`: exact gcd-free defect columns (`QF`), rounded upward onto the
  grid `1/S` (`abs_defectCols_le_roundCols`)
- `defectColB` / `blockBoundB`: grid accumulators on `1/S` in `Nat` arithmetic, with the
  column bound `colNormQ_defect_le_colValB`
- `DefectExact` / `DefectRound` / `DefectGrid` / `DefectBy`: the `Z₀` clauses on raw columns,
  each sound for the exact clause (`defectBy_sound`)
-/

namespace RadiiPolynomial.Certification.Rational

/-! ## Exact gcd-free defect columns, rounded onto the grid `1/S` -/

/-- `acc − b • col` entrywise; missing `col` entries read as `0`; zero entries skipped. -/
def axpy (b : ℚ) : List QF → List ℚ → List QF
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, c :: cs => (if c.num = 0 then a else QF.subMul a b c) :: axpy b as cs

/-- Walk a stored column `bs` of the right factor (row index `k`, fuel `n`), subtracting
`bs[k] • A_k`; zero coefficients skip the whole AXPY (sparsity of the right factor). -/
def colWalk (Acol : ℕ → Array ℚ) : ℕ → ℕ → List ℚ → List QF → List QF
  | 0, _, _, acc => acc
  | _ + 1, _, [], acc => acc
  | n + 1, k, b :: bs, acc =>
    colWalk Acol n (k + 1) bs (if b.num = 0 then acc else axpy b acc (Acol k).toList)

/-- Column `c` of the identity block (`δ = true`) or of the zero block, length `N + 1`. -/
def initCol (N : ℕ) (δ : Bool) (c : ℕ) : List QF :=
  (List.range (N + 1)).map fun i => if δ && i == c then QF.one else QF.zero

/-- Exact gcd-free column `c` of the defect block `δ_{lj} I − Σ_m A_{lm} DF_{mj}`. -/
def defectColF {L : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ) (l j : Fin L)
    (c : ℕ) : List QF :=
  (List.finRange L).foldl (fun acc m => colWalk (A_col l m) (N + 1) 0 (DF_col m j c).toList acc)
    (initCol N (decide (l = j)) c)

/-- Upward-rounded `|defect|` columns on the grid `1/S` (small denominators). -/
def roundCols {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ) :
    Fin L → Fin L → Fin (N + 1) → Array ℚ :=
  fun l j c => ((defectColF A_col DF_col N l j (c : ℕ)).map fun x =>
    ((QF.ceilAbs S x : ℕ) : ℚ) / (S : ℚ)).toArray

/-! ### Semantics of the column computation -/

theorem toList_getD (a : Array ℚ) (i : ℕ) : a.toList.getD i 0 = a.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem axpy_length (b : ℚ) : ∀ (as : List QF) (cs : List ℚ), (axpy b as cs).length = as.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: cs => by simp [axpy, axpy_length b as cs]

theorem axpy_getD (b : ℚ) : ∀ (as : List QF) (cs : List ℚ) (i : ℕ), i < as.length →
    ((axpy b as cs).getD i QF.zero).toRat = (as.getD i QF.zero).toRat - b * cs.getD i 0
  | [], _, _, h => absurd h (by simp)
  | a :: as, [], i, _ => by simp [axpy]
  | a :: as, c :: cs, 0, _ => by
    simp only [axpy, List.getD_cons_zero]
    split_ifs with hc
    · rw [Rat.num_eq_zero.mp hc]; ring
    · exact QF.toRat_subMul a b c
  | a :: as, c :: cs, i + 1, h => by
    simp only [axpy, List.getD_cons_succ]
    exact axpy_getD b as cs i (by simpa using h)

theorem colWalk_length (Acol : ℕ → Array ℚ) : ∀ (n k : ℕ) (bs : List ℚ) (acc : List QF),
    (colWalk Acol n k bs acc).length = acc.length
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | n + 1, k, b :: bs, acc => by
    rw [colWalk, colWalk_length Acol n (k + 1) bs]
    split_ifs
    · rfl
    · exact axpy_length _ _ _

theorem colWalk_getD (Acol : ℕ → Array ℚ) : ∀ (n k : ℕ) (bs : List ℚ) (acc : List QF) (i : ℕ),
    i < acc.length →
    ((colWalk Acol n k bs acc).getD i QF.zero).toRat =
      (acc.getD i QF.zero).toRat - ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + t)).getD i 0
  | 0, _, _, _, _, _ => by simp [colWalk]
  | _ + 1, _, [], _, _, _ => by simp [colWalk]
  | n + 1, k, b :: bs, acc, i, h => by
    have hlen : i < (if b.num = 0 then acc else axpy b acc (Acol k).toList).length := by
      split_ifs
      · exact h
      · rwa [axpy_length]
    rw [colWalk, colWalk_getD Acol n (k + 1) bs _ i hlen, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have hshift : ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + 1 + t)).getD i 0 =
        ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + (t + 1))).getD i 0 :=
      Finset.sum_congr rfl fun t _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    rw [hshift]
    split_ifs with hb
    · rw [Rat.num_eq_zero.mp hb]; ring
    · rw [axpy_getD _ _ _ _ h, toList_getD]; ring

/-- A left fold whose step preserves the accumulator's length preserves it. Used by both the
exact (`List QF`) and the grid (`List PM`) column accumulators. -/
theorem foldl_length {β ι : Type*} (f : List β → ι → List β)
    (hlen : ∀ acc m, (f acc m).length = acc.length) :
    ∀ (ms : List ι) (acc : List β), (ms.foldl f acc).length = acc.length
  | [], _ => rfl
  | m :: ms, acc => by rw [List.foldl_cons, foldl_length f hlen ms, hlen]

theorem foldl_getD {ι : Type*} (f : List QF → ι → List QF) (g : ι → ℕ → ℚ)
    (hlen : ∀ acc m, (f acc m).length = acc.length)
    (hf : ∀ acc m i, i < acc.length →
      ((f acc m).getD i QF.zero).toRat = (acc.getD i QF.zero).toRat - g m i) :
    ∀ (ms : List ι) (acc : List QF) (i : ℕ), i < acc.length →
      ((ms.foldl f acc).getD i QF.zero).toRat =
        (acc.getD i QF.zero).toRat - (ms.map fun m => g m i).sum
  | [], _, _, _ => by simp
  | m :: ms, acc, i, h => by
    rw [List.foldl_cons, foldl_getD f g hlen hf ms _ i (by rwa [hlen]), hf acc m i h,
      List.map_cons, List.sum_cons]
    ring

theorem initCol_length (N : ℕ) (δ : Bool) (c : ℕ) : (initCol N δ c).length = N + 1 := by
  simp [initCol]

theorem initCol_getD (N : ℕ) (δ : Bool) (c i : ℕ) (hi : i < N + 1) :
    ((initCol N δ c).getD i QF.zero).toRat = if δ = true ∧ i = c then 1 else 0 := by
  rw [initCol, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  by_cases h : δ = true ∧ i = c
  · obtain ⟨h1, h2⟩ := h; subst h1 h2; simp
  · rw [ite_eq_right h, ite_eq_right (by simpa [Bool.and_eq_true, beq_iff_eq] using h)]
    simp

theorem defectColF_length {L : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ)
    (l j : Fin L) (c : ℕ) : (defectColF A_col DF_col N l j c).length = N + 1 := by
  rw [defectColF, foldl_length _ (fun acc m => colWalk_length _ _ _ _ acc), initCol_length]

theorem defectColF_getD {L : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ)
    (l j : Fin L) (c i : ℕ) (hi : i < N + 1) :
    ((defectColF A_col DF_col N l j c).getD i QF.zero).toRat =
      (if l = j ∧ i = c then 1 else 0) -
        ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
          (DF_col m j c).getD t 0 * (A_col l m t).getD i 0 := by
  rw [defectColF, foldl_getD _ (fun m i => ∑ t ∈ Finset.range (N + 1),
      (DF_col m j c).getD t 0 * (A_col l m t).getD i 0)
    (fun acc m => colWalk_length _ _ _ _ acc)
    (fun acc m i h => by
      rw [colWalk_getD _ _ _ _ _ i h]
      simp only [zero_add, toList_getD])
    _ _ i (by rw [initCol_length]; exact hi), initCol_getD N _ c i hi, ← Fin.sum_univ_def]
  simp only [decide_eq_true_eq]

/-- Closed form of one entry of the library's block defect. -/
theorem blockDefect_eq_formula {L N : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (l j : Fin L) (i c : Fin (N + 1)) :
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j i c =
      (if l = j ∧ (i : ℕ) = c then 1 else 0) -
        ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
          (DF_col m j c).getD t 0 * (A_col l m t).getD i 0 := by
  simp only [blockDefectMatQ, Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply, matOfCols]
  congr 1
  · by_cases hlj : l = j
    · subst hlj; simp [Matrix.one_apply, Fin.val_inj]
    · simp [hlj]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun t => (DF_col m j c).getD t 0 * (A_col l m t).getD i 0)]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _

/-- The fast column is the exact `blockDefectMatQ` column. -/
theorem defectColF_eq_blockDefect {L N : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (l j : Fin L) (i c : Fin (N + 1)) :
    ((defectColF A_col DF_col N l j c).getD i QF.zero).toRat =
      blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ))
        l j i c := by
  rw [defectColF_getD _ _ _ _ _ _ _ i.isLt, blockDefect_eq_formula]

/-- Entry `i ≤ N` of the exact defect column, in closed form. -/
theorem defectCols_getD {L N : ℕ} (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L)
    (c : Fin (N + 1)) (i : ℕ) (hi : i ≤ N) :
    (defectCols A_col DF_col l j c).getD i 0 =
      (if l = j ∧ i = c then 1 else 0) -
        ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
          (DF_col m j c).getD t 0 * (A_col l m t).getD i 0 := by
  rw [show i = ((⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N + 1)) : ℕ) from rfl, defectCols,
    getD_ofFn_fin, blockDefect_eq_formula]

theorem roundCols_getD {L N : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (l j : Fin L) (c : Fin (N + 1)) (i : ℕ) (hi : i < N + 1) :
    (roundCols S A_col DF_col N l j c).getD i 0 =
      ((QF.ceilAbs S ((defectColF A_col DF_col N l j c).getD i QF.zero) : ℕ) : ℚ) /
        (S : ℚ) := by
  have hlen : i < (defectColF A_col DF_col N l j c).length := by
    rw [defectColF_length]; exact hi
  rw [roundCols, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hlen, List.getD_eq_getElem _ _ hlen]
  rfl

/-! ### Monotonicity of the library norm in the column entries -/

theorem colNormQ_mono {col col' : Array ℚ} {ν : ℚ} (hν : 0 ≤ ν) (N j : ℕ)
    (h : ∀ i ≤ N, |col.getD i 0| ≤ |col'.getD i 0|) :
    colNormQ col ν N j ≤ colNormQ col' ν N j :=
  Finset.sum_le_sum fun i hi =>
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (h i (Finset.mem_Icc.mp hi).2) (pow_nonneg hν i))
      (pow_nonneg hν j)

theorem finWeightedMatrixNormQ_mono {N : ℕ} {cols cols' : Fin (N + 1) → Array ℚ} {ν : ℚ}
    (hν : 0 ≤ ν) (h : ∀ c, ∀ i ≤ N, |(cols c).getD i 0| ≤ |(cols' c).getD i 0|) :
    finWeightedMatrixNormQ cols ν ≤ finWeightedMatrixNormQ cols' ν :=
  Finset.sup'_le _ _ fun c _ =>
    Finset.le_sup'_of_le _ (Finset.mem_univ c) (colNormQ_mono hν N c (h c))

theorem finiteBlockMatrixNormQ_mono {L N : ℕ} [NeZero L]
    {cols cols' : Fin L → Fin L → Fin (N + 1) → Array ℚ} {ν : ℚ} (hν : 0 ≤ ν)
    (h : ∀ l j c, ∀ i ≤ N, |(cols l j c).getD i 0| ≤ |(cols' l j c).getD i 0|) :
    finiteBlockMatrixNormQ L N cols ν ≤ finiteBlockMatrixNormQ L N cols' ν :=
  Finset.sup'_le _ _ fun l _ =>
    Finset.le_sup'_of_le _ (Finset.mem_univ l)
      (Finset.sum_le_sum fun j _ => finWeightedMatrixNormQ_mono hν (h l j))

/-- Entrywise: the rounded column dominates the exact defect column. -/
theorem abs_defectCols_le_roundCols {L N : ℕ} (S : ℕ) (hS : 0 < S)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (c : Fin (N + 1)) (i : ℕ)
    (hi : i ≤ N) :
    |(defectCols A_col DF_col l j c).getD i 0| ≤ |(roundCols S A_col DF_col N l j c).getD i 0| := by
  have hi' : i < N + 1 := Nat.lt_succ_of_le hi
  have h1 : (defectCols A_col DF_col l j c).getD i 0 =
      ((defectColF A_col DF_col N l j c).getD i QF.zero).toRat := by
    rw [show i = ((⟨i, hi'⟩ : Fin (N + 1)) : ℕ) from rfl, defectCols, getD_ofFn_fin,
      defectColF_eq_blockDefect]
  rw [h1, roundCols_getD S A_col DF_col l j c i hi']
  exact (QF.abs_toRat_le _ hS _).trans (le_abs_self _)

/-! ## Grid accumulators on `1/S`, `Nat`-only kernel arithmetic

Each defect entry is carried as a difference `P − M` of naturals on the grid `1/S`; the
product `b·c` of a right-factor entry and a left-factor entry enters as `⌊|b c| S⌋`, added to
`P` or `M` by sign. Each floor costs at most one grid unit, so after the `L(N+1)` possible
terms `|x S − (P − M)| ≤ L(N+1)`, and `(|P − M| + L(N+1)) / S` bounds `|x|`. The weighted
column sums are one `Nat` dot product with the integer weights `νn^i νd^(N−i)`
(`ν = νn/νd`). -/

/-- Sign bit of an integer (one constructor test). -/
def isNeg : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- Difference pair `P − M` of naturals (value on the grid `1/S`). -/
structure PM where
  P : ℕ
  M : ℕ

namespace PM
def val (a : PM) : ℚ := (a.P : ℚ) - a.M
def zero : PM := ⟨0, 0⟩
end PM

/-- `acc − b·c` on the grid: `t = ⌊|b c| S⌋`, added to `P` or `M` by sign; `bS = |b.num|·S`,
`bd = b.den`, `bneg` = sign of `b`. Zero `c` skipped. -/
def pmSub (bS bd : ℕ) (bneg : Bool) (a : PM) (c : ℚ) : PM :=
  if Nat.beq c.num.natAbs 0 then a else
  if bneg != isNeg c.num then
    ⟨Nat.add a.P (Nat.div (Nat.mul bS c.num.natAbs) (Nat.mul bd c.den)), a.M⟩
  else ⟨a.P, Nat.add a.M (Nat.div (Nat.mul bS c.num.natAbs) (Nat.mul bd c.den))⟩

/-- Grid AXPY `acc − b • col` (missing `col` entries read as `0`); recursor-direct,
kernel-only, hence `noncomputable`. -/
noncomputable def axpyB (bS bd : ℕ) (bneg : Bool) (as : List PM) : List ℚ → List PM :=
  List.rec (motive := fun _ => List ℚ → List PM) (fun _ => [])
    (fun a as ih cs => List.casesOn (motive := fun _ => List PM) cs (a :: as)
      (fun c cs' => pmSub bS bd bneg a c :: ih cs')) as

/-- Walk a stored right-factor column (row `k`, fuel `n`); zero coefficients skip the AXPY. -/
noncomputable def colWalkB (S : ℕ) (Acol : ℕ → Array ℚ) (n : ℕ) :
    ℕ → List ℚ → List PM → List PM :=
  Nat.rec (motive := fun _ => ℕ → List ℚ → List PM → List PM) (fun _ _ acc => acc)
    (fun _ ih k bs acc => List.casesOn (motive := fun _ => List PM) bs acc
      (fun b bs' => ih (k + 1) bs'
        (if Nat.beq b.num.natAbs 0 then acc
         else axpyB (Nat.mul b.num.natAbs S) b.den (isNeg b.num) acc (Acol k).toList))) n

theorem axpyB_cons_nil (bS bd : ℕ) (bneg : Bool) (a : PM) (as : List PM) :
    axpyB bS bd bneg (a :: as) [] = a :: as := rfl

theorem axpyB_cons_cons (bS bd : ℕ) (bneg : Bool) (a : PM) (as : List PM) (c : ℚ)
    (cs : List ℚ) :
    axpyB bS bd bneg (a :: as) (c :: cs) = pmSub bS bd bneg a c :: axpyB bS bd bneg as cs := rfl

theorem colWalkB_zero (S : ℕ) (Acol : ℕ → Array ℚ) (k : ℕ) (bs : List ℚ) (acc : List PM) :
    colWalkB S Acol 0 k bs acc = acc := rfl

theorem colWalkB_succ_nil (S : ℕ) (Acol : ℕ → Array ℚ) (n k : ℕ) (acc : List PM) :
    colWalkB S Acol (n + 1) k [] acc = acc := rfl

theorem colWalkB_succ_cons (S : ℕ) (Acol : ℕ → Array ℚ) (n k : ℕ) (b : ℚ) (bs : List ℚ)
    (acc : List PM) :
    colWalkB S Acol (n + 1) k (b :: bs) acc =
      colWalkB S Acol n (k + 1) bs
        (if Nat.beq b.num.natAbs 0 then acc
         else axpyB (Nat.mul b.num.natAbs S) b.den (isNeg b.num) acc (Acol k).toList) := rfl

/-- Identity (`δ = true`) or zero column on the grid. -/
def initColB (S N : ℕ) (δ : Bool) (c : ℕ) : List PM :=
  (List.range (N + 1)).map fun i => if δ && i == c then ⟨S, 0⟩ else ⟨0, 0⟩

/-- Grid column `c` of the defect block `(l, j)`. -/
noncomputable def defectColB {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ)
    (l j : Fin L) (c : ℕ) : List PM :=
  (List.finRange L).foldl
    (fun acc m => colWalkB S (A_col l m) (N + 1) 0 (DF_col m j c).toList acc)
    (initColB S N (decide (l = j)) c)

/-- Grid-rounded `|defect|` numerators `|P − M| + Lc`. -/
def roundNatsB (Lc : ℕ) (col : List PM) : List ℕ :=
  col.map fun a => Nat.add (Nat.add (Nat.sub a.P a.M) (Nat.sub a.M a.P)) Lc

/-- Integer weights `νn^i · νd^(N−i)` (so `ν^i = w_i / νd^N`). -/
def weightsB (N νn νd : ℕ) : List ℕ :=
  (List.range (N + 1)).map fun i => Nat.mul (Nat.pow νn i) (Nat.pow νd (N - i))

/-- Dot product of natural lists. -/
def dotN : List ℕ → List ℕ → ℕ
  | u :: us, w :: ws => Nat.add (Nat.mul u w) (dotN us ws)
  | _, _ => 0

/-- Upper bound of the weighted norm of defect column `c` of block `(l, j)` at grid `1/S`, when
`νn = |ν.num|`, `νd = ν.den` for a weight `0 < ν` and `0 < S` (`colNormQ_defect_le_colValB`). -/
noncomputable def colValB {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (N νn νd : ℕ) (l j : Fin L) (c : ℕ) : ℚ :=
  ((Nat.mul (dotN (roundNatsB (L * (N + 1)) (defectColB S A_col DF_col N l j c))
      (weightsB N νn νd)) (Nat.pow νd c) : ℕ) : ℚ) /
    ((Nat.mul (Nat.mul S (Nat.pow νd N)) (Nat.pow νn c) : ℕ) : ℚ)

/-- Upper bound of the weighted matrix norm of block `(l, j)` (max over columns), under the
same conditions (`finWeightedMatrixNormQ_defect_le_blockBoundB`). -/
noncomputable def blockBoundB {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (N νn νd : ℕ) (l j : Fin L) : ℚ :=
  ((List.range (N + 1)).map (colValB S A_col DF_col N νn νd l j)).foldl max 0

/-! ### Semantics of the grid accumulators -/

theorem isNeg_eq_true_iff (z : ℤ) : isNeg z = true ↔ z < 0 := by
  cases z with
  | ofNat n => simp [isNeg]
  | negSucc n => simp [isNeg, Int.negSucc_lt_zero]

theorem isNeg_eq_false_iff (z : ℤ) : isNeg z = false ↔ 0 ≤ z := by
  rw [← not_lt, ← isNeg_eq_true_iff]; simp

theorem natAbs_cast (z : ℤ) : ((z.natAbs : ℕ) : ℚ) = |(z : ℚ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem ndiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl


/-- `⌊x / y⌋` brackets `x / y`. -/
theorem floor_bounds (x y : ℕ) (hy : 0 < y) :
    ((x / y : ℕ) : ℚ) ≤ (x : ℚ) / y ∧ (x : ℚ) / y < ((x / y : ℕ) : ℚ) + 1 := by
  have hy' : (0 : ℚ) < y := by exact_mod_cast hy
  have h1 : (x / y) * y ≤ x := Nat.div_mul_le_self x y
  have h2 : x < (x / y + 1) * y := by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hy
  constructor
  · rw [le_div_iff₀ hy']; exact_mod_cast h1
  · rw [div_lt_iff₀ hy']; exact_mod_cast h2

/-- `|b c| S` as the quotient that `pmSub` floors. -/
theorem abs_mul_S_eq (b c : ℚ) (S : ℕ) :
    |b * c| * S = ((b.num.natAbs * S * c.num.natAbs : ℕ) : ℚ) / ((b.den * c.den : ℕ) : ℚ) := by
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have hc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  conv_lhs => rw [← Rat.num_div_den b, ← Rat.num_div_den c]
  rw [abs_mul, abs_div, abs_div, Nat.abs_cast, Nat.abs_cast]
  push_cast
  rw [natAbs_cast, natAbs_cast]
  field_simp

theorem mul_eq_neg_abs_of_bne (b c : ℚ) (h : (isNeg b.num != isNeg c.num) = true) :
    b * c = -|b * c| := by
  have hb := isNeg_eq_true_iff b.num; have hb' := isNeg_eq_false_iff b.num
  have hc := isNeg_eq_true_iff c.num; have hc' := isNeg_eq_false_iff c.num
  rw [Rat.num_neg] at hb hc; rw [Rat.num_nonneg] at hb' hc'
  rw [abs_of_nonpos, neg_neg]
  cases hB : isNeg b.num <;> cases hC : isNeg c.num <;> rw [hB, hC] at h
  · exact absurd h (by decide)
  · exact mul_nonpos_of_nonneg_of_nonpos (hb'.mp hB) (hc.mp hC).le
  · exact mul_nonpos_of_nonpos_of_nonneg (hb.mp hB).le (hc'.mp hC)
  · exact absurd h (by decide)

theorem mul_eq_abs_of_not_bne (b c : ℚ) (h : ¬ (isNeg b.num != isNeg c.num) = true) :
    b * c = |b * c| := by
  have hb := isNeg_eq_true_iff b.num; have hb' := isNeg_eq_false_iff b.num
  have hc := isNeg_eq_true_iff c.num; have hc' := isNeg_eq_false_iff c.num
  rw [Rat.num_neg] at hb hc; rw [Rat.num_nonneg] at hb' hc'
  rw [abs_of_nonneg]
  cases hB : isNeg b.num <;> cases hC : isNeg c.num <;> rw [hB, hC] at h
  · exact mul_nonneg (hb'.mp hB) (hc'.mp hC)
  · exact absurd rfl h
  · exact absurd rfl h
  · exact mul_nonneg_of_nonpos_of_nonpos (hb.mp hB).le (hc.mp hC).le

/-- One grid step: the invariant `|x S − (P − M)| ≤ K` loses at most one grid unit. -/
theorem pmSub_spec (S : ℕ) (b c : ℚ) (a : PM) (x K : ℚ) (h : |x * S - a.val| ≤ K) :
    |(x - b * c) * S - (pmSub (Nat.mul b.num.natAbs S) b.den (isNeg b.num) a c).val| ≤ K + 1 := by
  have hpos : 0 < Nat.mul b.den c.den := Nat.mul_pos b.den_pos c.den_pos
  obtain ⟨ht1, ht2⟩ := floor_bounds (Nat.mul (Nat.mul b.num.natAbs S) c.num.natAbs)
    (Nat.mul b.den c.den) hpos
  have hu := abs_mul_S_eq b c S
  simp only [Nat.mul_eq] at ht1 ht2 hpos
  rw [← hu] at ht1 ht2
  obtain ⟨hl, hr⟩ := abs_le.mp h
  unfold pmSub
  split_ifs with h0 hs
  · have hc0 : c = 0 := Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_of_beq_eq_true h0))
    subst hc0
    simp only [mul_zero, sub_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hneg := mul_eq_neg_abs_of_bne b c hs
    simp only [PM.val, Nat.add_eq, Nat.mul_eq, ndiv_eq, Nat.cast_add] at hl hr ⊢
    rw [sub_mul, hneg]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hpos' := mul_eq_abs_of_not_bne b c hs
    simp only [PM.val, Nat.add_eq, Nat.mul_eq, ndiv_eq, Nat.cast_add] at hl hr ⊢
    rw [sub_mul, hpos']
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem axpyB_length (bS bd : ℕ) (bneg : Bool) :
    ∀ (as : List PM) (cs : List ℚ), (axpyB bS bd bneg as cs).length = as.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: cs => by simp [axpyB_cons_cons, axpyB_length bS bd bneg as cs]

theorem axpyB_spec (S : ℕ) (b : ℚ) : ∀ (as : List PM) (cs : List ℚ) (i : ℕ) (x K : ℚ),
    i < as.length → |x * S - (as.getD i PM.zero).val| ≤ K →
    |(x - b * cs.getD i 0) * S -
      ((axpyB (Nat.mul b.num.natAbs S) b.den (isNeg b.num) as cs).getD i PM.zero).val| ≤ K + 1
  | [], _, _, _, _, hi, _ => absurd hi (by simp)
  | a :: as, [], i, x, K, _, h => by
    simp only [axpyB_cons_nil, List.getD_nil, mul_zero, sub_zero]
    linarith
  | a :: as, c :: cs, 0, x, K, _, h => by
    simp only [axpyB_cons_cons, List.getD_cons_zero] at h ⊢
    exact pmSub_spec S b c a x K h
  | a :: as, c :: cs, i + 1, x, K, hi, h => by
    simp only [axpyB_cons_cons, List.getD_cons_succ] at h ⊢
    exact axpyB_spec S b as cs i x K (by simpa using hi) h

theorem colWalkB_length (S : ℕ) (Acol : ℕ → Array ℚ) :
    ∀ (n k : ℕ) (bs : List ℚ) (acc : List PM), (colWalkB S Acol n k bs acc).length = acc.length
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | n + 1, k, b :: bs, acc => by
    rw [colWalkB_succ_cons, colWalkB_length S Acol n (k + 1) bs]
    split_ifs
    · rfl
    · exact axpyB_length _ _ _ _ _

theorem colWalkB_spec (S : ℕ) (Acol : ℕ → Array ℚ) :
    ∀ (n k : ℕ) (bs : List ℚ) (acc : List PM) (i : ℕ) (x K : ℚ),
    i < acc.length → |x * S - (acc.getD i PM.zero).val| ≤ K →
    |(x - ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + t)).getD i 0) * S -
      ((colWalkB S Acol n k bs acc).getD i PM.zero).val| ≤ K + n
  | 0, _, _, _, _, _, _, _, h => by simpa [colWalkB_zero] using h
  | n + 1, _, [], _, _, _, _, _, h => by
    simp only [colWalkB_succ_nil, List.getD_nil, zero_mul, Finset.sum_const_zero, sub_zero]
    push_cast
    linarith [abs_nonneg (0 : ℚ), (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
  | n + 1, k, b :: bs, acc, i, x, K, hi, h => by
    have h1 : |(x - b * (Acol k).getD i 0) * S -
        ((if Nat.beq b.num.natAbs 0 then acc
          else axpyB (Nat.mul b.num.natAbs S) b.den (isNeg b.num) acc (Acol k).toList).getD i
            PM.zero).val| ≤ K + 1 := by
      split_ifs with hb
      · have hb0 : b = 0 :=
          Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_of_beq_eq_true hb))
        simp only [hb0, zero_mul, sub_zero]; linarith
      · have := axpyB_spec S b acc (Acol k).toList i x K hi h
        rwa [toList_getD] at this
    have hlen : i < (if Nat.beq b.num.natAbs 0 then acc
        else axpyB (Nat.mul b.num.natAbs S) b.den (isNeg b.num) acc (Acol k).toList).length := by
      split_ifs
      · exact hi
      · rwa [axpyB_length]
    have h2 := colWalkB_spec S Acol n (k + 1) bs _ i _ _ hlen h1
    rw [colWalkB_succ_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have hshift : ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + 1 + t)).getD i 0 =
        ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + (t + 1))).getD i 0 :=
      Finset.sum_congr rfl fun t _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    rw [hshift] at h2
    have e : x - (∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + (t + 1))).getD i 0 +
        b * (Acol k).getD i 0) =
        x - b * (Acol k).getD i 0 - ∑ t ∈ Finset.range n, bs.getD t 0 * (Acol (k + (t + 1))).getD i 0 := by
      ring
    rw [e]
    push_cast
    linarith

theorem foldlB_spec {ι : Type*} (S : ℕ) (f : List PM → ι → List PM) (g : ι → ℕ → ℚ) (n0 : ℚ)
    (hlen : ∀ acc m, (f acc m).length = acc.length)
    (hf : ∀ acc m i (x K : ℚ), i < acc.length → |x * S - (acc.getD i PM.zero).val| ≤ K →
      |(x - g m i) * S - ((f acc m).getD i PM.zero).val| ≤ K + n0) :
    ∀ (ms : List ι) (acc : List PM) (i : ℕ) (x K : ℚ), i < acc.length →
      |x * S - (acc.getD i PM.zero).val| ≤ K →
      |(x - (ms.map fun m => g m i).sum) * S - ((ms.foldl f acc).getD i PM.zero).val| ≤
        K + ms.length * n0
  | [], _, _, _, _, _, h => by simpa using h
  | m :: ms, acc, i, x, K, hi, h => by
    have := foldlB_spec S f g n0 hlen hf ms (f acc m) i (x - g m i) (K + n0)
      (by rwa [hlen]) (hf acc m i x K hi h)
    rw [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons,
      show x - (g m i + (ms.map fun m => g m i).sum) = x - g m i - (ms.map fun m => g m i).sum by ring]
    push_cast
    linarith

theorem initColB_length (S N : ℕ) (δ : Bool) (c : ℕ) : (initColB S N δ c).length = N + 1 := by
  simp [initColB]

theorem initColB_spec (S N : ℕ) (δ : Bool) (c i : ℕ) (hi : i < N + 1) :
    |(if δ = true ∧ i = c then (1 : ℚ) else 0) * S - ((initColB S N δ c).getD i PM.zero).val| ≤ 0 := by
  rw [initColB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  by_cases h : δ = true ∧ i = c
  · obtain ⟨h1, h2⟩ := h; subst h1 h2; simp [PM.val]
  · rw [ite_eq_right h, ite_eq_right (by simpa [Bool.and_eq_true, beq_iff_eq] using h)]
    simp [PM.val]

theorem defectColB_length {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ)
    (l j : Fin L) (c : ℕ) : (defectColB S A_col DF_col N l j c).length = N + 1 := by
  rw [defectColB, foldl_length _ (fun acc m => colWalkB_length _ _ _ _ _ acc), initColB_length]

/-- The grid column tracks the exact defect entry within `L(N+1)` grid units. -/
theorem defectColB_spec {L : ℕ} (S : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ)
    (l j : Fin L) (c i : ℕ) (hi : i < N + 1) :
    |((if l = j ∧ i = c then 1 else 0) -
        ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
          (DF_col m j c).getD t 0 * (A_col l m t).getD i 0) * S -
      ((defectColB S A_col DF_col N l j c).getD i PM.zero).val| ≤ ((L * (N + 1) : ℕ) : ℚ) := by
  have := foldlB_spec S _ (fun m i => ∑ t ∈ Finset.range (N + 1),
      (DF_col m j c).getD t 0 * (A_col l m t).getD i 0) ((N + 1 : ℕ) : ℚ)
    (fun acc m => colWalkB_length _ _ _ _ _ acc)
    (fun acc m i x K h hx => by
      have := colWalkB_spec S (A_col l m) (N + 1) 0 (DF_col m j c).toList acc i x K h hx
      simpa only [zero_add, toList_getD] using this)
    (List.finRange L) (initColB S N (decide (l = j)) c) i
    (if l = j ∧ i = c then 1 else 0) 0 (by rw [initColB_length]; exact hi)
    (by simpa only [decide_eq_true_eq] using initColB_spec S N (decide (l = j)) c i hi)
  rw [← Fin.sum_univ_def, List.length_finRange, zero_add] at this
  rw [defectColB]
  push_cast at this ⊢
  exact this

theorem natDist_cast (P M : ℕ) :
    ((Nat.add (Nat.sub P M) (Nat.sub M P) : ℕ) : ℚ) = |(P : ℚ) - M| := by
  simp only [Nat.add_eq, Nat.sub_eq]
  rcases le_total P M with h | h
  · have hq : (P : ℚ) ≤ M := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, abs_of_nonpos (sub_nonpos.mpr hq), Nat.cast_sub h]
    ring
  · have hq : (M : ℚ) ≤ P := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, abs_of_nonneg (sub_nonneg.mpr hq), Nat.cast_sub h]

theorem getD_map_of_lt {α β : Type*} (f : α → β) (l : List α) (d : α) (e : β) (i : ℕ)
    (h : i < l.length) : (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-- Rounded entry: `|x| ≤ (|P − M| + L(N+1)) / S`. -/
theorem abs_defect_le_roundNatsB {L : ℕ} (S : ℕ) (hS : 0 < S)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (N : ℕ) (l j : Fin L) (c i : ℕ)
    (hi : i < N + 1) :
    |(if l = j ∧ i = c then 1 else 0) -
        ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
          (DF_col m j c).getD t 0 * (A_col l m t).getD i 0| ≤
      (((roundNatsB (L * (N + 1)) (defectColB S A_col DF_col N l j c)).getD i 0 : ℕ) : ℚ) / S := by
  have hS' : (0 : ℚ) < S := by exact_mod_cast hS
  have hspec := defectColB_spec S A_col DF_col N l j c i hi
  rw [roundNatsB, getD_map_of_lt _ _ PM.zero _ _ (by rw [defectColB_length]; exact hi)]
  rw [le_div_iff₀ hS', Nat.add_eq, Nat.cast_add, natDist_cast]
  set X := (if l = j ∧ i = c then (1 : ℚ) else 0) - ∑ m : Fin L, ∑ t ∈ Finset.range (N + 1),
      (DF_col m j c).getD t 0 * (A_col l m t).getD i 0
  set a := (defectColB S A_col DF_col N l j c).getD i PM.zero
  have e : |X| * S = |X * S| := by rw [abs_mul, abs_of_pos hS']
  have htri := abs_sub_abs_le_abs_sub (X * S) a.val
  rw [e]
  simp only [PM.val] at htri hspec ⊢
  linarith

theorem dotN_eq_sum : ∀ (us ws : List ℕ) (n : ℕ), us.length = n → ws.length = n →
    dotN us ws = ∑ i ∈ Finset.range n, us.getD i 0 * ws.getD i 0
  | [], ws, n, h, _ => by
    subst h; rw [List.length_nil, Finset.sum_range_zero]; cases ws <;> rfl
  | _ :: _, [], n, h1, h2 => by subst h2; exact absurd h1 (Nat.succ_ne_zero _)
  | u :: us, w :: ws, n, h1, h2 => by
    subst h1
    simp only [List.length_cons, add_left_inj] at h2
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← dotN_eq_sum us ws us.length rfl h2, dotN, Nat.add_eq, Nat.mul_eq, add_comm]

theorem weightsB_length (N νn νd : ℕ) : (weightsB N νn νd).length = N + 1 := by
  simp [weightsB]

theorem weightsB_getD (N νn νd i : ℕ) (hi : i < N + 1) :
    (weightsB N νn νd).getD i 0 = νn ^ i * νd ^ (N - i) := by
  rw [weightsB, getD_map_of_lt _ _ 0 _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_range]
  simp [Nat.mul_eq, Nat.pow_eq]

/-- Column bound: the library's weighted column norm of the EXACT defect column is at most
the grid value `colValB` at any denominator `S > 0`. -/
theorem colNormQ_defect_le_colValB {L N : ℕ} (S : ℕ) (hS : 0 < S)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (ν : ℚ) (hν : 0 < ν) (l j : Fin L) (c : Fin (N + 1)) :
    colNormQ (defectCols A_col DF_col l j c) ν N c ≤
      colValB S A_col DF_col N ν.num.natAbs ν.den l j c := by
  set νn := ν.num.natAbs
  set νd := ν.den
  have hn : (0 : ℚ) < νn := by
    rw [natAbs_cast, abs_pos, Int.cast_ne_zero]; exact (Rat.num_pos.mpr hν).ne'
  have hd : (0 : ℚ) < νd := by exact_mod_cast ν.den_pos
  have hS' : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
  have hνeq : ν = (νn : ℚ) / νd := by
    rw [natAbs_cast, abs_of_pos (Int.cast_pos.mpr (Rat.num_pos.mpr hν))]
    exact (Rat.num_div_den ν).symm
  set us := roundNatsB (L * (N + 1)) (defectColB S A_col DF_col N l j c)
  have hus : us.length = N + 1 := by simp [us, roundNatsB, defectColB_length]
  have hterm : ∀ i ∈ Finset.Icc 0 N,
      |(defectCols A_col DF_col l j c).getD i 0| * ν ^ i / ν ^ (c : ℕ) ≤
        ((us.getD i 0 : ℕ) : ℚ) * ((νn : ℚ) ^ i * (νd : ℚ) ^ (N - i)) * (νd : ℚ) ^ (c : ℕ) /
          ((S : ℚ) * (νd : ℚ) ^ N * (νn : ℚ) ^ (c : ℕ)) := by
    intro i hi
    have hiN := (Finset.mem_Icc.mp hi).2
    rw [defectCols_getD _ _ _ _ _ _ hiN]
    have hb := abs_defect_le_roundNatsB S hS A_col DF_col N l j c i (Nat.lt_succ_of_le hiN)
    have hνi : 0 ≤ ν ^ i / ν ^ (c : ℕ) := div_nonneg (pow_nonneg hν.le _) (pow_nonneg hν.le _)
    have key : ((us.getD i 0 : ℕ) : ℚ) / (S : ℚ) * (ν ^ i / ν ^ (c : ℕ)) =
        ((us.getD i 0 : ℕ) : ℚ) * ((νn : ℚ) ^ i * (νd : ℚ) ^ (N - i)) * (νd : ℚ) ^ (c : ℕ) /
          ((S : ℚ) * (νd : ℚ) ^ N * (νn : ℚ) ^ (c : ℕ)) := by
      have hsplit : (νd : ℚ) ^ N = (νd : ℚ) ^ (N - i) * (νd : ℚ) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiN]
      rw [hνeq, div_pow, div_pow, hsplit]
      field_simp
    rw [mul_div_assoc, ← key]
    exact mul_le_mul_of_nonneg_right hb hνi
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [colValB, dotN_eq_sum us (weightsB N νn νd) (N + 1) hus (weightsB_length N νn νd),
    ← Nat.range_succ_eq_Icc_zero]
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow]
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [weightsB_getD N νn νd i (Finset.mem_range.mp hi)]
  push_cast; ring

theorem le_foldl_max : ∀ (xs : List ℚ) (init : ℚ),
    init ≤ xs.foldl max init ∧ ∀ x ∈ xs, x ≤ xs.foldl max init
  | [], init => ⟨le_rfl, by simp⟩
  | y :: ys, init => by
    obtain ⟨h1, h2⟩ := le_foldl_max ys (max init y)
    refine ⟨(le_max_left _ _).trans h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right _ _).trans h1
    · exact h2 x hx

theorem finWeightedMatrixNormQ_defect_le_blockBoundB {L N : ℕ} (S : ℕ) (hS : 0 < S)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (ν : ℚ) (hν : 0 < ν) (l j : Fin L) :
    finWeightedMatrixNormQ (defectCols (N := N) A_col DF_col l j) ν ≤
      blockBoundB S A_col DF_col N ν.num.natAbs ν.den l j :=
  Finset.sup'_le _ _ fun c _ =>
    (colNormQ_defect_le_colValB S hS A_col DF_col ν hν l j c).trans
      ((le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨c, List.mem_range.mpr c.isLt, rfl⟩))

/-! ## The family-neutral `Z₀` clauses on raw `(A_col DF_col ν_q)`
Every clause lands on the exact predicate
`DefectExact` = `finiteBlockMatrixNormQ L N (defectCols A_col DF_col) ν_q ≤ Z₀`. -/

/-- Which `Z₀` checker is used. `exactCols`: exact gcd-free defect columns, rounded once at
the end (exact zeros stay zero, so `Z₀ = 0` is certifiable); `grid`: the grid accumulators
(every entry carries `L(N+1)` grid units of slack, so `Z₀ > 0`). -/
inductive Z₀Slot
  | exactCols
  | grid

section Clauses

variable (L N : ℕ) [NeZero L] (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ)

/-- Exact clause: the exact ℚ block norm of the defect. -/
abbrev DefectExact (Z₀ : ℚ) : Prop :=
  finiteBlockMatrixNormQ L N (defectCols A_col DF_col) ν_q ≤ Z₀

/-- Exact columns rounded up onto the grid `1/S`. -/
abbrev DefectRound (S : ℕ) (Z₀ : ℚ) : Prop :=
  0 < S ∧ 0 ≤ ν_q ∧ finiteBlockMatrixNormQ L N (roundCols S A_col DF_col N) ν_q ≤ Z₀

/-- Grid accumulators on `1/S`: for every block row `l`, the sum over `j` of the grid block
bounds is at most `Z₀`. -/
abbrev DefectGrid (S : ℕ) (Z₀ : ℚ) : Prop :=
  0 < S ∧ 0 < ν_q ∧ ∀ l : Fin L,
    ∑ j : Fin L, blockBoundB S A_col DF_col N ν_q.num.natAbs ν_q.den l j ≤ Z₀

/-- The `Z₀` clause at a chosen slot and grid denominator `S`. -/
def DefectBy : Z₀Slot → ℕ → ℚ → Prop
  | .exactCols, S, Z₀ => DefectRound L N A_col DF_col ν_q S Z₀
  | .grid, S, Z₀ => DefectGrid L N A_col DF_col ν_q S Z₀

noncomputable instance instDecidableDefectBy (s : Z₀Slot) (S : ℕ) (Z₀ : ℚ) :
    Decidable (DefectBy L N A_col DF_col ν_q s S Z₀) :=
  match s with
  | .exactCols => inferInstanceAs (Decidable (DefectRound L N A_col DF_col ν_q S Z₀))
  | .grid => inferInstanceAs (Decidable (DefectGrid L N A_col DF_col ν_q S Z₀))

end Clauses

section ClauseSound

variable {L N : ℕ} [NeZero L] {A_col DF_col : Fin L → Fin L → ℕ → Array ℚ} {ν_q : ℚ}
  {S : ℕ} {Z₀ : ℚ}

theorem defectRound_sound (h : DefectRound L N A_col DF_col ν_q S Z₀) :
    DefectExact L N A_col DF_col ν_q Z₀ :=
  (finiteBlockMatrixNormQ_mono h.2.1 fun l j c i hi =>
    abs_defectCols_le_roundCols S h.1 A_col DF_col l j c i hi).trans h.2.2

theorem defectGrid_sound (h : DefectGrid L N A_col DF_col ν_q S Z₀) :
    DefectExact L N A_col DF_col ν_q Z₀ :=
  Finset.sup'_le _ _ fun l _ =>
    (Finset.sum_le_sum fun j _ =>
      finWeightedMatrixNormQ_defect_le_blockBoundB S h.1 A_col DF_col ν_q h.2.1 l j).trans
      (h.2.2 l)

theorem defectBy_sound (s : Z₀Slot) (S : ℕ) (h : DefectBy L N A_col DF_col ν_q s S Z₀) :
    DefectExact L N A_col DF_col ν_q Z₀ :=
  match s, h with
  | .exactCols, h => defectRound_sound h
  | .grid, h => defectGrid_sound h

end ClauseSound

end RadiiPolynomial.Certification.Rational
