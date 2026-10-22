import RadiiPolynomial.Certification.IVP.Chebyshev.TC
import RadiiPolynomial.Certification.IVP.Chebyshev.Z1

/-!
# Chebyshev certification adapter: kernel-scale ℚ layer

The clipped Laurent interpreter `evalFast` (`evalFast_eq`), the sparse leakage columns
`colNormS` (`colNormS_eq`) with the soundness `epsGen_le_of_cols` of per-block leakage data,
and the closed-form `TC` rows `TCnormF` (`TCnormF_eq`).
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

/-! ### Kernel-scale checker

Four cost cuts, each with a generic soundness lemma, so that the kernel (`decide +kernel`)
closes certificates with a few dozen modes:

* `evalFast`: the Laurent interpreter with the convolution window clipped to the
  intersection of both factors' supports (`evalFast_eq`: equal to `evalLaurentCoeffSeq` on
  support-bounded inputs). The library interpreter sums over `laurentModes`, a
  `Finset.image` whose kernel reduction deduplicates `2R+1` integers per product node.
* `colNormS`: the `Z₁` leakage column as `A · w`, where `w` = (stored `DF` column) − (exact
  Jacobian column), summed over the support of `w` only (`colNormS_eq`: equal to
  `chebColNormQ`). Columns inside the stored block cancel to `w = 0` when `DF` is the exact
  Jacobian; columns beyond it keep only the Jacobian's nonzero rows.
* `TCnormF`: the `TC` column rows in closed form (two entries of `A` per row instead of an
  `N + 1`-term sum against the sparse `FCe`; `TCnormF_eq`: equal to `TCnormGen`).
* `ChecksK`: the `Z₀` conjunct of `Checks` replaced by a `DefectBy` slot (exact columns rounded
  onto a grid, or grid accumulators), the `ε` conjunct by per-block certificate data
  `E l j` (one comparison per column and one far-envelope comparison per block), and every
  conjunct stated separately so a certificate closes each by its own `decide +kernel`
  (`checks_of_checksK`: `ChecksK → Checks`; `Z₁_le_of_checksK`: the same `Z₁` operator
  bound `Z₁_le_of_Q` produces). -/

section KernelQ

variable {L : ℕ}

/-- Integer maximum through the core `Int.decLe` instance (kernel-reducible). -/
private def zmax (a b : ℤ) : ℤ := @ite _ (a ≤ b) (Int.decLe a b) b a

/-- Integer minimum through the core `Int.decLe` instance (kernel-reducible). -/
private def zmin (a b : ℤ) : ℤ := @ite _ (a ≤ b) (Int.decLe a b) a b

/-- Sum of `g` over the integer interval `[lo, hi]`, as a list fold. -/
private def zsum (lo hi : ℤ) (g : ℤ → ℚ) : ℚ :=
  ((List.range (hi + 1 - lo).toNat).map fun i : ℕ => g (lo + i)).sum

theorem list_range_map_sum (n : ℕ) (F : ℕ → ℚ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

private theorem zsum_eq (lo hi : ℤ) (g : ℤ → ℚ) : zsum lo hi g = ∑ k ∈ Finset.Icc lo hi, g k := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map, zsum, list_range_map_sum]
  rfl

/-- The Laurent interpreter with the product window clipped to both supports. -/
def evalFast : CompPoly L → (Fin L → ℕ) → (Fin L → ℤ → ℚ) → ℤ → ℚ
  | .C r, _, _, n => if n = 0 then r else 0
  | .X i, _, seqs, n => seqs i n
  | .add p q, radii, seqs, n => evalFast p radii seqs n + evalFast q radii seqs n
  | .sub p q, radii, seqs, n => evalFast p radii seqs n - evalFast q radii seqs n
  | .mul p q, radii, seqs, n =>
      zsum (zmax (-(q.laurentRadius radii : ℤ)) (n - p.laurentRadius radii))
        (zmin (q.laurentRadius radii : ℤ) (n + p.laurentRadius radii))
        fun k => evalFast p radii seqs (n - k) * evalFast q radii seqs k
  | .neg p, radii, seqs, n => -(evalFast p radii seqs n)
  | .smul r p, radii, seqs, n => r * evalFast p radii seqs n

/-- Soundness of the clipped interpreter on support-bounded inputs. -/
theorem evalFast_eq (p : CompPoly L) (radii : Fin L → ℕ) (seqs : Fin L → ℤ → ℚ)
    (hs : ∀ i n, radii i < n.natAbs → seqs i n = 0) (n : ℤ) :
    evalFast p radii seqs n = p.evalLaurentCoeffSeq radii seqs n := by
  induction p generalizing n with
  | C r => rfl
  | X i => rfl
  | add p q ihp ihq => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
  | sub p q ihp ihq => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
  | mul p q ihp ihq =>
      simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ihp, ihq]
      rw [zsum_eq]
      refine Finset.sum_subset (fun k hk => ?_) (fun k hk hnk => ?_)
      · rw [Finset.mem_Icc] at hk
        rw [CompPoly.mem_laurentModes_iff]
        unfold zmax zmin at hk
        split_ifs at hk <;> omega
      · rw [CompPoly.mem_laurentModes_iff] at hk
        rw [Finset.mem_Icc] at hnk
        have hp : p.laurentRadius radii < (n - k).natAbs := by
          unfold zmax zmin at hnk
          split_ifs at hnk <;> omega
        rw [CompPoly.evalLaurentCoeffSeq_eq_zero_of_radius_lt p radii seqs hs _ hp, zero_mul]
  | neg p ih => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ih]
  | smul r p ih => simp only [evalFast, CompPoly.evalLaurentCoeffSeq, ih]

/-- `evalChebCoeff` through the clipped interpreter. -/
def evalChebFast (p : CompPoly L) (arrs : Fin L → Array ℚ) : ℤ → ℚ :=
  evalFast p (fun i => (arrs i).size) (fun i n => (arrs i).getD n.natAbs 0)

theorem evalChebFast_eq (p : CompPoly L) (arrs : Fin L → Array ℚ) (n : ℤ) :
    evalChebFast p arrs n = p.evalChebCoeff arrs n :=
  evalFast_eq p _ _ (fun i k hk => by
    simp [Array.getD, show ¬k.natAbs < (arrs i).size by omega]) n

/-- `compPolyDphiQ` through the clipped interpreter. -/
def dphiFast (p : CompPoly L) (m : Fin L) (arrs : Fin L → Array ℚ) (k : ℕ) (n : ℤ) : ℚ :=
  if k = 0 then evalChebFast (p.pderiv m) arrs n
  else evalChebFast (p.pderiv m) arrs (n - k) + evalChebFast (p.pderiv m) arrs (n + k)

/-- `compPolyDFQ` through the clipped interpreter. -/
def dfFast (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (l m : Fin L) (row col : ℕ) : ℚ :=
  match row with
  | 0 => if l = m then (if col = 0 then -1 else -2 * (-1 : ℚ) ^ col) else 0
  | k + 1 => (if l = m ∧ k + 1 = col then 2 * ((k : ℚ) + 1) else 0) +
      dphiFast (f l) m arrs col (↑(k + 2) : ℤ) - dphiFast (f l) m arrs col (k : ℤ)

theorem dfFast_eq (f : Fin L → CompPoly L) (arrs : Fin L → Array ℚ) (l m : Fin L)
    (row col : ℕ) : dfFast f arrs l m row col = compPolyDFQ f arrs l m row col := by
  cases row with
  | zero => rfl
  | succ k => simp only [dfFast, compPolyDFQ, dphiFast, compPolyDphiQ, evalChebFast_eq]

/-- Residual column `w = (stored DF column, inside the block) − (exact Jacobian column)`
of input component `j`, mode `mn`, at output `(j', k)`. -/
def wQ (N : ℕ) (DF_col : Fin L → Fin L → ℕ → Array ℚ) (f : Fin L → CompPoly L)
    (arrs : Fin L → Array ℚ) (j : Fin L) (mn : ℕ) (x : Fin L × Fin (N + 1)) : ℚ :=
  (if mn ≤ N then (DF_col x.1 j mn).getD x.2 0 else 0) - dfFast f arrs x.1 j x.2 mn

/-- Support of the residual column. -/
def wSupp (N : ℕ) (DF_col : Fin L → Fin L → ℕ → Array ℚ) (f : Fin L → CompPoly L)
    (arrs : Fin L → Array ℚ) (j : Fin L) (mn : ℕ) : Finset (Fin L × Fin (N + 1)) :=
  Finset.univ.filter fun x => wQ N DF_col f arrs j mn x ≠ 0

/-- Row `n` of leakage column `mn` of block `(l, j)`, as `A · w` over the support of `w`. -/
def DcolS (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (arrs : Fin L → Array ℚ)
    (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) (n : Fin (N + 1)) : ℚ :=
  ∑ x ∈ wSupp N DF_col f arrs j mn, (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x

/-- Sparse weighted norm of leakage column `mn` of block `(l, j)`. -/
def colNormS (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (arrs : Fin L → Array ℚ)
    (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) : ℚ :=
  ∑ n : Fin (N + 1), |DcolS N A_col DF_col arrs f l j mn n| * ν_q ^ (n : ℕ)

/-- The sparse row is the exact leakage row `DcolAux` (generic in `L`, `N`, the data). -/
theorem DcolS_eq (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (arrs : Fin L → Array ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) :
    DcolS N A_col DF_col arrs f l j mn n =
      DcolAux N A_col DF_col l j mn (jacColQ N f arrs j mn) n := by
  rw [DcolAux_jac]
  unfold DcolS wSupp
  rw [Finset.sum_filter]
  have h1 : ∀ x : Fin L × Fin (N + 1),
      (if wQ N DF_col f arrs j mn x ≠ 0 then
        (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x else 0) =
        (A_col l x.1 x.2).getD n 0 * wQ N DF_col f arrs j mn x := fun x => by
    split_ifs with h
    · rfl
    · rw [not_not.mp h, mul_zero]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Fintype.sum_prod_type]
  simp only [wQ, dfFast_eq, mul_sub, Finset.sum_sub_distrib]
  congr 1
  by_cases hmn : mn ≤ N
  · rw [dite_eq_left hmn]
    simp only [ite_eq_left hmn]
    unfold blockDefectMatQ
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply, matOfCols]
    by_cases hlj : l = j
    · subst hlj
      simp only [ite_true, true_and, Matrix.one_apply, Fin.ext_iff]
      ring
    · simp only [hlj, ite_false, false_and, Matrix.zero_apply]
      ring
  · rw [dite_eq_right hmn, ite_eq_right (fun h : l = j ∧ (n : ℕ) = mn => hmn (h.2 ▸ Nat.lt_succ_iff.mp n.isLt))]
    simp only [ite_eq_right hmn, mul_zero, Finset.sum_const_zero, sub_zero]

theorem colNormS_eq (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (arrs : Fin L → Array ℚ) (ν_q : ℚ) (f : Fin L → CompPoly L) (l j : Fin L) (mn : ℕ) :
    colNormS N A_col DF_col arrs ν_q f l j mn = chebColNormQ N A_col DF_col arrs ν_q f l j mn := by
  unfold colNormS chebColNormQ colNormAux
  simp only [DcolS_eq]

/-- Soundness of the per-block certificate data: column checks up to `Mfar`, the far
envelope, and the row sums give the generated leakage bound `epsGen ≤ ε` the face consumes. -/
theorem epsGen_le_of_cols [NeZero L] (N : ℕ) (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ)
    (abar_Q : Fin L → Array ℚ) {ν_q : ℚ} (hν : 0 < ν_q) (f : Fin L → CompPoly L)
    (E : Fin L → Fin L → ℚ) {ε : ℚ}
    (hcol : ∀ l j, ∀ mn < Mfar N f abar_Q + 1,
      chebColNormQ N A_col DF_col abar_Q ν_q f l j mn ≤ E l j * ν_q ^ mn)
    (hfar : ∀ l j, rowA0Q N A_col ν_q l j ≤ E l j * ν_q ^ (Mfar N f abar_Q + 1))
    (hE : ∀ l, ∑ j, E l j ≤ ε) :
    epsGen N A_col DF_col abar_Q ν_q f ≤ ε := by
  unfold epsGen
  refine Finset.sup'_le _ _ fun l _ => (Finset.sum_le_sum fun j _ => ?_).trans (hE l)
  unfold epsBlockGen
  refine max_le (Finset.sup'_le _ _ fun mn _ => ?_) ?_
  · exact (div_le_iff₀ (pow_pos hν _)).mpr (hcol l j mn mn.isLt)
  · exact (div_le_iff₀ (pow_pos hν _)).mpr (hfar l j)

/-- Closed form of a `TC` column row: `FCe mn` has at most two nonzero entries
(`k = mn − 1` with coefficient `1`, `k = mn + 1` with coefficient `−1`). -/
def TCcolF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) : ℚ :=
  (if 2 ≤ mn ∧ mn ≤ N + 1 then (A_col l j (mn - 1)).getD n 0 else 0) -
    (if mn < N then (A_col l j (mn + 1)).getD n 0 else 0)

theorem TCcolQ_eq_F (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (l j : Fin L) (mn : ℕ)
    (n : Fin (N + 1)) : TCcolQ N A_col l j mn n = TCcolF N A_col l j mn n := by
  set a : ℕ → ℚ := fun k => (A_col l j k).getD n 0 with ha
  have key : ∀ c : ℕ, (∑ i ∈ Finset.range N, if i = c then a (i + 1) else 0) =
      if c < N then a (c + 1) else 0 := fun c => by
    rw [Finset.sum_ite_eq' (Finset.range N) c (fun i => a (i + 1))]
    simp only [Finset.mem_range]
  unfold TCcolQ TCcolF
  rw [Fin.sum_univ_eq_sum_range (fun k => (A_col l j k).getD n 0 * FCe mn k) (N + 1),
    Finset.sum_range_succ']
  simp only [FCe, mul_zero, add_zero, mul_sub, mul_ite, mul_one, Finset.sum_sub_distrib]
  change (∑ i ∈ Finset.range N, if i + 2 = mn then a (i + 1) else 0) -
      (∑ i ∈ Finset.range N, if i = mn then a (i + 1) else 0) = _
  rw [key mn]
  congr 1
  by_cases h2 : 2 ≤ mn
  · obtain ⟨c, rfl⟩ : ∃ c, mn = c + 2 := ⟨mn - 2, by omega⟩
    simp only [add_left_inj, key c]
    by_cases hc : c < N
    · rw [ite_eq_left hc, ite_eq_left ⟨h2, by omega⟩]
      rfl
    · rw [ite_eq_right hc, ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

/-- `TCcolNormQ` through the closed-form rows. -/
def TCcolNormF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L)
    (mn : ℕ) : ℚ :=
  ∑ n : Fin (N + 1), |TCcolF N A_col l j mn n| * ν_q ^ (n : ℕ)

/-- `TCblockGen` through the closed-form rows. -/
def TCblockF (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) (l j : Fin L) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun mn : Fin (N + 2) =>
    TCcolNormF N A_col ν_q l j mn / ν_q ^ (mn : ℕ)

/-- `TCnormGen` through the closed-form rows. -/
def TCnormF [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l : Fin L =>
    ∑ j : Fin L, (TCblockF N A_col ν_q l j + if l = j then ν_q / ((N : ℚ) + 1) else 0)

theorem TCnormF_eq [NeZero L] (N : ℕ) (A_col : Fin L → Fin L → ℕ → Array ℚ) (ν_q : ℚ) :
    TCnormF N A_col ν_q = TCnormGen N A_col ν_q := by
  unfold TCnormF TCblockF TCcolNormF TCnormGen TCblockGen TCcolNormQ
  simp only [TCcolQ_eq_F]

end KernelQ

end ChebyshevIVP
