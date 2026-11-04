import RadiiPolynomial.Applications.Fourier.Quadratic
import RadiiPolynomial.Applications.Fourier.IkData

/-!
# Rational-leaf adapter for the quadratic Fourier family on `ℓ²`

A certificate of the quadratic Fourier family `Applications/Fourier/Quadratic.lean` at a finite
head `headF N = Icc (−N) N`, a band `headF B` of `β = 2ā`, a weight `ν` and a symbol `μ` is, on the
numerical side, an exact rational leaf: the candidate `ā` and the head matrix `M` as integer pairs
over a common denominator `D`, rational mirrors `muQ`, `forcQ` of the symbol and the forcing, and
rational bound constants. This module is the adapter from such a leaf to the family's head
certificate `Cert (headF N) μ ν` and its bounds, generic in the symbol, the forcing, `N`, `B` and
`ν` (no equation-specific data):

* **the exact mirror** (computable): complex arithmetic on `ℚ × ℚ`, folds over `List.range` plus a
  shift (`Finset.Icc` on `ℤ` is noncomputable), the index lists `idx N`, `idx2 N`,
  `leakColsQ N B`, `leakRowsQ N B`, and the leaf-parametric mirror maps `DFQ`, `EQ`, `KMQ`, `GQ`,
  the `Y₀` summand `y0Term`, the normalized row and column sums and `betaQ`;
* **the leaf** `QuadFourierLeafQ` and its two decidable obligations: `Checks` (support of `ā` in
  the band, reality of `ā`, the chunk coverage of the index lists, the four bound combinations,
  nonnegativity; one `decide +kernel`) and `ChunkChecks` (the per-chunk row, column and part
  bounds, which a consumer discharges by one `native_decide` per chunk); the radii inequality is
  checked by the consumer through the rational check `generalRadiiPolynomial_neg_of_Q_const` of
  `Certification/RadiiPolynomialQ.lean`;
* **the bridges** from the mirror to the complex objects, under the bridge hypotheses
  `hν : ν = nuQ`, `hμ : μ n = toC (muQ n)`, `hg : coeff g n = toC (forcQ n)`;
* **the certificate** `QuadFourierLeafQ.cert` and the **soundness theorem**
  `QuadFourierLeafQ.cert_spec`: the `Y₀` bound, the squared `Z₁` inequality for every tail factor
  `x` with `(x²)⁻¹ ≤ tailInvSqQ`, the squared `Z₂` inequality with `T2 = t2Q`, and `0 ≤ Z1c`,
  `0 ≤ Z2c`, in the shape the family's existence theorems consume; the reality of the candidate
  is `conjRefl_abar`.

The tail facts of the symbol (nonvanishing off the head, the tail-sum bound `T2`, the tail factor)
and the support of the forcing stay with the consuming theorem.
-/

open scoped ENNReal NNReal

namespace RadiiPolynomial.Certification.Fourier.Quadratic

/-! ### A. The exact rational mirror -/

section Mirror

/-- Complex addition on `ℚ × ℚ` (real part, imaginary part). -/
def cadd (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 + y.1, x.2 + y.2)

/-- Complex subtraction on `ℚ × ℚ`. -/
def csub (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 - y.1, x.2 - y.2)

/-- Complex multiplication on `ℚ × ℚ`. -/
def cmul (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Real scaling on `ℚ × ℚ`. -/
def cscale (t : ℚ) (x : ℚ × ℚ) : ℚ × ℚ := (t * x.1, t * x.2)

/-- Complex conjugation on `ℚ × ℚ`. -/
def cconj (x : ℚ × ℚ) : ℚ × ℚ := (x.1, -x.2)

/-- The squared modulus `re² + im²` (EXACT). -/
def cnormSq (x : ℚ × ℚ) : ℚ := x.1 * x.1 + x.2 * x.2

/-- Complex inversion on `ℚ × ℚ` (`0⁻¹ = 0`). -/
def cinv (x : ℚ × ℚ) : ℚ × ℚ := (x.1 / cnormSq x, -x.2 / cnormSq x)

/-- The absolute value on `ℚ`, by one comparison. -/
def qabs (q : ℚ) : ℚ := if q < 0 then -q else q

/-- The rational modulus majorant `|re| + |im|` (UPPER for the modulus). -/
def reim (x : ℚ × ℚ) : ℚ := qabs x.1 + qabs x.2

/-- The complex sum of a family over a list of modes. -/
def csum (l : List ℤ) (f : ℤ → ℚ × ℚ) : ℚ × ℚ := l.foldr (fun k acc => cadd (f k) acc) (0, 0)

/-- The rational sum of a family over a list of modes. -/
def qsum (l : List ℤ) (f : ℤ → ℚ) : ℚ := l.foldr (fun k acc => f k + acc) 0

/-- A numerator pair over `D` as a rational complex number. -/
def ofNum (D : ℤ) (p : ℤ × ℤ) : ℚ × ℚ := ((p.1 : ℚ) / D, (p.2 : ℚ) / D)

/-- The head indices `−N, …, N` (range plus shift). -/
def idx (N : ℕ) : List ℤ := (List.range (2 * N + 1)).map fun (j : ℕ) => (j : ℤ) - N

/-- The residual support `F ∪ (F + F) = {|n| ≤ 2N}` of the head `F = headF N`. -/
def idx2 (N : ℕ) : List ℤ := (List.range (4 * N + 1)).map fun (j : ℕ) => (j : ℤ) - 2 * N

/-- The band columns `leakCols (headF N) (headF B) = {N < |k| ≤ N + B}`. -/
def leakColsQ (N B : ℕ) : List ℤ :=
  ((List.range B).map fun (j : ℕ) => (j : ℤ) - (N + B)) ++
    (List.range B).map fun (j : ℕ) => (j : ℤ) + (N + 1)

/-- The boundary rows `leakRows (headF N) (headF B) = {N − B < |n| ≤ N}` (for `B ≤ N`). -/
def leakRowsQ (N B : ℕ) : List ℤ :=
  ((List.range B).map fun (j : ℕ) => (j : ℤ) - N) ++
    (List.range B).map fun (j : ℕ) => (j : ℤ) + ((N : ℤ) + 1 - B)

end Mirror

/-! ### B. The rational leaf and its obligations -/

section Leaf

/-- **The exact rational leaf** of a quadratic Fourier certificate on the head `|n| ≤ N` with the
band `|b| ≤ B` of `β = 2ā`: the weight `nuQ`, the symbol and forcing mirrors, the candidate and the
head matrix as numerator pairs over `D`, the bound constants of record, the tail constants
`t2Q` (the `T2` bound) and `tailInvSqQ` (the square of the tail factor), and the chunks of the
`Y₀` residual and of the `U_row` sum (each with its generated upper bound) and of the head rows
and band columns. The chunks are an engineering choice; `Checks` verifies that they cover the
index lists. -/
structure QuadFourierLeafQ where
  /-- The head is `|n| ≤ N`. -/
  N : ℕ
  /-- The band of `β = 2ā` is `|b| ≤ B`. -/
  B : ℕ
  /-- The weight parameter. -/
  nuQ : ℚ
  /-- The symbol mirror. -/
  muQ : ℤ → ℚ × ℚ
  /-- The forcing mirror. -/
  forcQ : ℤ → ℚ × ℚ
  /-- The common denominator of the data. -/
  D : ℤ
  /-- The candidate `ā_n`, `n = −N, …, N`, as numerator pairs over `D`. -/
  abarNum : List (ℤ × ℤ)
  /-- The head matrix, rows and columns `−N, …, N`, as numerator pairs over `D`. -/
  MNum : List (List (ℤ × ℤ))
  /-- The `Y₀` constant of record. -/
  Y0c : ℚ
  /-- The `Z₀` constant of record. -/
  Z0c : ℚ
  /-- The `Z₁` constant of record. -/
  Z1c : ℚ
  /-- The `Z₂` constant of record. -/
  Z2c : ℚ
  /-- The upper bound of the normalized `Z₀` row sums. -/
  RzC : ℚ
  /-- The upper bound of the normalized `Z₀` column sums. -/
  CzC : ℚ
  /-- The upper bound of the composed-kernel row sums. -/
  RmC : ℚ
  /-- The upper bound of the composed-kernel column sums. -/
  CmC : ℚ
  /-- The tail-sum bound `T2`. -/
  t2Q : ℚ
  /-- An upper bound of the squared tail factor `‖tailSymbol‖_∞²`. -/
  tailInvSqQ : ℚ
  /-- The `Y₀` chunks of `idx2 N` with their upper bounds. -/
  y0Parts : List (List ℤ × ℚ)
  /-- The `U_row²` chunks of `idx N` with their upper bounds. -/
  uParts : List (List ℤ × ℚ)
  /-- The row chunks of `idx N` of the `Z₀` and composed-kernel checks. -/
  rowChunks : List (List ℤ)
  /-- The column chunks of `leakColsQ N B` of the composed-kernel checks. -/
  colChunks : List (List ℤ)

namespace QuadFourierLeafQ

variable (L : QuadFourierLeafQ)

/-- **The centre accessor** `ā_n` (`0` off `−N, …, N`). -/
def abarQ (n : ℤ) : ℚ × ℚ :=
  if -(L.N : ℤ) ≤ n ∧ n ≤ L.N then ofNum L.D (L.abarNum.getD (n + L.N).toNat (0, 0)) else (0, 0)

/-- **The matrix accessor** `M_ij` (`0` off the head block). -/
def MQ (i j : ℤ) : ℚ × ℚ :=
  if (-(L.N : ℤ) ≤ i ∧ i ≤ L.N) ∧ (-(L.N : ℤ) ≤ j ∧ j ≤ L.N) then
    ofNum L.D ((L.MNum.getD (i + L.N).toNat []).getD (j + L.N).toNat (0, 0))
  else (0, 0)

/-- The finite Jacobian `DF_{nj} = μ_n δ_{nj} − 2 ā_{n−j}`. -/
def DFQ (n j : ℤ) : ℚ × ℚ :=
  csub (if n = j then L.muQ n else (0, 0)) (cscale 2 (L.abarQ (n - j)))

/-- The `Z₀` defect matrix `E = I − M DF` on the head. -/
def EQ (i j : ℤ) : ℚ × ℚ :=
  csub (if i = j then (1, 0) else (0, 0)) (csum (idx L.N) fun n => cmul (L.MQ i n) (L.DFQ n j))

/-- The COMPOSED leakage kernel `K_M(i,k) = ∑_{n ∈ leakRows} M_in · 2 ā_{n−k}`. -/
def KMQ (i k : ℤ) : ℚ × ℚ :=
  csum (leakRowsQ L.N L.B) fun n => cmul (L.MQ i n) (cscale 2 (L.abarQ (n - k)))

/-- The raw product `(ā ⋆ ā)_n = ∑_{k ∈ head} ā_k ā_{n−k}`. -/
def convQ (n : ℤ) : ℚ × ℚ := csum (idx L.N) fun k => cmul (L.abarQ k) (L.abarQ (n - k))

/-- The raw residual `F_n(ā) = μ_n ā_n − (ā ⋆ ā)_n − g_n`. -/
def residQ (n : ℤ) : ℚ × ℚ := csub (csub (cmul (L.muQ n) (L.abarQ n)) (L.convQ n)) (L.forcQ n)

/-- The coefficients of `G ā`: `∑_j M_nj F_j(ā)` on the head, `F_n(ā)/μ_n` off it. -/
def GQ (n : ℤ) : ℚ × ℚ :=
  if -(L.N : ℤ) ≤ n ∧ n ≤ L.N then csum (idx L.N) (fun j => cmul (L.MQ n j) (L.residQ j))
  else cmul (cinv (L.muQ n)) (L.residQ n)

/-- The `Y₀` summand `‖coeff (G ā) n‖² ν^{2|n|}` (EXACT). -/
def y0Term (n : ℤ) : ℚ := cnormSq (L.GQ n) * L.nuQ ^ (2 * n.natAbs)

/-- The normalized `Z₀` row sum `∑_j (|Re| + |Im|)(E_ij) ν^{|i|−|j|}` (UPPER for the moduli). -/
def z0RowQ (i : ℤ) : ℚ :=
  qsum (idx L.N) fun j => reim (L.EQ i j) * L.nuQ ^ i.natAbs / L.nuQ ^ j.natAbs

/-- The normalized `Z₀` column sum. -/
def z0ColQ (j : ℤ) : ℚ :=
  qsum (idx L.N) fun i => reim (L.EQ i j) * L.nuQ ^ i.natAbs / L.nuQ ^ j.natAbs

/-- The normalized composed-kernel row sum over the band columns. -/
def kmRowQ (i : ℤ) : ℚ :=
  qsum (leakColsQ L.N L.B) fun k => reim (L.KMQ i k) * L.nuQ ^ i.natAbs / L.nuQ ^ k.natAbs

/-- The normalized composed-kernel column sum over the head rows. -/
def kmColQ (k : ℤ) : ℚ :=
  qsum (idx L.N) fun i => reim (L.KMQ i k) * L.nuQ ^ i.natAbs / L.nuQ ^ k.natAbs

/-- The symbol-norm majorant `∑_k 2 (|Re| + |Im|)(ā_k) ν^{|k|}` of `‖β‖` (UPPER). -/
def betaQ : ℚ := qsum (idx L.N) fun k => 2 * reim (L.abarQ k) * L.nuQ ^ k.natAbs

/-- The `U_row` row sum `∑_j (|Re| + |Im|)(M_ij) ν^{|i|−|j|}` (UPPER for the moduli). -/
def urowRowQ (i : ℤ) : ℚ :=
  qsum (idx L.N) fun j => reim (L.MQ i j) * L.nuQ ^ i.natAbs / L.nuQ ^ j.natAbs

/-- **The leaf obligations** (ONE conjunction, decided by `decide +kernel`): the band fits the
head, the candidate is supported in the band and real, the chunks cover the index lists, the four
bound combinations of record hold, and the constants are nonnegative. -/
abbrev Checks : Prop :=
  L.B ≤ L.N ∧
  (∀ n ∈ idx L.N, (L.B : ℤ) < |n| → L.abarQ n = (0, 0)) ∧
  (∀ n ∈ idx L.N, L.abarQ (-n) = cconj (L.abarQ n)) ∧
  idx2 L.N = (L.y0Parts.map Prod.fst).flatten ∧
  idx L.N = (L.uParts.map Prod.fst).flatten ∧
  idx L.N = L.rowChunks.flatten ∧
  leakColsQ L.N L.B = L.colChunks.flatten ∧
  (L.y0Parts.map Prod.snd).sum ≤ L.Y0c ^ 2 ∧
  L.RzC * L.CzC ≤ L.Z0c ^ 2 ∧
  L.RmC * L.CmC + L.betaQ ^ 2 * L.tailInvSqQ ≤ L.Z1c ^ 2 ∧
  4 * ((L.uParts.map Prod.snd).sum + L.t2Q) ≤ L.Z2c ^ 2 ∧
  0 ≤ L.Y0c ∧ 0 ≤ L.Z0c ∧ 0 ≤ L.Z1c ∧ 0 ≤ L.Z2c ∧
  0 ≤ L.RzC ∧ 0 ≤ L.CzC ∧ 0 ≤ L.RmC ∧ 0 ≤ L.CmC

/-- **The per-chunk obligations**: each `Y₀` part and each `U_row²` part is at most its bound, and
the normalized rows and columns of every chunk are at most `RzC`, `CzC`, `RmC`, `CmC`. A consumer
proves each chunk by its own `native_decide` and assembles this conjunction. -/
abbrev ChunkChecks : Prop :=
  (∀ p ∈ L.y0Parts, qsum p.1 L.y0Term ≤ p.2) ∧
  (∀ c ∈ L.rowChunks, ∀ i ∈ c, L.z0RowQ i ≤ L.RzC) ∧
  (∀ c ∈ L.rowChunks, ∀ j ∈ c, L.z0ColQ j ≤ L.CzC) ∧
  (∀ c ∈ L.rowChunks, ∀ i ∈ c, L.kmRowQ i ≤ L.RmC) ∧
  (∀ c ∈ L.colChunks, ∀ k ∈ c, L.kmColQ k ≤ L.CmC) ∧
  (∀ p ∈ L.uParts, qsum p.1 (fun i => L.urowRowQ i ^ 2) ≤ p.2)

end QuadFourierLeafQ

end Leaf

noncomputable section

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic RadiiPolynomial.Fourier.IkData

/-! ### C. Bridges from the mirror to the complex objects -/

section Bridges

/-- A rational complex pair as a complex number: `toC z = z.1 + z.2 i`. -/
def toC (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

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

/-- The normalized entry against its rational majorant, at a weight `ν = q`. -/
theorem weighted_le_reim {ν : PosReal} {q : ℚ} (hν : (ν : ℝ) = q) (z : ℚ × ℚ) (i j : ℤ) :
    ‖toC z‖ * (ν : ℝ) ^ i.natAbs / (ν : ℝ) ^ j.natAbs ≤
      ((reim z * q ^ i.natAbs / q ^ j.natAbs : ℚ) : ℝ) := by
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_pow, ← hν]
  gcongr
  all_goals first | exact norm_le_reim z | exact pow_nonneg ν.coe_pos.le _

/-! #### Folds over lists versus `Finset` sums -/

theorem toC_csum (l : List ℤ) (f : ℤ → ℚ × ℚ) :
    toC (csum l f) = (l.map fun k => toC (f k)).sum := by
  induction l with
  | nil => exact toC_zero
  | cons k l ih =>
    show toC (cadd (f k) (csum l f)) = _
    rw [toC_cadd, ih, List.map_cons, List.sum_cons]

/-- The fold `qsum` is the list sum (a `foldr` identity). -/
theorem qsum_eq_sum (l : List ℤ) (f : ℤ → ℚ) : qsum l f = (l.map f).sum := by
  rw [qsum, List.sum_eq_foldr, List.foldr_map]

theorem cast_qsum (l : List ℤ) (f : ℤ → ℚ) :
    ((qsum l f : ℚ) : ℝ) = (l.map fun k => (f k : ℝ)).sum := by
  rw [qsum_eq_sum, Rat.cast_list_sum, List.map_map]
  rfl

theorem qsum_append (l₁ l₂ : List ℤ) (f : ℤ → ℚ) :
    qsum (l₁ ++ l₂) f = qsum l₁ f + qsum l₂ f := by
  rw [qsum_eq_sum, qsum_eq_sum, qsum_eq_sum, List.map_append, List.sum_append]

/-- The fold over the concatenation of chunks is the sum of the chunk folds. -/
theorem qsum_flatten (ls : List (List ℤ)) (f : ℤ → ℚ) :
    qsum ls.flatten f = (ls.map fun l => qsum l f).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [List.flatten_cons, qsum_append, ih, List.map_cons, List.sum_cons]

/-- A `Finset` sum over `s` is the list sum over a duplicate-free list with the same members. -/
theorem sum_eq_list {R : Type*} [AddCommMonoid R] {s : Finset ℤ} {l : List ℤ} (hl : l.Nodup)
    (hs : ∀ n, n ∈ s ↔ n ∈ l) (f : ℤ → R) : ∑ n ∈ s, f n = (l.map f).sum := by
  rw [show s = l.toFinset from Finset.ext fun n => by rw [hs, List.mem_toFinset],
    List.sum_toFinset _ hl]

/-! #### The index lists -/

theorem mem_idx {N : ℕ} {k : ℤ} : k ∈ idx N ↔ -(N : ℤ) ≤ k ∧ k ≤ N := by
  simp only [idx, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k + N).toNat, by omega, by omega⟩

theorem mem_idx2 {N : ℕ} {k : ℤ} : k ∈ idx2 N ↔ -(2 * N : ℤ) ≤ k ∧ k ≤ 2 * N := by
  simp only [idx2, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k + 2 * N).toNat, by omega, by omega⟩

theorem mem_leakColsQ {N B : ℕ} {k : ℤ} :
    k ∈ leakColsQ N B ↔
      (-((N : ℤ) + B) ≤ k ∧ k ≤ -((N : ℤ) + 1)) ∨ ((N : ℤ) + 1 ≤ k ∧ k ≤ N + B) := by
  simp only [leakColsQ, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨(k + (N + B)).toNat, by omega, by omega⟩
    · exact Or.inr ⟨(k - (N + 1)).toNat, by omega, by omega⟩

theorem mem_leakRowsQ {N B : ℕ} {k : ℤ} :
    k ∈ leakRowsQ N B ↔
      (-(N : ℤ) ≤ k ∧ k ≤ -(N : ℤ) + B - 1) ∨ ((N : ℤ) + 1 - B ≤ k ∧ k ≤ N) := by
  simp only [leakRowsQ, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨(k + N).toNat, by omega, by omega⟩
    · exact Or.inr ⟨(k - ((N : ℤ) + 1 - B)).toNat, by omega, by omega⟩

theorem nodup_idx (N : ℕ) : (idx N).Nodup :=
  (List.nodup_range).map fun a b h => by omega

theorem nodup_idx2 (N : ℕ) : (idx2 N).Nodup :=
  (List.nodup_range).map fun a b h => by omega

theorem nodup_leakColsQ (N B : ℕ) : (leakColsQ N B).Nodup := by
  refine List.nodup_append.2 ⟨(List.nodup_range).map fun a b h => by omega,
    (List.nodup_range).map fun a b h => by omega, ?_⟩
  simp only [List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  omega

theorem nodup_leakRowsQ {N B : ℕ} (hB : B ≤ N) : (leakRowsQ N B).Nodup := by
  refine List.nodup_append.2 ⟨(List.nodup_range).map fun a b h => by omega,
    (List.nodup_range).map fun a b h => by omega, ?_⟩
  simp only [List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  omega

/-- **The index bridge** `∑_{k ∈ headF N} f k = ∑_{j < 2N+1} f (j − N)` (as the list `idx N`). -/
theorem sum_headF_eq_list {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℤ → R) :
    ∑ k ∈ headF N, f k = ((idx N).map f).sum :=
  sum_eq_list (nodup_idx N) (fun _ => by rw [Finset.mem_Icc, mem_idx]) f

/-- The band columns of the head `|n| ≤ N` and the band `|b| ≤ B`: `N < |k| ≤ N + B`. -/
theorem mem_leakCols_iff (N B : ℕ) (k : ℤ) :
    k ∈ leakCols (headF N) (headF B) ↔ k ∈ leakColsQ N B := by
  simp only [mem_leakCols, mem_leakColsQ, Finset.mem_Icc]
  constructor
  · rintro ⟨hk, n, hn, hb⟩
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h
    · exact ⟨-(N : ℤ), by omega, by omega⟩
    · exact ⟨(N : ℤ), by omega, by omega⟩

/-- The boundary rows of the head `|n| ≤ N` and the band `|b| ≤ B ≤ N`: `N − B < |n| ≤ N`. -/
theorem mem_leakRows_iff {N B : ℕ} (hB : B ≤ N) (n : ℤ) :
    n ∈ leakRows (headF N) (headF B) ↔ n ∈ leakRowsQ N B := by
  simp only [leakRows, Finset.mem_filter, mem_leakRowsQ, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, b, hb, hnb⟩
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h
    · exact ⟨(B : ℤ), by omega, by omega⟩
    · exact ⟨-(B : ℤ), by omega, by omega⟩

theorem leakCols_eq (N B : ℕ) : leakCols (headF N) (headF B) = (leakColsQ N B).toFinset :=
  Finset.ext fun k => by rw [List.mem_toFinset]; exact mem_leakCols_iff N B k

theorem leakRows_eq {N B : ℕ} (hB : B ≤ N) :
    leakRows (headF N) (headF B) = (leakRowsQ N B).toFinset :=
  Finset.ext fun n => by rw [List.mem_toFinset]; exact mem_leakRows_iff hB n

/-- The residual support `F ∪ (F + F) = {|n| ≤ 2N}` of the head `F = headF N`. -/
theorem mem_support_iff (N : ℕ) (n : ℤ) :
    n ∈ headF N ∪ (headF N).image₂ (· + ·) (headF N) ↔ n ∈ idx2 N := by
  rw [mem_idx2, Finset.mem_union, Finset.mem_image₂, Finset.mem_Icc]
  constructor
  · rintro (h | ⟨a, ha, b, hb, rfl⟩)
    · omega
    · rw [Finset.mem_Icc] at ha hb
      omega
  · intro h
    by_cases h' : -(N : ℤ) ≤ n ∧ n ≤ N
    · exact Or.inl h'
    · right
      rcases le_or_gt n 0 with hn | hn
      · exact ⟨-(N : ℤ), Finset.mem_Icc.2 (by omega), n + N, Finset.mem_Icc.2 (by omega), by ring⟩
      · exact ⟨(N : ℤ), Finset.mem_Icc.2 (by omega), n - N, Finset.mem_Icc.2 (by omega), by ring⟩

/-- Chunk coverage for folds: the fold over the covered list is at most the sum of the chunk
bounds. -/
theorem qsum_le_of_parts {ps : List (List ℤ × ℚ)} {l : List ℤ} (h : l = (ps.map Prod.fst).flatten)
    {f : ℤ → ℚ} (hp : ∀ p ∈ ps, qsum p.1 f ≤ p.2) : qsum l f ≤ (ps.map Prod.snd).sum := by
  rw [h, qsum_flatten, List.map_map]
  exact List.sum_le_sum hp

end Bridges

/-! ### D. The leaf as complex objects -/

namespace QuadFourierLeafQ

variable (L : QuadFourierLeafQ)

section Objects

variable (ν : PosReal)

/-- **The candidate** `ā = J_F (ā_n)` on the head `|n| ≤ N`. -/
def abar : X₂ ℂ ν := headOfRaw (headF L.N) fun n => toC (L.abarQ n)

theorem abar_supp : ∀ k ∉ headF L.N, coeff (L.abar ν) k = 0 := fun k hk => by
  rw [abar, coeff_headOfRaw, ite_eq_right hk]

/-- **The head matrix** as a bounded operator (a finite matrix on `headF N`). -/
def Mop : X₂ ℂ ν →L[ℂ] X₂ ℂ ν :=
  finMatrixCLM (E := geomFiberZ ℂ ν) (p := 2) (headF L.N) fun i j => toC (L.MQ i j)

/-- `P M = M` by construction (no computation). -/
theorem hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) (headF L.N) ∘L L.Mop ν = L.Mop ν :=
  headProj_comp_finMatrixCLM _ _

end Objects

section Data

variable {ν : PosReal}

theorem abarQ_eq_zero {n : ℤ} (hn : n ∉ headF L.N) : L.abarQ n = (0, 0) := by
  rw [abarQ, ite_eq_right fun h => hn (Finset.mem_Icc.2 h)]

theorem coeff_abar (n : ℤ) : coeff (L.abar ν) n = toC (L.abarQ n) := by
  rw [abar, coeff_headOfRaw]
  split_ifs with h
  · rfl
  · rw [L.abarQ_eq_zero h, toC_zero]

theorem MQ_eq_zero {i j : ℤ} (h : ¬(i ∈ headF L.N ∧ j ∈ headF L.N)) : L.MQ i j = (0, 0) := by
  rw [MQ, ite_eq_right fun h' => h ⟨Finset.mem_Icc.2 h'.1, Finset.mem_Icc.2 h'.2⟩]

/-- **The matrix of `M`** is the mirror (every `i`, `j`; `0` off the head block on both sides). -/
theorem matrixOf_Mop (i j : ℤ) : matrixOf (L.Mop ν) i j = toC (L.MQ i j) := by
  rw [Mop, matrixOf_finMatrixCLM]
  split_ifs with h
  · rfl
  · rw [L.MQ_eq_zero h, toC_zero]

theorem convCoeff_abar (n : ℤ) : convCoeff (L.abar ν) (L.abar ν) n = toC (L.convQ n) := by
  rw [convCoeff_eq_sum (headF L.N) (L.abar_supp ν) (L.abar ν) n, convQ, toC_csum,
    sum_headF_eq_list]
  simp only [L.coeff_abar, toC_cmul]

/-- The raw Fourier map at the candidate is the mirror residual. -/
theorem rawF_abar {μ : ℤ → ℂ} (hμ : ∀ n, μ n = toC (L.muQ n)) {g : X₂ ℂ ν}
    (hg : ∀ n, coeff g n = toC (L.forcQ n)) (j : ℤ) :
    rawF μ g (L.abar ν) j = toC (L.residQ j) := by
  rw [rawF, hμ, L.coeff_abar, L.convCoeff_abar, hg, residQ, toC_csub, toC_csub, toC_cmul]

/-- **The band of `β = 2ā`**: `rawSymbol β l = 0` for `|l| > B` (the support clause). -/
theorem band_beta (hL : L.Checks) :
    ∀ l ∉ headF L.B, rawSymbol (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)) l = 0 :=
  fun l hl => by
    simp only [rawSymbol_betaOf, L.coeff_abar]
    by_cases h : l ∈ idx L.N
    · have hB : (L.B : ℤ) < |l| := lt_abs.2 (by rw [Finset.mem_Icc] at hl; omega)
      rw [hL.2.1 l h hB, toC_zero, mul_zero]
    · rw [L.abarQ_eq_zero fun h' => h (mem_idx.2 (Finset.mem_Icc.1 h')), toC_zero, mul_zero]

/-- **The composed leakage kernel** is the mirror `K_M` (every `i`, `k`; `B ≤ N`). -/
theorem composedLeakKernel_eq (hB : L.B ≤ L.N) (i k : ℤ) :
    composedLeakKernel (L.Mop ν) (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)) (headF L.N)
      (headF L.B) i k = toC (L.KMQ i k) := by
  rw [composedLeakKernel, KMQ, toC_csum, leakRows_eq hB, List.sum_toFinset _ (nodup_leakRowsQ hB)]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  rw [L.matrixOf_Mop, toC_cmul, toC_cscale]
  simp only [rawSymbol_betaOf, L.coeff_abar]
  push_cast
  ring

/-- **The symbol norm** `‖β‖ = ∑ 2 ‖ā_k‖ ν^{|k|} ≤ betaQ` (UPPER through `|Re| + |Im|`). -/
theorem norm_beta_le (hν : (ν : ℝ) = L.nuQ) :
    ‖betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)‖ ≤ (L.betaQ : ℝ) := by
  rw [norm_symbol_eq, tsum_eq_sum (s := headF L.N) fun l hl => by
      simp only [rawSymbol_betaOf, L.abar_supp ν l hl, mul_zero, norm_zero, zero_mul],
    betaQ, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [rawSymbol_betaOf]
  simp only [L.coeff_abar, norm_mul, Complex.norm_two, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    ← hν]
  gcongr
  all_goals first | exact norm_le_reim _ | exact pow_nonneg ν.coe_pos.le _

/-- **Reality of the candidate** `R ā = ā` (the reality clause). -/
theorem conjRefl_abar (hL : L.Checks) : conjRefl (L.abar ν) = L.abar ν :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjRefl, L.coeff_abar, L.coeff_abar]
    by_cases h : n ∈ idx L.N
    · have hn : -n ∈ idx L.N := mem_idx.2 (by have := mem_idx.1 h; omega)
      have e := hL.2.2.1 (-n) hn
      rw [neg_neg] at e
      rw [e, toC_cconj]
    · have hn : -n ∉ headF L.N := fun h' =>
        h (mem_idx.2 (by have := Finset.mem_Icc.1 h'; omega))
      rw [L.abarQ_eq_zero hn, L.abarQ_eq_zero fun h' => h (mem_idx.2 (Finset.mem_Icc.1 h')),
        toC_zero, map_zero]

variable [Fact (1 ≤ (ν : ℝ))]

/-- **The coefficients of `G ā`** are the mirror `GQ` (the coefficient identity `coeff_G`, with
the forcing support and the nonvanishing tail symbol). -/
theorem coeff_G_abar_eq {μ : ℤ → ℂ} (hμ : ∀ n, μ n = toC (L.muQ n)) {g : X₂ ℂ ν}
    (hg : ∀ n, coeff g n = toC (L.forcQ n)) (hgs : ∀ k ∉ headF L.N, coeff g k = 0)
    (hμ0 : ∀ k ∉ headF L.N, μ k ≠ 0)
    (hs : Summable fun k => ‖tailSymbol ((headF L.N : Finset ℤ) : Set ℤ) μ k‖ ^ 2) (n : ℤ) :
    coeff (G (headF L.N) μ hs (L.Mop ν) g (L.abar ν)) n = toC (L.GQ n) := by
  have h := congrFun (coeff_G (headF L.N) μ hs (L.Mop ν) g hgs hμ0 (L.abar ν)) n
  rw [h, rawA, Mop, coeff_finMatrixCLM, GQ]
  by_cases hn : n ∈ headF L.N
  · rw [ite_eq_left hn, ite_eq_left (Finset.mem_Icc.1 hn), tailSymbol_of_mem (Finset.mem_coe.2 hn),
      zero_mul, add_zero, toC_csum, ← sum_headF_eq_list]
    exact Finset.sum_congr rfl fun j hj => by
      rw [coeff_headOfRaw, ite_eq_left hj, L.rawF_abar hμ hg, toC_cmul]
  · rw [ite_eq_right hn, ite_eq_right fun h' => hn (Finset.mem_Icc.2 h'),
      tailSymbol_of_notMem fun h' => hn (Finset.mem_coe.1 h'), zero_add, L.rawF_abar hμ hg,
      hμ, toC_cmul, toC_cinv]

/-- The Jacobian block `K_H` has the mirror matrix `DF` on the head block. -/
theorem matrixOf_Kh {μ : ℤ → ℂ} (hμ : ∀ n, μ n = toC (L.muQ n)) {n j : ℤ} (hn : n ∈ headF L.N)
    (hj : j ∈ headF L.N) :
    matrixOf (Kh (headF L.N) μ (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν))) n j =
      toC (L.DFQ n j) := by
  rw [Kh, matrixOf_sub, LamH, matrixOf_diagCLM, matrixOf_headProj_symbolAction_headProj,
    ite_eq_left (show n ∈ headF L.N ∧ j ∈ headF L.N from ⟨hn, hj⟩), DFQ, toC_csub, toC_cscale]
  simp only [rawSymbol_betaOf, L.coeff_abar, headSym]
  by_cases h : n = j
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left hn, hμ]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h, toC_zero]
    push_cast
    ring

/-- **The `Z₀` matrix** `P − M K_H` on the head block is the mirror `E = I − M DF`. -/
theorem matrixOf_Z0op_eq {μ : ℤ → ℂ} (hμ : ∀ n, μ n = toC (L.muQ n)) (i j : ℤ)
    (hi : i ∈ headF L.N) (hj : j ∈ headF L.N) :
    matrixOf (headProj (headF L.N) - L.Mop ν ∘L Kh (headF L.N) μ
      (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν))) i j = toC (L.EQ i j) := by
  have h₂ : ∀ x, ∀ n ∉ headF L.N,
      coeff (Kh (headF L.N) μ (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)) x) n = 0 :=
    fun x n hn => by
      rw [← headProj_comp_Kh (headF L.N) μ (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)),
        ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hn]
  rw [matrixOf_sub, matrixOf_headProj, matrixOf_comp_of_support (L.Mop ν) _ h₂, EQ, toC_csub,
    toC_csum, ← sum_headF_eq_list]
  congr 1
  · by_cases h : i = j
    · rw [ite_eq_left ⟨h, hi⟩, ite_eq_left h]
      exact Complex.ext (by simp) (by simp)
    · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h, toC_zero]
  · exact Finset.sum_congr rfl fun n hn => by rw [L.matrixOf_Mop, L.matrixOf_Kh hμ hn hj, toC_cmul]

end Data

/-! ### E. The bounds, the certificate and its soundness -/

section Bounds

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

private theorem Y0_le (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) {μ : ℤ → ℂ}
    (hμ : ∀ n, μ n = toC (L.muQ n)) {g : X₂ ℂ ν} (hg : ∀ n, coeff g n = toC (L.forcQ n))
    (hgs : ∀ k ∉ headF L.N, coeff g k = 0) (hμ0 : ∀ k ∉ headF L.N, μ k ≠ 0)
    (hs : Summable fun k => ‖tailSymbol ((headF L.N : Finset ℤ) : Set ℤ) μ k‖ ^ 2) :
    ‖G (headF L.N) μ hs (L.Mop ν) g (L.abar ν)‖ ≤ (L.Y0c : ℝ) := by
  have hval : ‖G (headF L.N) μ hs (L.Mop ν) g (L.abar ν)‖ ^ 2 =
      ((qsum (idx2 L.N) L.y0Term : ℚ) : ℝ) := by
    rw [norm_sq_G_abar (headF L.N) μ hs (L.Mop ν) g (L.hPM ν) (L.abar_supp ν),
      sum_eq_list (nodup_idx2 L.N) (mem_support_iff L.N), cast_qsum]
    congr 1
    refine List.map_congr_left fun n _ => ?_
    rw [L.coeff_G_abar_eq hμ hg hgs hμ0 hs, sq_norm_toC, y0Term, Rat.cast_mul, Rat.cast_pow, hν]
  have hle : ((qsum (idx2 L.N) L.y0Term : ℚ) : ℝ) ≤ (L.Y0c : ℝ) ^ 2 := by
    exact_mod_cast (qsum_le_of_parts hL.2.2.2.1 hC.1).trans hL.2.2.2.2.2.2.2.1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by exact_mod_cast hL.2.2.2.2.2.2.2.2.2.2.2.1)
    two_ne_zero).1 (hval.trans_le hle)

private theorem Z0_le (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) {μ : ℤ → ℂ}
    (hμ : ∀ n, μ n = toC (L.muQ n)) :
    ‖headProj (headF L.N) - L.Mop ν ∘L Kh (headF L.N) μ
      (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν))‖ ≤ (L.Z0c : ℝ) := by
  obtain ⟨-, -, -, -, -, hcR, -, -, hZ0, -, -, -, hZ0c, -, -, hRz, hCz, -, -⟩ := hL
  have hrow := hcR ▸ List.forall_mem_flatten.2 hC.2.1
  have hcol := hcR ▸ List.forall_mem_flatten.2 hC.2.2.1
  refine (norm_le_sqrt_of_block _ (block_one_sub_B0 (headF L.N) μ (L.Mop ν) (L.hPM ν) _)
    (R := (L.RzC : ℝ)) (C := (L.CzC : ℝ)) (by exact_mod_cast hRz) (by exact_mod_cast hCz) ?_
    ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (L.z0RowQ i : ℝ) ≤ L.RzC by
      exact_mod_cast hrow i (mem_idx.2 (Finset.mem_Icc.1 hi)))
    rw [z0RowQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [schurEntry, L.matrixOf_Z0op_eq hμ i j hi hj, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim hν _ i j
  · intro j hj
    refine le_trans ?_ (show (L.z0ColQ j : ℝ) ≤ L.CzC by
      exact_mod_cast hcol j (mem_idx.2 (Finset.mem_Icc.1 hj)))
    rw [z0ColQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [schurEntry, L.matrixOf_Z0op_eq hμ i j hi hj, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim hν _ i j
  · exact (Real.sqrt_le_sqrt (show (L.RzC : ℝ) * L.CzC ≤ (L.Z0c : ℝ) ^ 2 by
      exact_mod_cast hZ0)).trans_eq (Real.sqrt_sq (by exact_mod_cast hZ0c))

private theorem H_le (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) :
    ‖L.Mop ν ∘L headProj (headF L.N) ∘L
      symbolAction₀ (p := 2) RadiiPolynomial.WeightedLp.Fourier.moderate_geomFiberZ
        (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)) ∘L tailProj (headF L.N)‖ ≤
      √((L.RmC : ℝ) * L.CmC) := by
  obtain ⟨hB, -, -, -, -, hcR, hcC, -, -, -, -, -, -, -, -, -, -, hRm, hCm⟩ := id hL
  have hrow := hcR ▸ List.forall_mem_flatten.2 hC.2.2.2.1
  have hcol := hcC ▸ List.forall_mem_flatten.2 hC.2.2.2.2.1
  refine norm_head_term_le_composed RadiiPolynomial.WeightedLp.Fourier.moderate_geomFiberZ
    (betaOf (headF L.N) (L.abar ν) (L.abar_supp ν)) (headF L.N) (headF L.B) (L.Mop ν)
    (L.band_beta hL) (L.hPM ν) (by exact_mod_cast hRm) (by exact_mod_cast hCm) ?_ ?_
  · intro i hi
    refine le_trans ?_ (show (L.kmRowQ i : ℝ) ≤ L.RmC by
      exact_mod_cast hrow i (mem_idx.2 (Finset.mem_Icc.1 hi)))
    rw [kmRowQ, cast_qsum, ← List.sum_toFinset _ (nodup_leakColsQ _ _), ← leakCols_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [L.composedLeakKernel_eq hB, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim hν _ i k
  · intro k hk
    refine le_trans ?_ (show (L.kmColQ k : ℝ) ≤ L.CmC by
      exact_mod_cast hcol k ((mem_leakCols_iff _ _ k).1 hk))
    rw [kmColQ, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [L.composedLeakKernel_eq hB, geomFiberZ_weight, geomFiberZ_weight]
    exact weighted_le_reim hν _ i k

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem U_le (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) :
    ‖L.Mop ν ∘L headReal (headF L.N)‖ ≤ √((((L.uParts.map Prod.snd).sum : ℚ) : ℝ)) := by
  refine (norm_comp_headReal_le_urow (headF L.N) (L.Mop ν) (L.hPM ν)).trans (Real.sqrt_le_sqrt ?_)
  have hsum : ((qsum (idx L.N) fun i => L.urowRowQ i ^ 2 : ℚ) : ℝ) =
      ∑ i ∈ headF L.N, ((L.urowRowQ i : ℚ) : ℝ) ^ 2 := by
    rw [cast_qsum, sum_headF_eq_list]
    simp only [Rat.cast_pow]
  refine le_trans ?_ (show ((qsum (idx L.N) fun i => L.urowRowQ i ^ 2 : ℚ) : ℝ) ≤
      (((L.uParts.map Prod.snd).sum : ℚ) : ℝ) by
    exact_mod_cast qsum_le_of_parts hL.2.2.2.2.1 hC.2.2.2.2.2)
  rw [hsum]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg ν.2.le _)) (pow_nonneg ν.2.le _)) ?_ 2
  rw [urowRowQ, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [L.matrixOf_Mop]
  exact weighted_le_reim hν _ i j

omit [Fact (1 ≤ (ν : ℝ))] in
private theorem uParts_sum_nonneg (hL : L.Checks) (hC : L.ChunkChecks) :
    (0 : ℝ) ≤ (((L.uParts.map Prod.snd).sum : ℚ) : ℝ) := by
  have h := qsum_le_of_parts hL.2.2.2.2.1 hC.2.2.2.2.2
  have h0 : (0 : ℚ) ≤ qsum (idx L.N) fun i => L.urowRowQ i ^ 2 := by
    rw [qsum_eq_sum]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact sq_nonneg _
  exact_mod_cast h0.trans h

/-- **The certificate of the leaf**: the candidate `L.abar ν`, the head matrix `L.Mop ν`, the
numbers `Z₀ = Z0c`, `H = √(RmC CmC)`, `U = √(∑ U_row² bounds)` and their operator bounds, under
the leaf obligations and the bridges `ν = nuQ`, `μ = toC ∘ muQ`. -/
def cert (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) {μ : ℤ → ℂ}
    (hμ : ∀ n, μ n = toC (L.muQ n)) : Cert (headF L.N) μ ν where
  abar := L.abar ν
  M := L.Mop ν
  Z₀ := L.Z0c
  H := √((L.RmC : ℝ) * L.CmC)
  U := √((((L.uParts.map Prod.snd).sum : ℚ) : ℝ))
  abar_supp := L.abar_supp ν
  hPM := L.hPM ν
  hZ₀ := L.Z0_le hL hC hν hμ
  hH := L.H_le hL hC hν
  hU := L.U_le hL hC hν

/-- **THE SOUNDNESS THEOREM of the adapter**: under the leaf obligations, the bridges `ν = nuQ`,
`μ = toC ∘ muQ`, `coeff g = toC ∘ forcQ`, the forcing support, the nonvanishing tail symbol and
its square summability, the certificate `L.cert` satisfies the `Y₀` bound `‖G ā‖ ≤ Y0c`, the
squared `Z₁` inequality `H² + (‖β‖ / x)² ≤ Z1c²` for every tail factor `x` with
`(x²)⁻¹ ≤ tailInvSqQ`, the squared `Z₂` inequality `4 (U² + t2Q) ≤ Z2c²`, and `0 ≤ Z1c`,
`0 ≤ Z2c`: the bound hypotheses of the family's existence theorems at `T2 = t2Q`. -/
theorem cert_spec (hL : L.Checks) (hC : L.ChunkChecks) (hν : (ν : ℝ) = L.nuQ) {μ : ℤ → ℂ}
    (hμ : ∀ n, μ n = toC (L.muQ n)) {g : X₂ ℂ ν} (hg : ∀ n, coeff g n = toC (L.forcQ n))
    (hgs : ∀ k ∉ headF L.N, coeff g k = 0) (hμ0 : ∀ k ∉ headF L.N, μ k ≠ 0)
    (hs : Summable fun k => ‖tailSymbol ((headF L.N : Finset ℤ) : Set ℤ) μ k‖ ^ 2) :
    ‖G (headF L.N) μ hs (L.cert hL hC hν hμ).M g (L.cert hL hC hν hμ).abar‖ ≤ (L.Y0c : ℝ) ∧
      (∀ x : ℝ, (x ^ 2)⁻¹ ≤ (L.tailInvSqQ : ℝ) →
        (L.cert hL hC hν hμ).H ^ 2 + (‖betaOf (headF L.N) (L.cert hL hC hν hμ).abar
          (L.cert hL hC hν hμ).abar_supp‖ / x) ^ 2 ≤ (L.Z1c : ℝ) ^ 2) ∧
      4 * ((L.cert hL hC hν hμ).U ^ 2 + (L.t2Q : ℝ)) ≤ (L.Z2c : ℝ) ^ 2 ∧
      (0 : ℝ) ≤ L.Z1c ∧ (0 : ℝ) ≤ L.Z2c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, hZ2, -, -, hZ1c, hZ2c, -, -, hRm, hCm⟩ := id hL
  refine ⟨L.Y0_le hL hC hν hμ hg hgs hμ0 hs, fun x hx => ?_, ?_, by exact_mod_cast hZ1c,
    by exact_mod_cast hZ2c⟩
  · have hH : (L.cert hL hC hν hμ).H ^ 2 = (L.RmC : ℝ) * L.CmC :=
      Real.sq_sqrt (mul_nonneg (by exact_mod_cast hRm) (by exact_mod_cast hCm))
    have hβ : ‖betaOf (headF L.N) (L.cert hL hC hν hμ).abar (L.cert hL hC hν hμ).abar_supp‖ ^ 2 ≤
        (L.betaQ : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (L.norm_beta_le hν) 2
    have hc : ((L.RmC * L.CmC + L.betaQ ^ 2 * L.tailInvSqQ : ℚ) : ℝ) ≤ ((L.Z1c ^ 2 : ℚ) : ℝ) :=
      Rat.cast_le.2 hZ1
    push_cast at hc
    have hm := mul_le_mul hβ hx (inv_nonneg.2 (sq_nonneg x)) (sq_nonneg _)
    rw [hH, div_pow, div_eq_mul_inv]
    linarith
  · rw [show (L.cert hL hC hν hμ).U ^ 2 = (((L.uParts.map Prod.snd).sum : ℚ) : ℝ) from
      Real.sq_sqrt (L.uParts_sum_nonneg hL hC)]
    exact_mod_cast hZ2

end Bounds

end QuadFourierLeafQ

end

end RadiiPolynomial.Certification.Fourier.Quadratic
