import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reality
import RadiiPolynomial.Core.Quadratic
import RadiiPolynomial.Core.Transport

/-!
# The quadratic Fourier family on `ℓ²`

The family is the raw Fourier coefficient map of a semilinear quadratic periodic equation with
symbol `μ`, square nonlinearity and forcing `g`:
`rawF μ g a n = μₙ aₙ − (a ⋆ a)ₙ − gₙ`.
Its scope is the bilateral geometric complex carrier `X = X₂ ℂ ν = ℓ²_m(ℤ; ℂ)`
(`m_k = ν ^ |k|`; the moderate-weight services assume `ν ≥ 1`) with an arbitrary symbol
`μ : ℤ → ℂ`, a finite head `F : Finset ℤ`, a forcing `g : X` and an approximate head inverse
`M : X →L[ℂ] X`. It is not an API for every exponent, weight, scalar field or polynomial degree.
The consumers are the book §10.1 Helmholtz–Duffing family (`Applications/Fourier/Duffing.lean`,
`μₙ = −n² + i c₁ n + c₂`, with its examples `Examples/Fourier/Duffing/`) and the forced Riccati
equation (`Examples/Fourier/Riccati/Certificate.lean`, `μₙ = 1 + i n`).

## The maps

With projections `P = headProj F`, `Q = tailProj F`, the square-summable tail symbol
`d = tailSymbol ↑F μ` (hypothesis `hs`), the finite-head diagonal `Λ_H = headDiag F μ`, the head
realization `H_F = headReal F` and the cross-exponent tail diagonal `T∞ = tailInf ↑F μ hs`:
* `rawF μ g a : ℤ → ℂ` is a RAW coefficient family (no typed codomain; it need not lie in
  `ℓ^∞_m`), and so is the raw preconditioner `rawA F μ M f n = coeff (M (headOfRaw F f)) n + dₙ fₙ`;
* `G(a) = M (Λ_H a − H_F (a ⋆ a) − g) + Q a − T∞ (a ⋆ a)` is the BOUNDED preconditioned residual,
  a self-map of `X`; its Newton map is `a ↦ a − G a`. It is the canonical quadratic map of
  `Core/Quadratic.lean` (`G_eq`), with derivative `DG(a) = M Λ_H + Q − 2 • quadCLM A_Y a`,
  `A_Y = M H_F + T∞` (`DG_eq`);
* the coefficient identity `coeff (G a) = rawA (rawF a)` (`coeff_G`) is the statement relating
  them (support `supp g ⊆ F`, `μₙ ≠ 0` off `F`); the typed composition `G = A_Y ∘ F_raw` is not
  written.

## The services

* **Centre and defect.** At a candidate `ā` supported in `F`, with `β = 2ā ∈ ℓ¹_m` (`betaOf`),
  the head block `K_H = Λ_H − P L_β P = headBlock F μ L_β` (on the head range, the finite
  Jacobian of the book's truncation (10.3) at `β = 2ā`) and `B₀ = M K_H + Q = blockMap F μ L_β M`
  (`Operators/FiniteBlock.lean`), the defect is the tail defect of
  `Operators/TailDefect.lean`: `DG(ā) − B₀ = −(M P L_β Q + T₂ L_β)` (`DG_sub_B0`).
* **The four bound faces.** `Y₀`: the exact finite residual
  `‖G ā‖² = ∑_{n ∈ F ∪ (F + F)} ‖coeff (G ā) n‖² ν^{2|n|}` (`norm_sq_G_abar`; the head range of
  `M` confines `M g`, no support of `g` is assumed); `Z₀`: `I − B₀ = P − M K_H` lives on the
  block `F × F` (`headProj_comp_id_sub_blockMap_comp_headProj`); `Z₁`: the tail-defect bound
  (`norm_DG_sub_B0_le`, UPPER);
  `Z₂`: the symmetrized bilinear norm is at most `2 √(U² + T2)`
  (`norm_quadComp_add_flip_le_of_bounds` with the weight-generic `U_row` head certificate
  `Bilateral.norm_comp_headReal_le_urow`, UPPER).
* **The head certificate.** `Cert F μ ν` packages a candidate supported in `F`, a head matrix
  with `P M = M` and the three head numbers `Z₀`, `H`, `U` with their operator bounds; the forcing,
  tail and radius hypotheses stay with the consuming theorem.
* **Existence and transfer of zeros.** One application of `quadratic_radii_theorem_local`
  (`A = id`, `A† = B₀`) gives a unique zero of `G` in the ball (`existsUnique_G`). The radii
  inequality gives `‖P − M K_H‖ < 1`, so `M` is injective on the finite-dimensional head range
  (`WeightedLp.eq_zero_of_headProj_eq_of_norm_lt_one`, from `P K_H = K_H`): this is HEAD
  injectivity, not injectivity of the nonlinear `rawF`. With `P M = M`, `supp g ⊆ F` and
  `μₙ ≠ 0` off `F`, the coefficient identity `coeff_G` is a finite-head / diagonal-tail solver
  identity with `d = tailSymbol ↑F μ`, so zeros of `G` are exactly the raw zeros
  (`WeightedLp.eq_zero_iff_of_coeff_eq_headSolve`), and the unique zero of `G` transports to a
  unique raw zero in the ball (`existsUnique_rawF`, through `existsUnique_zero_transport` at the
  identity isometry).
* **Conjugate reflection and reflection.** `(R a)ₙ = conj (a₋ₙ)` (`conjRefl`, any positive `ν`;
  the geometric specialization of `WeightedLp.conjReflL`) is an additive isometry of `X`
  (`isometry_conjRefl`; a real structure, not a complex-linear map), and
  `(R a ⋆ R a)ₙ = conj ((a ⋆ a)₋ₙ)` (`convCoeff_conjRefl`, the diagonal square identity). The raw
  map is `R`-equivariant, `F(R a)ₙ = conj (F(a)₋ₙ)`, for a conjugate-symmetric symbol and forcing
  (`rawF_conjRefl`), and equivariant under the plain reflection `refl` of `WeightedLp.Bilateral`,
  `F(refl a)ₙ = F(a)₋ₙ`, for an even symbol and forcing (`rawF_refl`). The symmetry of a
  particular symbol and forcing is the consumer's hypothesis.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.Fourier.Quadratic

open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.WeightedLp.Bilateral

/-- The moderate constant `C = 1` of the geometric carrier weight against itself (`ν ≥ 1`). -/
local notation "hC" => Fourier.moderate_geomFiberZ

/-! ### A. The maps and the coefficient identity -/

section Maps

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- **The bounded self-map** `G(a) = M (Λ_H a − H_F (a ⋆ a) − g) + Q a − T∞ (a ⋆ a)`. -/
def G (a : X₂ ℂ ν) : X₂ ℂ ν :=
  M (headDiag F μ a - headReal F (prodCLM (geomSubmul ν) a a) - g) + tailProj (𝕜 := ℂ) F a -
    tailInf (F : Set ℤ) μ hs (prodCLM (geomSubmul ν) a a)

/-- `G` is the canonical quadratic map, with bilinear part `-quadCLM A_Y`. -/
theorem G_eq (a : X₂ ℂ ν) :
    G F μ hs M g a = quadMap (-M g)
      (M ∘L headDiag F μ + tailProj (𝕜 := ℂ) F)
      (-quadCLM (AY F M (F : Set ℤ) μ hs)) a := by
  simp only [G, quadMap, quadCLM_apply, AY, add_apply, ContinuousLinearMap.comp_apply,
    neg_apply, map_sub]
  abel

/-- The derivative in the symmetric product representation used by the head defect. -/
def DG (a : X₂ ℂ ν) : X₂ ℂ ν →L[ℂ] X₂ ℂ ν :=
  M ∘L headDiag F μ + tailProj (𝕜 := ℂ) F - (2 : ℂ) • quadCLM (AY F M (F : Set ℤ) μ hs) a

/-- The derivative expression agrees with the canonical quadratic derivative. -/
theorem DG_eq (a : X₂ ℂ ν) : DG F μ hs M a =
    quadDeriv (M ∘L headDiag F μ + tailProj (𝕜 := ℂ) F)
      (-quadCLM (AY F M (F : Set ℤ) μ hs)) a := by
  ext h
  simp only [DG, quadDeriv, sub_apply, smul_apply, two_smul, add_apply,
    neg_apply, ContinuousLinearMap.flip_apply]
  rw [quadCLM_comm _ h a]
  abel_nf

/-- **The raw Fourier map** `F_raw(a)ₙ = μₙ aₙ − (a ⋆ a)ₙ − gₙ` (raw codomain, no typed space). -/
def rawF (a : X₂ ℂ ν) (n : ℤ) : ℂ := μ n * coeff a n - convCoeff a a n - coeff g n

omit [Fact (1 ≤ (ν : ℝ))] in
/-- A raw family restricted to the finite head is an element of `X₂ ℂ ν`. -/
theorem memℓp_headOfRaw (f : ℤ → ℂ) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ ℂ ν) k
      (if k ∈ F then f k else 0)) 2 :=
  memℓp_two_of_summable _ (summable_of_ne_finset_zero (s := F) fun k hk => by
    simp only [ite_eq_right hk, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul])

/-- **The head realization of a raw family**: the element with coefficients `1_F f`. -/
def headOfRaw (f : ℤ → ℂ) : X₂ ℂ ν :=
  ofCoeff (fun k => if k ∈ F then f k else 0) (memℓp_headOfRaw (ν := ν) F f)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The head realization in coordinates. -/
@[simp] theorem coeff_headOfRaw (f : ℤ → ℂ) (k : ℤ) :
    coeff (headOfRaw (ν := ν) F f) k = if k ∈ F then f k else 0 :=
  coeff_ofCoeff _ _ k

/-- **The raw preconditioner** `A_raw f = M (J_F f) + d f` (raw output). -/
def rawA (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  coeff (M (headOfRaw F f)) n + tailSymbol (F : Set ℤ) μ n * f n

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The raw product with a head-supported left factor is a finite sum. -/
theorem convCoeff_eq_sum {x : X₂ ℂ ν} (hx : ∀ k ∉ F, coeff x k = 0) (y : X₂ ℂ ν) (n : ℤ) :
    convCoeff x y n = ∑ j ∈ F, coeff x j * coeff y (n - j) :=
  tsum_eq_sum (s := F) fun j hj => by rw [hx j hj, zero_mul]

/-- **The coefficient identity** `coeff (G a) = A_raw (F_raw a)`: the head part
reads the forcing through `supp g ⊆ F`, the tail part inverts `μ` off `F`. -/
theorem coeff_G (hg : ∀ k ∉ F, coeff g k = 0) (hμ : ∀ k ∉ F, μ k ≠ 0) (a : X₂ ℂ ν) :
    coeff (G F μ hs M g a) = rawA F μ M (rawF μ g a) := by
  have hH : headOfRaw F (rawF μ g a) = headDiag F μ a - headReal F (prodCLM (geomSubmul ν) a a) - g :=
    ext_coeff <| funext fun k => by
      rw [coeff_headOfRaw, coeff_sub, coeff_sub, Pi.sub_apply, Pi.sub_apply, coeff_headDiag,
        coeff_headReal, coeff_prodCLM]
      by_cases hk : k ∈ F
      · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk, rawF]
      · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, hg k hk, sub_zero, sub_zero]
  funext n
  rw [rawA, hH]
  simp only [G, coeff_add, coeff_sub, Pi.add_apply, Pi.sub_apply, coeff_tailProj, coeff_tailInf,
    coeff_prodCLM]
  by_cases hn : n ∈ F
  · rw [ite_eq_left hn, tailSymbol_of_mem (Finset.mem_coe.2 hn), zero_mul, zero_mul, add_zero,
      sub_zero]
  · rw [ite_eq_right hn, tailSymbol_of_notMem (fun h => hn (Finset.mem_coe.1 h)), rawF, hg n hn,
      sub_zero, mul_sub, ← mul_assoc, inv_mul_cancel₀ (hμ n hn), one_mul, add_sub_assoc]

end Maps

/-! ### B. The centre and the defect identity -/

section Centre

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)


/-- **The derivative of the quadratic at the centre**: for `supp ā ⊆ F` and `β = 2ā`,
`2 • quadCLM A_Y ā = M P L_β + T₂ L_β` (the `β`-bridge and the bridges `H_F ι = P`, `T∞ ι = T₂`). -/
theorem two_smul_quadCLM_AY_abar {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) :
    (2 : ℂ) • quadCLM (AY F M (F : Set ℤ) μ hs) ā =
      M ∘L headProj (𝕜 := ℂ) F ∘L symbolAction₀ (p := 2) hC (betaOf F ā hā) +
        tailDiag (E := geomFiberZ ℂ ν) (p := 2) (F : Set ℤ) μ (bddAbove_of_summable_sq hs) ∘L
          symbolAction₀ (p := 2) hC (betaOf F ā hā) := by
  have hAι : AY F M (F : Set ℤ) μ hs ∘L incl =
      M ∘L headProj (𝕜 := ℂ) F + tailDiag (E := geomFiberZ ℂ ν) (p := 2) (F : Set ℤ) μ
        (bddAbove_of_summable_sq hs) := by
    rw [AY, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, headReal_comp_incl,
      tailInf_comp_incl]
  refine ContinuousLinearMap.ext fun h => ?_
  have e := DFunLike.congr_fun hAι (symbolAction₀ (p := 2) hC (betaOf F ā hā) h)
  rw [smul_apply, quadCLM_apply, ← map_smul,
    two_smul_prodCLM_eq_incl_symbolAction₀ F ā hā h]
  exact e

/-- **The defect identity** `DG(ā) − B₀ = −(M P L_β Q + T₂ L_β)`: the full shared-input
tail defect at a head-supported centre, with `L_β` supplied by the operator series. -/
theorem DG_sub_B0 {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) :
    DG F μ hs M ā - blockMap F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā)) M =
      -tailDefect hC (betaOf F ā hā) F M (tailSymbol (F : Set ℤ) μ)
        (bddAbove_of_summable_sq hs) := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [DG, two_smul_quadCLM_AY_abar F μ hs M hā, blockMap, headBlock, tailDefect, tailProj_eq_id_sub_headProj,
    tailDiag, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

end Centre

/-! ### C. The four bound faces -/

section Bounds

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- **The `Z₁` face** (UPPER): the tail-defect bound `norm_tailDefect_le` at the composed head
bound `H` and a tail bound `R` of the tail symbol (`C = 1`; `0 ≤ R` follows from `hR`). The two
defect terms share the input, so no exactness is claimed. -/
theorem norm_DG_sub_B0_le {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0)
    (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) {H R : ℝ}
    (hH : ‖M ∘L headProj (𝕜 := ℂ) F ∘L symbolAction₀ (p := 2) hC (betaOf F ā hā) ∘L tailProj (𝕜 := ℂ) F‖ ≤ H)
    (hR : ∀ k, ‖tailSymbol (F : Set ℤ) μ k‖ ≤ R) :
    ‖DG F μ hs M ā - blockMap F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā)) M‖ ≤
      √(H ^ 2 + (R * 1 * ‖betaOf F ā hā‖) ^ 2) := by
  rw [DG_sub_B0 F μ hs M hā, norm_neg]
  exact norm_tailDefect_le hC (betaOf F ā hā) F M (tailSymbol (F : Set ℤ) μ)
    (bddAbove_of_summable_sq hs) hPM (fun k hk => tailSymbol_of_mem (Finset.mem_coe.2 hk)) hH
    (norm_tail_term_le_of_bound hC (betaOf F ā hā) _ _ hR ((norm_nonneg _).trans (hR 0)))

/-- The curvature socket for the canonical quadratic map, from the geometry bounds. -/
theorem norm_quadComp_add_flip_le_of_bounds
    (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) {U T2 : ℝ}
    (hU : ‖M ∘L headReal F‖ ≤ U) (hT2 : ∑' k, ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2 ≤ T2) :
    ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ 2 * √(U ^ 2 + T2) := by
  refine (norm_quadComp_add_flip_le _ _).trans
    (mul_le_mul_of_nonneg_left ?_ zero_le_two)
  have hid : quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
      (-quadCLM (AY F M (F : Set ℤ) μ hs)) = -quadCLM (AY F M (F : Set ℤ) μ hs) := by
    ext z h
    rfl
  rw [hid, ContinuousLinearMap.opNorm_neg]
  exact (norm_quadCLM_le _).trans ((norm_AY_le_sqrt_tsum F M μ hs hPM).trans
    (Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hU 2) hT2)))

/-- **Finite support of the residual**: `G ā` vanishes off `F ∪ (F + F)` (`P M = M`,
`supp ā ⊆ F`). -/
theorem coeff_G_abar_eq_zero (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M)
    {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) {n : ℤ} (hn : n ∉ F ∪ F.image₂ (· + ·) F) :
    coeff (G F μ hs M g ā) n = 0 := by
  have hnF : n ∉ F := fun h => hn (Finset.mem_union_left _ h)
  have hconv : convCoeff ā ā n = 0 := by
    rw [convCoeff_eq_sum F hā]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hā (n - j) fun h => hn (Finset.mem_union_right _
      (Finset.mem_image₂.2 ⟨j, hj, n - j, h, by omega⟩)), mul_zero]
  simp only [G, coeff_add, coeff_sub, Pi.add_apply, Pi.sub_apply, coeff_tailProj, coeff_tailInf,
    coeff_prodCLM, hconv, mul_zero, ite_eq_right hnF, hā n hnF,
    coeff_eq_zero_of_headProj_comp F M hPM _ hnF, add_zero, sub_zero]

/-- **The `Y₀` face, exact**: `‖G ā‖² = ∑_{n ∈ F ∪ (F + F)} ‖coeff (G ā) n‖² ν^{2|n|}`, a finite
sum (the library-carrier norm law `norm_sq_X₂`). -/
theorem norm_sq_G_abar (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M)
    {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) :
    ‖G F μ hs M g ā‖ ^ 2 = ∑ n ∈ F ∪ F.image₂ (· + ·) F,
      ‖coeff (G F μ hs M g ā) n‖ ^ 2 * (ν : ℝ) ^ (2 * n.natAbs) := by
  rw [norm_sq_X₂, tsum_eq_sum fun n hn => by
    rw [coeff_G_abar_eq_zero F μ hs M g hPM hā hn, norm_zero, sq, zero_mul, zero_mul]]

end Bounds

/-! ### C′. The head certificate -/

section Certificate

/-- **The head certificate** (book Theorem 10.1.3's data, any finite head `F` and symbol `μ`):
the candidate `ā` supported in `F`, the head matrix `M` with `P M = M`, and the three numerical
head hypotheses `Z₀` (head block), `H` (composed leakage) and `U` (`U_row`). -/
structure Cert (F : Finset ℤ) (μ : ℤ → ℂ) (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] where
  /-- The candidate. -/
  abar : X₂ ℂ ν
  /-- The head matrix. -/
  M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν
  /-- The `Z₀` number. -/
  Z₀ : ℝ
  /-- The composed-leakage number of `Z₁`. -/
  H : ℝ
  /-- The `U_row` number of `Z₂`. -/
  U : ℝ
  abar_supp : ∀ k ∉ F, coeff abar k = 0
  hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M
  hZ₀ : ‖headProj F - M ∘L headBlock F μ (symbolAction₀ (p := 2) hC (betaOf F abar abar_supp))‖ ≤ Z₀
  hH : ‖M ∘L headProj F ∘L symbolAction₀ (p := 2) hC (betaOf F abar abar_supp) ∘L
    tailProj F‖ ≤ H
  hU : ‖M ∘L headReal F‖ ≤ U

end Certificate

/-! ### D. Existence and the transfer of zeros -/

section Existence

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- A unique zero of `G` from the canonical quadratic radii theorem. -/
theorem existsUnique_G {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀) (hY₀ : ‖G F μ hs M g ā‖ ≤ Y₀)
    (hZ₀ : ‖headProj (𝕜 := ℂ) F - M ∘L headBlock F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā))‖ ≤ Z₀)
    (hZ₁ : ‖DG F μ hs M ā - blockMap F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā)) M‖ ≤ Z₁)
    (hZ₂ : ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall ā r₀, G F μ hs M g a = 0 := by
  simp_rw [G_eq F μ hs M g] at hY₀ ⊢
  refine quadratic_radii_theorem_local
    (A := ContinuousLinearMap.id ℂ (X₂ ℂ ν))
    (A_dagger := blockMap F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā)) M) hr₀ hY₀ ?_ ?_ hZ₂ hrad
    fun _ _ h => h
  · rwa [ContinuousLinearMap.id_comp, id_sub_blockMap]
  · rwa [ContinuousLinearMap.id_comp, ← DG_eq, norm_sub_rev]

/-- **A unique raw zero of the Fourier map in the ball** (generic `F`, `μ`): the zero of `G` from
`existsUnique_G`, transferred through `Z₀ < 1` (from `p(r₀) < 0`): head injectivity
(`eq_zero_of_headProj_eq_of_norm_lt_one`), the raw-zero equivalence of the solver identity
`coeff_G` (`eq_zero_iff_of_coeff_eq_headSolve`) and `existsUnique_zero_transport` at the identity
isometry. -/
theorem existsUnique_rawF {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0)
    (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) (hg : ∀ k ∉ F, coeff g k = 0)
    (hμ : ∀ k ∉ F, μ k ≠ 0) {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ} (hr₀ : 0 < r₀) (hY₀ : ‖G F μ hs M g ā‖ ≤ Y₀)
    (hZ₀ : ‖headProj (𝕜 := ℂ) F - M ∘L headBlock F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā))‖ ≤ Z₀)
    (hZ₁ : ‖DG F μ hs M ā - blockMap F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā)) M‖ ≤ Z₁)
    (hZ₂ : ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall ā r₀, rawF μ g a = 0 := by
  have hlt : ‖headProj (𝕜 := ℂ) F - M ∘L headBlock F μ (symbolAction₀ (p := 2) hC (betaOf F ā hā))‖ <
      1 := by
    have hY0 : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
    have hZ10 : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁
    have hZ20 : 0 ≤ Z₂ := (ContinuousLinearMap.opNorm_nonneg _).trans hZ₂
    have h := general_radii_poly_neg_implies_Z_lt_one hY0 hr₀ hrad
    simp only [Z_bound_general] at h
    nlinarith [mul_nonneg hZ20 hr₀.le]
  have hinj := eq_zero_of_headProj_eq_of_norm_lt_one F
    (by rw [← ContinuousLinearMap.comp_assoc, headProj_comp_headBlock]) hlt
  refine existsUnique_zero_transport (IsometryEquiv.refl _) (fun a => ?_)
    (existsUnique_G F μ hs M g hā hr₀ hY₀ hZ₀ hZ₁ hZ₂ hrad)
  exact (eq_zero_iff_of_coeff_eq_headSolve F M (tailSymbol (F : Set ℤ) μ) (coeff_headOfRaw F)
    (by rw [← ContinuousLinearMap.comp_assoc, hPM]) hinj
    (fun k hk => tailSymbol_of_mem (Finset.mem_coe.2 hk))
    (fun k hk => by
      rw [tailSymbol_of_notMem (fun h => hk (Finset.mem_coe.1 h))]
      exact inv_ne_zero (hμ k hk))
    (fun a k => congrFun (coeff_G F μ hs M g hg hμ a) k) a).symm


end Existence

/-! ### E. Conjugate reflection -/

section Reality

variable {ν : PosReal}

/-- **The conjugate reflection** `(R a)ₙ = conj (a₋ₙ)`: the geometric specialization of the
conjugate reflection `conjReflL` of `WeightedLp`, at the symmetric weight `ν^|k|`
(`geomFiberZ_weight_neg`). -/
def conjRefl (a : X₂ ℂ ν) : X₂ ℂ ν :=
  conjReflL (geomFiberZ_weight_neg ν) a

/-- `R` in coordinates. -/
@[simp] theorem coeff_conjRefl (a : X₂ ℂ ν) (n : ℤ) :
    coeff (conjRefl a) n = starRingEnd ℂ (coeff a (-n)) :=
  coeff_conjReflL _ a n

/-- The product commutes with `R`: `(R a ⋆ R a)ₙ = conj ((a ⋆ a)₋ₙ)` (`Complex.conj_tsum` and the
reindex `j ↦ −j`). -/
theorem convCoeff_conjRefl (a : X₂ ℂ ν) (n : ℤ) :
    convCoeff (conjRefl a) (conjRefl a) n = starRingEnd ℂ (convCoeff a a (-n)) := by
  rw [convCoeff, convCoeff, Complex.conj_tsum]
  refine (tsum_congr fun j => ?_).trans
    ((Equiv.neg ℤ).tsum_eq fun j => starRingEnd ℂ (coeff a j * coeff a (-n - j)))
  rw [coeff_conjRefl, coeff_conjRefl, Equiv.neg_apply, map_mul,
    show -(n - j) = -n - -j by ring]

/-- **`R` is an isometry** of `X₂ ℂ ν`. -/
theorem isometry_conjRefl : Isometry (conjRefl : X₂ ℂ ν → X₂ ℂ ν) :=
  isometry_conjReflL _

/-- **Conjugate equivariance of the raw map**: a conjugate-symmetric symbol
`μ₋ₙ = conj μₙ` and forcing `g₋ₙ = conj gₙ` give `F(R a)ₙ = conj (F(a)₋ₙ)`. -/
theorem rawF_conjRefl {μ : ℤ → ℂ} {g : X₂ ℂ ν} (hμ : ∀ n, μ (-n) = starRingEnd ℂ (μ n))
    (hg : ∀ n, coeff g (-n) = starRingEnd ℂ (coeff g n)) (a : X₂ ℂ ν) (n : ℤ) :
    rawF μ g (conjRefl a) n = starRingEnd ℂ (rawF μ g a (-n)) := by
  rw [rawF, rawF, coeff_conjRefl, convCoeff_conjRefl, hμ, hg, map_sub, map_sub, map_mul,
    Complex.conj_conj, Complex.conj_conj]

/-- **Equivariance of the raw map under the reflection**: an even symbol `μ₋ₙ = μₙ` and an even
forcing `g₋ₙ = gₙ` give `F(refl a)ₙ = F(a)₋ₙ` (`refl` of `WeightedLp.Bilateral`). -/
theorem rawF_refl {μ : ℤ → ℂ} {g : X₂ ℂ ν} (hμ : ∀ n, μ (-n) = μ n)
    (hg : ∀ n, coeff g (-n) = coeff g n) (a : X₂ ℂ ν) (n : ℤ) :
    rawF μ g (refl a) n = rawF μ g a (-n) := by
  rw [rawF, rawF, coeff_refl, convCoeff_refl, hμ, hg]

end Reality

end RadiiPolynomial.Fourier.Quadratic

end
