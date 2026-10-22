import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Quadratic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock
import RadiiPolynomial.Examples.Fourier.Duffing.IkData
import RadiiPolynomial.Core.Quadratic

/-!
# The Fourier consumer on `ℓ²`: book §10.1 Helmholtz–Duffing

The equation `u'' + c₁ u' + c₂ u − u² = c₃ cos t` (book (10.1)) with the `2π`-periodic ansatz
`u = ∑ aₙ e^{int}` becomes the raw Fourier map (book §10.1, `F_n`)
`F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ`, `b_{±1} = 1/2`.
This file proves, on the bilateral geometric carrier `X = X₂ ℂ ν = ℓ²_m(ℤ; ℂ)`
(`m_k = ν ^ |k|`, `ν ≥ 1`), that every certificate whose four bounds satisfy the radii inequality
yields a unique zero of the raw Fourier map in the closed ball of radius `r₀` around the
candidate, and that this zero is conjugate-symmetric (`conj ã₋ₙ = ãₙ`) when the candidate is.

## The maps (generic finite head `F`, generic symbol `μ`)

For a finite head `F : Finset ℤ` with projections `P = headProj F`, `Q = tailProj F`, a symbol
`μ : ℤ → ℂ` with the square-summable tail symbol `d = tailSymbol ↑F μ`, a bounded `M` and a forcing
`g` supported in `F`, the bounded self-map is
`G(a) = M (Λ_H a − H_F (a ⋆ a) − g) + Q a − T∞ (a ⋆ a)`,
with the finite-head diagonal `Λ_H = LamH F μ`, the head realization `H_F = headReal F`, and the
cross-exponent tail diagonal `T∞ = tailInf ↑F μ hs`. Its derivative is
`DG(a) = M Λ_H + Q − 2 • quadCLM A_Y a` with `A_Y = M H_F + T∞`. The raw Fourier map is
the raw coefficient family `rawF μ g a n = μₙ aₙ − (a ⋆ a)ₙ − gₙ` (no typed codomain), and the
raw preconditioner is `rawA F μ M f n = coeff (M (headOfRaw F f)) n + dₙ fₙ`. The COEFFICIENT
identity `coeff (G a) = rawA (rawF a)` (`coeff_G`) is the statement; the typed composition
`G = A_Y ∘ F_raw` on all of `X` is not written (`F_raw a` need not lie in `ℓ^∞_m`).

## The centre and the four bounds

At a finitely supported candidate `ā` the symbol `β = 2ā` lies in `ℓ¹_m` (`betaOf`), and with
`K_H = Λ_H − P L_β P`, `B₀ = M K_H + Q` the defect is the tail defect of
`Operators/TailDefect.lean`:
`DG(ā) − B₀ = −(M P L_β Q + T₂ L_β)` (`DG_sub_B0`). The four bound faces are
* `Y₀`: the exact finite residual `‖G ā‖² = ∑_{n ∈ F ∪ (F + F)} ‖coeff (G ā) n‖² ν^{2|n|}`
  (`norm_sq_G_abar`);
* `Z₀`: `I − B₀ = P − M K_H` lives on the block `F × F` (`one_sub_B0`, `block_one_sub_B0`);
* `Z₁`: the tail-defect bound `norm_tailDefect_le` (UPPER; the two defect terms share the input);
* `Z₂`: the symmetrized bilinear norm is at most `2 √(U² + T2)`, through `norm_AY_le_sqrt_tsum` and the
  `U_row` head certificate `norm_comp_headReal_le_urow` (both UPPER).

## Existence and the Fourier-map endpoint

One application of the library's `quadratic_radii_theorem_local` (`A = id`, `A† = B₀`) gives a unique zero of `G` (`existsUnique_G`). From
`Z₀ < 1`, `B₀` is a unit (the library's Neumann rung), so `M` maps the finite-dimensional head
range onto itself and is injective there; with `μₙ ≠ 0` off `F` this transfers zeros of `G` to
zeros of the raw Fourier map and back (`existsUnique_rawF`). The Duffing endpoint is
`duffing_existsUnique`; conjugate symmetry is `duffing_existsUnique_real` (book Prop 10.1.2
route: raw
uniqueness, not `R`-equivariance of `M`).
-/

open scoped ENNReal NNReal

noncomputable section

namespace FourierDuffing

open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.WeightedLp.Bilateral FourierDuffing.IkData

/-- The moderate constant `C = 1` of the geometric carrier weight against itself (`ν ≥ 1`). -/
local notation "hC" => Fourier.moderate_geomFiberZ

/-! ### A. The maps and the coefficient identity -/

section Maps

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- The finite-head symbol `1_{k ∈ F} μ k`. -/
def headSym (k : ℤ) : ℂ := if k ∈ F then μ k else 0

/-- The finite-head symbol is bounded (finite support). -/
theorem bddAbove_headSym : BddAbove (Set.range fun k => ‖headSym F μ k‖) := by
  refine ⟨∑ j ∈ F, ‖μ j‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  show ‖headSym F μ k‖ ≤ _
  unfold headSym
  split_ifs with hk
  · exact Finset.single_le_sum (f := fun j => ‖μ j‖) (fun _ _ => norm_nonneg _) hk
  · rw [norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The finite-head diagonal** `Λ_H = diag(1_F μ)` on `X₂ ℂ ν`. -/
def LamH : X₂ ℂ ν →L[ℂ] X₂ ℂ ν := diagCLM (headSym F μ) (bddAbove_headSym F μ)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- `Λ_H` in coordinates. -/
@[simp] theorem coeff_LamH (x : X₂ ℂ ν) (k : ℤ) :
    coeff (LamH F μ x) k = if k ∈ F then μ k * coeff x k else 0 := by
  rw [LamH, coeff_diagCLM, headSym]
  split_ifs <;> simp

/-- The head block `K_H = Λ_H − P L_β P` of the approximate derivative. On the head range it is
the finite Jacobian `DF^{(N)}(ā)` of the book's truncation (10.3) at `β = 2ā` when `supp ā ⊆ F`:
the truncation of the convolution to `|j₁|, |j₂| ≤ N` is vacuous on a head-supported candidate. -/
def Kh (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) : X₂ ℂ ν →L[ℂ] X₂ ℂ ν :=
  LamH F μ - headProj (𝕜 := ℂ) F ∘L symbolAction₀ (p := 2) hC β ∘L headProj (𝕜 := ℂ) F

/-- **The approximate derivative** `B₀ = M K_H + Q`. -/
def B0 (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) : X₂ ℂ ν →L[ℂ] X₂ ℂ ν := M ∘L Kh F μ β + tailProj (𝕜 := ℂ) F

/-- **The bounded self-map** `G(a) = M (Λ_H a − H_F (a ⋆ a) − g) + Q a − T∞ (a ⋆ a)`. -/
def G (a : X₂ ℂ ν) : X₂ ℂ ν :=
  M (LamH F μ a - headReal F (prodCLM a a) - g) + tailProj (𝕜 := ℂ) F a - tailInf (F : Set ℤ) μ hs (prodCLM a a)

/-- `G` is the canonical quadratic map, with bilinear part `-quadCLM A_Y`. -/
theorem G_eq (a : X₂ ℂ ν) :
    G F μ hs M g a = quadMap (-M g)
      (M ∘L LamH F μ + tailProj (𝕜 := ℂ) F)
      (-quadCLM (AY F M (F : Set ℤ) μ hs)) a := by
  simp only [G, quadMap, quadCLM_apply, AY, add_apply, ContinuousLinearMap.comp_apply,
    neg_apply, map_sub]
  abel

/-- The derivative in the symmetric product representation used by the head defect. -/
def DG (a : X₂ ℂ ν) : X₂ ℂ ν →L[ℂ] X₂ ℂ ν :=
  M ∘L LamH F μ + tailProj (𝕜 := ℂ) F - (2 : ℂ) • quadCLM (AY F M (F : Set ℤ) μ hs) a

/-- The derivative expression agrees with the canonical quadratic derivative. -/
theorem DG_eq (a : X₂ ℂ ν) : DG F μ hs M a =
    quadDeriv (M ∘L LamH F μ + tailProj (𝕜 := ℂ) F)
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

/-- **The coefficient identity** `coeff (G a) = A_raw (F_raw a)` (consensus §2): the head part
reads the forcing through `supp g ⊆ F`, the tail part inverts `μ` off `F`. -/
theorem coeff_G (hg : ∀ k ∉ F, coeff g k = 0) (hμ : ∀ k ∉ F, μ k ≠ 0) (a : X₂ ℂ ν) :
    coeff (G F μ hs M g a) = rawA F μ M (rawF μ g a) := by
  have hH : headOfRaw F (rawF μ g a) = LamH F μ a - headReal F (prodCLM a a) - g :=
    ext_coeff <| funext fun k => by
      rw [coeff_headOfRaw, coeff_sub, coeff_sub, Pi.sub_apply, Pi.sub_apply, coeff_LamH,
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
tail defect at the Duffing centre, with `L_β` supplied by the operator series. -/
theorem DG_sub_B0 {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) :
    DG F μ hs M ā - B0 F μ M (betaOf F ā hā) =
      -tailDefect hC (betaOf F ā hā) F M (tailSymbol (F : Set ℤ) μ)
        (bddAbove_of_summable_sq hs) := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [DG, two_smul_quadCLM_AY_abar F μ hs M hā, B0, Kh, tailDefect, tailProj_eq_id_sub_headProj,
    tailDiag, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

end Centre

/-! ### C. The four bound faces -/

section Bounds

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- `I − B₀ = P − M K_H`. -/
theorem one_sub_B0 (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ContinuousLinearMap.id ℂ (X₂ ℂ ν) - B0 F μ M β = headProj (𝕜 := ℂ) F - M ∘L Kh F μ β := by
  rw [B0, tailProj_eq_id_sub_headProj]
  abel

omit [Fact (1 ≤ (ν : ℝ))] in
/-- `Λ_H` has its range in the head: `P Λ_H = Λ_H`. -/
theorem headProj_comp_LamH :
    headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L LamH F μ = LamH F μ :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_headProj, coeff_LamH]
    split_ifs <;> rfl

omit [Fact (1 ≤ (ν : ℝ))] in
/-- `Λ_H` reads the head only: `Λ_H P = Λ_H`. -/
theorem LamH_comp_headProj :
    LamH F μ ∘L headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F = LamH F μ :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_LamH, coeff_LamH, coeff_headProj]
    split_ifs <;> rfl

/-- `K_H` has its range in the head: `P K_H = K_H`. -/
theorem headProj_comp_Kh (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    headProj (𝕜 := ℂ) F ∘L Kh F μ β = Kh F μ β := by
  rw [Kh, ContinuousLinearMap.comp_sub, headProj_comp_LamH, ← ContinuousLinearMap.comp_assoc,
    headProj_comp_headProj]

/-- `K_H` reads the head only: `K_H P = K_H`. -/
theorem Kh_comp_headProj (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    Kh F μ β ∘L headProj (𝕜 := ℂ) F = Kh F μ β := by
  rw [Kh, ContinuousLinearMap.sub_comp, LamH_comp_headProj, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, headProj_comp_headProj]

/-- **`I − B₀` lives on the block `F × F`** under `P M = M`: `P (P − M K_H) P = P − M K_H`, so
`norm_le_sqrt_of_block` applies to the `Z₀` operator. -/
theorem block_one_sub_B0 (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M)
    (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    headProj (𝕜 := ℂ) F ∘L (headProj (𝕜 := ℂ) F - M ∘L Kh F μ β) ∘L headProj (𝕜 := ℂ) F = headProj (𝕜 := ℂ) F - M ∘L Kh F μ β := by
  rw [ContinuousLinearMap.sub_comp, headProj_comp_headProj, ContinuousLinearMap.comp_assoc,
    Kh_comp_headProj, ContinuousLinearMap.comp_sub, headProj_comp_headProj,
    ← ContinuousLinearMap.comp_assoc, hPM]

/-- **The `Z₁` face** (UPPER): the tail-defect bound `norm_tailDefect_le` at the composed head
bound `H`
and a tail bound `R` of the tail symbol (`C = 1`). The two defect terms share the input, so no
exactness is claimed. -/
theorem norm_DG_sub_B0_le {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0)
    (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) {H R : ℝ}
    (hH : ‖M ∘L headProj (𝕜 := ℂ) F ∘L symbolAction₀ (p := 2) hC (betaOf F ā hā) ∘L tailProj (𝕜 := ℂ) F‖ ≤ H)
    (hR : ∀ k, ‖tailSymbol (F : Set ℤ) μ k‖ ≤ R) (hR0 : 0 ≤ R) :
    ‖DG F μ hs M ā - B0 F μ M (betaOf F ā hā)‖ ≤ √(H ^ 2 + (R * 1 * ‖betaOf F ā hā‖) ^ 2) := by
  rw [DG_sub_B0 F μ hs M hā, norm_neg]
  exact norm_tailDefect_le hC (betaOf F ā hā) F M (tailSymbol (F : Set ℤ) μ)
    (bddAbove_of_summable_sq hs) hPM (fun k hk => tailSymbol_of_mem (Finset.mem_coe.2 hk)) hH
    (norm_tail_term_le_of_bound hC (betaOf F ā hā) _ _ hR hR0)

omit [Fact (1 ≤ (ν : ℝ))] in
/-- **The `U_row` head certificate** (consensus §6; UPPER): with `B_ij = m_i M_ij / m_j`,
`‖M H_F‖ ≤ √(∑_{i ∈ F} (∑_{j ∈ F} |B_ij|)²)` under `P M = M`. -/
theorem norm_comp_headReal_le_urow (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) :
    ‖M ∘L headReal F‖ ≤ √(∑ i ∈ F, (∑ j ∈ F, ‖matrixOf M i j‖ * (ν : ℝ) ^ i.natAbs /
      (ν : ℝ) ^ j.natAbs) ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
  have hHy : ∀ k ∉ F, coeff (headReal F y) k = 0 := fun k hk => by
    rw [coeff_headReal, ite_eq_right hk]
  have hterm : ∀ i, ‖coeff (M (headReal F y)) i‖ * (ν : ℝ) ^ i.natAbs ≤
      (∑ j ∈ F, ‖matrixOf M i j‖ * (ν : ℝ) ^ i.natAbs / (ν : ℝ) ^ j.natAbs) * ‖y‖ := fun i => by
    rw [coeff_apply_of_coeff_eq_zero M hHy i, Finset.sum_mul]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_pos ν.coe_pos _).le).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [norm_mul, coeff_headReal, ite_eq_left hj]
    have hνj : 0 < (ν : ℝ) ^ j.natAbs := pow_pos ν.coe_pos _
    have hy := mul_le_mul_of_nonneg_left (normMag_le_norm_Y y j)
      (div_nonneg (mul_nonneg (norm_nonneg (matrixOf M i j)) (pow_pos ν.coe_pos i.natAbs).le)
        hνj.le)
    refine Eq.trans_le ?_ hy
    field_simp
  have hsq : ‖(M ∘L headReal F) y‖ ^ 2 ≤ (√(∑ i ∈ F, (∑ j ∈ F, ‖matrixOf M i j‖ *
      (ν : ℝ) ^ i.natAbs / (ν : ℝ) ^ j.natAbs) ^ 2) * ‖y‖) ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, norm_sq_X₂, tsum_eq_sum (s := F) fun i hi => by
        rw [coeff_eq_zero_of_headProj_comp F M hPM _ hi, norm_zero, sq, zero_mul, zero_mul],
      mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [pow_mul', ← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (pow_pos ν.coe_pos _).le) (hterm i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

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

/-! ### D. The Duffing symbol and its producers -/

section DuffingSymbol

/-! The Duffing symbol `duffing`, its norm identity, the tail witness inequality, the exact
rational control at the certificate data and the square summability of its tail symbol, on the
head `headZ` of `FourierDuffing.IkData` (`Examples/Fourier/Duffing/IkData.lean`). -/

/-- The Duffing symbol `μ_n = -n² + i c₁ n + c₂` (real parameters, as complex). -/
def duffing (c₁ c₂ : ℝ) (n : ℤ) : ℂ := -(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂

/-- `|μ_n|² = (n² - c₂)² + c₁² n²`. -/
theorem sq_norm_duffing (c₁ c₂ : ℝ) (n : ℤ) :
    ‖duffing c₁ c₂ n‖ ^ 2 = ((n : ℝ) ^ 2 - c₂) ^ 2 + c₁ ^ 2 * (n : ℝ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [duffing, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, sq]
  ring

/-- The witness inequality: on the tail `|n| > N`, `(N+1)² > c₂` gives
`|μ_{N+1}|² ≤ |μ_n|²` (increasing in `n²` above `c₂`; no sign assumption on `c₁`). -/
theorem duffing_min {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    ∀ n ∉ headZ N, ‖duffing c₁ c₂ ((N : ℤ) + 1)‖ ≤ ‖duffing c₁ c₂ n‖ := fun n hn => by
  simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
  have ha : ((N : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs (n : ℝ)]
    have : (N : ℝ) + 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    exact pow_le_pow_left₀ (by positivity) this 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [sq_norm_duffing, sq_norm_duffing]
  push_cast
  have h1 : 0 < ((N : ℝ) + 1) ^ 2 - c₂ := by linarith
  have h2 : ((N : ℝ) + 1) ^ 2 - c₂ ≤ (n : ℝ) ^ 2 - c₂ := by linarith
  nlinarith [mul_le_mul h2 h2 h1.le (h1.le.trans h2), mul_le_mul_of_nonneg_left ha (sq_nonneg c₁)]

theorem duffing_succ_ne_zero {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    duffing c₁ c₂ ((N : ℤ) + 1) ≠ 0 := fun h => by
  have e := sq_norm_duffing c₁ c₂ ((N : ℤ) + 1)
  rw [h, norm_zero] at e
  push_cast at e
  have h1 : 0 < ((N : ℝ) + 1) ^ 2 - c₂ := by linarith
  nlinarith [mul_pos h1 h1, sq_nonneg (c₁ * ((N : ℝ) + 1))]


/-- **The exact rational control** at `c₁ = 1/10`, `c₂ = 4`, `N = 10`:
`|μ₁₁|² = 117² + (11/10)² = 13689 + 121/100`. -/
theorem sq_norm_duffing_control : ‖duffing (1 / 10) 4 11‖ ^ 2 = 13689 + 121 / 100 := by
  rw [sq_norm_duffing]; norm_num

/-- The control hypothesis `(10 + 1)² > 4`. -/
theorem control_hN : (4 : ℝ) < (((10 : ℕ) : ℝ) + 1) ^ 2 := by norm_num


/-- **The summability hypothesis of `tailDiagInf` at the Duffing symbol**: `Summable ‖d‖²` (`|μ_n|⁻² ≲ n⁻⁴`); the sum is
not computed. -/
theorem summable_sq_tailSymbol_duffing {c₁ c₂ : ℝ} {N : ℕ} (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    Summable fun n : ℤ => ‖tailSymbol (headZ N) (duffing c₁ c₂) n‖ ^ 2 := by
  set a : ℝ := ((N : ℝ) + 1) ^ 2
  set δ : ℝ := a - c₂
  have hδ : 0 < δ := by simp only [δ, a]; linarith
  have hK : 0 < a + |c₂| := by positivity
  set ε : ℝ := δ / (a + |c₂|)
  have hε : 0 < ε := div_pos hδ hK
  -- on the tail: `ε n² ≤ n² - c₂ ≤ |μ_n|`
  have hlow : ∀ n ∉ headZ N, ε * (n : ℝ) ^ 2 ≤ ‖duffing c₁ c₂ n‖ := fun n hn => by
    simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
    have ha : a ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs (n : ℝ)]
      have : (N : ℝ) + 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) this 2
    have hpos : 0 ≤ (n : ℝ) ^ 2 - c₂ := by simp only [δ, a] at hδ ha ⊢; linarith
    have hkey : δ * (n : ℝ) ^ 2 ≤ (a + |c₂|) * ((n : ℝ) ^ 2 - c₂) := by
      rcases le_or_gt 0 c₂ with hc | hc
      · rw [abs_of_nonneg hc]; simp only [δ]; nlinarith
      · rw [abs_of_neg hc]; simp only [δ]; nlinarith
    have hsq : ((n : ℝ) ^ 2 - c₂) ≤ ‖duffing c₁ c₂ n‖ := by
      refine (pow_le_pow_iff_left₀ hpos (norm_nonneg _) two_ne_zero).1 ?_
      rw [sq_norm_duffing]; nlinarith [sq_nonneg (c₁ * n)]
    refine le_trans ?_ hsq
    rw [show ε * (n : ℝ) ^ 2 = δ * (n : ℝ) ^ 2 / (a + |c₂|) by simp only [ε]; ring,
      div_le_iff₀ hK, mul_comm _ (a + |c₂|)]
    exact hkey
  have hg : Summable fun n : ℤ => (ε ^ 2)⁻¹ * (1 / (n : ℝ) ^ 4) :=
    (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hg
  rw [norm_tailSymbol]
  split_ifs with hn
  · rw [sq, mul_zero]; positivity
  · have hn0 : (n : ℝ) ≠ 0 := by
      simp only [headZ, Set.mem_ofPred_eq, not_le] at hn
      exact_mod_cast (show n ≠ 0 by rintro rfl; rw [abs_zero] at hn; omega)
    have hl := hlow n hn
    have hεn : 0 < ε * (n : ℝ) ^ 2 := by positivity
    rw [inv_pow, one_div, ← mul_inv, show (ε ^ 2 * (n : ℝ) ^ 4) = (ε * (n : ℝ) ^ 2) ^ 2 by ring]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hεn.le hl 2)


/-! The same facts on the `Finset` head `headF N`, and the producers of the certificate
hypotheses. -/

/-- The head `|k| ≤ N` as a `Finset`. -/
abbrev headF (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem mem_headF {N : ℕ} {k : ℤ} : k ∈ headF N ↔ |k| ≤ (N : ℤ) := by
  rw [Finset.mem_Icc, abs_le]

/-- **The Finset/Set head bridge** at the symbol level: the tail symbol on `↑(headF N)` is the
tail symbol on `headZ N` (the two decidability instances differ; the functions agree). -/
theorem tailSymbol_headF (N : ℕ) (μ : ℤ → ℂ) :
    tailSymbol ((headF N : Finset ℤ) : Set ℤ) μ = tailSymbol (headZ N) μ := by
  funext k
  by_cases h : |k| ≤ (N : ℤ)
  · rw [tailSymbol_of_mem (Finset.mem_coe.2 (mem_headF.2 h)),
      tailSymbol_of_mem (show k ∈ headZ N from h)]
  · rw [tailSymbol_of_notMem (fun h' => h (mem_headF.1 (Finset.mem_coe.1 h'))),
      tailSymbol_of_notMem (show k ∉ headZ N from h)]

variable {c₁ c₂ : ℝ} {N : ℕ}

/-- The Duffing tail symbol on the `Finset` head is square summable (the summability hypothesis
of `tailDiagInf`, through the head bridge). -/
theorem summable_sq_tailSymbol_duffing_headF (hN : c₂ < ((N : ℝ) + 1) ^ 2) :
    Summable fun k => ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 := by
  rw [tailSymbol_headF]
  exact summable_sq_tailSymbol_duffing hN

/-- The Duffing symbol does not vanish off the head. -/
theorem duffing_ne_zero (hN : c₂ < ((N : ℝ) + 1) ^ 2) : ∀ k ∉ headF N, duffing c₁ c₂ k ≠ 0 :=
  fun k hk => norm_pos_iff.1 ((norm_pos_iff.2 (duffing_succ_ne_zero hN)).trans_le
    (duffing_min hN k fun h => hk (mem_headF.2 h)))

/-- The Duffing tail symbol is bounded by `|μ_{N+1}|⁻¹` (the witness bound
`norm_tailSymbol_le_of_witness`). -/
theorem norm_tailSymbol_duffing_le (hN : c₂ < ((N : ℝ) + 1) ^ 2) (k : ℤ) :
    ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ≤
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖⁻¹ := by
  rw [tailSymbol_headF]
  exact norm_tailSymbol_le_of_witness _ _ (duffing_succ_ne_zero hN) (duffing_min hN) k

/-- **The linear lower bound** under `0 ≤ c₂ < (N+1)²`: on the tail,
`κ |k| ≤ |μ_k|` with `κ = (N + 1) − c₂/(N + 1)` (from `|μ_k| ≥ k² − c₂` and
`k² − c₂ − κ|k| = (|k| − (N+1)) (|k| + c₂/(N+1)) ≥ 0`). -/
theorem duffing_lower_linear (hN : c₂ < ((N : ℝ) + 1) ^ 2) (hc₂ : 0 ≤ c₂) :
    ∀ k ∉ headZ N, ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) * ‖ik k‖ ≤ ‖duffing c₁ c₂ k‖ :=
  fun k hk => by
  simp only [headZ, Set.mem_ofPred_eq, not_le] at hk
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht : (N : ℝ) + 1 ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hk
  have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have hpos : 0 ≤ (k : ℝ) ^ 2 - c₂ := by nlinarith
  have hsq : (k : ℝ) ^ 2 - c₂ ≤ ‖duffing c₁ c₂ k‖ := by
    refine (pow_le_pow_iff_left₀ hpos (norm_nonneg _) two_ne_zero).1 ?_
    rw [sq_norm_duffing]
    nlinarith [sq_nonneg (c₁ * k)]
  refine le_trans ?_ hsq
  rw [norm_ik, Int.cast_abs]
  have hc : c₂ ≤ c₂ * |(k : ℝ)| / ((N : ℝ) + 1) := by
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_left ht hc₂]
  have key : ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) * |(k : ℝ)| =
      |(k : ℝ)| * ((N : ℝ) + 1) - c₂ * |(k : ℝ)| / ((N : ℝ) + 1) := by
    field_simp
  rw [key, hk2]
  nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg (k : ℝ))]

/-- **The tail-sum producer for `T2`** (UPPER; consumer-owned comparison with the `ik` data):
under `0 ≤ c₂ < (N+1)²`,
`∑' ‖d‖² ≤ κ⁻² ∑' ‖tailSymbol (headZ N) ik‖² = κ⁻² · 2 psi1 N ≤ 4 / ((2N + 1) κ²)`. -/
theorem tsum_sq_tailSymbol_duffing_le (hN : c₂ < ((N : ℝ) + 1) ^ 2) (hc₂ : 0 ≤ c₂) :
    ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤
      4 / ((2 * N + 1) * ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2) := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hκ0 : 0 < (N : ℝ) + 1 - c₂ / ((N : ℝ) + 1) := by
    rw [sub_pos, div_lt_iff₀ ha]
    nlinarith
  have hterm : ∀ k, ‖tailSymbol (headZ N) (duffing c₁ c₂) k‖ ^ 2 ≤
      (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹ * ‖tailSymbol (headZ N) ik k‖ ^ 2 := fun k => by
    rw [norm_tailSymbol, norm_tailSymbol]
    split_ifs with hk
    · simp
    · have hl := duffing_lower_linear (c₁ := c₁) hN hc₂ k hk
      have hik : 0 < ‖ik k‖ := by
        simp only [headZ, Set.mem_ofPred_eq, not_le] at hk
        rw [norm_ik]
        exact_mod_cast (by omega : (0 : ℤ) < |k|)
      have hp := mul_pos hκ0 hik
      rw [inv_pow, inv_pow, ← mul_inv, ← mul_pow]
      exact inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le hl 2)
  rw [tailSymbol_headF]
  refine (Summable.tsum_le_tsum hterm (summable_sq_tailSymbol_duffing hN)
    ((summable_sq_tailSymbol_ik N).mul_left _)).trans ?_
  rw [tsum_mul_left, (hasSum_sq_tailSymbol_ik N).tsum_eq]
  have h2N : (0 : ℝ) < 2 * N + 1 := by positivity
  have hp := (le_div_iff₀ h2N).1 (RadiiPolynomial.WeightedLp.psi1_le N)
  rw [le_div_iff₀ (mul_pos h2N (pow_pos hκ0 2)),
    show (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹ * (2 * RadiiPolynomial.WeightedLp.psi1 N) *
        ((2 * N + 1) * ((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2) =
      2 * (RadiiPolynomial.WeightedLp.psi1 N * (2 * N + 1)) *
        (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2 * (((N : ℝ) + 1 - c₂ / ((N : ℝ) + 1)) ^ 2)⁻¹) by
      ring,
    mul_inv_cancel₀ (pow_ne_zero 2 hκ0.ne'), mul_one]
  linarith

variable {ν : PosReal}

/-- **The forcing** `g = c₃ b = (c₃/2)(δ₁ + δ₋₁)` (book: `b_{±1} = 1/2`). -/
def forcing (c₃ : ℝ) : X₂ ℂ ν := ((c₃ / 2 : ℝ) : ℂ) • (atom ℂ ν 1 + atom ℂ ν (-1))

theorem coeff_forcing (c₃ : ℝ) (n : ℤ) :
    coeff (forcing (ν := ν) c₃) n = if n = 1 ∨ n = -1 then ((c₃ / 2 : ℝ) : ℂ) else 0 := by
  rw [forcing, coeff_smul, coeff_add, Pi.smul_apply, Pi.add_apply, coeff_atom, coeff_atom,
    smul_eq_mul]
  by_cases h1 : n = 1
  · subst h1
    simp
  · by_cases h2 : n = -1
    · subst h2
      simp
    · simp [h1, h2]

/-- **The producer for `hg`**: `supp (c₃ b) ⊆ headF N` under `N ≥ 1`. -/
theorem forcing_supp {c₃ : ℝ} (hN1 : 1 ≤ N) :
    ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0 := fun k hk => by
  rw [coeff_forcing, ite_eq_right]
  rintro (rfl | rfl)
  · exact hk (mem_headF.2 (by rw [abs_one]; exact_mod_cast hN1))
  · exact hk (mem_headF.2 (by rw [abs_neg, abs_one]; exact_mod_cast hN1))

/-- **The raw Fourier map at the Duffing data is the book's `F_n`** (book §10.1):
`F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ`. -/
theorem rawF_duffing {c₃ : ℝ} (a : X₂ ℂ ν) (n : ℤ) :
    rawF (duffing c₁ c₂) (forcing c₃) a n =
      (-(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂) * coeff a n - convCoeff a a n -
        c₃ * (if n = 1 ∨ n = -1 then 1 / 2 else 0) := by
  rw [rawF, duffing, coeff_forcing]
  split_ifs
  · push_cast
    ring
  · ring

end DuffingSymbol

/-! ### E. Existence, raw injectivity, the endpoint -/

section Existence

section Generic

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (μ : ℤ → ℂ)
  (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) (M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν)
  (g : X₂ ℂ ν)

/-- A unique zero of `G` from the canonical quadratic radii theorem. -/
theorem existsUnique_G {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0) {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀) (hY₀ : ‖G F μ hs M g ā‖ ≤ Y₀)
    (hZ₀ : ‖headProj (𝕜 := ℂ) F - M ∘L Kh F μ (betaOf F ā hā)‖ ≤ Z₀)
    (hZ₁ : ‖DG F μ hs M ā - B0 F μ M (betaOf F ā hā)‖ ≤ Z₁)
    (hZ₂ : ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall ā r₀, G F μ hs M g a = 0 := by
  simp_rw [G_eq F μ hs M g] at hY₀ ⊢
  refine quadratic_radii_theorem_local
    (A := ContinuousLinearMap.id ℂ (X₂ ℂ ν))
    (A_dagger := B0 F μ M (betaOf F ā hā)) hr₀ hY₀ ?_ ?_ hZ₂ hrad fun _ _ h => h
  · rwa [ContinuousLinearMap.id_comp, one_sub_B0]
  · rwa [ContinuousLinearMap.id_comp, ← DG_eq, norm_sub_rev]

/-- **`M` is injective on the head range** when `‖P − M K_H‖ < 1` and `P M = M`: `B₀` is a unit
(Mathlib's complex Neumann series `isUnit_one_sub_of_norm_lt_one`), so `M` maps
the finite-dimensional range of `P` onto itself (`finiteDimensional_range_headProj`),
hence injectively (`LinearMap.injective_iff_surjective`). -/
theorem injOn_head_of_norm_lt_one (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M)
    (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) (h : ‖headProj (𝕜 := ℂ) F - M ∘L Kh F μ β‖ < 1) :
    ∀ x : X₂ ℂ ν, headProj (𝕜 := ℂ) F x = x → M x = 0 → x = 0 := by
  have : FiniteDimensional ℂ
      (LinearMap.range (headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F).toLinearMap) :=
    finiteDimensional_range_headProj (𝕜 := ℂ) F
  have hBsurj : Function.Surjective (B0 F μ M β) := by
    have hB : IsUnit (B0 F μ M β) := by
      rw [← one_sub_B0] at h
      simpa using isUnit_one_sub_of_norm_lt_one
        (R := X₂ ℂ ν →L[ℂ] X₂ ℂ ν) (x := 1 - B0 F μ M β) h
    obtain ⟨u, hu⟩ := hB
    intro y
    refine ⟨(↑u⁻¹ : X₂ ℂ ν →L[ℂ] X₂ ℂ ν) y, ?_⟩
    have e := DFunLike.congr_fun u.mul_inv y
    rw [hu] at e
    exact e
  have hMV : ∀ x ∈ LinearMap.range (headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F).toLinearMap,
      M x ∈ LinearMap.range (headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F).toLinearMap :=
    fun x _ => LinearMap.mem_range.2 ⟨M x, DFunLike.congr_fun hPM x⟩
  have hsurj : Function.Surjective (M.toLinearMap.restrict hMV) := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hy
    obtain ⟨z, hz⟩ := hBsurj (headProj (𝕜 := ℂ) F w)
    refine ⟨⟨Kh F μ β z, LinearMap.mem_range.2 ⟨Kh F μ β z,
      DFunLike.congr_fun (headProj_comp_Kh F μ β) z⟩⟩, Subtype.ext ?_⟩
    have e1 := DFunLike.congr_fun hPM (Kh F μ β z)
    have e2 := DFunLike.congr_fun (headProj_comp_tailProj (E := geomFiberZ ℂ ν) (p := 2)
      (𝕜 := ℂ) F) z
    have e3 := DFunLike.congr_fun (headProj_comp_headProj (E := geomFiberZ ℂ ν) (p := 2)
      (𝕜 := ℂ) F) w
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at e1 e2 e3
    have h1 := congrArg (headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F) hz
    simp only [B0, add_apply, ContinuousLinearMap.comp_apply, map_add, e1, e2, e3, add_zero] at h1
    exact h1
  have hinj := LinearMap.injective_iff_surjective.2 hsurj
  intro x hx hMx
  have h0 := @hinj ⟨x, LinearMap.mem_range.2 ⟨x, hx⟩⟩ 0 (Subtype.ext (by
    rw [map_zero, Submodule.coe_zero]
    exact hMx))
  exact congrArg Subtype.val h0

/-- **Zeros of `G` are raw zeros** (`P M = M`, `supp g ⊆ F`, `μ ≠ 0` off `F`, `M` injective on the
head range): the tail of `A_raw` inverts `d`, the head of `A_raw` is `M` on the head range. -/
theorem rawF_eq_zero_of_G_eq_zero (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M)
    (hg : ∀ k ∉ F, coeff g k = 0) (hμ : ∀ k ∉ F, μ k ≠ 0)
    (hinj : ∀ x : X₂ ℂ ν, headProj (𝕜 := ℂ) F x = x → M x = 0 → x = 0) {a : X₂ ℂ ν}
    (ha : G F μ hs M g a = 0) : rawF μ g a = 0 := by
  have hA : ∀ n, rawA F μ M (rawF μ g a) n = 0 := fun n => by
    rw [← coeff_G F μ hs M g hg hμ a, ha, coeff_zero, Pi.zero_apply]
  have htail : ∀ n ∉ F, rawF μ g a n = 0 := fun n hn => by
    have h := hA n
    rw [rawA, coeff_eq_zero_of_headProj_comp F M hPM _ hn, zero_add,
      tailSymbol_of_notMem (fun h' => hn (Finset.mem_coe.1 h')), mul_eq_zero] at h
    exact h.resolve_left (inv_ne_zero (hμ n hn))
  have hM : M (headOfRaw F (rawF μ g a)) = 0 := ext_coeff <| funext fun n => by
    rw [coeff_zero, Pi.zero_apply]
    by_cases hn : n ∈ F
    · have h := hA n
      rwa [rawA, tailSymbol_of_mem (Finset.mem_coe.2 hn), zero_mul, add_zero] at h
    · exact coeff_eq_zero_of_headProj_comp F M hPM _ hn
  have hP : headProj (𝕜 := ℂ) F (headOfRaw (ν := ν) F (rawF μ g a)) = headOfRaw F (rawF μ g a) :=
    ext_coeff <| funext fun n => by
      rw [coeff_headProj, coeff_headOfRaw]
      split_ifs <;> rfl
  have h0 := hinj _ hP hM
  funext n
  by_cases hn : n ∈ F
  · have e := congrArg (fun x => coeff x n) h0
    simp only [coeff_headOfRaw, ite_eq_left hn, coeff_zero, Pi.zero_apply] at e
    exact e
  · exact htail n hn

/-- **Raw zeros are zeros of `G`** (the coefficient identity at `F_raw a = 0`). -/
theorem G_eq_zero_of_rawF_eq_zero (hg : ∀ k ∉ F, coeff g k = 0) (hμ : ∀ k ∉ F, μ k ≠ 0)
    {a : X₂ ℂ ν} (ha : rawF μ g a = 0) : G F μ hs M g a = 0 := by
  have h0 : headOfRaw (ν := ν) F 0 = 0 := ext_coeff <| funext fun n => by
    rw [coeff_headOfRaw, coeff_zero, Pi.zero_apply]
    split_ifs <;> rfl
  refine ext_coeff ?_
  rw [coeff_G F μ hs M g hg hμ a, ha, coeff_zero]
  funext n
  rw [rawA, h0, map_zero]
  simp

/-- **A unique raw zero of the Fourier map in the ball** (generic `F`, `μ`): the zero of `G` from
`existsUnique_G`, transferred through `Z₀ < 1` (from `p(r₀) < 0`) and the finite head. -/
theorem existsUnique_rawF {ā : X₂ ℂ ν} (hā : ∀ k ∉ F, coeff ā k = 0)
    (hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F ∘L M = M) (hg : ∀ k ∉ F, coeff g k = 0)
    (hμ : ∀ k ∉ F, μ k ≠ 0) {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ} (hr₀ : 0 < r₀) (hY₀ : ‖G F μ hs M g ā‖ ≤ Y₀)
    (hZ₀ : ‖headProj (𝕜 := ℂ) F - M ∘L Kh F μ (betaOf F ā hā)‖ ≤ Z₀)
    (hZ₁ : ‖DG F μ hs M ā - B0 F μ M (betaOf F ā hā)‖ ≤ Z₁)
    (hZ₂ : ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ Z₂)
    (hrad : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall ā r₀, rawF μ g a = 0 := by
  have hlt : ‖headProj (𝕜 := ℂ) F - M ∘L Kh F μ (betaOf F ā hā)‖ < 1 := by
    have hY0 : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
    have hZ10 : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁
    have hZ20 : 0 ≤ Z₂ := (ContinuousLinearMap.opNorm_nonneg _).trans hZ₂
    have h := general_radii_poly_neg_implies_Z_lt_one hY0 hr₀ hrad
    simp only [Z_bound_general] at h
    nlinarith [mul_nonneg hZ20 hr₀.le]
  have hinj := injOn_head_of_norm_lt_one F μ M hPM _ hlt
  obtain ⟨a, ⟨ha, hGa⟩, hu⟩ := existsUnique_G F μ hs M g hā hr₀ hY₀ hZ₀ hZ₁ hZ₂ hrad
  exact ⟨a, ⟨ha, rawF_eq_zero_of_G_eq_zero F μ hs M g hPM hg hμ hinj hGa⟩,
    fun z ⟨hz, hz0⟩ => hu z ⟨hz, G_eq_zero_of_rawF_eq_zero F μ hs M g hg hμ hz0⟩⟩

end Generic

/-- **The head certificate** (book Theorem 10.1.3's data; the Example81 `Cert` pattern): the
candidate `ā` supported in `headF N`, the head matrix `M` with `P M = M`, and the three numerical
head hypotheses `Z₀` (head block), `H` (composed leakage) and `U` (`U_row`). -/
structure Cert (c₁ c₂ : ℝ) (N : ℕ) (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] where
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
  abar_supp : ∀ k ∉ headF N, coeff abar k = 0
  hPM : headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) (headF N) ∘L M = M
  hZ₀ : ‖headProj (headF N) - M ∘L Kh (headF N) (duffing c₁ c₂)
    (betaOf (headF N) abar abar_supp)‖ ≤ Z₀
  hH : ‖M ∘L headProj (headF N) ∘L symbolAction₀ (p := 2) hC
    (betaOf (headF N) abar abar_supp) ∘L tailProj (headF N)‖ ≤ H
  hU : ‖M ∘L headReal (headF N)‖ ≤ U

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {c₁ c₂ c₃ : ℝ} {N : ℕ}

/-- **THE ENDPOINT: a unique zero of the Fourier map in the ball** (book Theorem 10.1.3 on
`ℓ²_ν`): under `(N+1)² > c₂`, a certificate, `supp (c₃ b) ⊆ headF N`, the four bounds and the
radii inequality, the raw Fourier map `F_n(a) = (−n² + i c₁ n + c₂) aₙ − (a ⋆ a)ₙ − c₃ bₙ` has a
unique zero in the closed ball of radius `r₀` around the candidate. -/
theorem duffing_existsUnique (hN : c₂ < ((N : ℝ) + 1) ^ 2) (cert : Cert c₁ c₂ N ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ : ℝ}
    (hY₀ : ‖G (headF N) (duffing c₁ c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀)
    (hrad : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃! a ∈ Metric.closedBall cert.abar r₀, ∀ n : ℤ, rawF (duffing c₁ c₂) (forcing c₃) a n = 0 := by
  have hs := summable_sq_tailSymbol_duffing_headF (c₁ := c₁) hN
  have hZ1' : ‖DG (headF N) (duffing c₁ c₂) hs cert.M cert.abar -
      B0 (headF N) (duffing c₁ c₂) cert.M (betaOf (headF N) cert.abar cert.abar_supp)‖ ≤ Z₁ := by
    refine (norm_DG_sub_B0_le (headF N) (duffing c₁ c₂) hs cert.M cert.abar_supp cert.hPM
      cert.hH (norm_tailSymbol_duffing_le hN) (inv_nonneg.2 (norm_nonneg _))).trans ?_
    rw [mul_one, inv_mul_eq_div]
    exact (Real.sqrt_le_sqrt hZ₁).trans_eq (Real.sqrt_sq hZ₁0)
  have hT20 : 0 ≤ T2 := (tsum_nonneg fun _ => sq_nonneg _).trans hT2
  have h2 : 2 * √(cert.U ^ 2 + T2) ≤ Z₂ := by
    refine (pow_le_pow_iff_left₀ (by positivity) hZ₂0 two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    linarith
  have hZ2' := (norm_quadComp_add_flip_le_of_bounds (headF N) (duffing c₁ c₂) hs cert.M
    cert.hPM cert.hU hT2).trans h2
  obtain ⟨a, ⟨ha, hFa⟩, hu⟩ := existsUnique_rawF (headF N) (duffing c₁ c₂) hs cert.M (forcing c₃)
    cert.abar_supp cert.hPM hg (duffing_ne_zero hN) hr₀ hY₀ cert.hZ₀ hZ1' hZ2' hrad
  exact ⟨a, ⟨ha, fun n => congrFun hFa n⟩, fun z ⟨hz, hz0⟩ => hu z ⟨hz, funext hz0⟩⟩

end Existence

/-! ### F. Reality -/

section Reality

variable {ν : PosReal}

/-- The conjugate reflection of a coefficient family stays in `X₂ ℂ ν` (symmetric weight). -/
theorem memℓp_conjRefl (a : X₂ ℂ ν) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ ℂ ν) k
      (starRingEnd ℂ (coeff a (-k)))) 2 :=
  memℓp_two_of_summable _ (((Equiv.neg ℤ).summable_iff.2 (summable_sq_X₂ a)).congr fun k => by
    simp only [Function.comp_apply, Equiv.neg_apply, Int.natAbs_neg, Complex.norm_conj])

/-- **The conjugate reflection** `(R a)ₙ = conj (a₋ₙ)`. -/
def conjRefl (a : X₂ ℂ ν) : X₂ ℂ ν :=
  ofCoeff (fun n => starRingEnd ℂ (coeff a (-n))) (memℓp_conjRefl a)

@[simp] theorem coeff_conjRefl (a : X₂ ℂ ν) (n : ℤ) :
    coeff (conjRefl a) n = starRingEnd ℂ (coeff a (-n)) :=
  coeff_ofCoeff _ _ n

/-- `R` is an isometry (`m₋ₙ = mₙ`). -/
theorem norm_conjRefl (a : X₂ ℂ ν) : ‖conjRefl a‖ = ‖a‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_X₂, norm_sq_X₂, ← (Equiv.neg ℤ).tsum_eq]
  exact tsum_congr fun k => by
    simp only [coeff_conjRefl, Equiv.neg_apply, neg_neg, Int.natAbs_neg, Complex.norm_conj]

/-- `R` is additive. -/
theorem conjRefl_sub (a b : X₂ ℂ ν) : conjRefl (a - b) = conjRefl a - conjRefl b :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjRefl, coeff_sub, coeff_sub, Pi.sub_apply, Pi.sub_apply, coeff_conjRefl,
      coeff_conjRefl, map_sub]

/-- The product commutes with `R`: `(R a ⋆ R a)ₙ = conj ((a ⋆ a)₋ₙ)` (`Complex.conj_tsum` and the
reindex `j ↦ −j`). -/
theorem convCoeff_conjRefl (a : X₂ ℂ ν) (n : ℤ) :
    convCoeff (conjRefl a) (conjRefl a) n = starRingEnd ℂ (convCoeff a a (-n)) := by
  rw [convCoeff, convCoeff, Complex.conj_tsum]
  refine (tsum_congr fun j => ?_).trans
    ((Equiv.neg ℤ).tsum_eq fun j => starRingEnd ℂ (coeff a j * coeff a (-n - j)))
  rw [coeff_conjRefl, coeff_conjRefl, Equiv.neg_apply, map_mul,
    show -(n - j) = -n - -j by ring]

variable [Fact (1 ≤ (ν : ℝ))] {c₁ c₂ c₃ : ℝ} {N : ℕ}

omit [Fact (1 ≤ (ν : ℝ))] in
/-- **Real parameters make the Duffing map `R`-equivariant**:
`F(R a)ₙ = conj (F(a)₋ₙ)`. -/
theorem rawF_duffing_conjRefl (a : X₂ ℂ ν) (n : ℤ) :
    rawF (duffing c₁ c₂) (forcing c₃) (conjRefl a) n =
      starRingEnd ℂ (rawF (duffing c₁ c₂) (forcing c₃) a (-n)) := by
  rw [rawF_duffing, rawF_duffing, coeff_conjRefl, convCoeff_conjRefl]
  by_cases h : n = 1 ∨ n = -1
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    simp only [map_sub, map_mul, map_add, map_neg, map_pow, Complex.conj_ofReal, Complex.conj_I,
      map_intCast, map_div₀, map_one, map_ofNat, Int.cast_neg]
    ring
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    simp only [map_sub, map_mul, map_add, map_neg, map_pow, Complex.conj_ofReal, Complex.conj_I,
      map_intCast, map_zero, Int.cast_neg]
    ring

/-- **THE CONJUGATE-SYMMETRIC ENDPOINT** (book Prop 10.1.2 route): with the hypotheses of
`duffing_existsUnique` and `R ā = ā`, the unique zero of the Fourier map in the ball satisfies
`R ã = ã`, i.e. `conj ã₋ₙ = ãₙ` (uniqueness of the raw zero, not `R`-equivariance of `M`). -/
theorem duffing_existsUnique_real (hN : c₂ < ((N : ℝ) + 1) ^ 2) (cert : Cert c₁ c₂ N ν)
    (hg : ∀ k ∉ headF N, coeff (forcing (ν := ν) c₃) k = 0) {Y₀ Z₁ Z₂ T2 r₀ : ℝ}
    (hY₀ : ‖G (headF N) (duffing c₁ c₂) (summable_sq_tailSymbol_duffing_headF hN) cert.M
      (forcing c₃) cert.abar‖ ≤ Y₀)
    (hZ₁ : cert.H ^ 2 + (‖betaOf (headF N) cert.abar cert.abar_supp‖ /
      ‖duffing c₁ c₂ ((N : ℤ) + 1)‖) ^ 2 ≤ Z₁ ^ 2) (hZ₁0 : 0 ≤ Z₁)
    (hT2 : ∑' k, ‖tailSymbol ((headF N : Finset ℤ) : Set ℤ) (duffing c₁ c₂) k‖ ^ 2 ≤ T2)
    (hZ₂ : 4 * (cert.U ^ 2 + T2) ≤ Z₂ ^ 2) (hZ₂0 : 0 ≤ Z₂) (hr₀ : 0 < r₀)
    (hrad : generalRadiiPolynomial Y₀ cert.Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hR : conjRefl cert.abar = cert.abar) :
    ∃ a ∈ Metric.closedBall cert.abar r₀, (∀ n, rawF (duffing c₁ c₂) (forcing c₃) a n = 0) ∧
      conjRefl a = a ∧ ∀ z ∈ Metric.closedBall cert.abar r₀,
        (∀ n, rawF (duffing c₁ c₂) (forcing c₃) z n = 0) → z = a := by
  obtain ⟨a, ⟨ha, hFa⟩, hu⟩ := duffing_existsUnique hN cert hg hY₀ hZ₁ hZ₁0 hT2 hZ₂ hZ₂0 hr₀ hrad
  have hRa : conjRefl a ∈ Metric.closedBall cert.abar r₀ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ha ⊢
    rwa [← hR, ← conjRefl_sub, norm_conjRefl]
  have hFRa : ∀ n, rawF (duffing c₁ c₂) (forcing c₃) (conjRefl a) n = 0 := fun n => by
    rw [rawF_duffing_conjRefl, hFa, map_zero]
  exact ⟨a, ha, hFa, hu _ ⟨hRa, hFRa⟩, fun z hz hz0 => hu z ⟨hz, hz0⟩⟩

end Reality

end FourierDuffing

end

