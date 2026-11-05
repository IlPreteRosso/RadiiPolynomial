import RadiiPolynomial.Core.Quadratic
import RadiiPolynomial.Analysis.Norm.FiniteSum
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Pairing
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.RealityConvolution
import RadiiPolynomial.Operators.BlockDiagonal.ProdBlock

/-!
# The bordered eigenpair map and its radii-polynomial faces

For a conjugate-symmetric symbol `μ`, a symmetric finite head `S`, a real potential `q` and a
bordered head inverse `(Mv, mv, ψ, c)` (`EigenData`), the bordered map
`eigenMap : XR × ℝ → XR × ℝ` (`XR = realSub hw`) is the shipped quadratic map
`quadMap (cG …) (LG …) (BilG …)` (`eigenMap_eq_quadMap`). Under bordered head injectivity
(`borderInj`, produced from a norm bound by `borderInj_of_norm_id_sub_lt_one` and
`borderInj_of_eigenB0`), its zeros are the normalized eigenpairs: (E1) `μₙvₙ + (q ⋆ v)ₙ − λvₙ = 0`,
(E2) `pairing v v = 1` (`eigenMap_eq_zero_iff`; tail nonresonance `hres` and the head support
`hmvS` of `mv` are hypotheses there). `existsUnique_eigenpair` is the radii-polynomial existence and
local uniqueness theorem; the `Y₀`, `Z₀`, `Z₁`, `Z₂` faces (`norm_eigenMap_le`,
`norm_id_sub_eigenB0_le`, `norm_eigenB0_sub_quadDeriv_le`, `norm_quadComp_BilG_add_flip_le`) bound
its hypotheses from a finite potential `q̄` and a potential split `‖q − q̄‖ ≤ ρ_q`. The index `M` is
generic; only the reality structure is the Fourier one.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.Fourier.Eigenpair

open RadiiPolynomial.WeightedLp

section Data

/-! ### The data of the eigenpair face -/

/-- The raw data of the eigenpair face: the symbol `μ`, the head `S`, the potential
`q`, the shift `lbar`, the bound `hr` of the corrected tail inverse `tailDiag S (μ - lbar)`, and the
bordered head inverse `(Mv, mv, ψ, c)`. -/
structure EigenRaw (M : Type*) [DecidableEq M] (w : M → ℝ) [PosWeight w] where
  μ : M → ℂ
  S : Finset M
  q : WeightedLp M (WeightedScalar ℂ w) 2
  lbar : ℝ
  hr : BddAbove (Set.range fun n => ‖tailSymbol (↑S : Set M) (fun n => μ n - (lbar : ℂ)) n‖)
  Mv : WeightedLp M (WeightedScalar ℂ w) 2 →L[ℂ] WeightedLp M (WeightedScalar ℂ w) 2
  mv : WeightedLp M (WeightedScalar ℂ w) 2
  ψ : WeightedLp M (WeightedScalar ℂ w) 2
  c : ℝ

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

/-- The data of the eigenpair face: the raw data with a conjugate-symmetric symbol `hμ`, a symmetric
head `hS`, a real potential `hq`, a head-valued `K`-symmetric `Mv`, and a real `mv`. Tail
nonresonance and the head support of `mv` are hypotheses of the theorems that use them. -/
structure EigenData (hw : ∀ n, w (-n) = w n) extends EigenRaw M w where
  hμ : ∀ n, μ (-n) = starRingEnd ℂ (μ n)
  hS : ∀ n, -n ∈ S ↔ n ∈ S
  hq : q ∈ realSub hw
  hPMv : headProj (𝕜 := ℂ) S ∘L Mv = Mv
  hKMv : ∀ x, conjReflL hw (Mv x) = Mv (conjReflL hw x)
  hmv : mv ∈ realSub hw

end Data

section Helpers

/-! ### Private helpers: real multiples, commutation of composites, the tail coordinate -/

variable {M : Type*} {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The tail coordinate identity `x + a⁻¹ (y - (l - lb) x) = a⁻¹ (μ x + y - l x)`, `a = μ - lb`. -/
private theorem tail_coeff_eq {μ lb l x y : ℂ} (ha : μ - lb ≠ 0) :
    x + (μ - lb)⁻¹ * (y - (l - lb) * x) = (μ - lb)⁻¹ * (μ * x + y - l * x) := by
  linear_combination (-x) * inv_mul_cancel₀ ha

end Helpers

section CommHelpers

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w] (hw : ∀ n, w (-n) = w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- Commutation with `K` passes to composites. -/
private theorem conjReflL_comm_comp {T U : X →L[ℂ] X}
    (hT : ∀ x, conjReflL hw (T x) = T (conjReflL hw x))
    (hU : ∀ x, conjReflL hw (U x) = U (conjReflL hw x)) (x : X) :
    conjReflL hw ((T ∘L U) x) = (T ∘L U) (conjReflL hw x) := by
  rw [ContinuousLinearMap.comp_apply, hT, hU, ContinuousLinearMap.comp_apply]

/-- Commutation with `K` passes to sums. -/
private theorem conjReflL_comm_add {T U : X →L[ℂ] X}
    (hT : ∀ x, conjReflL hw (T x) = T (conjReflL hw x))
    (hU : ∀ x, conjReflL hw (U x) = U (conjReflL hw x)) (x : X) :
    conjReflL hw ((T + U) x) = (T + U) (conjReflL hw x) := by
  rw [add_apply, map_add, hT, hU, add_apply]

/-- Commutation with `K` passes to real multiples. -/
private theorem conjReflL_comm_ofReal_smul (r : ℝ) {T : X →L[ℂ] X}
    (hT : ∀ x, conjReflL hw (T x) = T (conjReflL hw x)) (x : X) :
    conjReflL hw (((r : ℂ) • T) x) = ((r : ℂ) • T) (conjReflL hw x) := by
  rw [smul_apply, conjReflL_smul, Complex.conj_ofReal, hT, smul_apply]

end CommHelpers

section HeadSupport

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- A head-supported vector vanishes off the head. -/
private theorem coeff_eq_zero_of_headProj_eq {S : Finset M} {x : X}
    (hx : headProj (𝕜 := ℂ) S x = x) {n : M} (hn : n ∉ S) : coeff x n = 0 := by
  rw [← hx, coeff_headProj, ite_eq_right hn]

end HeadSupport

section Pieces

/-! ### The ambient pieces and their commutation with `K` -/

section Diagonal

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- `Λ_S`, the diagonal multiplier by the head part `(↑S : Set M).indicator μ` of `μ`
(`μ n` on the head `S`, `0` off it). -/
def eigenLam (R : EigenRaw M w) : X →L[ℂ] X :=
  diagCLM ((↑R.S : Set M).indicator R.μ) (NormHelpers.bddAbove_norm_indicator_finset _ _)

/-- `Λ_S` in coordinates: `coeff (Λ_S x) n = Λ_S(n) coeff x n`. -/
theorem coeff_eigenLam (R : EigenRaw M w) (x : X) (n : M) :
    coeff (eigenLam R x) n = (↑R.S : Set M).indicator R.μ n * coeff x n :=
  coeff_diagCLM _ _ x n

/-- The corrected tail inverse `T_t = tailDiag S (μ - lbar)`. -/
def eigenTail (R : EigenRaw M w) : X →L[ℂ] X :=
  tailDiag (↑R.S : Set M) (fun n => R.μ n - (R.lbar : ℂ)) R.hr

/-- `T_t` vanishes on the head: `coeff (T_t x) n = 0` for `n ∈ S`. -/
theorem coeff_eigenTail_of_mem (R : EigenRaw M w) (x : X) {n : M} (hn : n ∈ R.S) :
    coeff (eigenTail R x) n = 0 := by
  rw [eigenTail, coeff_tailDiag, tailSymbol_of_mem (Finset.mem_coe.2 hn), zero_mul]

/-- `T_t` off the head: `coeff (T_t x) n = (μ n - lbar)⁻¹ coeff x n` for `n ∉ S`. -/
theorem coeff_eigenTail_of_notMem (R : EigenRaw M w) (x : X) {n : M} (hn : n ∉ R.S) :
    coeff (eigenTail R x) n = (R.μ n - (R.lbar : ℂ))⁻¹ * coeff x n := by
  rw [eigenTail, coeff_tailDiag, tailSymbol_of_notMem (mt Finset.mem_coe.1 hn)]

/-- The coefficient of `-l` in `Bil_G`: `Mv P_S + T_t`. -/
def eigenBilOp (R : EigenRaw M w) : X →L[ℂ] X := R.Mv ∘L headProj R.S + eigenTail R

end Diagonal

section Potential

variable {M : Type*} [AddMonoid M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable {Kc : ℝ} (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The potential `v ↦ q ⋆ v`. -/
def eigenPot (R : EigenRaw M w) : X →L[ℂ] X :=
  convCLM h R.q

/-- The `v`-block of `L_G`: `Mv P_S (Λ_S + q ⋆) + Q_S + T_t (q ⋆) + lbar T_t`. -/
def eigenLin (R : EigenRaw M w) : X →L[ℂ] X :=
  R.Mv ∘L headProj R.S ∘L (eigenLam R + eigenPot h R) + tailProj R.S + eigenTail R ∘L eigenPot h R +
    (R.lbar : ℂ) • eigenTail R

end Potential

section DiagonalComm

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]
  (hw : ∀ n, w (-n) = w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- `Λ_S` commutes with `K`. -/
theorem conjReflL_eigenLam (D : EigenData hw) (x : X) :
    conjReflL hw (eigenLam D.toEigenRaw x) = eigenLam D.toEigenRaw (conjReflL hw x) :=
  conjReflL_diagCLM hw _ (fun n => by
    rw [map_indicator]
    exact Set.indicator_eq_indicator
      (Finset.mem_coe.trans ((D.hS n).trans Finset.mem_coe.symm)) (D.hμ n)) x

/-- `T_t` commutes with `K`. -/
theorem conjReflL_eigenTail (D : EigenData hw) (x : X) :
    conjReflL hw (eigenTail D.toEigenRaw x) = eigenTail D.toEigenRaw (conjReflL hw x) :=
  conjReflL_tailDiag hw (fun n => Finset.mem_coe.trans ((D.hS n).trans Finset.mem_coe.symm))
    (fun n => by
      rw [D.hμ, map_sub, Complex.conj_ofReal])
    D.hr x

/-- `Mv P_S + T_t` commutes with `K`. -/
theorem conjReflL_eigenBilOp (D : EigenData hw) (x : X) :
    conjReflL hw (eigenBilOp D.toEigenRaw x) = eigenBilOp D.toEigenRaw (conjReflL hw x) :=
  conjReflL_comm_add hw (conjReflL_comm_comp hw D.hKMv (conjReflL_headProj hw D.S D.hS))
    (conjReflL_eigenTail hw D) x

end DiagonalComm

section PotentialComm

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]
  (hw : ∀ n, w (-n) = w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The potential `q ⋆ ·` of a real `q` commutes with `K`. -/
theorem conjReflL_eigenPot (D : EigenData hw) (x : X) :
    conjReflL hw (eigenPot h D.toEigenRaw x) = eigenPot h D.toEigenRaw (conjReflL hw x) := by
  rw [eigenPot, conjReflL_convCLM hw h, (mem_realSub hw).1 D.hq]

/-- The `v`-block of `L_G` commutes with `K`. -/
theorem conjReflL_eigenLin (D : EigenData hw) (x : X) :
    conjReflL hw (eigenLin h D.toEigenRaw x) = eigenLin h D.toEigenRaw (conjReflL hw x) :=
  conjReflL_comm_add hw (conjReflL_comm_add hw (conjReflL_comm_add hw
    (conjReflL_comm_comp hw D.hKMv (conjReflL_comm_comp hw (conjReflL_headProj hw D.S D.hS)
      (conjReflL_comm_add hw (conjReflL_eigenLam hw D) (conjReflL_eigenPot hw h D))))
    (conjReflL_tailProj hw D.S D.hS))
    (conjReflL_comm_comp hw (conjReflL_eigenTail hw D) (conjReflL_eigenPot hw h D)))
    (conjReflL_comm_ofReal_smul hw D.lbar (conjReflL_eigenTail hw D)) x

end PotentialComm

end Pieces

section Map

/-! ### `G` maps `Y = XR × ℝ` into `Y` -/

section Residual

variable {M : Type*} [AddMonoid M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The head residual `ρ(v, l) = P_S (Λ_S v + q ⋆ v - l v)`. -/
def eigenHeadRes (R : EigenRaw M w) (v : X) (l : ℝ) : X :=
  headProj (𝕜 := ℂ) R.S (eigenLam R v + eigenPot h R v - l • v)

/-- The first component of `G`. -/
def eigenFst (R : EigenRaw M w) (v : X) (l : ℝ) : X :=
  R.Mv (eigenHeadRes h R v l) + (pairing h1 v v - 1) • R.mv + tailProj (𝕜 := ℂ) R.S v +
    eigenTail R (eigenPot h R v - (l - R.lbar) • v)

/-- The second component of `G`. -/
def eigenSnd (R : EigenRaw M w) (v : X) (l : ℝ) : ℝ :=
  pairing h1 R.ψ (eigenHeadRes h R v l) + R.c * (pairing h1 v v - 1)

end Residual

section Reality

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The head residual of a real `v` is real: `ρ(v, l) ∈ XR`. -/
theorem eigenHeadRes_mem (D : EigenData hw) {v : X} (hv : v ∈ realSub hw) (l : ℝ) :
    eigenHeadRes h D.toEigenRaw v l ∈ realSub hw := by
  rw [mem_realSub hw] at hv ⊢
  rw [eigenHeadRes, conjReflL_headProj hw D.S D.hS, map_sub (conjReflL hw), map_add (conjReflL hw),
    map_smul (conjReflL hw), conjReflL_eigenLam hw D, conjReflL_eigenPot hw h D, hv]

/-- The first component of `G` at a real `v` is real. -/
theorem eigenFst_mem (D : EigenData hw) {v : X} (hv : v ∈ realSub hw) (l : ℝ) :
    eigenFst h1 h D.toEigenRaw v l ∈ realSub hw := by
  have hρ := (mem_realSub hw).1 (eigenHeadRes_mem hw h D hv l)
  rw [mem_realSub hw] at hv ⊢
  rw [eigenFst, map_add (conjReflL hw), map_add (conjReflL hw), map_add (conjReflL hw), D.hKMv, hρ,
    map_smul (conjReflL hw), (mem_realSub hw).1 D.hmv, conjReflL_tailProj hw D.S D.hS,
    conjReflL_eigenTail hw D, map_sub (conjReflL hw), map_smul (conjReflL hw),
    conjReflL_eigenPot hw h D, hv]

/-- **The eigenpair map** `G : Y → Y`, `Y = XR × ℝ`. -/
def eigenMap (D : EigenData hw) (y : realSub hw × ℝ) : realSub hw × ℝ :=
  (⟨eigenFst h1 h D.toEigenRaw (y.1 : X) y.2, eigenFst_mem hw h1 h D y.1.2 y.2⟩,
    eigenSnd h1 h D.toEigenRaw (y.1 : X) y.2)

/-- The first component of `G y` is `eigenFst` at `y`. -/
theorem coe_eigenMap_fst (D : EigenData hw) (y : realSub hw × ℝ) :
    ((eigenMap hw h1 h D y).1 : X) = eigenFst h1 h D.toEigenRaw (y.1 : X) y.2 := rfl

/-- The second component of `G y` is `eigenSnd` at `y`. -/
theorem eigenMap_snd (D : EigenData hw) (y : realSub hw × ℝ) :
    (eigenMap hw h1 h D y).2 = eigenSnd h1 h D.toEigenRaw (y.1 : X) y.2 := rfl

end Reality

end Map

section Quadratic

/-! ### The quadratic data `c_G`, `L_G`, `Bil_G`, and `G = quadMap c_G L_G Bil_G` -/

section ConstBil

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)

/-- The constant part `c_G = (-mv, -c)`. -/
def cG (D : EigenData hw) : realSub hw × ℝ := (-⟨D.mv, D.hmv⟩, -D.c)

/-- The first component of `c_G` is `-mv`. -/
theorem coe_cG_fst (D : EigenData hw) : ((cG hw D).1 : X) = -D.mv := rfl

/-- The second component of `c_G` is `-c`. -/
theorem cG_snd (D : EigenData hw) : (cG hw D).2 = -D.c := rfl

/-- The bilinear part
`Bil_G((v, l), (v', l')) = (-l (Mv P_S v' + T_t v') + b(v, v') mv, -l b(ψ, P_S v') + c b(v, v'))`,
at the type its constructors produce. Both summands are built by normed-form constructors
(`lsmul` through `bilinearComp`; `compL`/`toSpanSingleton` after `bilinearComp`), with no
`smulRight`. -/
def BilG (D : EigenData hw) :=
  -(ContinuousLinearMap.lsmul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ (realSub hw) ℝ)
      (((restrictReal hw ((eigenBilOp D.toEigenRaw).restrictScalars ℝ)
          (conjReflL_eigenBilOp hw D)).prod
        (((pairing h1 D.ψ).comp ((headProj (𝕜 := ℂ) D.S).restrictScalars ℝ)).comp
          (realSub hw).subtypeL)).comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)) +
    (ContinuousLinearMap.compL ℝ (realSub hw × ℝ) ℝ (realSub hw × ℝ)
      (ContinuousLinearMap.toSpanSingleton ℝ ((⟨D.mv, D.hmv⟩ : realSub hw), D.c))).comp
      ((pairingR hw h1).bilinearComp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)
        (ContinuousLinearMap.fst ℝ (realSub hw) ℝ))

/-- The first component of `Bil_G(y, y')` is `-l (Mv P_S + T_t) v' + b(v, v') mv`. -/
theorem coe_BilG_fst (D : EigenData hw) (y y' : realSub hw × ℝ) :
    ((BilG hw h1 D y y').1 : X) =
      -(y.2 • eigenBilOp D.toEigenRaw (y'.1 : X)) + pairing h1 (y.1 : X) (y'.1 : X) • D.mv := rfl

/-- The second component of `Bil_G(y, y')` is `-l b(ψ, P_S v') + c b(v, v')`. -/
theorem BilG_snd (D : EigenData hw) (y y' : realSub hw × ℝ) :
    (BilG hw h1 D y y').2 = -(y.2 * pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S (y'.1 : X))) +
      D.c * pairing h1 (y.1 : X) (y'.1 : X) :=
  congrArg (-(y.2 * pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S (y'.1 : X))) + ·) (mul_comm _ _)

end ConstBil

section Lin

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The linear part `L_G(v, l) = (eigenLin v, b(ψ, P_S (Λ_S v + q ⋆ v)))`. -/
def LG (D : EigenData hw) : (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ) :=
  ((restrictReal hw ((eigenLin h D.toEigenRaw).restrictScalars ℝ) (conjReflL_eigenLin hw h D)).comp
      (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)).prod
    (((pairing h1 D.ψ).comp
        ((headProj (𝕜 := ℂ) D.S ∘L
          (eigenLam D.toEigenRaw + eigenPot h D.toEigenRaw)).restrictScalars ℝ)).comp
      ((realSub hw).subtypeL.comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)))

/-- The first component of `L_G y` is `eigenLin v`. -/
theorem coe_LG_fst (D : EigenData hw) (y : realSub hw × ℝ) :
    ((LG hw h1 h D y).1 : X) = eigenLin h D.toEigenRaw (y.1 : X) := rfl

/-- The second component of `L_G y` is `b(ψ, P_S (Λ_S v + q ⋆ v))`. -/
theorem LG_snd (D : EigenData hw) (y : realSub hw × ℝ) :
    (LG hw h1 h D y).2 = pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S
      (eigenLam D.toEigenRaw (y.1 : X) + eigenPot h D.toEigenRaw (y.1 : X))) := rfl

/-- `G` is the shipped quadratic map `quadMap c_G L_G Bil_G`. -/
theorem eigenMap_eq_quadMap (D : EigenData hw) :
    eigenMap hw h1 h D = quadMap (cG hw D) (LG hw h1 h D) (BilG hw h1 D) := by
  funext y
  refine Prod.ext (Subtype.ext ?_) ?_
  · rw [coe_eigenMap_fst, quadMap, Prod.fst_add, Prod.fst_add, Submodule.coe_add, Submodule.coe_add,
      coe_cG_fst, coe_LG_fst, coe_BilG_fst]
    simp only [eigenFst, eigenHeadRes, eigenLin, eigenBilOp, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, map_add, map_sub, ContinuousLinearMap.map_smul_of_tower]
    rw [← RCLike.ofReal_eq_complex_ofReal, ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
    module
  · rw [eigenMap_snd, quadMap, Prod.snd_add, Prod.snd_add, cG_snd, LG_snd, BilG_snd]
    simp only [eigenSnd, eigenHeadRes, map_add, map_sub, ContinuousLinearMap.map_smul_of_tower,
      map_smul, smul_eq_mul]
    ring

end Lin

end Quadratic

section Semantics

/-! ### The zeros of `G` are the normalized eigenpairs -/

section Border

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)

/-- **Bordered head injectivity**: the bordered head block `(ρ, e) ↦ (Mv ρ + e mv, b(ψ, ρ) + c e)`
is injective on `(P_S XR) × ℝ`. -/
def borderInj (D : EigenData hw) : Prop :=
  ∀ ρ ∈ realSub hw, headProj (𝕜 := ℂ) D.S ρ = ρ → ∀ e : ℝ, D.Mv ρ + e • D.mv = 0 →
    pairing h1 D.ψ ρ + D.c * e = 0 → ρ = 0 ∧ e = 0

private theorem headProj_Mv (D : EigenData hw) (z : X) :
    headProj (𝕜 := ℂ) D.S (D.Mv z) = D.Mv z :=
  DFunLike.congr_fun D.hPMv z

end Border

section ResidualCoeff

variable {M : Type*} [AddMonoid M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

private theorem headProj_eigenHeadRes (R : EigenRaw M w) (v : X) (l : ℝ) :
    headProj (𝕜 := ℂ) R.S (eigenHeadRes h R v l) = eigenHeadRes h R v l :=
  DFunLike.congr_fun (headProj_comp_headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) R.S) _

/-- The head residual on the head is the head of (E1). -/
theorem coeff_eigenHeadRes_of_mem (R : EigenRaw M w) (v : X) (l : ℝ) {n : M} (hn : n ∈ R.S) :
    coeff (eigenHeadRes h R v l) n =
      R.μ n * coeff v n + coeff (convCLM h R.q v) n - (l : ℂ) * coeff v n := by
  rw [eigenHeadRes, eigenPot, coeff_headProj, ite_eq_left hn, coeff_sub, coeff_add, Pi.sub_apply,
    Pi.add_apply, coeff_eigenLam, Set.indicator_of_mem (Finset.mem_coe.2 hn), coeff_real_smul]

private theorem eigenHeadRes_eq_zero (R : EigenRaw M w) (v : X) (l : ℝ)
    (hE1 : ∀ n ∈ R.S, R.μ n * coeff v n + coeff (convCLM h R.q v) n - (l : ℂ) * coeff v n = 0) :
    eigenHeadRes h R v l = 0 := ext_coeff <| funext fun n => by
  rw [coeff_zero, Pi.zero_apply]
  by_cases hn : n ∈ R.S
  · rw [coeff_eigenHeadRes_of_mem h R v l hn, hE1 n hn]
  · rw [eigenHeadRes, coeff_headProj, ite_eq_right hn]

/-- `G₁` on the head: `coeff (Mv ρ) n + (b(v, v) - 1) coeff mv n`. -/
theorem coeff_eigenFst_of_mem (R : EigenRaw M w) (v : X) (l : ℝ) {n : M} (hn : n ∈ R.S) :
    coeff (eigenFst h1 h R v l) n =
      coeff (R.Mv (eigenHeadRes h R v l)) n + ((pairing h1 v v - 1 : ℝ) : ℂ) * coeff R.mv n := by
  rw [eigenFst, coeff_add, coeff_add, coeff_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
    coeff_real_smul, coeff_tailProj, ite_eq_left hn, coeff_eigenTail_of_mem R _ hn, add_zero,
    add_zero]

end ResidualCoeff

section Zeros

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- `G₁` off the head: `coeff v n + (μ n - lbar)⁻¹ (coeff (q ⋆ v) n - (l - lbar) coeff v n)`. -/
theorem coeff_eigenFst_of_notMem (D : EigenData hw) (hmvS : headProj (𝕜 := ℂ) D.S D.mv = D.mv)
    (v : X) (l : ℝ) {n : M} (hn : n ∉ D.S) :
    coeff (eigenFst h1 h D.toEigenRaw v l) n = coeff v n +
      (D.μ n - (D.lbar : ℂ))⁻¹ * (coeff (convCLM h D.q v) n - ((l : ℂ) - D.lbar) * coeff v n) := by
  rw [eigenFst, eigenPot, coeff_add, coeff_add, coeff_add, Pi.add_apply, Pi.add_apply,
    Pi.add_apply, coeff_real_smul, coeff_eq_zero_of_headProj_eq (headProj_Mv hw D _) hn,
    coeff_eq_zero_of_headProj_eq hmvS hn, mul_zero, zero_add, zero_add, coeff_tailProj,
    ite_eq_right hn, coeff_eigenTail_of_notMem _ _ hn, coeff_sub, Pi.sub_apply, coeff_real_smul,
    Complex.ofReal_sub]

private theorem eigenMap_eq_zero_iff_fst_snd (D : EigenData hw) (y : realSub hw × ℝ) :
    eigenMap hw h1 h D y = 0 ↔ eigenFst h1 h D.toEigenRaw (y.1 : X) y.2 = 0 ∧
      eigenSnd h1 h D.toEigenRaw (y.1 : X) y.2 = 0 :=
  Prod.ext_iff.trans (and_congr Submodule.coe_eq_zero.symm Iff.rfl)

/-- **Eigenpairs are zeros** (no injectivity needed): (E1) `μ_n v_n + (q ⋆ v)_n - l v_n = 0`
for all `n` and (E2) `b(v, v) = 1` give `G(v, l) = 0`. -/
theorem eigenMap_eq_zero_of_eigen (D : EigenData hw)
    (hres : ∀ n ∉ D.S, D.μ n ≠ (D.lbar : ℂ)) (y : realSub hw × ℝ)
    (hE1 : ∀ n, D.μ n * coeff (y.1 : X) n + coeff (convCLM h D.q (y.1 : X)) n -
      (y.2 : ℂ) * coeff (y.1 : X) n = 0)
    (hE2 : pairing h1 (y.1 : X) (y.1 : X) = 1) : eigenMap hw h1 h D y = 0 := by
  have hρ : eigenHeadRes h D.toEigenRaw (y.1 : X) y.2 = 0 :=
    ext_coeff <| funext fun n => by
      rw [coeff_zero, Pi.zero_apply]
      by_cases hn : n ∈ D.S
      · rw [coeff_eigenHeadRes_of_mem h D.toEigenRaw (y.1 : X) y.2 hn, hE1 n]
      · rw [eigenHeadRes, coeff_headProj, ite_eq_right hn]
  refine Prod.ext (Subtype.ext ?_) ?_
  · change eigenFst h1 h D.toEigenRaw (y.1 : X) y.2 = 0
    rw [eigenFst, hρ, map_zero, hE2, sub_self, zero_smul, zero_add, zero_add]
    refine ext_coeff <| funext fun n => ?_
    rw [coeff_add, Pi.add_apply, coeff_zero, Pi.zero_apply]
    by_cases hn : n ∈ D.S
    · rw [coeff_tailProj, ite_eq_left hn, coeff_eigenTail_of_mem D.toEigenRaw _ hn, add_zero]
    · rw [coeff_tailProj, ite_eq_right hn, coeff_eigenTail_of_notMem D.toEigenRaw _ hn,
        eigenPot, coeff_sub, Pi.sub_apply, coeff_real_smul, Complex.ofReal_sub]
      have ht : coeff (y.1 : X) n + (D.μ n - (D.lbar : ℂ))⁻¹ *
          (coeff (convCLM h D.q (y.1 : X)) n - ((y.2 : ℂ) - D.lbar) * coeff (y.1 : X) n) =
          (D.μ n - (D.lbar : ℂ))⁻¹ *
            (D.μ n * coeff (y.1 : X) n + coeff (convCLM h D.q (y.1 : X)) n -
              (y.2 : ℂ) * coeff (y.1 : X) n) := by
        linear_combination (-coeff (y.1 : X) n) * inv_mul_cancel₀ (sub_ne_zero.2 (hres n hn))
      rw [ht, hE1 n, mul_zero]
  · change eigenSnd h1 h D.toEigenRaw (y.1 : X) y.2 = 0
    rw [eigenSnd, hρ, map_zero, hE2, sub_self, mul_zero, add_zero]

/-- Under bordered head injectivity, the zeros of `G` are exactly the normalized
eigenpairs: (E1) `μ_n v_n + (q ⋆ v)_n - l v_n = 0` for all `n`, and (E2) `b(v, v) = 1`. -/
theorem eigenMap_eq_zero_iff (D : EigenData hw) (hres : ∀ n ∉ D.S, D.μ n ≠ (D.lbar : ℂ))
    (hmvS : headProj (𝕜 := ℂ) D.S D.mv = D.mv) (hinj : borderInj hw h1 D) (y : realSub hw × ℝ) :
    eigenMap hw h1 h D y = 0 ↔
      (∀ n, D.μ n * coeff (y.1 : X) n + coeff (convCLM h D.q (y.1 : X)) n -
        (y.2 : ℂ) * coeff (y.1 : X) n = 0) ∧ pairing h1 (y.1 : X) (y.1 : X) = 1 := by
  refine ⟨fun h0 => ?_, fun hE => eigenMap_eq_zero_of_eigen hw h1 h D hres y hE.1 hE.2⟩
  obtain ⟨hG1, hG2⟩ := (eigenMap_eq_zero_iff_fst_snd hw h1 h D y).1 h0
  have hhead : D.Mv (eigenHeadRes h D.toEigenRaw (y.1 : X) y.2) +
      (pairing h1 (y.1 : X) (y.1 : X) - 1) • D.mv = 0 := ext_coeff <| funext fun n => by
    rw [coeff_add, Pi.add_apply, coeff_real_smul, coeff_zero, Pi.zero_apply]
    by_cases hn : n ∈ D.S
    · rw [← coeff_eigenFst_of_mem h1 h D.toEigenRaw (y.1 : X) y.2 hn, hG1, coeff_zero,
        Pi.zero_apply]
    · rw [coeff_eq_zero_of_headProj_eq (headProj_Mv hw D _) hn,
        coeff_eq_zero_of_headProj_eq hmvS hn, mul_zero, add_zero]
  obtain ⟨hρ, hb⟩ := hinj _ (eigenHeadRes_mem hw h D y.1.2 y.2)
    (headProj_eigenHeadRes h D.toEigenRaw (y.1 : X) y.2) _ hhead hG2
  refine ⟨fun n => ?_, sub_eq_zero.1 hb⟩
  by_cases hn : n ∈ D.S
  · rw [← coeff_eigenHeadRes_of_mem h D.toEigenRaw (y.1 : X) y.2 hn, hρ, coeff_zero, Pi.zero_apply]
  · have hG := congrFun (congrArg coeff hG1) n
    rw [coeff_eigenFst_of_notMem hw h1 h D hmvS (y.1 : X) y.2 hn,
      tail_coeff_eq (sub_ne_zero.2 (hres n hn)), coeff_zero, Pi.zero_apply] at hG
    exact (mul_eq_zero.1 hG).resolve_left (inv_ne_zero (sub_ne_zero.2 (hres n hn)))

end Zeros

end Semantics

section Radii

/-! ### Existence and uniqueness of the eigenpair -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The four radii bounds at `A = id`, `A† = B₀` give a unique nondegenerate zero of
`G` in the ball. -/
theorem existsUnique_eigenpair (D : EigenData hw) {ybar : realSub hw × ℝ}
    {B₀ : (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ)} {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ} (hr₀ : 0 < r₀)
    (hY₀ : ‖eigenMap hw h1 h D ybar‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (realSub hw × ℝ) - B₀‖ ≤ Z₀)
    (hZ₁ : ‖B₀ - quadDeriv (LG hw h1 h D) (BilG hw h1 D) ybar‖ ≤ Z₁)
    (hZ₂ : ‖quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D) +
      (quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D)).flip‖ ≤ Z₂)
    (hp : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0) :
    ∃ y ∈ Metric.ball ybar r₀, eigenMap hw h1 h D y = 0 ∧
      (ContinuousLinearMap.restrictScalars ℝ
        (quadDeriv (LG hw h1 h D) (BilG hw h1 D) y)).IsInvertible ∧
      ∀ z ∈ Metric.closedBall ybar r₀, eigenMap hw h1 h D z = 0 → z = y := by
  rw [eigenMap_eq_quadMap] at hY₀ ⊢
  exact quadratic_radii_theorem_nondegenerate_local (A := ContinuousLinearMap.id ℝ _)
    (A_dagger := B₀) hr₀ (by rwa [ContinuousLinearMap.id_apply])
    (by rwa [ContinuousLinearMap.id_comp]) (by rwa [ContinuousLinearMap.id_comp]) hZ₂ hp
    fun _ _ hxy => hxy

end Radii

section BorderInjIdx

/-! The index class of items 1–3: `[InvolutiveNeg M] [DecidableEq M]`. `h1` enters only the
declarations that mention it (items 2–3). -/

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]
  (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-! ### The real head space `V = (P_S XR) × ℝ`, its finite dimension and its projection -/

/-- **The real head space** `V = (P_S XR) × ℝ` inside `Y = XR × ℝ`: the pairs whose first
component is head-supported. -/
def headSubY (S : Finset M) : Submodule ℝ (realSub hw × ℝ) where
  carrier := {y | headProj (𝕜 := ℂ) S (y.1 : X) = y.1}
  zero_mem' := map_zero _
  add_mem' {a b} ha hb := (map_add _ (a.1 : X) b.1).trans (congrArg₂ (· + ·) ha hb)
  smul_mem' r y hy :=
    (ContinuousLinearMap.map_smul_of_tower _ r (y.1 : X)).trans (congrArg (r • ·) hy)

/-- Membership in the real head space: the first component is fixed by `P_S`. -/
theorem mem_headSubY {S : Finset M} {y : realSub hw × ℝ} :
    y ∈ headSubY hw S ↔ headProj (𝕜 := ℂ) S (y.1 : X) = y.1 :=
  Iff.rfl

/-- **The real head space is finite-dimensional over `ℝ`.** The head range is finite-dimensional
over `ℂ` (`finiteDimensional_range_headProj`), hence over `ℝ` (`Module.Finite.trans ℂ`), and
`y ↦ (y.1, y.2)` embeds `V` `ℝ`-linearly into its product with `ℝ`. -/
instance finiteDimensional_headSubY (S : Finset M) : FiniteDimensional ℝ (headSubY hw S) := by
  have := finiteDimensional_range_headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) S
  have : Module.Finite ℝ
      ↥(LinearMap.range (headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) S).toLinearMap) :=
    Module.Finite.trans ℂ _
  exact Module.Finite.of_injective
    ({ toFun := fun y => (⟨(y.1.1 : X), LinearMap.mem_range.2 ⟨(y.1.1 : X), y.2⟩⟩, y.1.2)
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : headSubY hw S →ₗ[ℝ]
        ↥(LinearMap.range (headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) S).toLinearMap) ×
          ℝ)
    fun _ _ h => Subtype.ext <| Prod.ext (Subtype.ext (congrArg (fun z => (z.1 : X)) h))
      (congrArg Prod.snd h :)

/-- **The projection** `P_V` of `Y` onto `V` along `(Q_S XR) × 0`: `P_S` on `XR` (it commutes with
`K` on a symmetric head), the identity on `ℝ`. -/
def headProjY (S : Finset M) (hS : ∀ n, -n ∈ S ↔ n ∈ S) :
    (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ) :=
  (restrictReal hw ((headProj (𝕜 := ℂ) S).restrictScalars ℝ) (conjReflL_headProj hw S hS)).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

/-- The first component of `P_V y` is `P_S v`. -/
theorem coe_headProjY_fst (S : Finset M) (hS : ∀ n, -n ∈ S ↔ n ∈ S) (y : realSub hw × ℝ) :
    ((headProjY hw S hS y).1 : X) = headProj (𝕜 := ℂ) S (y.1 : X) :=
  rfl

/-- The second component of `P_V y` is `l`. -/
theorem headProjY_snd (S : Finset M) (hS : ∀ n, -n ∈ S ↔ n ∈ S) (y : realSub hw × ℝ) :
    (headProjY hw S hS y).2 = y.2 :=
  rfl

/-- `P_V` fixes `V` (the `hP` of `eq_zero_of_mem_of_norm_sub_comp_lt_one`). -/
theorem headProjY_of_mem (S : Finset M) (hS : ∀ n, -n ∈ S ↔ n ∈ S) {y : realSub hw × ℝ}
    (hy : y ∈ headSubY hw S) : headProjY hw S hS y = y :=
  Prod.ext (Subtype.ext ((coe_headProjY_fst hw S hS y).trans hy)) (headProjY_snd hw S hS y)

/-! ### The bordered head block `A_N` on `Y` -/

/-- **The bordered head block** `A_N (ρ, e) = (Mv ρ + e mv, b(ψ, ρ) + c e)` on all of `Y`, in the
entry form `(A.coprod B).prod (C.coprod D)`. -/
def borderOp (D : EigenData hw) : (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ) :=
  ((restrictReal hw (D.Mv.restrictScalars ℝ) D.hKMv).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (⟨D.mv, D.hmv⟩ : realSub hw))).prod
    (((pairing h1 D.ψ).comp (realSub hw).subtypeL).coprod (D.c • ContinuousLinearMap.id ℝ ℝ))

/-- The first component of `A_N (ρ, e)` is `Mv ρ + e mv`. -/
theorem coe_borderOp_fst (D : EigenData hw) (y : realSub hw × ℝ) :
    ((borderOp hw h1 D y).1 : X) = D.Mv (y.1 : X) + y.2 • D.mv :=
  rfl

/-- The second component of `A_N (ρ, e)` is `b(ψ, ρ) + c e`. -/
theorem borderOp_snd (D : EigenData hw) (y : realSub hw × ℝ) :
    (borderOp hw h1 D y).2 = pairing h1 D.ψ (y.1 : X) + D.c * y.2 :=
  rfl

/-- **The bridge**: bordered head injectivity is injectivity of `A_N` on `V`. -/
theorem borderInj_iff (D : EigenData hw) :
    borderInj hw h1 D ↔ ∀ y ∈ headSubY hw D.S, borderOp hw h1 D y = 0 → y = 0 := by
  refine ⟨fun hinj y hy hy0 => ?_, fun hV ρ hρR hρS e hρ he => ?_⟩
  · obtain ⟨hρ0, he0⟩ := hinj (y.1 : X) y.1.2 ((mem_headSubY hw).1 hy) y.2
      ((coe_borderOp_fst hw h1 D y).symm.trans (congrArg (fun z => (z.1 : X)) hy0))
      ((borderOp_snd hw h1 D y).symm.trans (congrArg Prod.snd hy0))
    exact Prod.ext (Subtype.ext hρ0) he0
  · have h0 := hV (⟨ρ, hρR⟩, e) hρS
      (Prod.ext (Subtype.ext ((coe_borderOp_fst hw h1 D _).trans hρ))
        ((borderOp_snd hw h1 D _).trans he))
    exact ⟨congrArg (fun z => (z.1 : X)) h0, congrArg Prod.snd h0⟩

/-! ### The producer of `borderInj` from a norm bound -/

/-- **Border injectivity from a norm bound**: if `K` maps `V` into `V` and
`‖P_V - A_N ∘ K‖ < 1`, the bordered head block is injective on `V`. -/
theorem borderInj_of_norm_lt_one (D : EigenData hw) {K : (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ)}
    (hK : ∀ y ∈ headSubY hw D.S, K y ∈ headSubY hw D.S)
    (hBK : ‖headProjY hw D.S D.hS - borderOp hw h1 D ∘L K‖ < 1) : borderInj hw h1 D :=
  (borderInj_iff hw h1 D).2 fun _ hy hy0 =>
    eq_zero_of_mem_of_norm_sub_comp_lt_one (headSubY hw D.S)
      (fun _ hv => headProjY_of_mem hw D.S D.hS hv) hK hBK hy hy0

/-- **The defect form** `‖I - B₀‖ < 1` with `B₀ = A_N ∘ K + (I - P_V)`: then
`I - B₀ = P_V - A_N ∘ K`. -/
theorem borderInj_of_norm_id_sub_lt_one (D : EigenData hw)
    {K B₀ : (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ)}
    (hK : ∀ y ∈ headSubY hw D.S, K y ∈ headSubY hw D.S)
    (hB₀ : ∀ y, B₀ y = borderOp hw h1 D (K y) + (y - headProjY hw D.S D.hS y))
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (realSub hw × ℝ) - B₀‖ < 1) : borderInj hw h1 D := by
  refine borderInj_of_norm_lt_one hw h1 D hK ((congrArg norm ?_).trans_lt hZ₀)
  refine ContinuousLinearMap.ext fun y => ?_
  rw [sub_apply, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hB₀]
  abel

end BorderInjIdx

section HeadBounds

/-! ### The head projection and `Mv P_S + T_t` (`[DecidableEq M]`) -/

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- `‖Mv P_S + T_t‖ ≤ max sM t` (by `norm_comp_headProj_add_diagCLM_le`). -/
theorem norm_eigenBilOp_le (R : EigenRaw M w)
    (hPMP : headProj (𝕜 := ℂ) R.S ∘L (R.Mv ∘L headProj (𝕜 := ℂ) R.S) =
      R.Mv ∘L headProj (𝕜 := ℂ) R.S)
    {sM t : ℝ} (hMv : ‖R.Mv‖ ≤ sM)
    (ht : ∀ n, ‖tailSymbol (↑R.S : Set M) (fun n => R.μ n - (R.lbar : ℂ)) n‖ ≤ t) :
    ‖eigenBilOp R‖ ≤ max sM t :=
  norm_comp_headProj_add_diagCLM_le R.S R.Mv
    hPMP _ R.hr (fun _ hk => tailSymbol_of_mem (Finset.mem_coe.2 hk)) hMv ht

end HeadBounds

section WithPot

/-! ### The data at a finite potential `q̄` (`[DecidableEq M]`) -/

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The raw data with the potential `q` replaced by `q̄`. -/
def EigenRaw.withPot (R : EigenRaw M w) (qbar : X) : EigenRaw M w := { R with q := qbar }

end WithPot

section Split

/-! ### The potential split and the head Jacobian block (`[AddMonoid M]`) -/

variable {M : Type*} [AddMonoid M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- The first component of `G` at the finite potential `q̄`, unfolded (the residual
`G_{q̄}` that a consumer evaluates for `hfin₁`). -/
theorem eigenFst_withPot (R : EigenRaw M w) (qbar v : X) (l : ℝ) :
    eigenFst h1 h (R.withPot qbar) v l =
      R.Mv (headProj (𝕜 := ℂ) R.S (eigenLam R v + convCLM h qbar v - l • v)) +
        (pairing h1 v v - 1) • R.mv + tailProj (𝕜 := ℂ) R.S v +
          eigenTail R (convCLM h qbar v - (l - R.lbar) • v) :=
  rfl

/-- The second component of `G` at the finite potential `q̄`, unfolded (the residual
`G_{q̄}` that a consumer evaluates for `hfin₂`). -/
theorem eigenSnd_withPot (R : EigenRaw M w) (qbar v : X) (l : ℝ) :
    eigenSnd h1 h (R.withPot qbar) v l =
      pairing h1 R.ψ (headProj (𝕜 := ℂ) R.S (eigenLam R v + convCLM h qbar v - l • v)) +
        R.c * (pairing h1 v v - 1) :=
  rfl

/-- The first component of `G` at `q` minus the one at `q̄` is
`(Mv P_S + T_t) ((q - q̄) ⋆ v)`. -/
theorem eigenFst_sub_withPot (R : EigenRaw M w) (qbar v : X) (l : ℝ) :
    eigenFst h1 h R v l - eigenFst h1 h (R.withPot qbar) v l =
      eigenBilOp R (convCLM h (R.q - qbar) v) := by
  rw [eigenFst_withPot, eigenFst, eigenHeadRes, eigenPot, map_sub (convCLM h), sub_apply,
    eigenBilOp, add_apply, ContinuousLinearMap.comp_apply]
  simp only [map_add, map_sub]
  abel

/-- The second component of `G` at `q` minus the one at `q̄` is
`b(ψ, P_S ((q - q̄) ⋆ v))`. -/
theorem eigenSnd_sub_withPot (R : EigenRaw M w) (qbar v : X) (l : ℝ) :
    eigenSnd h1 h R v l - eigenSnd h1 h (R.withPot qbar) v l =
      pairing h1 R.ψ (headProj (𝕜 := ℂ) R.S (convCLM h (R.q - qbar) v)) := by
  rw [eigenSnd_withPot, eigenSnd, eigenHeadRes, eigenPot, map_sub (convCLM h), sub_apply]
  simp only [map_add, map_sub]
  ring

/-- The `v → v` block `P_S (Λ_S + q̄ ⋆ - lbar) P_S` of the complexified head Jacobian at
the finite potential `q̄`. -/
def eigenHeadJac (R : EigenRaw M w) (qbar : X) : X →L[ℂ] X :=
  headProj (𝕜 := ℂ) R.S ∘L
    (eigenLam R + convCLM h qbar - (R.lbar : ℂ) • ContinuousLinearMap.id ℂ X) ∘L
      headProj (𝕜 := ℂ) R.S

end Split

section Y0

/-! ### The `Y₀` face (`[AddCommGroup M]`) -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- **The `Y₀` face.** The residual at `ȳ` is the finite residual at `q̄` plus the potential
split `(Mv P_S + T_t, b(ψ, P_S ·)) ((q - q̄) ⋆ v̄)`. -/
theorem norm_eigenMap_le (D : EigenData hw) (qbar : X) (ybar : realSub hw × ℝ)
    {Yfin sM t sψ ρq nv : ℝ}
    (hfin₁ : ‖eigenFst h1 h (D.toEigenRaw.withPot qbar) (ybar.1 : X) ybar.2‖ ≤ Yfin)
    (hfin₂ : |eigenSnd h1 h (D.toEigenRaw.withPot qbar) (ybar.1 : X) ybar.2| ≤ Yfin)
    (hMv : ‖D.Mv‖ ≤ sM)
    (ht : ∀ n, ‖tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ)) n‖ ≤ t)
    (hψn : ‖D.ψ‖ ≤ sψ) (hδq : ‖D.q - qbar‖ ≤ ρq) (hv : ‖(ybar.1 : X)‖ ≤ nv) :
    ‖eigenMap hw h1 h D ybar‖ ≤ Yfin + max (max sM t) sψ * (Kc * ρq * nv) := by
  have hmax0 : 0 ≤ max (max sM t) sψ :=
    ((norm_nonneg _).trans hMv).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hδ :=
    (norm_convCLM_apply_le h _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hδq (RowBound.nonneg h)) hv (norm_nonneg _)
      (mul_nonneg (RowBound.nonneg h) ((norm_nonneg _).trans hδq)))
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [← Submodule.norm_coe, coe_eigenMap_fst,
      sub_eq_iff_eq_add'.1 (eigenFst_sub_withPot h1 h D.toEigenRaw qbar (ybar.1 : X) ybar.2)]
    exact (norm_add_le _ _).trans (add_le_add hfin₁
      ((ContinuousLinearMap.le_of_opNorm_le _ (norm_eigenBilOp_le D.toEigenRaw
        (by rw [← ContinuousLinearMap.comp_assoc, D.hPMv]) hMv ht)
        _).trans (mul_le_mul (le_max_left _ _) hδ (norm_nonneg _) hmax0)))
  · rw [Real.norm_eq_abs, eigenMap_snd,
      sub_eq_iff_eq_add'.1 (eigenSnd_sub_withPot h1 h D.toEigenRaw qbar (ybar.1 : X) ybar.2)]
    exact (abs_add_le _ _).trans (add_le_add hfin₂ ((abs_pairing_le h1 _ _).trans
      (mul_le_mul (hψn.trans (le_max_right _ _)) ((norm_headProj_apply_le _ _).trans hδ)
        (norm_nonneg _) hmax0)))

end Y0

section MvReal

/-! ### The column `Mv v̄` of `B₀` is real (`[InvolutiveNeg M]`) -/

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n)

/-- `Mv v̄ ∈ XR`. -/
private theorem Mv_mem_realSub (D : EigenData hw) (vbar : realSub hw) :
    D.Mv (vbar : X) ∈ realSub hw :=
  (mem_realSub hw).2 ((D.hKMv _).trans (congrArg D.Mv ((mem_realSub hw).1 vbar.2)))

end MvReal

section Z0

/-! ### `B₀` and the `Z₀` face by the block route (`[AddCommGroup M]`) -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- At a real finite potential `q̄` the head Jacobian block commutes with `K`. -/
theorem conjReflL_eigenHeadJac (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (x : X) :
    conjReflL hw (eigenHeadJac h D.toEigenRaw qbar x) =
      eigenHeadJac h D.toEigenRaw qbar (conjReflL hw x) := by
  have hA : ∀ y, conjReflL hw ((eigenLam D.toEigenRaw + convCLM h qbar -
      (D.lbar : ℂ) • ContinuousLinearMap.id ℂ X) y) = (eigenLam D.toEigenRaw + convCLM h qbar -
        (D.lbar : ℂ) • ContinuousLinearMap.id ℂ X) (conjReflL hw y) := fun y => by
    rw [sub_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub, map_add,
      conjReflL_eigenLam hw D, conjReflL_convCLM hw h, (mem_realSub hw).1 hqbar, conjReflL_smul,
      Complex.conj_ofReal, sub_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply]
  simp only [eigenHeadJac, ContinuousLinearMap.comp_apply, conjReflL_headProj hw D.S D.hS, hA]

/-- **`B₀`.** The preconditioned approximate derivative `A_N J̄ ⊕ Q_S` on `Y = XR × ℝ`: the
bordered head approximate inverse `A_N(ρ, e) = (Mv ρ + e mv, b(ψ, ρ) + c e)` composed after the
bordered head Jacobian `J̄(h, η) = (eigenHeadJac h - η v̄, 2 b(v̄, P_S h))` at `(v̄, lbar)` with
the potential `q̄`, plus the identity tail `Q_S`. -/
def eigenB0 (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw) (vbar : realSub hw) :
    (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ) :=
  ((restrictReal hw ((D.Mv ∘L eigenHeadJac h D.toEigenRaw qbar).restrictScalars ℝ)
          (fun x => (D.hKMv _).trans
            (congrArg D.Mv (conjReflL_eigenHeadJac hw h D qbar hqbar x)))).comp
        (ContinuousLinearMap.fst ℝ (realSub hw) ℝ) -
      (ContinuousLinearMap.toSpanSingleton ℝ
        (⟨D.Mv (vbar : X), Mv_mem_realSub hw D vbar⟩ : realSub hw)).comp
        (ContinuousLinearMap.snd ℝ (realSub hw) ℝ) +
      (ContinuousLinearMap.toSpanSingleton ℝ (⟨D.mv, D.hmv⟩ : realSub hw)).comp
        ((2 : ℝ) • ((pairing h1 (vbar : X)).comp ((headProj (𝕜 := ℂ) D.S).restrictScalars ℝ)).comp
          ((realSub hw).subtypeL.comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ))) +
      (restrictReal hw ((tailProj (𝕜 := ℂ) D.S).restrictScalars ℝ)
          (conjReflL_tailProj hw D.S D.hS)).comp
        (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)).prod
    (((pairing h1 D.ψ).comp ((eigenHeadJac h D.toEigenRaw qbar).restrictScalars ℝ)).comp
        ((realSub hw).subtypeL.comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)) -
      (ContinuousLinearMap.toSpanSingleton ℝ (pairing h1 D.ψ (vbar : X))).comp
        (ContinuousLinearMap.snd ℝ (realSub hw) ℝ) +
      (2 * D.c) • ((pairing h1 (vbar : X)).comp ((headProj (𝕜 := ℂ) D.S).restrictScalars ℝ)).comp
        ((realSub hw).subtypeL.comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)))

/-- The first component of `B₀ y` in closed form. -/
theorem coe_eigenB0_fst (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (y : realSub hw × ℝ) :
    ((eigenB0 hw h1 h D qbar hqbar vbar y).1 : X) =
      D.Mv (eigenHeadJac h D.toEigenRaw qbar (y.1 : X)) - y.2 • D.Mv (vbar : X) +
        (2 * pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S (y.1 : X))) • D.mv +
          tailProj (𝕜 := ℂ) D.S (y.1 : X) :=
  rfl

/-- The second component of `B₀ y` in closed form. -/
theorem eigenB0_snd (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (y : realSub hw × ℝ) :
    (eigenB0 hw h1 h D qbar hqbar vbar y).2 =
      pairing h1 D.ψ (eigenHeadJac h D.toEigenRaw qbar (y.1 : X)) -
        y.2 * pairing h1 D.ψ (vbar : X) +
          2 * D.c * pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S (y.1 : X)) :=
  rfl

/-- **The `Z₀` face** (block route, `opNorm_le_max_of_rows`): the four blocks of `E = id - B₀` are
`E(x, 0)₁ = P_S x - Mv (eigenHeadJac x) - 2 b(v̄, P_S x) mv` (`hE₁₁`), `E(0, η)₁ = η Mv v̄`,
`E(x, 0)₂ = -(b(ψ, eigenHeadJac x) + 2 c b(v̄, P_S x))` (`hE₂₁`) and
`E(0, η)₂ = η (1 + b(ψ, v̄))`. -/
theorem norm_id_sub_eigenB0_le (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) {z₁₁ z₂₁ : ℝ}
    (hE₁₁ : ∀ x ∈ realSub hw, ‖headProj (𝕜 := ℂ) D.S x - D.Mv (eigenHeadJac h D.toEigenRaw qbar x) -
      (2 * pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S x)) • D.mv‖ ≤ z₁₁ * ‖x‖)
    (hE₂₁ : ∀ x ∈ realSub hw, |pairing h1 D.ψ (eigenHeadJac h D.toEigenRaw qbar x) +
      2 * D.c * pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S x)| ≤ z₂₁ * ‖x‖) :
    ‖ContinuousLinearMap.id ℝ (realSub hw × ℝ) - eigenB0 hw h1 h D qbar hqbar vbar‖ ≤
      max (z₁₁ + ‖D.Mv (vbar : X)‖) (z₂₁ + |1 + pairing h1 D.ψ (vbar : X)|) := by
  have he := single_zero_mem_realSub (M := M) (w := w) hw 1
  have hpos : 0 < ‖(single 0 ((1 : ℝ) : ℂ) : X)‖ := norm_pos_iff.2 (single_ne_zero (by norm_num))
  have hz₁₁ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hE₁₁ _ he)) hpos
  have hz₂₁ := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hE₂₁ _ he)) hpos
  refine opNorm_le_max_of_rows _ hz₁₁ (norm_nonneg _) hz₂₁ (abs_nonneg _) (fun x => ?_)
    (fun η => ?_) (fun x => ?_) (fun η => ?_)
  · rw [← Submodule.norm_coe]
    refine (congrArg norm ?_).trans_le ((hE₁₁ (x : X) x.2).trans_eq (by rw [Submodule.norm_coe]))
    rw [sub_apply, ContinuousLinearMap.id_apply, Prod.fst_sub, Submodule.coe_sub, coe_eigenB0_fst]
    dsimp only
    rw [zero_smul, sub_zero, tailProj_eq_id_sub_headProj, sub_apply, ContinuousLinearMap.id_apply]
    abel
  · refine le_of_eq ?_
    rw [← Submodule.norm_coe, sub_apply, ContinuousLinearMap.id_apply, Prod.fst_sub,
      Submodule.coe_sub, coe_eigenB0_fst]
    dsimp only
    simp only [ZeroMemClass.coe_zero, map_zero, mul_zero, zero_smul, add_zero, zero_sub, neg_neg]
    rw [norm_smul, mul_comm]
  · rw [Real.norm_eq_abs, sub_apply, ContinuousLinearMap.id_apply, Prod.snd_sub, eigenB0_snd]
    dsimp only
    rw [zero_mul, sub_zero, zero_sub, abs_neg]
    exact (hE₂₁ (x : X) x.2).trans_eq (by rw [Submodule.norm_coe])
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_apply, ContinuousLinearMap.id_apply, Prod.snd_sub,
      eigenB0_snd]
    dsimp only
    simp only [ZeroMemClass.coe_zero, map_zero, mul_zero, add_zero]
    rw [show η - (0 - η * pairing h1 D.ψ (vbar : X)) = (1 + pairing h1 D.ψ (vbar : X)) * η by
      ring, abs_mul]

end Z0

section HeadAlgebra

/-! ### The head part acts on the head (`[DecidableEq M]`) -/

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- `Λ_S P_S = Λ_S`: the head part of the symbol vanishes off the head. -/
private theorem eigenLam_headProj (R : EigenRaw M w) (x : X) :
    eigenLam R (headProj (𝕜 := ℂ) R.S x) = eigenLam R x :=
  ext_coeff <| funext fun n => by
    rw [coeff_eigenLam, coeff_eigenLam, coeff_headProj]
    by_cases hn : n ∈ R.S
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, Set.indicator_of_notMem (mt Finset.mem_coe.1 hn), zero_mul, zero_mul]

/-- `P_S P_S = P_S`, applied. -/
private theorem headProj_headProj_apply (S : Finset M) (x : X) :
    headProj (𝕜 := ℂ) S (headProj (𝕜 := ℂ) S x) = headProj (𝕜 := ℂ) S x :=
  DFunLike.congr_fun (headProj_comp_headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) S) x

/-- `T_t` vanishes on head-supported vectors. -/
private theorem eigenTail_eq_zero_of_headProj_eq (R : EigenRaw M w) {x : X}
    (hx : headProj (𝕜 := ℂ) R.S x = x) : eigenTail R x = 0 :=
  ext_coeff <| funext fun n => by
    rw [coeff_zero, Pi.zero_apply]
    by_cases hn : n ∈ R.S
    · exact coeff_eigenTail_of_mem R x hn
    · rw [coeff_eigenTail_of_notMem R x hn, ← hx, coeff_headProj, ite_eq_right hn, mul_zero]

end HeadAlgebra

section Z1

/-! ### The `Z₁` face (`[AddCommGroup M]`) -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- **Exactness (vector row).** At a head-supported centre `(v̄, lbar)`, `DG(ȳ) - B₀` has
no `λ`-column; at `q = q̄`, its head-output/head-input block vanishes: its vector row is the
restricted tail defect at `q̄` plus the potential split `(Mv P_S + T_t) ((q - q̄) ⋆ ·)`. -/
theorem coe_quadDeriv_sub_eigenB0_fst (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (hvS : headProj (𝕜 := ℂ) D.S (vbar : X) = vbar) (y : realSub hw × ℝ) :
    (((quadDeriv (LG hw h1 h D) (BilG hw h1 D) (vbar, D.lbar) -
        eigenB0 hw h1 h D qbar hqbar vbar) y).1 : X) =
      D.Mv (headProj (𝕜 := ℂ) D.S (convCLM h qbar (tailProj (𝕜 := ℂ) D.S (y.1 : X)))) +
        eigenTail D.toEigenRaw (convCLM h qbar (y.1 : X)) +
          eigenBilOp D.toEigenRaw (convCLM h (D.q - qbar) (y.1 : X)) := by
  have hBv : eigenBilOp D.toEigenRaw (vbar : X) = D.Mv (vbar : X) := by
    rw [eigenBilOp, add_apply, ContinuousLinearMap.comp_apply, hvS,
      eigenTail_eq_zero_of_headProj_eq D.toEigenRaw hvS, add_zero]
  have hb : pairing h1 (vbar : X) (y.1 : X) =
      pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S (y.1 : X)) := by
    rw [← pairing_headProj_comm, hvS]
  have hsm : ∀ z : X, (D.lbar : ℂ) • z = D.lbar • z := fun z => by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]
  rw [sub_apply, Prod.fst_sub, Submodule.coe_sub, add_apply, add_apply,
    ContinuousLinearMap.flip_apply, Prod.fst_add, Prod.fst_add, Submodule.coe_add,
    Submodule.coe_add, coe_LG_fst, coe_BilG_fst, coe_BilG_fst, coe_eigenB0_fst]
  dsimp only
  rw [hBv, pairing_comm h1 (y.1 : X) (vbar : X), hb, tailProj_eq_id_sub_headProj]
  simp only [eigenLin, eigenHeadJac, eigenBilOp, eigenPot, tailProj_eq_id_sub_headProj, add_apply,
    sub_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_add,
    map_sub, ContinuousLinearMap.map_smul_of_tower, eigenLam_headProj, headProj_headProj_apply, hsm]
  module

/-- **Exactness (scalar row).** The scalar row of `DG(ȳ) - B₀` is the scalar-row
leakage `b(ψ, P_S (q̄ ⋆ Q_S ·))` plus the potential split `b(ψ, P_S ((q - q̄) ⋆ ·))`. -/
theorem quadDeriv_sub_eigenB0_snd (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (hvS : headProj (𝕜 := ℂ) D.S (vbar : X) = vbar) (y : realSub hw × ℝ) :
    ((quadDeriv (LG hw h1 h D) (BilG hw h1 D) (vbar, D.lbar) -
        eigenB0 hw h1 h D qbar hqbar vbar) y).2 =
      pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S (convCLM h qbar (tailProj (𝕜 := ℂ) D.S (y.1 : X)))) +
        pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S (convCLM h (D.q - qbar) (y.1 : X))) := by
  have hb : pairing h1 (vbar : X) (y.1 : X) =
      pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S (y.1 : X)) := by
    rw [← pairing_headProj_comm, hvS]
  have hsm : ∀ z : X, (D.lbar : ℂ) • z = D.lbar • z := fun z => by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]
  rw [sub_apply, Prod.snd_sub, add_apply, add_apply, ContinuousLinearMap.flip_apply, Prod.snd_add,
    Prod.snd_add, LG_snd, BilG_snd, BilG_snd, eigenB0_snd]
  dsimp only
  rw [hvS, pairing_comm h1 (y.1 : X) (vbar : X), hb, tailProj_eq_id_sub_headProj]
  simp only [eigenHeadJac, eigenPot, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    ContinuousLinearMap.map_smul_of_tower, eigenLam_headProj, headProj_headProj_apply, hsm,
    smul_eq_mul]
  ring

/-- **The `Z₁` face.** With `β` the ℓ¹ symbol of `-q̄` (`hβ`), the vector row of
`B₀ - DG(ȳ)` is minus the shipped tail defect plus the potential split, and its scalar row is
the leakage (`hleak`) plus the split: `‖B₀ - DG(ȳ)‖ ≤ max(√(H² + T²), ℓ) + max(sM, t, sψ) Kc ρq`. -/
theorem norm_eigenB0_sub_quadDeriv_le (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (hvS : headProj (𝕜 := ℂ) D.S (vbar : X) = vbar) {v : M → ℝ}
    [PosWeight v] {C : ℝ} (hC : Moderate (FiberTrivialization.weight (E := WeightedScalar ℂ w)) v C)
    (β : lpOneAlg M (WeightedScalar ℂ v)) (hβ : symbolAction₀ (p := 2) hC β = -convCLM h qbar)
    {H T ℓ sM t sψ ρq : ℝ}
    (hH : ‖D.Mv ∘L headProj (𝕜 := ℂ) D.S ∘L symbolAction₀ hC β ∘L tailProj (𝕜 := ℂ) D.S‖ ≤ H)
    (hT : ‖diagCLM (E := WeightedScalar ℂ w) (p := 2)
      (tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ))) D.hr ∘L symbolAction₀ hC β‖ ≤ T)
    (hleak : ∀ x ∈ realSub hw, |pairing h1 D.ψ (headProj (𝕜 := ℂ) D.S
      (convCLM h qbar (tailProj (𝕜 := ℂ) D.S x)))| ≤ ℓ * ‖x‖)
    (hMv : ‖D.Mv‖ ≤ sM)
    (ht : ∀ n, ‖tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ)) n‖ ≤ t)
    (hψn : ‖D.ψ‖ ≤ sψ) (hδq : ‖D.q - qbar‖ ≤ ρq) :
    ‖eigenB0 hw h1 h D qbar hqbar vbar - quadDeriv (LG hw h1 h D) (BilG hw h1 D) (vbar, D.lbar)‖ ≤
      max (√(H ^ 2 + T ^ 2)) ℓ + max (max sM t) sψ * (Kc * ρq) := by
  have hmax0 : 0 ≤ max (max sM t) sψ :=
    ((norm_nonneg _).trans hMv).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hKρ := mul_nonneg (RowBound.nonneg h) ((norm_nonneg _).trans hδq)
  have hsq : 0 ≤ max (√(H ^ 2 + T ^ 2)) ℓ := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hδ : ∀ x : X, ‖convCLM h (D.q - qbar) x‖ ≤ Kc * ρq * ‖x‖ := fun x =>
    (norm_convCLM_apply_le h _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδq (RowBound.nonneg h))
        (norm_nonneg _))
  have hβ' : ∀ z : X, symbolAction₀ (p := 2) hC β z = -convCLM h qbar z := fun z => by
    rw [hβ, neg_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hsq (mul_nonneg hmax0 hKρ)) fun y => ?_
  rw [sub_apply, ← neg_sub, ← sub_apply, norm_neg]
  have hy1 := (Submodule.norm_coe _).trans_le (norm_fst_le y)
  have hε : ∀ z : X, ‖z‖ ≤ ‖convCLM h (D.q - qbar) (y.1 : X)‖ →
      max sM t * ‖z‖ ≤ max (max sM t) sψ * (Kc * ρq) * ‖y‖ := fun z hz =>
    (mul_le_mul (le_max_left _ _) (hz.trans ((hδ _).trans (mul_le_mul_of_nonneg_left hy1 hKρ)))
      (norm_nonneg _) hmax0).trans_eq (by ring)
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have hTD : D.Mv (headProj (𝕜 := ℂ) D.S (convCLM h qbar (tailProj (𝕜 := ℂ) D.S (y.1 : X)))) +
        eigenTail D.toEigenRaw (convCLM h qbar (y.1 : X)) =
          -(tailDefect hC β D.S D.Mv (tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ)))
            D.hr (y.1 : X)) := by
      rw [tailDefect_apply, hβ', hβ']
      simp only [map_neg, neg_add, neg_neg]
      rfl
    rw [← Submodule.norm_coe, coe_quadDeriv_sub_eigenB0_fst hw h1 h D qbar hqbar vbar hvS y, hTD]
    refine (norm_add_le _ _).trans ((add_le_add ?_ ?_).trans_eq (add_mul _ _ _).symm)
    · exact (norm_neg _).trans_le ((ContinuousLinearMap.le_of_opNorm_le _
        (norm_tailDefect_le hC β D.S D.Mv _ D.hr D.hPMv
          (fun _ hk => tailSymbol_of_mem (Finset.mem_coe.2 hk)) hH hT) _).trans
        (mul_le_mul (le_max_left _ _) hy1 (norm_nonneg _) hsq))
    · exact (ContinuousLinearMap.le_of_opNorm_le _
        (norm_eigenBilOp_le D.toEigenRaw
        (by rw [← ContinuousLinearMap.comp_assoc, D.hPMv]) hMv ht) _).trans (hε _ le_rfl)
  · rw [Real.norm_eq_abs, quadDeriv_sub_eigenB0_snd hw h1 h D qbar hqbar vbar hvS y]
    refine (abs_add_le _ _).trans ((add_le_add ((hleak _ y.1.2).trans
      (mul_le_mul (le_max_right _ _) hy1 (norm_nonneg _) hsq)) ((abs_pairing_le h1 _ _).trans
        ?_)).trans_eq (add_mul _ _ _).symm)
    exact (mul_le_mul (hψn.trans (le_max_right _ _))
      ((norm_headProj_apply_le _ _).trans ((hδ _).trans (mul_le_mul_of_nonneg_left hy1 hKρ)))
        (norm_nonneg _) hmax0).trans_eq (by ring)

end Z1

section Leak

/-! ### The `ℓ_rows` producer of `hleak` (`[AddCommGroup M]`) -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- **Support.** For `q̄` supported in the band `B`, the head leakage
`P_S (q̄ ⋆ Q_S x)` is supported on the boundary rows `leakRows S B`. -/
theorem coeff_headProj_convCLM_tailProj_eq_zero {S B : Finset M} {qbar : X}
    (hB : ∀ l ∉ B, coeff qbar l = 0) (x : X) {n : M} (hn : n ∉ leakRows S B) :
    coeff (headProj (𝕜 := ℂ) S (convCLM h qbar (tailProj (𝕜 := ℂ) S x))) n = 0 := by
  rw [coeff_headProj]
  by_cases hnS : n ∈ S
  · rw [ite_eq_left hnS, coeff_convCLM, DiscreteConvolution.addRingConvolution_apply]
    refine (tsum_congr fun ab => ?_).trans tsum_zero
    by_cases hb : (ab : M × M).1 ∈ B
    · have h2 : (ab : M × M).2 ∈ S := by
        by_contra h2
        refine hn (Finset.mem_filter.2 ⟨hnS, (ab : M × M).1, hb, fun hm => h2 ?_⟩)
        rwa [sub_eq_of_eq_add' (DiscreteConvolution.mem_addFiber.1 ab.2).symm] at hm
      rw [coeff_tailProj, ite_eq_left h2, mul_zero]
    · rw [hB _ hb, zero_mul]
  · exact ite_eq_right hnS

/-- **The producer.** `|b(ψ, P_S (q̄ ⋆ Q_S x))| ≤ ‖P_{leakRows} ψ‖ s_L ‖x‖`: the
scalar-row leakage `ℓ_rows = ‖ψ|_rows‖ s_L`, by the row restriction `abs_pairing_le_headProj`. -/
theorem abs_pairing_leak_le {S B : Finset M} {qbar : X} (hB : ∀ l ∉ B, coeff qbar l = 0) (ψ : X)
    {sL : ℝ} (hsL : ‖headProj (𝕜 := ℂ) S ∘L convCLM h qbar ∘L tailProj (𝕜 := ℂ) S‖ ≤ sL)
    (x : X) :
    |pairing h1 ψ (headProj (𝕜 := ℂ) S (convCLM h qbar (tailProj (𝕜 := ℂ) S x)))| ≤
      ‖headProj (𝕜 := ℂ) (leakRows S B) ψ‖ * sL * ‖x‖ :=
  (abs_pairing_le_headProj h1 (leakRows S B) ψ _
    fun _ hn => coeff_headProj_convCLM_tailProj_eq_zero h hB x hn).trans <| by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_of_opNorm_le _ hsL x) (norm_nonneg _)

end Leak

section Z2

/-! ### The `Z₂` face (`[InvolutiveNeg M]`) -/

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)

/-- `‖Bil_G‖ ≤ max(max(sM, t) + sm, sψ + |c|)`, at `BilG`'s own type. -/
theorem norm_BilG_le (D : EigenData hw) {sM t sm sψ : ℝ} (hMv : ‖D.Mv‖ ≤ sM)
    (ht : ∀ n, ‖tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ)) n‖ ≤ t)
    (hmn : ‖D.mv‖ ≤ sm) (hψn : ‖D.ψ‖ ≤ sψ) :
    ‖BilG hw h1 D‖ ≤ max (max sM t + sm) (sψ + |D.c|) := by
  have hst0 : 0 ≤ max sM t := (norm_nonneg _).trans (hMv.trans (le_max_left _ _))
  refine ContinuousLinearMap.opNorm_le_bound₂ _
    ((add_nonneg hst0 ((norm_nonneg _).trans hmn)).trans (le_max_left _ _)) fun y y' => ?_
  have hy1 := (Submodule.norm_coe _).trans_le (norm_fst_le y)
  have hy'1 := (Submodule.norm_coe _).trans_le (norm_fst_le y')
  have hy2 := (Real.norm_eq_abs y.2).symm.trans_le (norm_snd_le y)
  have hb :=
    (abs_pairing_le h1 _ _).trans (mul_le_mul hy1 hy'1 (norm_nonneg _) (norm_nonneg _))
  have hyy : 0 ≤ ‖y‖ * ‖y'‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [← Submodule.norm_coe, coe_BilG_fst]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine (add_le_add ((mul_le_mul hy2 ((ContinuousLinearMap.le_of_opNorm_le _
      (norm_eigenBilOp_le D.toEigenRaw
        (by rw [← ContinuousLinearMap.comp_assoc, D.hPMv]) hMv ht) _).trans
        (mul_le_mul_of_nonneg_left hy'1 hst0)) (norm_nonneg _) (norm_nonneg _)).trans_eq
          (mul_left_comm _ _ _)) (mul_le_mul hb hmn (norm_nonneg _) hyy)).trans ?_
    rw [mul_comm (‖y‖ * ‖y'‖) sm, ← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (norm_nonneg _)
  · rw [Real.norm_eq_abs, BilG_snd]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul]
    refine (add_le_add (mul_le_mul hy2 ((abs_pairing_le h1 _ _).trans
      (mul_le_mul hψn ((norm_headProj_apply_le _ _).trans hy'1) (norm_nonneg _)
        ((norm_nonneg _).trans hψn))) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))).trans ?_
    rw [mul_left_comm, ← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
      (norm_nonneg _)

/-- `‖B + B.flip‖ ≤ 2 ‖Bil_G‖` for `B = quadComp id Bil_G`. -/
theorem norm_quadComp_BilG_add_flip_le_two_mul (D : EigenData hw) :
    ‖quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D) +
      (quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D)).flip‖ ≤
        2 * ‖BilG hw h1 D‖ := by
  refine (norm_quadComp_add_flip_le _ _).trans (mul_le_mul_of_nonneg_left ?_ zero_le_two)
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _) fun y y' => ?_
  rw [quadComp_apply, ContinuousLinearMap.id_apply]
  exact (BilG hw h1 D).le_opNorm₂ y y'

/-- **The `Z₂` face.** `‖B + B.flip‖ ≤ 2 max(max(sM, t) + sm, sψ + |c|)`. -/
theorem norm_quadComp_BilG_add_flip_le (D : EigenData hw) {sM t sm sψ : ℝ} (hMv : ‖D.Mv‖ ≤ sM)
    (ht : ∀ n, ‖tailSymbol (↑D.S : Set M) (fun n => D.μ n - (D.lbar : ℂ)) n‖ ≤ t)
    (hmn : ‖D.mv‖ ≤ sm) (hψn : ‖D.ψ‖ ≤ sψ) :
    ‖quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D) +
      (quadComp (ContinuousLinearMap.id ℝ (realSub hw × ℝ)) (BilG hw h1 D)).flip‖ ≤
        2 * max (max sM t + sm) (sψ + |D.c|) :=
  (norm_quadComp_BilG_add_flip_le_two_mul hw h1 D).trans
    (mul_le_mul_of_nonneg_left (norm_BilG_le hw h1 D hMv ht hmn hψn) zero_le_two)

end Z2

section BorderInjFromB0

/-! ### The bordered head Jacobian `J̄` and the identification of `B₀` -/

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n) {Kc : ℝ}
  (h : RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ w)) 2 Kc)

/-- **The bordered head Jacobian** `J̄(x, η) = (eigenHeadJac x - η v̄, 2 b(v̄, P_S x))` at
`(v̄, lbar)` with the finite potential `q̄`, on `Y = XR × ℝ` (the factor `K` of
`B₀ = A_N K + (I - P_V)`). -/
def eigenJbar (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw) (vbar : realSub hw) :
    (realSub hw × ℝ) →L[ℝ] (realSub hw × ℝ) :=
  ((restrictReal hw ((eigenHeadJac h D.toEigenRaw qbar).restrictScalars ℝ)
          (conjReflL_eigenHeadJac hw h D qbar hqbar)).comp
        (ContinuousLinearMap.fst ℝ (realSub hw) ℝ) -
      (ContinuousLinearMap.toSpanSingleton ℝ vbar).comp
        (ContinuousLinearMap.snd ℝ (realSub hw) ℝ)).prod
    ((2 : ℝ) • ((pairing h1 (vbar : X)).comp ((headProj (𝕜 := ℂ) D.S).restrictScalars ℝ)).comp
      ((realSub hw).subtypeL.comp (ContinuousLinearMap.fst ℝ (realSub hw) ℝ)))

/-- The first component of `J̄(x, η)` is `eigenHeadJac x - η v̄`. -/
theorem coe_eigenJbar_fst (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (y : realSub hw × ℝ) :
    ((eigenJbar hw h1 h D qbar hqbar vbar y).1 : X) =
      eigenHeadJac h D.toEigenRaw qbar (y.1 : X) - y.2 • (vbar : X) :=
  rfl

/-- The second component of `J̄(x, η)` is `2 b(v̄, P_S x)`. -/
theorem eigenJbar_snd (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (y : realSub hw × ℝ) :
    (eigenJbar hw h1 h D qbar hqbar vbar y).2 =
      2 * pairing h1 (vbar : X) (headProj (𝕜 := ℂ) D.S (y.1 : X)) :=
  rfl

/-- `J̄` maps the real head space `V = (P_S XR) × ℝ` into itself (the `hK` of
`borderInj_of_norm_id_sub_lt_one`):
`eigenHeadJac` ends with `P_S`, and the centre is head-supported (`hvS`). -/
theorem eigenJbar_mapsTo (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    {vbar : realSub hw} (hvS : headProj (𝕜 := ℂ) D.S (vbar : X) = vbar) :
    ∀ y ∈ headSubY hw D.S, eigenJbar hw h1 h D qbar hqbar vbar y ∈ headSubY hw D.S := fun y _ => by
  have hJ : headProj (𝕜 := ℂ) D.S (eigenHeadJac h D.toEigenRaw qbar (y.1 : X)) =
      eigenHeadJac h D.toEigenRaw qbar (y.1 : X) :=
    DFunLike.congr_fun (headProj_comp_headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) D.S)
      (((eigenLam D.toEigenRaw + convCLM h qbar - (D.lbar : ℂ) • ContinuousLinearMap.id ℂ X) ∘L
        headProj (𝕜 := ℂ) D.S) (y.1 : X))
  rw [mem_headSubY, coe_eigenJbar_fst, map_sub, ContinuousLinearMap.map_smul_of_tower, hvS, hJ]

/-- **The identification** : `eigenB0` is the bordered shape
`B₀ = A_N J̄ + (I - P_V)`. -/
theorem eigenB0_apply_eq_jbar (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    (vbar : realSub hw) (y : realSub hw × ℝ) :
    eigenB0 hw h1 h D qbar hqbar vbar y =
      borderOp hw h1 D (eigenJbar hw h1 h D qbar hqbar vbar y) + (y - headProjY hw D.S D.hS y) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · rw [coe_eigenB0_fst, Prod.fst_add, Submodule.coe_add, coe_borderOp_fst, coe_eigenJbar_fst,
      eigenJbar_snd, Prod.fst_sub, Submodule.coe_sub, coe_headProjY_fst, map_sub,
      ContinuousLinearMap.map_smul_of_tower, tailProj_eq_id_sub_headProj, sub_apply,
      ContinuousLinearMap.id_apply]
  · rw [eigenB0_snd, Prod.snd_add, borderOp_snd, coe_eigenJbar_fst, eigenJbar_snd, Prod.snd_sub,
      headProjY_snd, map_sub, map_smul, smul_eq_mul]
    ring

/-- **Border injectivity from the `Z₀` bound**: `‖I - B₀‖ < 1` at `eigenB0` gives
`borderInj`, through `borderInj_of_norm_id_sub_lt_one` at `K = J̄`. -/
theorem borderInj_of_eigenB0 (D : EigenData hw) (qbar : X) (hqbar : qbar ∈ realSub hw)
    {vbar : realSub hw} (hvS : headProj (𝕜 := ℂ) D.S (vbar : X) = vbar)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (realSub hw × ℝ) - eigenB0 hw h1 h D qbar hqbar vbar‖ < 1) :
    borderInj hw h1 D :=
  borderInj_of_norm_id_sub_lt_one hw h1 D (eigenJbar_mapsTo hw h1 h D qbar hqbar hvS)
    (eigenB0_apply_eq_jbar hw h1 h D qbar hqbar vbar) hZ₀

end BorderInjFromB0

end RadiiPolynomial.Fourier.Eigenpair

end
