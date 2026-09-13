import RadiiPolynomial.Applications.IVP.Chebyshev.BlockDiagonal
import RadiiPolynomial.Operators.BlockDiagonal.Composition
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Evaluation

/-!
# Standard Chebyshev IVP Data Bundle

Packages the standard Chebyshev IVP numerical data (approximate inverse, approximate derivative,
approximate solution) into a single structure, with all generic constructions auto-derived.

## Architecture

Every Chebyshev IVP with the standard tail structure (`A.tailDiag = 1/(2k)`, `A†.tailDiag = 2k`)
shares identical boilerplate. `StdChebIVPData` bundles the numerical arrays and auto-derives
all of these in its namespace. The user provides equation-specific data (φ, p, bounds).

Parallel to `IVP.StdIVPData` for Taylor IVP, with:
- `tailDiag = 1/(2k)` instead of `1/n`
- `tailCancel: 1/(2k) * 2k = 1`
- `abar` embedded into `XCheb ν L` (ℤ-indexed) via `ChebyshevIVP.embedNatToInt`

## Certificate faces

`composedApproxCLM` (§6: identity on negative modes, block action on non-negatives),
`Z₀_le` (§7), `defect_finBlockNorm_lt_one_of_radii` and `existsUnique` (§8) are all derived
here from the bundle. A certificate written from one polynomial system does not call them
directly: it calls the faces of `Chebyshev/Polynomial.lean`
(`StdChebIVPData.existsUnique_of_compPoly`, `Z₂_le_of_compPoly_max`) and of
`Chebyshev/AnalyticPolynomial.lean` (`solution_existsUnique_of_compPoly`,
`solution_existsUnique_of_two_le_of_compPoly`,
`analytic_solution_existsUnique_of_two_le_of_compPoly`). The only bound still assembled at
the example level is `Z₁` (componentwise, `chebyshev_Z₁_le_relaxed`).
-/

open scoped BigOperators Topology NNReal ENNReal
open RadiiPolynomial ChebyshevIVP

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

/-- Standard Chebyshev IVP numerical data bundle.
Contains matrix arrays and approximate solution arrays from a numerical solver.
All standard Chebyshev IVP constructions are auto-derived in the namespace. -/
structure StdChebIVPData (ν : PosReal) (L N : ℕ) [NeZero L] [Fact (1 ≤ (ν : ℝ))] where
  /-- Approximate inverse matrix columns: `A_col l j k` is column `k` of block `(l,j)`. -/
  A_col : Fin L → Fin L → ℕ → Array ℚ
  /-- Jacobian matrix columns: `DF_col l j k` is column `k` of block `(l,j)`. -/
  DF_col : Fin L → Fin L → ℕ → Array ℚ
  /-- Approximate solution coefficient arrays per component. -/
  abar_Q : Fin L → Array ℚ
  /-- Weight as ℚ (for `finsum_bound` / `native_decide`). -/
  ν_q : ℚ
  /-- Bridge: ν_val = ν_q cast to ℝ. -/
  hν : (ν : ℝ) = ((ν_q : ℚ) : ℝ)
  /-- Each abar_Q array has exactly N+1 entries. -/
  habar_size : ∀ l, (abar_Q l).size = N + 1

namespace StdChebIVPData

variable (d : StdChebIVPData ν L N)

/-! ## 1. Approximate Inverse A -/

/-- Finite block of the approximate inverse, cast from ℚ column arrays. -/
def A_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((d.A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate inverse with Chebyshev tail structure:
tailDiag = 1/(2k), tailBound = 1/(2(N+1)). -/
def approxInverse : SystemBlockDiagData L N where
  finBlock := d.A_finBlock
  tailDiag := fun _ n => if n = 0 then 0 else 1 / (2 * (n : ℝ))
  tailBound := 1 / (2 * ((N : ℝ) + 1))
  tailBound_spec := by
    intro _ n (hn : N < n)
    have hne : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have hN1 : 2 * ((N : ℝ) + 1) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show 2 * (N + 1) ≤ 2 * n by omega)
    rw [if_neg hne, abs_of_pos (div_pos one_pos hpos)]
    exact one_div_le_one_div_of_le (by positivity) hN1

/-- Bridge: A_finBlock entries = ℚ cast of A_col data. -/
lemma A_finBlock_eq (l j : Fin L) (i k : Fin (N + 1)) :
    d.A_finBlock l j i k = ((d.A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) := rfl

/-! ## 2. Approximate Derivative A† -/

/-- Finite block of the Jacobian, cast from ℚ column arrays. -/
def DF_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((d.DF_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate derivative with Chebyshev tail structure: tailDiag = 2k. -/
def approxDeriv : BlockDiagOp L N where
  finBlock := d.DF_finBlock
  tailDiag := fun _ n => 2 * (n : ℝ)

/-! ## 3. Structural Hypotheses -/

/-- Tail cancellation: (1/(2k)) * (2k) = 1 for k > N. -/
lemma tailCancel (l : Fin L) (n : ℕ) (hn : N < n) :
    d.approxInverse.tailDiag l n * d.approxDeriv.tailDiag l n = 1 := by
  simp only [approxInverse, approxDeriv]
  rw [if_neg (by omega : n ≠ 0)]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- A.tailDiag = 1/(2k) for k > N. -/
lemma htail_diag_inv (l : Fin L) (n : ℕ) (hn : N < n) :
    d.approxInverse.tailDiag l n = 1 / (2 * (↑n : ℝ)) := by
  simp only [approxInverse, if_neg (by omega : n ≠ 0)]

/-- Defect D = I - A·A†. -/
def defect : SystemBlockDiagData L N :=
  defectOfBlockDiagOp d.approxInverse d.approxDeriv

/-- Composed approximate derivative A·A† (as SystemBlockDiagData for numerical bounds). -/
def composedApprox : SystemBlockDiagData L N :=
  d.approxInverse.composedApprox d.approxDeriv d.tailCancel

/-! ## 4. Approximate Solution ābar -/

/-- ābar coefficient sequence: finite support (modes 0..N), zero beyond. -/
def abar_seq (l : Fin L) (n : ℕ) : ℝ :=
  if n ≤ N then ((d.abar_Q l).getD n 0 : ℝ) else 0

lemma abar_seq_support (l : Fin L) (n : ℕ) (hn : N < n) :
    d.abar_seq l n = 0 := by
  simp [abar_seq, show ¬(n ≤ N) from by omega]

/-- ābar toSeq = raw ℚ getD (extends by zero beyond array size). -/
lemma abar_seq_eq_getD (l : Fin L) (k : ℕ) :
    d.abar_seq l k = ((d.abar_Q l).getD k 0 : ℝ) := by
  simp only [abar_seq]
  by_cases hk : k ≤ N
  · simp [hk]
  · simp only [show ¬(k ≤ N) from hk, ↓reduceIte]
    symm; simp only [Array.getD]
    rw [dif_neg (by rw [d.habar_size l]; omega)]; simp

/-- Memℓp proof for the finitely-supported abar embedding. -/
lemma abar_memℓp (l : Fin L) :
    Memℓp (show ∀ k : ℤ, ScaledRealZ ν k from
      ChebyshevIVP.embedNatToInt (d.abar_seq l)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    have hlt : N < n := by simp [Finset.mem_range] at hn; omega
    show ‖(show ∀ k : ℤ, ScaledRealZ ν k from
      ChebyshevIVP.embedNatToInt (d.abar_seq l)) (↑n : ℤ)‖ = 0
    simp [d.abar_seq_support l n hlt, lpAlgRingData.ofReal_zero, norm_zero]
  · have : (fun n : ℕ => ‖(show ∀ k : ℤ, ScaledRealZ ν k from
        ChebyshevIVP.embedNatToInt (d.abar_seq l)) (-(↑n + 1 : ℤ))‖) =
        fun _ => (0 : ℝ) := by
      ext n; have h : -(↑n + 1 : ℤ) = Int.negSucc n := by omega
      rw [h]; simp
    rw [this]; exact summable_zero

/-- Approximate solution as XCheb (ℤ-indexed, zeros on negatives and beyond N). -/
def abar : XCheb ν L := fun l =>
  ⟨⟨ChebyshevIVP.embedNatToInt (d.abar_seq l), d.abar_memℓp l⟩⟩

/-- Bridge: toSeq(abar l)(↑k) = (abar_Q l).getD k 0. -/
lemma abar_toSeq_eq (l : Fin L) (k : ℕ) :
    l1Chebyshev.toSeq (abar d l) (↑k : ℤ) = ((d.abar_Q l).getD k 0 : ℝ) := by
  show lpAlgRingData.toReal (↑k : ℤ)
    (ChebyshevIVP.embedNatToInt (d.abar_seq l) (↑k : ℤ)) = _
  simp [ChebyshevIVP.embedNatToInt, lpAlgRingData.toReal_ofReal, d.abar_seq_eq_getD]

/-- The stored candidate vanishes at negative indices (`embedNatToInt` is one-sided). -/
lemma abar_toSeq_negSucc (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (abar d l) (-((n : ℤ) + 1)) = 0 := by
  show lpAlgRingData.toReal (-((n : ℤ) + 1))
    (ChebyshevIVP.embedNatToInt (d.abar_seq l) (-((n : ℤ) + 1))) = _
  rw [(Int.negSucc_eq n).symm]
  simp [ChebyshevIVP.embedNatToInt, lpAlgRingData.toReal_zero]

/-- `‖ā l‖ ≤ ‖S(ā l)‖`: the stored candidate lives on the indices `0..N`, so its norm is
dominated by the norm of its symmetrization — the bridge from a certificate's exact-ℚ
bound on `‖S(ā)‖` (the quantity the Chebyshev certificate evaluates) to the trajectory
radius `‖ā‖ + r₀` of the solution faces. -/
lemma norm_abar_le_norm_symmetrize (l : Fin L) :
    ‖abar d l‖ ≤ ‖l1Chebyshev.symmetrize (abar d l)‖ :=
  l1Chebyshev.norm_le_norm_symmetrize_of_neg_eq_zero _ (d.abar_toSeq_negSucc l)

/-! ## 5. Composed Map G (needs φ, p) -/

/-- The composed Chebyshev IVP map G = A ∘ F. -/
def G (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ) :
    XCheb ν L → XCheb ν L :=
  chebyshevIvpMap d.approxInverse φ p
    (chebyshevIvpMap_mem_of_tailDiag_half _ φ p d.htail_diag_inv)

/-! ## 6. Composed Approximate Derivative CLM on XCheb -/

/-- The composed approximate derivative as a CLM on XCheb.
Acts as identity on negative and tail modes, finite block action on modes 0..N. -/
def composedApproxCLM : XCheb ν L →L[ℝ] XCheb ν L :=
  composedApproxCheb (defectOfBlockDiagOp d.approxInverse d.approxDeriv)

/-! ## 7. Z₀ Bound -/

/-- Z₀ bound: `‖id - composedApproxCLM‖ ≤ Z₀`. -/
lemma Z₀_le {Z₀ : ℝ}
    (hZ₀ : finiteBlockMatrixNorm ν (defectOfBlockDiagOp d.approxInverse d.approxDeriv).finBlock
      ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ (XCheb ν L) - d.composedApproxCLM‖ ≤ Z₀ :=
  composedApproxCheb_Z₀ _ hZ₀

/-- Radii-polynomial negativity makes the finite defect strictly smaller than one.
Chebyshev mirror of `IVP.StdIVPData.defect_finBlockNorm_lt_one_of_radii`: it is the
injectivity fact that returning from the preconditioned map `G` to the raw coefficient
residual needs, and it is derived from the same four bounds the certificate already
proves — in particular from the finite-block form of `Z₀`, so no separate
`‖defect‖ < 1` obligation is stated at the example level. -/
lemma defect_finBlockNorm_lt_one_of_radii
    (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G φ p (abar d)‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (abar d) r₀,
      ‖fderiv ℝ (d.G φ p) c - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0) :
    finiteBlockMatrixNorm ν d.defect.finBlock < 1 := by
  have hY₀_nonneg : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
  have hZ₁_nonneg : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁
  have hZ₂r_nonneg : 0 ≤ Z₂_val * r₀ :=
    (norm_nonneg _).trans (hZ₂ (abar d) (Metric.mem_closedBall_self hr₀.le))
  have hZ_lt_one := general_radii_poly_neg_implies_Z_lt_one hY₀_nonneg hr₀ h_radii
  unfold Z_bound_general at hZ_lt_one
  have hZ₀_lt_one : Z₀ < 1 := by nlinarith
  exact hZ₀fin.trans_lt hZ₀_lt_one

/-! ## 8. Main Existence/Uniqueness -/

/-- Main existence/uniqueness theorem for standard Chebyshev IVP systems.
The user provides equation-specific bounds; structural hypotheses are auto-derived. -/
theorem existsUnique
    (φ : XCheb ν L → Fin L → l1Chebyshev ν) (p : Fin L → ℝ)
    (hG_diff : Differentiable ℝ (d.G φ p))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G φ p (abar d)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (XCheb ν L) - d.composedApproxCLM‖ ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall (abar d) r₀,
      ‖fderiv ℝ (d.G φ p) c - fderiv ℝ (d.G φ p) (abar d)‖ ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (abar d) r₀, d.G φ p xTilde = 0 :=
  chebyshev_system_theorem (d.G φ p) (abar d) hG_diff d.composedApproxCLM
    hr₀ hY₀ hZ₀ hZ₁ hZ₂ h_radii

end StdChebIVPData

end ChebyshevIVP

end
