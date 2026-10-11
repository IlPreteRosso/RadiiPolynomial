import RadiiPolynomial.Analysis.SequenceSpace.Fourier.GammaLeakage
import RadiiPolynomial.Operators.HeadTail
import RadiiPolynomial.Algebra.Polynomial.MvPolynomial.Calculus

/-!
# The general-symbol semilinear consumer on the bilateral geometric carrier

On `E = lpOneAlg ℤ (geomFiberZ 𝕜 ν)` with the head window `P = headProj (winZ N)`, the tail
projection `Q = tailProj (winZ N)`, left multiplication `L_c = mulLeftCLM c` and a bounded tail
diagonal `D_r = diagCLM r C hr` (`‖r k‖ ≤ C`), this file treats the semilinear model
`λ_k a_k − τ Φ̂(a)_k` for an ARBITRARY symbol `lam : ℤ → 𝕜` and a one-variable polynomial
nonlinearity `Φ ∈ 𝕜[X₀]`, `Φ̂(a) = aeval a Φ`, in six layers:

1. the symbol: `lamHead N lam = 1_{W_N} lam` and the finite-head diagonal `headDiag N lam`, bounded
   by the finite head maximum `headBound N lam` (no global bound or growth hypothesis on `lam`);
2. the preconditioned map `precondMap N M lam r C hr τ Φ`,
   `G(a) = M(Λ_H a − τ P Φ̂(a)) + Q a − τ D_r Φ̂(a)`, its derivative and the model
   `modelDeriv N M lam τ Φ abar = M(Λ_H − P L_β P) + Q` with `β = beta τ Φ abar = τ Φ̂′(ā)`:
   `DG(ā) − B₀ = −defect N M r C hr β` for EVERY bounded `M` and `r` (`fderiv_sub_modelDeriv`);
3. the raw identification: the coefficients of `G(a)` are the raw preconditioner `rawPrecond`
   applied to the raw map `rawMap` when `r = 0` on the head and `r_k λ_k = 1` off it
   (`toRealSeq_precondMap`); over a field, `r = tailInv N lam` under tail nonvanishing, with the
   uniform bound of the tail inverse supplied separately (`toRealSeq_precondMap_tailInv`);
4. the exact finite window: `‖DG(ā) − B₀‖` is the finite maximum of its column ratios over
   `|j| ≤ B + max (N + 1) K₀` when `β` has band `B` and `‖r‖` is two-ray nonincreasing from
   `max (N + 1) K₀`, attained at an atom (the explicit `a_j + s_j` form needs `P M = M` and
   `r = 0` on the head);
5. the degree window `(d − 1) N + max (N + 1) K₀`, equal to `d N + 1` when `d ≥ 1` and
   `K₀ ≤ N + 1` (`window_deg_eq`);
6. the Γ majorant `‖DG(ā) − B₀‖ ≤ (‖M P Γ‖ + C) ‖β‖` over the L004 Γ diagonal (`𝕜` a normed
   `ℝ`-algebra).

The Γ majorant is a universal head bound: it is NOT the exact window norm of layer 4. The
first-order family `λ_k = i k` (first-tail bound `1/(N + 1)`, `K₀ = 1`, window `N + m + 1`) is the
specialization in `Applications/Fourier/SemilinearFirstOrder.lean`; no first-tail bound or
first-tail window is assumed here.

Promoted from the S028b `FourierSemilinear` / `FourierSemilinearGamma` sources by unit
L005-FourierSemilinear (see `RENAMES.md`).
-/

noncomputable section

namespace RadiiPolynomial.Fourier.Semilinear

/-- The symbol restricted to the head window: `lamHead N lam k = 1_{|k| ≤ N} lam k`. -/
def lamHead {𝕜 : Type*} [NormedField 𝕜] (N : ℕ) (lam : ℤ → 𝕜) (k : ℤ) : 𝕜 :=
    if k ∈ winZ N then lam k else 0

/-- The finite-head bound of the symbol: `max_{|k| ≤ N} ‖lam k‖`. -/
def headBound {𝕜 : Type*} [NormedField 𝕜] (N : ℕ) (lam : ℤ → 𝕜) : ℝ :=
    (winZ N).sup' (winZ_nonempty N) (fun k => ‖lam k‖)

section
variable {𝕜 : Type*} [NormedField 𝕜]

/-- The head symbol is bounded by the finite head maximum (no hypothesis on `lam`). -/
theorem norm_lamHead_le (N : ℕ) (lam : ℤ → 𝕜) :
    ∀ k, ‖lamHead N lam k‖ ≤ headBound N lam := by
  intro k
  unfold lamHead
  split_ifs with hk
  · exact Finset.le_sup' (fun k => ‖lam k‖) hk
  · rw [norm_zero]
    exact (norm_nonneg (lam 0)).trans
      (Finset.le_sup' (fun k => ‖lam k‖) (mem_winZ.mpr (Nat.zero_le N)))

end

/-- The tail inverse of the symbol: `0` on the head window, `(lam k)⁻¹` off it (`0⁻¹ = 0`). -/
def tailInv {𝕜 : Type*} [NormedField 𝕜] (N : ℕ) (lam : ℤ → 𝕜) (k : ℤ) : 𝕜 :=
    if k ∈ winZ N then 0 else (lam k)⁻¹

section
variable {𝕜 : Type*} [NormedField 𝕜]

/-- The tail inverse vanishes on the head window. -/
theorem tailInv_head_zero (N : ℕ) (lam : ℤ → 𝕜) :
    ∀ k : ℤ, k.natAbs ≤ N → tailInv N lam k = 0 := by
  intro k hk
  exact ite_eq_left (mem_winZ.mpr hk)

/-- Under tail nonvanishing the tail inverse inverts the symbol off the head window. -/
theorem tailInv_mul_self (N : ℕ) (lam : ℤ → 𝕜) (hlam : ∀ k : ℤ, N < k.natAbs → lam k ≠ 0) :
    ∀ k : ℤ, N < k.natAbs → tailInv N lam k * lam k = 1 := by
  intro k hk
  rw [tailInv, ite_eq_right (fun h => absurd (mem_winZ.mp h) (Nat.not_le.mpr hk))]
  exact inv_mul_cancel₀ (hlam k hk)

end

/-- The finite-head diagonal `Λ_H = diag(1_{W_N} lam)`, bounded by `headBound N lam`. -/
def headDiag {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal} (N : ℕ) (lam : ℤ → 𝕜) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) (lamHead N lam) (headBound N lam) (norm_lamHead_le N lam)

section
variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- Coefficient face of the head diagonal. -/
theorem toRealSeq_headDiag (N : ℕ) (lam : ℤ → 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    lpOneAlg.toRealSeq ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a) k = lamHead N lam k * lpOneAlg.toRealSeq a k :=
  lpOneAlg.toRealSeq_diagCLM _ _ _ a k

/-- Atom face of the head diagonal. -/
theorem headDiag_single (N : ℕ) (lam : ℤ → 𝕜) (k : ℤ) (x : 𝕜) :
    (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lpOneAlg.single k x) = (lpOneAlg.single k (lamHead N lam k * x) : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :=
  lpOneAlg.diagCLM_single _ _ _ k x

/-- `P Λ_H = Λ_H`. -/
theorem headProj_comp_headDiag (N : ℕ) (lam : ℤ → 𝕜) :
    (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) := by
  refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.toRealSeq_headProj, toRealSeq_headDiag]
  by_cases hk : k ∈ winZ N
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, lamHead, ite_eq_right hk, zero_mul]

/-- `Λ_H P = Λ_H`. -/
theorem headDiag_comp_headProj (N : ℕ) (lam : ℤ → 𝕜) :
    (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) := by
  refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [ContinuousLinearMap.comp_apply, toRealSeq_headDiag, toRealSeq_headDiag,
    lpOneAlg.toRealSeq_headProj]
  by_cases hk : k ∈ winZ N
  · rw [ite_eq_left hk]
  · simp only [lamHead, ite_eq_right hk, zero_mul]

/-- A bounded diagonal vanishing on the head window annihilates the head: `D_r P = 0`. -/
theorem diagCLM_comp_headProj_of_head_zero (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = 0 := by
  refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [ContinuousLinearMap.comp_apply, lpOneAlg.toRealSeq_diagCLM, lpOneAlg.toRealSeq_headProj,
    zero_apply, lpOneAlg.toRealSeq_zero, Pi.zero_apply]
  by_cases hk : k ∈ winZ N
  · rw [hr0 k (mem_winZ.mp hk), zero_mul]
  · rw [ite_eq_right hk, mul_zero]

/-- Coefficient extraction commutes with a finite sum. -/
theorem toRealSeq_finset_sum {ι : Type*} (s : Finset ι) (a : ι → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    lpOneAlg.toRealSeq (∑ i ∈ s, a i) k = ∑ i ∈ s, lpOneAlg.toRealSeq (a i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lpOneAlg.toRealSeq_zero, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, lpOneAlg.toRealSeq_add, Pi.add_apply, ih]

end

/-- The head embedding of a raw sequence: `Σ_{|k| ≤ N} y_k e_k`. -/
def headEmbed {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal} (N : ℕ) (y : ℤ → 𝕜) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    ∑ k ∈ winZ N, (lpOneAlg.single k (y k) : lpOneAlg ℤ (geomFiberZ 𝕜 ν))

section
variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- Coefficient face of the head embedding. -/
theorem toRealSeq_headEmbed (N : ℕ) (y : ℤ → 𝕜) (k : ℤ) :
    lpOneAlg.toRealSeq (headEmbed N y : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) k = if k ∈ winZ N then y k else 0 := by
  simp only [headEmbed, toRealSeq_finset_sum, lpOneAlg.toRealSeq_single, Finset.sum_ite_eq]

end

/-- The raw preconditioner `A y = M (headEmbed y) + 1_{|k| > N} r_k y_k`: a plain function of raw
sequences, not a bounded operator. -/
def rawPrecond {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal} (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (r y : ℤ → 𝕜) : ℤ → 𝕜 :=
    fun k => lpOneAlg.toRealSeq (M (headEmbed N y)) k + (if k ∈ winZ N then 0 else r k * y k)

/-- The polynomial nonlinearity `Φ̂(a) = aeval a Φ`. -/
def phiHat {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    MvPolynomial.aeval (fun _ : Fin 1 => a) Φ

/-- The derivative symbol `Φ̂′(a) = aeval a (∂₀ Φ)`. -/
def phiHatDeriv {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    MvPolynomial.aeval (fun _ : Fin 1 => a) (MvPolynomial.pderiv 0 Φ)

/-- The model coefficient `β = τ Φ̂′(ā)`. -/
def beta {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    τ • phiHatDeriv Φ abar

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The polynomial nonlinearity has derivative `L_{Φ̂′(ā)}` at `ā`. -/
theorem hasFDerivAt_phiHat (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    HasFDerivAt (phiHat Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar := by
  let diagonal : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] (Fin 1 → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :=
    ContinuousLinearMap.pi (fun _ : Fin 1 => ContinuousLinearMap.id 𝕜 _)
  have hlinear : (MvPolynomial.polynomialDerivative (𝕜 := 𝕜) Φ (fun _ : Fin 1 => abar)) ∘L
      diagonal = lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) := by
    ext1 h
    simp only [ContinuousLinearMap.comp_apply, MvPolynomial.polynomialDerivative_apply,
      Fin.sum_univ_one, diagonal, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply,
      lpOneAlg.mulLeftCLM_apply, phiHatDeriv]
  have hd := (MvPolynomial.hasFDerivAt_aeval (𝕜 := 𝕜) Φ (fun _ : Fin 1 => abar)).comp
    abar (diagonal.hasFDerivAt)
  rw [hlinear] at hd
  convert hd using 1
  rfl

end

section
variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- Under a band-`N` centre and `deg q ≤ e`, `q(ā)` has band `e N`. -/
theorem band_aeval (N e : ℕ) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (q : MvPolynomial (Fin 1) 𝕜) (hdeg : q.totalDegree ≤ e) :
    ∀ k : ℤ, e * N < k.natAbs →
      lpOneAlg.toRealSeq (MvPolynomial.aeval (fun _ : Fin 1 => abar) q) k = 0 := by
  classical
  intro k hk
  rw [q.as_sum, map_sum, toRealSeq_finset_sum]
  apply Finset.sum_eq_zero
  intro mon hmon
  have he : mon 0 ≤ e := by
    have ht := MvPolynomial.le_totalDegree hmon
    rw [Finsupp.sum_fintype mon (fun _ n => n) (fun _ => rfl), Fin.sum_univ_one] at ht
    exact ht.trans hdeg
  rw [MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype mon (fun _ n => abar ^ n) (fun _ => pow_zero abar), Fin.prod_univ_one,
    ← Algebra.smul_def, lpOneAlg.toRealSeq_smul, Pi.smul_apply,
    band_pow N abar habar (mon 0) k ((Nat.mul_le_mul_right N he).trans_lt hk), smul_zero]

/-- Under a band-`N` centre and `deg ∂₀Φ ≤ d − 1`, `β` has band `(d − 1) N`. -/
theorem band_beta (N d : ℕ) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1) :
    ∀ i : ℤ, (d - 1) * N < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0 := by
  intro i hi
  rw [beta, lpOneAlg.toRealSeq_smul, Pi.smul_apply, phiHatDeriv,
    band_aeval N (d - 1) abar habar (MvPolynomial.pderiv 0 Φ) hdeg i hi, smul_zero]

end

/-- The preconditioned map `G(a) = M(Λ_H a − τ P Φ̂(a)) + Q a − τ D_r Φ̂(a)` for any symbol and any
bounded tail diagonal `(r, C, hr)`. -/
def precondMap {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    M ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a - τ • (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (phiHat Φ a)) + (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a -
      τ • (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (phiHat Φ a)

/-- The model derivative `B₀ = M(Λ_H − P L_β P) + Q`. -/
def modelDeriv {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam : ℤ → 𝕜) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    M ∘L ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) + (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The derivative of the preconditioned map. -/
theorem hasFDerivAt_precondMap (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    HasFDerivAt (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν))
      (M ∘L ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - τ • ((lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) + (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) -
        τ • ((lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (phiHatDeriv Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) abar := by
  have hphi := hasFDerivAt_phiHat Φ abar
  have hp := (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)).hasFDerivAt.comp abar hphi
  have hm := M.hasFDerivAt.comp abar
    ((headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)).hasFDerivAt.sub
      (hp.const_smul τ))
  have hR := (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)).hasFDerivAt.comp abar hphi
  have hq := (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)).hasFDerivAt (x := abar)
  convert (hm.add hq).sub (hR.const_smul τ) using 1
  rfl

/-- `DG(ā) − B₀ = −defect` for every bounded `M` and every bounded `r`. -/
theorem fderiv_sub_modelDeriv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    (fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = -(defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) := by
  rw [(hasFDerivAt_precondMap N M lam r C hr τ Φ abar).fderiv, modelDeriv, defect]
  refine ContinuousLinearMap.ext fun a => ?_
  simp only [beta, sub_apply, add_apply, neg_apply, ContinuousLinearMap.comp_apply, smul_apply,
    lpOneAlg.tailProj_eq_one_sub, one_apply_eq_self, lpOneAlg.mulLeftCLM_apply, smul_mul_assoc,
    map_sub, map_smul]
  module

/-- The transport form of `DG(ā) − B₀` (composition identity), under `r = 0` on the head
(`D_r P = 0`). -/
theorem fderiv_sub_modelDeriv_hZ (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    (fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (-1 : 𝕜) •
      ((M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) + (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) ∘L
        ((lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (1 - (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) + (1 - (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)))) := by
  rw [HeadTail.composition_identity _ M _ _ (lpOneAlg.isIdempotentElem_headProj (winZ N))
    (diagCLM_comp_headProj_of_head_zero N r C hr hr0)]
  exact (fderiv_sub_modelDeriv N M lam r C hr τ Φ abar).trans (neg_one_smul 𝕜 _).symm

/-- `‖DG(ā) − B₀‖ = ‖defect‖`. -/
theorem norm_fderiv_sub_modelDeriv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ = ‖(defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ := by
  rw [fderiv_sub_modelDeriv, norm_neg]

end

/-- The raw map `F(a)_k = lam_k a_k − τ Φ̂(a)_k`. -/
def rawMap {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (lam : ℤ → 𝕜) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) : ℤ → 𝕜 :=
    fun k => lam k * lpOneAlg.toRealSeq a k - τ * lpOneAlg.toRealSeq (phiHat Φ a) k

section
variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The head embedding of the raw map is the head part of the preconditioned map. -/
theorem headEmbed_rawMap (N : ℕ) (lam : ℤ → 𝕜) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    (headEmbed N (rawMap lam τ Φ a) : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (headDiag N lam : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a - τ • (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (phiHat Φ a) := by
  refine lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_headEmbed, lpOneAlg.toRealSeq_sub, Pi.sub_apply, toRealSeq_headDiag,
    lpOneAlg.toRealSeq_smul, Pi.smul_apply, lpOneAlg.toRealSeq_headProj]
  by_cases hk : k ∈ winZ N
  · simp only [lamHead, ite_eq_left hk, rawMap, smul_eq_mul]
  · simp only [lamHead, ite_eq_right hk, zero_mul, smul_zero, sub_zero]

/-- The coefficients of `G(a)` are the raw preconditioner applied to the raw map, when `r = 0` on the
head and `r_k lam_k = 1` off it. -/
theorem toRealSeq_precondMap (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (hrlam : ∀ k : ℤ, N < k.natAbs → r k * lam k = 1) :
    lpOneAlg.toRealSeq (precondMap N M lam r C hr τ Φ a) = rawPrecond N M r (rawMap lam τ Φ a) := by
  funext k
  simp only [precondMap, rawPrecond, headEmbed_rawMap, lpOneAlg.toRealSeq_sub,
    lpOneAlg.toRealSeq_add, Pi.sub_apply, Pi.add_apply, lpOneAlg.toRealSeq_smul, Pi.smul_apply,
    lpOneAlg.toRealSeq_tailProj, lpOneAlg.toRealSeq_diagCLM]
  by_cases hk : k ∈ winZ N
  · simp only [ite_eq_left hk, hr0 k (mem_winZ.mp hk), zero_mul, smul_zero, sub_zero, add_zero]
  · have h1 := hrlam k (Nat.lt_of_not_le fun h => hk (mem_winZ.mpr h))
    simp only [ite_eq_right hk, rawMap, smul_eq_mul]
    linear_combination (-(lpOneAlg.toRealSeq a k)) * h1

/-- The raw identification at the tail inverse, under tail nonvanishing; the uniform bound `hC` of the
tail inverse is separate data (nonvanishing alone does not bound it). -/
theorem toRealSeq_precondMap_tailInv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam : ℤ → 𝕜) (C : ℝ)
    (hC : ∀ k, ‖tailInv N lam k‖ ≤ C) (τ : 𝕜) (Φ : MvPolynomial (Fin 1) 𝕜) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hlam : ∀ k : ℤ, N < k.natAbs → lam k ≠ 0) :
    lpOneAlg.toRealSeq (precondMap N M lam (tailInv N lam) C hC τ Φ a) =
      rawPrecond N M (tailInv N lam) (rawMap lam τ Φ a) :=
  toRealSeq_precondMap N M lam (tailInv N lam) C hC τ Φ a (tailInv_head_zero N lam)
    (tailInv_mul_self N lam hlam)

end

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The exact finite window, column-ratio form: under the band `B` of `β` and moduli `‖r‖` two-ray
nonincreasing from `max (N + 1) K₀`, `‖DG(ā) − B₀‖` is the maximum of the column ratios over
`|j| ≤ B + max (N + 1) K₀`. -/
theorem norm_fderiv_sub_modelDeriv_eq_sup' (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ (B + max (N + 1) K₀)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio (defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) j) := by
  rw [norm_fderiv_sub_modelDeriv]
  exact opNorm_defect_eq_sup' N B K₀ M r C hr (beta τ Φ abar) hβ hmono

/-- The exact finite window, explicit form `max (a_j + s_j)`, under `P M = M` and `r = 0` on the
head. -/
theorem norm_fderiv_sub_modelDeriv_eq_sup'_explicit (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hPM : (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ (B + max (N + 1) K₀)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol B r (beta τ Φ abar) j) := by
  rw [norm_fderiv_sub_modelDeriv]
  exact opNorm_defect_eq_sup'_explicit N B K₀ M r C hr (beta τ Φ abar) hβ hPM hr0 hmono

/-- The norm of `DG(ā) − B₀` is attained as a weighted column ratio at an atom of the window. -/
theorem fderiv_sub_modelDeriv_attained (N B K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hβ : ∀ i : ℤ, B < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ∃ j ∈ winZ (B + max (N + 1) K₀),
      ‖((fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))) (lpOneAlg.single j 1)‖ =
        ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ * (ν : ℝ) ^ j.natAbs := by
  obtain ⟨j, hj, h⟩ := defect_attained N B K₀ M r C hr (beta τ Φ abar) hβ hmono
  refine ⟨j, hj, ?_⟩
  rw [fderiv_sub_modelDeriv, neg_apply, norm_neg, norm_neg]
  exact h

/-- The degree window `(d − 1) N + max (N + 1) K₀`, column-ratio form. -/
theorem norm_fderiv_sub_modelDeriv_eq_sup'_deg (N d K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ ((d - 1) * N + max (N + 1) K₀)).sup' (winZ_nonempty _) (fun j => lpOneAlg.colRatio (defect N M r C hr (beta τ Φ abar) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup' N ((d - 1) * N) K₀ M lam r C hr τ Φ abar
    (band_beta N d τ Φ abar habar hdeg) hmono

end

section

/-- The degree window equals `d N + 1` when `d ≥ 1` and `K₀ ≤ N + 1`. -/
theorem window_deg_eq (N d K₀ : ℕ) (hd : 1 ≤ d) (hK : K₀ ≤ N + 1) :
    (d - 1) * N + max (N + 1) K₀ = d * N + 1 := by
  rw [max_eq_left hK]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [Nat.add_sub_cancel_left]
  ring

end

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The degree window, explicit form, under `P M = M` and `r = 0` on the head. -/
theorem norm_fderiv_sub_modelDeriv_eq_sup'_deg_explicit (N d K₀ : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0)
    (hdeg : (MvPolynomial.pderiv 0 Φ).totalDegree ≤ d - 1)
    (hPM : (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ =
      (winZ ((d - 1) * N + max (N + 1) K₀)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol ((d - 1) * N) r (beta τ Φ abar) j) :=
  norm_fderiv_sub_modelDeriv_eq_sup'_explicit N ((d - 1) * N) K₀ M lam r C hr τ Φ abar
    (band_beta N d τ Φ abar habar hdeg) hPM hr0 hmono

end

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The Γ majorant `‖DG(ā) − B₀‖ ≤ (‖M P Γ‖ + C) ‖β‖` with `C` the uniform bound of `r`. This universal
head bound is not the exact window norm (`norm_fderiv_sub_modelDeriv_eq_sup'`). -/
theorem norm_fderiv_sub_modelDeriv_le_gamma (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lam r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (τ : 𝕜)
    (Φ : MvPolynomial (Fin 1) 𝕜) (abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(fderiv 𝕜 (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ 𝕜 ν) → lpOneAlg ℤ (geomFiberZ 𝕜 ν)) abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤
      (‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ + C) * ‖(beta τ Φ abar : lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ := by
  rw [norm_fderiv_sub_modelDeriv]
  exact norm_defect_le_gamma N M r C hr (beta τ Φ abar)

end

section
variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- At `𝕜 = ℂ` the real-linear norm of `DG(ā) − B₀` is its complex-linear norm. -/
theorem norm_restrictScalars_fderiv_sub_modelDeriv (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) (lam r : ℤ → ℂ) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (τ : ℂ) (Φ : MvPolynomial (Fin 1) ℂ) (abar : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖((fderiv ℂ (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ ℂ ν) → lpOneAlg ℤ (geomFiberZ ℂ ν)) abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))).restrictScalars ℝ‖ =
      ‖(fderiv ℂ (precondMap N M lam r C hr τ Φ : lpOneAlg ℤ (geomFiberZ ℂ ν) → lpOneAlg ℤ (geomFiberZ ℂ ν)) abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) - (modelDeriv N M lam τ Φ abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))‖ :=
  ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) _

end

end RadiiPolynomial.Fourier.Semilinear

end
