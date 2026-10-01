import RadiiPolynomial.Analysis.SequenceSpace.Fourier.GammaLeakage

/-!
# FZ Γ-leakage tests: old-shape witnesses (T19, L004)

Each `old_<name>` restates a proposition of the frozen sources of record in its OLD shape and proves
it by APPLYING the new library API (no re-proof). Nothing here imports or revalidates a frozen
scratch constant: the old propositions are written over library symbols with the explicit
old → new symbol mapping

* `FourierSemilinear.gammaC N k ↦ (gammaScalar (ν : ℝ) N k : ℂ)` (`old_gammaC`: the old ℂ cast
  `((gammaW ν N k : ℝ) : ℂ)` is `algebraMap ℝ ℂ` by `rfl`),
* `ReesBridge.gammaW ν ↦ Rees.Laurent.gammaW (ν : ℝ)`,
* `HeadTailColumns.H N ↦ winZ N` (`old_winZ_eq_H`: `winZ N = Finset.Icc (-(N : ℤ)) N` by `rfl`, FSG:81),
* `HeadTailColumns.P_H ↦ lpOneAlg.headProj`, `1 - P_H ↦ tailProj` (the source's literal
  `1 - headProj (winZ N)` is restated; `tailProj_eq_one_sub` is `rfl`),
* `DΓ ↦ gammaDiag`, `DΓplus ↦ gammaInvDiag`.

Sources: FSG = `tmp/units/S028b-FourierSemilinearZ1/freeze/v1/FourierSemilinearGamma.lean`
(`609f2dff…`), RB = `tmp/filtration_probe/ReesBridge.lean` (`0af50219…`).

* (a) FSG :19, :23, :29, :41, :59, :70 (with the ℂ cast), :84, :131 at `𝕜 = ℂ`;
* (b) the FSG:155 conclusion shape at `C = 1 / (N + 1)` for every such diagonal `r`;
* (c) RB:331 at `ν : PosReal` with `Fact (1 ≤ ν)`;
* (d) the RCLike fallback shapes (`RA`/`RAf`) of every fallback-eligible target, and the RCLike
  specializations of `norm_gammaScalar`, `norm_gamma_head_le`, `norm_gamma_inv_head_le`, each by
  application of the PROVED-primary declaration;
* (e) the generic sum-form companion for L005: the decomposition through `defect_eq` and its norm
  majorant through `norm_head_leak_le_coeff`, `norm_tail_leak_le_coeff` and `norm_add_le`.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.GammaLeakage

/-! ### (a) FSG shapes at `𝕜 = ℂ` -/

section FSGComplexScalar

open RadiiPolynomial.Fourier

variable {ν : PosReal}

/-- FSG:16 `gammaC N k := ((ReesBridge.gammaW ν N k : ℝ) : ℂ)`: the old ℂ cast is the real-scalar
map at `𝕜 = ℂ`. -/
theorem old_gammaC (N : ℕ) (k : ℤ) :
    (gammaScalar (ν : ℝ) N k : ℂ) = ((Rees.Laurent.gammaW (ν : ℝ) N k : ℝ) : ℂ) :=
  rfl

/-- FSG:81 `winZ_eq_H`: the S027 head `HeadTailColumns.H N = Finset.Icc (-(N : ℤ)) N` is `winZ N`. -/
theorem old_winZ_eq_H (N : ℕ) : winZ N = Finset.Icc (-(N : ℤ)) N :=
  rfl

/-- FSG:19 `norm_gammaC` (`gammaC ↦ gammaScalar`, `ReesBridge.gammaW ν ↦ Rees.Laurent.gammaW ν`). -/
theorem old_norm_gammaC (N : ℕ) (k : ℤ) :
    ‖(gammaScalar (ν : ℝ) N k : ℂ)‖ = Rees.Laurent.gammaW (ν : ℝ) N k :=
  norm_gammaScalar (ν : ℝ) N k

/-- FSG:23 `gammaC_ne_zero`. -/
theorem old_gammaC_ne_zero (N : ℕ) (k : ℤ) : (gammaScalar (ν : ℝ) N k : ℂ) ≠ 0 :=
  gammaScalar_ne_zero ν.coe_pos N k

end FSGComplexScalar

section FSGComplex

open RadiiPolynomial.Fourier

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- FSG:29 `norm_gamma_head_le` (`HeadTailColumns.H N ↦ winZ N`). -/
theorem old_norm_gamma_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : ℂ) else 0)‖ ≤ 1 :=
  norm_gamma_head_le N

/-- FSG:41 `norm_gamma_inv_head_le`. -/
theorem old_norm_gamma_inv_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : ℂ)⁻¹ else 0)‖ ≤
      (ν : ℝ) ^ (2 * (N + 1)) :=
  norm_gamma_inv_head_le N

/-- FSG:59 `DΓ_comp_DΓplus` (`DΓ ↦ gammaDiag`, `DΓplus ↦ gammaInvDiag`, `P_H ↦ headProj`). -/
theorem old_DΓ_comp_DΓplus (N : ℕ) :
    (gammaDiag N : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L gammaInvDiag N =
      lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) :=
  gammaDiag_comp_gammaInvDiag N

/-- FSG:70 `DΓ_entry_eq_rees` with the old ℂ cast `((… : ℝ) : ℂ)` (`ReesBridge.aN ↦ Rees.Laurent.aN`). -/
theorem old_DΓ_entry_eq_rees (N : ℕ) : ∀ k ∈ winZ N,
    lpOneAlg.toRealSeq ((gammaDiag N : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))
      (lpOneAlg.single k 1)) k =
      ((Polynomial.eval (1 / (ν : ℝ))
        ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN N k) : ℝ) : ℂ) :=
  gammaDiag_entry_eq_rees N

/-- FSG:84 `norm_DΓplus_leak_le` with the source's literal tail `1 - headProj (winZ N)`. -/
theorem old_norm_DΓplus_leak_le (N : ℕ) (c : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖(gammaInvDiag N : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L
      lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) ∘L
      lpOneAlg.mulLeftCLM (𝕜 := ℂ) c ∘L
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N))‖ ≤ ‖c‖ :=
  norm_gammaInvDiag_leak_le N c

/-- FSG:131 `norm_head_leak_le_coeff` with the source's literal tail `1 - headProj (winZ N)`. -/
theorem old_norm_head_leak_le_coeff (N : ℕ)
    (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))
    (c : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) ∘L
      lpOneAlg.mulLeftCLM (𝕜 := ℂ) c ∘L
        (1 - lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N))‖ ≤
      ‖M ∘L lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) ∘L gammaDiag N‖ * ‖c‖ :=
  norm_head_leak_le_coeff N M c

/-! ### (b) the FSG:155 conclusion shape at `C = 1 / (N + 1)` -/

/-- FSG:155 `norm_tail_leak_le_coeff` shape `‖R N ∘L L_c‖ ≤ ‖c‖ / (N + 1)`, for EVERY diagonal `r`
with `‖r_k‖ ≤ 1 / (N + 1)` (the `rTail` instance itself is unit (v)'s). -/
theorem old_norm_tail_leak_le_coeff (N : ℕ) (r : ℤ → ℂ) (hr : ∀ k, ‖r k‖ ≤ 1 / ((N : ℝ) + 1))
    (c : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖(lpOneAlg.diagCLM (G := geomFiberZ ℂ ν) r (1 / ((N : ℝ) + 1)) hr :
        lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L
      lpOneAlg.mulLeftCLM (𝕜 := ℂ) c‖ ≤ ‖c‖ / ((N : ℝ) + 1) :=
  (norm_tail_leak_le_coeff r (1 / ((N : ℝ) + 1)) hr c).trans_eq (one_div_mul_eq_div _ _)

/-! ### (c) RB:331 -/

/-- RB:331 `ReesBridge.gammaW_inv_le` at `ν : PosReal` with `Fact (1 ≤ ν)`
(`ReesBridge.gammaW ν ↦ Rees.Laurent.gammaW (ν : ℝ)`). -/
theorem old_gammaW_inv_le (N : ℕ) (k : ℤ) :
    (Rees.Laurent.gammaW (ν : ℝ) N k)⁻¹ ≤ (ν : ℝ) ^ (2 * (N + 1)) :=
  Rees.Laurent.gammaW_inv_le Fact.out N k

end FSGComplex

/-! ### (d) RCLike fallback shapes and RCLike specializations (by application of the primary) -/

section D_T3_rclike_witness

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜]

/-- (d) T3/rclike_witness (context RA): the RCLike specialization of `RadiiPolynomial.Fourier.norm_gammaScalar`, by application of the PROVED-primary declaration (template sha256 `b8c267faf1119fdc…`). -/
theorem old_rclike_norm_gammaScalar (ν : ℝ) (N : ℕ) (k : ℤ) :
    ‖(gammaScalar ν N k : 𝕜)‖ = Rees.Laurent.gammaW ν N k :=
  norm_gammaScalar ν N k

end D_T3_rclike_witness

section D_T4_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜]

/-- (d) T4/fallback (context RA): the RCLike fallback shape of `RadiiPolynomial.Fourier.gammaScalar_ne_zero`, by application of the PROVED-primary declaration (template sha256 `c18e1aaaea1b47f0…`). -/
theorem old_rclike_gammaScalar_ne_zero {ν : ℝ} (hν : 0 < ν) (N : ℕ) (k : ℤ) :
    (gammaScalar ν N k : 𝕜) ≠ 0 :=
  gammaScalar_ne_zero hν N k

end D_T4_fallback

section D_T5_rclike_witness

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T5/rclike_witness (context RAf): the RCLike specialization of `RadiiPolynomial.Fourier.norm_gamma_head_le`, by application of the PROVED-primary declaration (template sha256 `98b9ee127abe6aeb…`). -/
theorem old_rclike_norm_gamma_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜) else 0)‖ ≤ 1 :=
  norm_gamma_head_le N

end D_T5_rclike_witness

section D_T6_rclike_witness

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T6/rclike_witness (context RAf): the RCLike specialization of `RadiiPolynomial.Fourier.norm_gamma_inv_head_le`, by application of the PROVED-primary declaration (template sha256 `93b69dbae41a82e8…`). -/
theorem old_rclike_norm_gamma_inv_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜)⁻¹ else 0)‖ ≤
      (ν : ℝ) ^ (2 * (N + 1)) :=
  norm_gamma_inv_head_le N

end D_T6_rclike_witness

section D_T9_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T9/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.gammaDiag_comp_gammaInvDiag`, by application of the PROVED-primary declaration (template sha256 `ff946a60d4dacaa0…`). -/
theorem old_rclike_gammaDiag_comp_gammaInvDiag (N : ℕ) :
    (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (gammaInvDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :=
  gammaDiag_comp_gammaInvDiag N

end D_T9_fallback

section D_T10_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T10/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.gammaDiag_entry_eq_rees`, by application of the PROVED-primary declaration (template sha256 `05faa9f5c20c73f4…`). -/
theorem old_rclike_gammaDiag_entry_eq_rees (N : ℕ) :
    ∀ k ∈ winZ N, lpOneAlg.toRealSeq ((gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (lpOneAlg.single k 1)) k =
      algebraMap ℝ 𝕜 (Polynomial.eval (1 / (ν : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN N k)) :=
  gammaDiag_entry_eq_rees N

end D_T10_fallback

section D_T11_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T11/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.norm_mulLeftCLM_le`, by application of the PROVED-primary declaration (template sha256 `ec5cea66ba842e1f…`). -/
theorem old_rclike_norm_mulLeftCLM_le (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(lpOneAlg.mulLeftCLM (𝕜 := 𝕜) c : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤ ‖c‖ :=
  norm_mulLeftCLM_le c

end D_T11_fallback

section D_T12_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T12/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.norm_gammaInvDiag_leak_le`, by application of the PROVED-primary declaration (template sha256 `6e96669a90d3fccd…`). -/
theorem old_rclike_norm_gammaInvDiag_leak_le (N : ℕ) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(gammaInvDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
      (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) c : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤ ‖c‖ :=
  norm_gammaInvDiag_leak_le N c

end D_T12_fallback

section D_T13_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T13/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.norm_head_leak_le_coeff`, by application of the PROVED-primary declaration (template sha256 `f925ea12f3fa9bcc…`). -/
theorem old_rclike_norm_head_leak_le_coeff (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) c : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
      (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤
      ‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ * ‖c‖ :=
  norm_head_leak_le_coeff N M c

end D_T13_fallback

section D_T14_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T14/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.norm_tail_leak_le_coeff`, by application of the PROVED-primary declaration (template sha256 `808eb6344786a262…`). -/
theorem old_rclike_norm_tail_leak_le_coeff (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖(lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
      (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) c : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ ≤ C * ‖c‖ :=
  norm_tail_leak_le_coeff r C hr c

end D_T14_fallback

section D_T15_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T15/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.norm_defect_le_gamma`, by application of the PROVED-primary declaration (template sha256 `3b1658cd4f94b7fa…`). -/
theorem old_rclike_norm_defect_le_gamma (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖defect N M r C hr c‖ ≤ (‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ + C) * ‖c‖ :=
  norm_defect_le_gamma N M r C hr c

end D_T15_fallback

section D_T16a_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T16a/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.toRealSeq_gammaDiag`, by application of the PROVED-primary declaration (template sha256 `c91fb4d40b50374d…`). -/
theorem old_rclike_toRealSeq_gammaDiag (N : ℕ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    lpOneAlg.toRealSeq ((gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a) k =
      (if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜) else 0) * lpOneAlg.toRealSeq a k :=
  toRealSeq_gammaDiag N a k

end D_T16a_fallback

section D_T16b_fallback

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- (d) T16b/fallback (context RAf): the RCLike fallback shape of `RadiiPolynomial.Fourier.toRealSeq_gammaInvDiag`, by application of the PROVED-primary declaration (template sha256 `b0e64fb9f83cb457…`). -/
theorem old_rclike_toRealSeq_gammaInvDiag (N : ℕ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    lpOneAlg.toRealSeq ((gammaInvDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) a) k =
      (if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜)⁻¹ else 0) * lpOneAlg.toRealSeq a k :=
  toRealSeq_gammaInvDiag N a k

end D_T16b_fallback

/-! ### (e) the generic sum-form companion for L005 (Codex CHANGES C1 on contract/v1) -/

section SumForm

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

omit [NormedAlgebra ℝ 𝕜] in
/-- (e) The decomposition of the defect, by application of L002 `defect_eq`. -/
theorem sumForm_defect_eq (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    defect N M r C hr c = defectHead N M c + defectTail r C hr c :=
  defect_eq N M r C hr c

/-- (e) The sum-norm Γ majorant: `norm_add_le` with one application each of
`norm_head_leak_le_coeff` (T13) and `norm_tail_leak_le_coeff` (T14). -/
theorem sumForm_norm_le (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖defectHead N M c + defectTail r C hr c‖ ≤
      ‖M ∘L (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
          (gammaDiag N : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))‖ * ‖c‖ + C * ‖c‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_head_leak_le_coeff N M c) (norm_tail_leak_le_coeff r C hr c))

end SumForm

end RadiiPolynomial.Tests.FZ.GammaLeakage
