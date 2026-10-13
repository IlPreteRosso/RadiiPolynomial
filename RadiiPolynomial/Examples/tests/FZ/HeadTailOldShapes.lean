import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import RadiiPolynomial.Algebra.Ring.HeadTailIdentities
import RadiiPolynomial.Operators.HeadTail
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import Mathlib.Analysis.RCLike.Basic

/-!
# L001 tests (T45): old statement shapes, proved by the new API

Each `old_<name>` restates a proposition of a frozen scratch source of record and proves it by
applying the library declarations of L001. No frozen scratch constant is imported or
revalidated: the old propositions are restated through the explicit symbol mapping below.

Sources (cited by path, sha256 prefix and line):
* T6C = `tmp/units/S027-HeadTailColumns/freeze/v1/T6Consumer.lean` (d1d33800…) :8, :45–:131;
* HTC = `tmp/units/S027-HeadTailColumns/freeze/v1/HeadTailColumns.lean` (614b7107…);
* SL25 = `tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean` (2c938be2…).

Old → new symbol mapping:
* carrier `FZ 𝕜 ν` (SL25 :71) ↦ `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` (definitionally equal,
  `old_carrier_eq`);
* SL25 `headP N`, HTC `P_H (H N)` ↦ `lpOneAlg.headProj (Finset.Icc (-(N : ℤ)) N)`; membership
  `k ∈ Finset.Icc (-(N : ℤ)) N ↔ k.natAbs ≤ N` (`mem_oldHead`);
* SL25 `tailQ N`, HTC `1 - P_H (H N)` ↦ `lpOneAlg.tailProj (Finset.Icc (-(N : ℤ)) N)`
  (`= 1 - headProj …`, `tailProj_eq_one_sub`);
* SL25 `colRatio T j = ‖T e_j‖ / ν^|j|` ↦ the same expression, equal to `lpOneAlg.colRatio T j`
  (`oldColRatio_eq`);
* SL25 `diagCLM`, HTC `D_r` ↦ `lpOneAlg.diagCLM` (argument order `r C hr`);
* SL25 Part E ring identities, HTC `composition_identity` ↦ `HeadTail.*` with
  `IsIdempotentElem P` (`P * P = P`) and `Commute Λ P` (`Λ * P = P * Λ`) — definitionally the
  raw hypotheses.

Kernel-only; imported by nothing.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.HeadTail

open RadiiPolynomial lpOneAlg HeadTail

/-- The old head `[-N, N]` in `natAbs` form. -/
theorem mem_oldHead {N : ℕ} {k : ℤ} : k ∈ Finset.Icc (-(N : ℤ)) N ↔ k.natAbs ≤ N := by
  rw [Finset.mem_Icc]; omega

/-- The old column ratio `‖T e_j‖ / ν^|j|` is the library `colRatio`. -/
theorem oldColRatio_eq {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] F) (j : ℤ) :
    ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs = colRatio T j := by
  rw [colRatio, geomFiberZ_weight]

/-! ### (a) The fifteen T6C compatibility propositions (`[RCLike 𝕜]`) -/

/-- T6C :8 `carrier_eq`: the slice-25 carrier is the library carrier. -/
theorem old_carrier_eq {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal) :
    lpOneAlg ℤ (WeightedScalar 𝕜 (fun k : ℤ => (ν : ℝ) ^ k.natAbs)) =
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) := rfl

section T6C

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- T6C :45 (SL25 :184 `opNorm_le_iff_cols`), by `lpOneAlg.opNorm_le_iff_cols`. -/
theorem old_opNorm_le_iff_cols (T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ j : ℤ, ‖T (single j 1)‖ ≤ C * (ν : ℝ) ^ j.natAbs := by
  simpa only [geomFiberZ_weight] using opNorm_le_iff_cols T hC

/-- T6C :50 (SL25 :203 `colRatio_le_opNorm`), by `lpOneAlg.colRatio_le_opNorm`. -/
theorem old_colRatio_le_opNorm (T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] F) (j : ℤ) :
    ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs ≤ ‖T‖ :=
  (oldColRatio_eq T j).trans_le (colRatio_le_opNorm T j)

/-- T6C :56 (SL25 :212 `opNorm_eq_iSup_cols`), by `lpOneAlg.opNorm_eq_iSup_cols`. -/
theorem old_opNorm_eq_iSup_cols (T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] F) :
    ‖T‖ = ⨆ j : ℤ, ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs := by
  simp only [oldColRatio_eq]; exact opNorm_eq_iSup_cols T

/-- T6C :62 (SL25 :309 `toRealSeq_headP`), by `lpOneAlg.toRealSeq_headProj`. -/
theorem old_toRealSeq_headP (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    toRealSeq (headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x) k =
      if k.natAbs ≤ N then toRealSeq x k else 0 := by
  simp only [toRealSeq_headProj, mem_oldHead]

/-- T6C :68 (SL25 :315 `toRealSeq_tailQ`), by `lpOneAlg.toRealSeq_tailProj`. -/
theorem old_toRealSeq_tailQ (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    toRealSeq (tailProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x) k =
      if k.natAbs ≤ N then 0 else toRealSeq x k := by
  simp only [toRealSeq_tailProj, mem_oldHead]

/-- T6C :74 (SL25 :324 `headP_single`), by `lpOneAlg.headProj_single`. -/
theorem old_headP_single (N : ℕ) (j : ℤ) (x : 𝕜) :
    headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) =
      if j.natAbs ≤ N then single j x else 0 := by
  simp only [headProj_single, mem_oldHead]

/-- T6C :80 (SL25 :338 `tailQ_single`), by `lpOneAlg.tailProj_single`. -/
theorem old_tailQ_single (N : ℕ) (j : ℤ) (x : 𝕜) :
    tailProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) =
      if j.natAbs ≤ N then 0 else single j x := by
  simp only [tailProj_single, mem_oldHead]

/-- T6C :86 (SL25 :344 `headP_comp_headP`), by `lpOneAlg.headProj_comp_headProj`. -/
theorem old_headP_comp_headP (N : ℕ) :
    (headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        headProj (Finset.Icc (-(N : ℤ)) N) = headProj (Finset.Icc (-(N : ℤ)) N) :=
  headProj_comp_headProj _

/-- T6C :92 (SL25 :351 `headP_comp_tailQ`), by `lpOneAlg.headProj_comp_tailProj`. -/
theorem old_headP_comp_tailQ (N : ℕ) :
    (headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        tailProj (Finset.Icc (-(N : ℤ)) N) = 0 :=
  headProj_comp_tailProj _

/-- T6C :98 (SL25 :357 `tailQ_comp_headP`), by `lpOneAlg.tailProj_comp_headProj`. -/
theorem old_tailQ_comp_headP (N : ℕ) :
    (tailProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        headProj (Finset.Icc (-(N : ℤ)) N) = 0 :=
  tailProj_comp_headProj _

/-- T6C :104 (SL25 :279 `toRealSeq_diagCLM`), by `lpOneAlg.toRealSeq_diagCLM`. -/
theorem old_toRealSeq_diagCLM (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (k : ℤ) :
    toRealSeq (diagCLM r C hr x) k = r k * toRealSeq x k :=
  toRealSeq_diagCLM r C hr x k

/-- T6C :110 (SL25 :288 `diagCLM_single`), by `lpOneAlg.diagCLM_single`. -/
theorem old_diagCLM_single (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (j : ℤ) (x : 𝕜) :
    diagCLM r C hr (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = single j (r j * x) :=
  diagCLM_single r C hr j x

/-- T6C :116 (SL25 :434 `norm_add_of_head_tail`), by `lpOneAlg.norm_add_of_head_tail`. -/
theorem old_norm_add_of_head_tail (N : ℕ) (x y : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hx : headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x = x)
    (hy : tailProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) y = y) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  norm_add_of_head_tail _ x y hx hy

/-- T6C :123 (SL25 :461 `colRatio_add_of_head_tail`), by `lpOneAlg.colRatio_add_of_head_tail`. -/
theorem old_colRatio_add_of_head_tail (N : ℕ)
    (S T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hS : headProj (Finset.Icc (-(N : ℤ)) N) ∘L S = S)
    (hT : tailProj (Finset.Icc (-(N : ℤ)) N) ∘L T = T) (j : ℤ) :
    ‖(S + T) (single j 1)‖ / (ν : ℝ) ^ j.natAbs =
      ‖S (single j 1)‖ / (ν : ℝ) ^ j.natAbs + ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs := by
  simp only [oldColRatio_eq]; exact colRatio_add_of_head_tail _ S T hS hT j

/-- T6C :131 (SL25 :470 `opNorm_add_eq_iSup`), by `lpOneAlg.opNorm_add_eq_iSup`. -/
theorem old_opNorm_add_eq_iSup (N : ℕ)
    (S T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hS : headProj (Finset.Icc (-(N : ℤ)) N) ∘L S = S)
    (hT : tailProj (Finset.Icc (-(N : ℤ)) N) ∘L T = T) :
    ‖S + T‖ = ⨆ j : ℤ,
      (‖S (single j 1)‖ / (ν : ℝ) ^ j.natAbs + ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs) := by
  simp only [oldColRatio_eq]; exact opNorm_add_eq_iSup _ S T hS hT

end T6C

/-! ### (a) HTC Fourier-carrier faces (`[NormedField 𝕜]`, HTC :310–:347) -/

section HTCGeom

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- HTC :310 `geom_toRealSeq_P_H`, by `lpOneAlg.toRealSeq_headProj`. -/
theorem old_toRealSeq_P_H (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (j : ℤ) :
    toRealSeq (headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x) j =
      if j.natAbs ≤ N then toRealSeq x j else 0 := by
  simp only [toRealSeq_headProj, mem_oldHead]

/-- HTC :315 `geom_toRealSeq_Q_H`, by `lpOneAlg.toRealSeq_tailProj`. -/
theorem old_toRealSeq_Q_H (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (j : ℤ) :
    toRealSeq ((1 - headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N)) x) j =
      if j.natAbs ≤ N then 0 else toRealSeq x j := by
  simp only [← tailProj_eq_one_sub, toRealSeq_tailProj, mem_oldHead]

/-- HTC :320 `geom_toRealSeq_D_r`, by `lpOneAlg.toRealSeq_diagCLM`. -/
theorem old_toRealSeq_D_r (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C)
    (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (j : ℤ) :
    toRealSeq (diagCLM r C hr x) j = r j * toRealSeq x j :=
  toRealSeq_diagCLM r C hr x j

/-- HTC :325 `geom_P_H_single`, by `lpOneAlg.headProj_single`. -/
theorem old_P_H_single (N : ℕ) (j : ℤ) (x : 𝕜) :
    headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) =
      if j.natAbs ≤ N then single j x else 0 := by
  simp only [headProj_single, mem_oldHead]

/-- HTC :330 `geom_Q_H_single`, by `lpOneAlg.tailProj_single`. -/
theorem old_Q_H_single (N : ℕ) (j : ℤ) (x : 𝕜) :
    (1 - headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N))
        (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) =
      if j.natAbs ≤ N then 0 else single j x := by
  simp only [← tailProj_eq_one_sub, tailProj_single, mem_oldHead]

/-- HTC :335 `geom_D_r_single`, by `lpOneAlg.diagCLM_single`. -/
theorem old_D_r_single (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (j : ℤ) (x : 𝕜) :
    diagCLM r C hr (single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) = single j (r j * x) :=
  diagCLM_single r C hr j x

/-- HTC :339 `geom_P_H_comp_P_H`, by `lpOneAlg.headProj_comp_headProj`. -/
theorem old_P_H_comp_P_H (N : ℕ) :
    (headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        headProj (Finset.Icc (-(N : ℤ)) N) = headProj (Finset.Icc (-(N : ℤ)) N) :=
  headProj_comp_headProj _

/-- HTC :343 `geom_P_H_comp_Q_H`, by `lpOneAlg.headProj_comp_tailProj`. -/
theorem old_P_H_comp_Q_H (N : ℕ) :
    (headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        (1 - headProj (Finset.Icc (-(N : ℤ)) N)) = 0 :=
  headProj_comp_tailProj _

/-- HTC :347 `geom_Q_H_comp_P_H`, by `lpOneAlg.tailProj_comp_headProj`. -/
theorem old_Q_H_comp_P_H (N : ℕ) :
    (1 - headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L
        headProj (Finset.Icc (-(N : ℤ)) N) = 0 :=
  tailProj_comp_headProj _

end HTCGeom

/-! ### (b) SL25 ranges, head-vanishing diagonals and the B2 joint forms (one `N`) -/

section SL25

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal}

/-- SL25 :382 `headP_eq_self_iff`, by `lpOneAlg.headProj_apply_eq_self_iff`. -/
theorem old_headP_eq_self_iff (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    headProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x = x ↔
      ∀ k : ℤ, N < k.natAbs → toRealSeq x k = 0 := by
  rw [headProj_apply_eq_self_iff]
  exact forall_congr' fun k => by rw [mem_oldHead, not_le]

/-- SL25 :395 `tailQ_eq_self_iff`, by `lpOneAlg.tailProj_apply_eq_self_iff`. -/
theorem old_tailQ_eq_self_iff (N : ℕ) (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    tailProj (𝕜 := 𝕜) (Finset.Icc (-(N : ℤ)) N) x = x ↔
      ∀ k : ℤ, k.natAbs ≤ N → toRealSeq x k = 0 := by
  rw [tailProj_apply_eq_self_iff]
  exact forall_congr' fun k => by rw [mem_oldHead]

/-- SL25 :408 `headP_comp_diagCLM`, by `lpOneAlg.headProj_comp_diagCLM`. -/
theorem old_headP_comp_diagCLM (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    (headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L diagCLM r C hr = 0 :=
  headProj_comp_diagCLM _ r C hr fun k hk => hr0 k (mem_oldHead.mp hk)

/-- SL25 :419 `tailQ_comp_diagCLM`, by `lpOneAlg.tailProj_comp_diagCLM`. -/
theorem old_tailQ_comp_diagCLM (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    (tailProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L diagCLM r C hr =
      diagCLM r C hr :=
  tailProj_comp_diagCLM _ r C hr fun k hk => hr0 k (mem_oldHead.mp hk)

/-- SL25 :476 `colRatio_Z_tail`, by `lpOneAlg.colRatio_eq_zero_of_comp_tailProj`. -/
theorem old_colRatio_Z_tail (N : ℕ)
    (Z : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hZQ : Z ∘L tailProj (Finset.Icc (-(N : ℤ)) N) = 0) (j : ℤ) (hj : N < j.natAbs) :
    ‖Z (single j 1)‖ / (ν : ℝ) ^ j.natAbs = 0 := by
  rw [oldColRatio_eq]
  exact colRatio_eq_zero_of_comp_tailProj _ Z hZQ j fun h => absurd (mem_oldHead.mp h) (by omega)

/-- SL25 :484 `colRatio_S_head`, by `lpOneAlg.colRatio_eq_zero_of_comp_headProj`. -/
theorem old_colRatio_S_head (N : ℕ)
    (S : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hSP : S ∘L headProj (Finset.Icc (-(N : ℤ)) N) = 0) (j : ℤ) (hj : j.natAbs ≤ N) :
    ‖S (single j 1)‖ / (ν : ℝ) ^ j.natAbs = 0 := by
  rw [oldColRatio_eq]
  exact colRatio_eq_zero_of_comp_headProj _ S hSP j (mem_oldHead.mpr hj)

/-- SL25 :492 `colRatio_Z_add_S`, by `lpOneAlg.colRatio_add_of_comp_split`. -/
theorem old_colRatio_Z_add_S (N : ℕ)
    (Z S : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hZQ : Z ∘L tailProj (Finset.Icc (-(N : ℤ)) N) = 0)
    (hSP : S ∘L headProj (Finset.Icc (-(N : ℤ)) N) = 0) (j : ℤ) :
    ‖(Z + S) (single j 1)‖ / (ν : ℝ) ^ j.natAbs =
      ‖Z (single j 1)‖ / (ν : ℝ) ^ j.natAbs + ‖S (single j 1)‖ / (ν : ℝ) ^ j.natAbs := by
  simp only [oldColRatio_eq]; exact colRatio_add_of_comp_split _ Z S hZQ hSP j

/-- SL25 :510 `opNorm_joint_eq_iSup` (one `N` for both heads), by
`lpOneAlg.opNorm_joint_eq_iSup`. -/
theorem old_opNorm_joint_eq_iSup (N : ℕ)
    (Z S T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hPZ : headProj (Finset.Icc (-(N : ℤ)) N) ∘L Z = Z)
    (hZQ : Z ∘L tailProj (Finset.Icc (-(N : ℤ)) N) = 0)
    (hPS : headProj (Finset.Icc (-(N : ℤ)) N) ∘L S = S)
    (hSP : S ∘L headProj (Finset.Icc (-(N : ℤ)) N) = 0)
    (hT : tailProj (Finset.Icc (-(N : ℤ)) N) ∘L T = T) :
    ‖Z + S + T‖ = ⨆ j : ℤ, (‖Z (single j 1)‖ / (ν : ℝ) ^ j.natAbs +
      ‖S (single j 1)‖ / (ν : ℝ) ^ j.natAbs + ‖T (single j 1)‖ / (ν : ℝ) ^ j.natAbs) := by
  simp only [oldColRatio_eq]; exact opNorm_joint_eq_iSup _ _ Z S T hPZ hZQ hPS hSP hT

end SL25

/-! ### (c) HTC :55 explicit-`C` iff (test witness, not an alias) -/

/-- HTC :55 `opNorm_le_iff_cols` with `C` explicit, by `lpOneAlg.opNorm_le_iff_cols`. -/
theorem old_HTC_opNorm_le_iff_cols {𝕜 : Type*} [NontriviallyNormedField 𝕜] {I : Type*}
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq I]
    [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 I E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (T : lpOneAlg I E →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ i, ‖T (single i (1 : 𝕜))‖ ≤ C * FiberTrivialization.weight (E := E) i :=
  opNorm_le_iff_cols T hC

/-! ### (d) SL25 Part E ring identities with raw hypotheses -/

section RingOld

variable {R : Type*} [Ring R]

/-- SL25 :975 `defect_identity_ring` (raw `P * P = P`, `Λ * P = P * Λ`), by
`HeadTail.defect_identity_ring`. -/
theorem old_defect_identity_ring (P M G Λ L : R) (hP : P * P = P) (hΛ : Λ * P = P * Λ)
    (hG : G * P = 0) :
    (M * P + G) * ((P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L))
      = -(M * P * L * (1 - P) + G * (1 - P) * L) :=
  defect_identity_ring P M G Λ L hP hΛ hG

/-- SL25 :994 `inverse_defect_ring_core` (raw `P * P = P`), by `HeadTail.inverse_defect_ring`. -/
theorem old_inverse_defect_ring_core (P M G Λ L : R) (hP : P * P = P)
    (hG : G * P = 0) (hGΛ : G * Λ * (1 - P) = 1 - P) :
    1 - (M * P + G) * (P * (Λ + L) * P + (1 - P) * Λ * (1 - P))
      = P - M * P * (Λ + L) * P :=
  inverse_defect_ring P M G Λ L hP hG hGΛ

/-- SL25 :1017 `inverse_defect_ring` (with its unused `_hΛ`), by `HeadTail.inverse_defect_ring`. -/
theorem old_inverse_defect_ring (P M G Λ L : R) (hP : P * P = P) (_hΛ : Λ * P = P * Λ)
    (hG : G * P = 0) (hGΛ : G * Λ * (1 - P) = 1 - P) :
    1 - (M * P + G) * (P * (Λ + L) * P + (1 - P) * Λ * (1 - P))
      = P - M * P * (Λ + L) * P :=
  inverse_defect_ring P M G Λ L hP hG hGΛ

end RingOld

/-! ### (e) The HTC/D12-context faces of T21/T22/T25/T26 (fallback context D12) -/

section D12

variable {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
  [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)]

/-- T21 in D12, by `lpOneAlg.isIdempotentElem_headProj`. -/
theorem old_D12_isIdempotentElem_headProj [FiberTrivialization 𝕜 J G]
    [DecidableEq J] (H : Finset J) :
    IsIdempotentElem (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) :=
  isIdempotentElem_headProj H

/-- HTC :178 `P_H_comp_P_H` (D12 context), by `lpOneAlg.headProj_comp_headProj`. -/
theorem old_P_H_comp_P_H_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L headProj H = headProj H :=
  headProj_comp_headProj H

/-- HTC :185 `P_H_comp_Q_H` (D12 context), by `lpOneAlg.headProj_comp_tailProj`. -/
theorem old_P_H_comp_Q_H_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L (1 - headProj H) = 0 :=
  headProj_comp_tailProj H

/-- HTC :190 `Q_H_comp_P_H` (D12 context), by `lpOneAlg.tailProj_comp_headProj`. -/
theorem old_Q_H_comp_P_H_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) :
    (1 - headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L headProj H = 0 :=
  tailProj_comp_headProj H

/-- HTC :195 `Q_H_comp_Q_H` (D12 context), by `lpOneAlg.tailProj_comp_tailProj`. -/
theorem old_Q_H_comp_Q_H_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) :
    (1 - headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L (1 - headProj H) = 1 - headProj H :=
  tailProj_comp_tailProj H

/-- HTC :201 `P_H_add_Q_H` (D12 context), by `lpOneAlg.headProj_add_tailProj`. -/
theorem old_P_H_add_Q_H_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) + (1 - headProj H) = 1 :=
  headProj_add_tailProj H

/-- T25 (head face) in D12, by `lpOneAlg.headProj_comp_diagCLM`. -/
theorem old_D12_headProj_comp_diagCLM [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hr0 : ∀ j ∈ H, r j = 0) :
    (headProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L diagCLM r C hr = 0 :=
  headProj_comp_diagCLM H r C hr hr0

/-- T25 (tail face) in D12, by `lpOneAlg.tailProj_comp_diagCLM`. -/
theorem old_D12_tailProj_comp_diagCLM [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (r : J → 𝕜) (C : ℝ) (hr : ∀ j, ‖r j‖ ≤ C) (hr0 : ∀ j ∈ H, r j = 0) :
    (tailProj H : lpOneAlg J G →L[𝕜] lpOneAlg J G) ∘L diagCLM r C hr = diagCLM r C hr :=
  tailProj_comp_diagCLM H r C hr hr0

/-- HTC :205 `norm_add_of_head_tail` (D12 context), by `lpOneAlg.norm_add_of_head_tail`. -/
theorem old_norm_add_of_head_tail_D12 [FiberTrivialization 𝕜 J G] [DecidableEq J]
    (H : Finset J) (x y : lpOneAlg J G) (hx : headProj (𝕜 := 𝕜) H x = x)
    (hy : (1 - headProj (𝕜 := 𝕜) H) y = y) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  norm_add_of_head_tail H x y hx hy

end D12

/-! ### (f) HTC :269 with the raw `hP : P ∘L P = P` -/

/-- HTC :269 `composition_identity` (raw idempotence), by `HeadTail.composition_identity`. -/
theorem old_composition_identity {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (P M R L : E →L[𝕜] E) (hP : P ∘L P = P) (hRP : R ∘L P = 0) :
    (M ∘L P + R) ∘L (P ∘L L ∘L (1 - P) + (1 - P) ∘L L) =
      M ∘L P ∘L L ∘L (1 - P) + R ∘L L :=
  composition_identity P M R L ((ContinuousLinearMap.mul_def P P).trans hP) hRP

end RadiiPolynomial.Tests.FZ.HeadTail
