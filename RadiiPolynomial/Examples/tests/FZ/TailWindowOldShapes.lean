import RadiiPolynomial.Analysis.SequenceSpace.Fourier.TailWindow

/-!
# FZ tail-window tests: old-shape witnesses (T45, L002)

Each `old_<name>` restates a proposition of the frozen sources of record in its OLD shape and
proves it by applying the new library API (no re-proof). The docstring of each witness gives the
explicit old → new symbol mapping. Nothing here imports or revalidates a frozen scratch constant:
the old propositions are written over library symbols.

Sources: SL25 = `tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean` (`2c938be2…`),
FS = `tmp/units/S028b-FourierSemilinearZ1/freeze/v1/FourierSemilinear.lean` (`d448cfad…`),
S027 head `HeadTailColumns.H N = Finset.Icc (-(N : ℤ)) N` (HTC:295) with
`HeadTailColumns.P_H ↦ lpOneAlg.headProj` (L001).

* (a) the FS-consumed SL25 shapes and FS `band_mul`/`band_pow` at `𝕜 = ℂ`, with the S027 head
  `Finset.Icc (-(N : ℤ)) N` in the range hypothesis;
* (b) SL25's statement of record :831 and C4 :681 with SL25's column ratio `‖T e_j‖ / ν^|j|`
  and `headP N` read as `headProj (winZ N)`, in the `RCLike` + `Fact (1 ≤ ν)` context;
* (c) SL25 :604's explicit-sum column shape.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.TailWindow

/-! ### (a) FS-consumed shapes at `𝕜 = ℂ` -/

section FSShapesNormed

open RadiiPolynomial.Fourier

variable {ν : PosReal}

/-- Old shape SL25:99 at `𝕜 = ℂ` (`FZ ℂ ν ↦ lpOneAlg ℤ (geomFiberZ ℂ ν)`;
`FourierZ1Window.norm_eq_tsum_coeff ↦ Fourier.norm_eq_tsum_coeff`). -/
theorem old_norm_eq_tsum_coeff (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖a‖ = ∑' k : ℤ, ‖lpOneAlg.toRealSeq a k‖ * (ν : ℝ) ^ k.natAbs :=
  norm_eq_tsum_coeff a

/-- Old shape SL25:104 at `𝕜 = ℂ` (`FourierZ1Window.summable_coeff ↦ Fourier.summable_coeff`). -/
theorem old_summable_coeff (a : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    Summable (fun k : ℤ => ‖lpOneAlg.toRealSeq a k‖ * (ν : ℝ) ^ k.natAbs) :=
  summable_coeff a

/-- Old shape SL25:1230 at `𝕜 = ℂ`, as FS:201 consumes it
(`FourierZ1Window.band_one ↦ Fourier.band_one`). -/
theorem old_band_one :
    ∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (1 : lpOneAlg ℤ (geomFiberZ ℂ ν)) i = 0 :=
  band_one

/-- Old shape SL25:1234 at `𝕜 = ℂ` (`FourierZ1Window.band_single ↦ Fourier.band_single`). -/
theorem old_band_single (m : ℕ) (j : ℤ) (x : ℂ) (hj : j.natAbs ≤ m) :
    ∀ i : ℤ, m < i.natAbs →
      lpOneAlg.toRealSeq (lpOneAlg.single j x : lpOneAlg ℤ (geomFiberZ ℂ ν)) i = 0 :=
  band_single m j x hj

/-- Old shape SL25:881 (`FourierZ1Window.window_eq_of_le ↦ Fourier.window_eq_of_le`;
no scalars). -/
theorem old_window_eq_of_le (N m K₀ : ℕ) (hK : K₀ ≤ N + 1) : m + max (N + 1) K₀ = N + m + 1 :=
  window_eq_of_le N m K₀ hK

end FSShapesNormed

section FSShapesComplete

open RadiiPolynomial.Fourier

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- Old shape SL25:527 at `𝕜 = ℂ`
(`FourierZ1Window.toRealSeq_mul_single ↦ Fourier.toRealSeq_mul_single`). -/
theorem old_toRealSeq_mul_single (x : lpOneAlg ℤ (geomFiberZ ℂ ν)) (j k : ℤ) :
    lpOneAlg.toRealSeq (x * lpOneAlg.single j 1) k = lpOneAlg.toRealSeq x (k - j) :=
  toRealSeq_mul_single x j k

/-- Old shape FS:180 (`FourierSemilinear.band_mul ↦ Fourier.band_mul`, at `𝕜 = ℂ`). -/
theorem old_band_mul (m n : ℕ) (x y : lpOneAlg ℤ (geomFiberZ ℂ ν))
    (hx : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq x i = 0)
    (hy : ∀ i : ℤ, n < i.natAbs → lpOneAlg.toRealSeq y i = 0) :
    ∀ k : ℤ, m + n < k.natAbs → lpOneAlg.toRealSeq (x * y) k = 0 :=
  band_mul m n x y hx hy

/-- Old shape FS:195 (`FourierSemilinear.band_pow ↦ Fourier.band_pow`, at `𝕜 = ℂ`). -/
theorem old_band_pow (N : ℕ) (abar : lpOneAlg ℤ (geomFiberZ ℂ ν))
    (habar : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq abar i = 0) :
    ∀ n i, n * N < i.natAbs → lpOneAlg.toRealSeq (abar ^ n) i = 0 :=
  band_pow N abar habar

/-- Old shape SL25:852 at `𝕜 = ℂ` as FS:394 consumes it, with the S027 head in the range
hypothesis (`FourierZ1Window.defect ↦ Fourier.defect`, `aCol ↦ headCol`, `sCol ↦ tailCol`,
`FourierZ1Window.winZ ↦ Fourier.winZ`, `headP N` and `HeadTailColumns.P_H (H N)` ↦
`lpOneAlg.headProj (Finset.Icc (-(N : ℤ)) N)` = `headProj (winZ N)` definitionally). -/
theorem old_opNorm_defect_eq_sup'_explicit (N m K₀ : ℕ)
    (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) (r : ℤ → ℂ) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : lpOneAlg ℤ (geomFiberZ ℂ ν))
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hPM : (lpOneAlg.headProj (Finset.Icc (-(N : ℤ)) N) :
      lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => headCol N M b j + tailCol m r b j) :=
  opNorm_defect_eq_sup'_explicit N m K₀ M r C hr b hb hPM hr0 hmono

/-- Old shape SL25:866 at `𝕜 = ℂ` as FS:408 consumes it
(`FourierZ1Window.defect_attained ↦ Fourier.defect_attained`; attainment as a weighted column
ratio at the atom `single j 1`). -/
theorem old_defect_attained (N m K₀ : ℕ)
    (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) (r : ℤ → ℂ) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : lpOneAlg ℤ (geomFiberZ ℂ ν))
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ∃ j ∈ winZ (m + max (N + 1) K₀),
      ‖defect N M r C hr b (lpOneAlg.single j 1)‖ = ‖defect N M r C hr b‖ * (ν : ℝ) ^ j.natAbs :=
  defect_attained N m K₀ M r C hr b hb hmono

end FSShapesComplete

/-! ### (b) SL25's statement of record and C4 with SL25's column ratio, `RCLike` context -/

section SL25Record

open RadiiPolynomial.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- Old shape SL25:831, the statement of record (`FourierZ1Window.defect ↦ Fourier.defect`,
whose head is `headP N ↦ headProj (winZ N)`; SL25's `colRatio T j = ‖T e_j‖ / ν^|j|` ↦ the
explicit ratio, via `colRatio_geom`; `FourierZ1Window.winZ ↦ Fourier.winZ`). -/
theorem old_opNorm_defect_eq_sup' (N m K₀ : ℕ)
    (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => ‖defect N M r C hr b (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs) :=
  (opNorm_defect_eq_sup' (𝕜 := 𝕜) (ν := ν) N m K₀ M r C hr b hb hmono).trans
    (Finset.sup'_congr _ rfl fun j _ => colRatio_geom _ j)

/-- Old shape SL25:681 (C4) (`Hd ↦ defectHead`, `Tl ↦ defectTail`, `headP N ↦ headProj (winZ N)`
in the range hypothesis, SL25's `colRatio` ↦ the explicit ratio `‖T e_j‖ / ν^|j|`). -/
theorem old_colRatio_defect (N : ℕ)
    (M : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hPM : (lpOneAlg.headProj (winZ N) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν)) ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (j : ℤ) :
    ‖defect N M r C hr b (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs
      = ‖defectHead N M b (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs
        + ‖defectTail r C hr b (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs := by
  have h := colRatio_defect (𝕜 := 𝕜) (ν := ν) N M r C hr b hPM hr0 j
  rwa [colRatio_geom, colRatio_geom, colRatio_geom] at h

/-! ### (c) SL25 :604, the explicit-sum tail column -/

/-- Old shape SL25:604 (`colRatio_Tl ↦ colRatio_defectTail` with `tailCol` unfolded;
`Tl ↦ defectTail`; SL25's `colRatio` ↦ the explicit ratio). -/
theorem old_colRatio_Tl (m : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (b : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ) :
    ‖defectTail r C hr b (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs
      = (∑ i ∈ winZ m, ‖r (j + i)‖ * ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ (j + i).natAbs)
          / (ν : ℝ) ^ j.natAbs :=
  (colRatio_geom _ j).symm.trans (colRatio_defectTail (𝕜 := 𝕜) (ν := ν) m r C hr b hb j)

end SL25Record

end RadiiPolynomial.Tests.FZ.TailWindow
