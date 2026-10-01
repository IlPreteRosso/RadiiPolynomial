import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift

/-!
# Bilateral windows and band support on the geometric carrier

On the bilateral geometric carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` (weight `ν^|k|`, any
normed field `𝕜`), this file collects the support facts shared by the exact finite-window
operator norm (`Fourier/TailWindow.lean`) and the later semilinear consumers.

* Windows: `winZ n = Icc (-n) n` (`|j| ≤ n`), with the natAbs membership face `mem_winZ` and
  the window maximum principle for functions on `ℤ` that are antitone outward beyond `±W`
  (`le_sup'_of_far_antitone`, `iSup_eq_sup'_of_far_antitone`).
* Coefficient norm: `‖a‖ = ∑' k, ‖aₖ‖ ν^|k|` (`norm_eq_tsum_coeff`, `summable_coeff`), from
  the generic fiber-norm face `lpOneAlg.norm_eq_abs_toReal_mul_weight` and the carrier weight
  `geomFiberZ_weight`.
* Band facts: the unit and the atoms are banded (`toRealSeq_one`, `band_one`, `band_single`),
  right multiplication by a unit atom shifts coefficients (`toRealSeq_mul_single`), and bands
  add under products and scale under powers (`band_mul`, `band_pow`).

The band facts that involve the product need `[CompleteSpace 𝕜]` and `Fact (1 ≤ ν)`: the
`ℤ`-indexed convolution is an absolutely convergent series (`lpOneAlg.instConvCompatOfWeightMul`).
Everything else holds over a bare `[NormedField 𝕜]`.
-/

noncomputable section

namespace RadiiPolynomial.Fourier

/-! ### Windows and the far-antitone maximum principle -/

/-- **(T1, L002.)** The bilateral window `{j : |j| ≤ n} = Icc (−n) n`. -/
def winZ (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

/-- **(T2, L002.)** Window membership in natAbs form. -/
theorem mem_winZ {n : ℕ} {j : ℤ} : j ∈ winZ n ↔ j.natAbs ≤ n := by
  rw [winZ, Finset.mem_Icc]; omega

/-- **(T3, L002.)** Windows are nonempty. -/
theorem winZ_nonempty (n : ℕ) : (winZ n).Nonempty := ⟨0, mem_winZ.mpr (Nat.zero_le n)⟩

/-- **(T4, L002.)** A function on `ℤ` that is antitone outward beyond `±W` is bounded by its
maximum over `winZ W`. -/
theorem le_sup'_of_far_antitone (f : ℤ → ℝ) (W : ℕ)
    (hpos : ∀ j : ℤ, (W : ℤ) ≤ j → f (j + 1) ≤ f j)
    (hneg : ∀ j : ℤ, j ≤ -(W : ℤ) → f (j - 1) ≤ f j) (j : ℤ) :
    f j ≤ (winZ W).sup' (winZ_nonempty W) f := by
  have hup : ∀ n : ℕ, f ((W : ℤ) + n) ≤ f W := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine le_trans ?_ ih
      have h := hpos ((W : ℤ) + n) (by omega)
      rwa [show (W : ℤ) + n + 1 = (W : ℤ) + ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
  have hdown : ∀ n : ℕ, f (-(W : ℤ) - n) ≤ f (-(W : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine le_trans ?_ ih
      have h := hneg (-(W : ℤ) - n) (by omega)
      rwa [show -(W : ℤ) - n - 1 = -(W : ℤ) - ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
  by_cases hj : j.natAbs ≤ W
  · exact Finset.le_sup' f (mem_winZ.mpr hj)
  · rcases (show (W : ℤ) < j ∨ j < -(W : ℤ) by omega) with h | h
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (W : ℤ) + n := ⟨(j - W).toNat, by omega⟩
      exact (hup n).trans (Finset.le_sup' f (mem_winZ.mpr (by simp)))
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(W : ℤ) - n := ⟨(-(W : ℤ) - j).toNat, by omega⟩
      exact (hdown n).trans (Finset.le_sup' f (mem_winZ.mpr (by simp)))

/-- **(T5, L002.)** The supremum of a far-antitone function on `ℤ` is its finite maximum over
`winZ W`. -/
theorem iSup_eq_sup'_of_far_antitone (f : ℤ → ℝ) (W : ℕ)
    (hpos : ∀ j : ℤ, (W : ℤ) ≤ j → f (j + 1) ≤ f j)
    (hneg : ∀ j : ℤ, j ≤ -(W : ℤ) → f (j - 1) ≤ f j) :
    ⨆ j : ℤ, f j = (winZ W).sup' (winZ_nonempty W) f := by
  have hle := le_sup'_of_far_antitone f W hpos hneg
  refine le_antisymm (ciSup_le hle) ?_
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (winZ_nonempty W) f
  exact hj ▸ le_ciSup ⟨_, by rintro _ ⟨i, rfl⟩; exact hle i⟩ j

/-! ### Coefficient norm and banded atoms (any normed field) -/

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- **(T6, L002.)** The norm of the bilateral geometric carrier as a coefficient series. -/
theorem norm_eq_tsum_coeff (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    ‖a‖ = ∑' k : ℤ, ‖lpOneAlg.toRealSeq a k‖ * (ν : ℝ) ^ k.natAbs := by
  rw [lpOneAlg.norm_eq_tsum]
  exact tsum_congr fun k => by rw [lpOneAlg.norm_eq_abs_toReal_mul_weight, geomFiberZ_weight]

/-- **(T7, L002.)** The weighted coefficient series is summable. -/
theorem summable_coeff (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) :
    Summable (fun k : ℤ => ‖lpOneAlg.toRealSeq a k‖ * (ν : ℝ) ^ k.natAbs) :=
  (lpOneAlg.summable_norm a).congr fun k => by
    rw [lpOneAlg.norm_eq_abs_toReal_mul_weight, geomFiberZ_weight]

/-- **(T8, L002.)** The coefficients of the unit: `1 = e₀`. -/
theorem toRealSeq_one (k : ℤ) :
    lpOneAlg.toRealSeq (1 : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) k = if k = 0 then 1 else 0 := by
  rw [lpOneAlg.one_eq_single_zero, lpOneAlg.toRealSeq_single]

/-- **(T9, L002.)** The unit has band `0`. -/
theorem band_one :
    ∀ i : ℤ, 0 < i.natAbs → lpOneAlg.toRealSeq (1 : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) i = 0 :=
  fun i hi => by rw [toRealSeq_one, ite_eq_right (show ¬i = 0 by omega)]

/-- **(T10, L002.)** An atom `x e_j` with `|j| ≤ m` has band `m`. -/
theorem band_single (m : ℕ) (j : ℤ) (x : 𝕜) (hj : j.natAbs ≤ m) :
    ∀ i : ℤ, m < i.natAbs →
      lpOneAlg.toRealSeq (lpOneAlg.single j x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) i = 0 :=
  fun i hi => by rw [lpOneAlg.toRealSeq_single, ite_eq_right (show ¬i = j by omega)]

end NormedField

/-! ### Products and powers (complete field, `ν ≥ 1`) -/

section Complete

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- **(T11, L002.)** Right multiplication by a unit atom shifts the coefficients. -/
theorem toRealSeq_mul_single (x : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (j k : ℤ) :
    lpOneAlg.toRealSeq (x * lpOneAlg.single j 1) k = lpOneAlg.toRealSeq x (k - j) := by
  rw [lpOneAlg.toRealSeq_mul_eq_finsum x _ k {j} fun i hi => by
    rw [lpOneAlg.toRealSeq_single, ite_eq_right (by simpa using hi)]]
  rw [Finset.sum_singleton, lpOneAlg.toRealSeq_single, ite_eq_left rfl, mul_one]

/-- **(T12, L002.)** Bands add under products: band `m` times band `n` has band `m + n`. -/
theorem band_mul (m n : ℕ) (x y : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (hx : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq x i = 0)
    (hy : ∀ i : ℤ, n < i.natAbs → lpOneAlg.toRealSeq y i = 0) :
    ∀ k : ℤ, m + n < k.natAbs → lpOneAlg.toRealSeq (x * y) k = 0 := by
  intro k hk
  rw [lpOneAlg.toRealSeq_mul_eq_finsum x y k (winZ n) fun i hi =>
    hy i (by rw [mem_winZ] at hi; omega)]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [mem_winZ] at hi
  rw [hx (k - i) (by omega), zero_mul]

/-- **(T13, L002.)** Bands scale under powers: band `N` gives band `n N` for the `n`-th power. -/
theorem band_pow (N : ℕ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν))
    (ha : ∀ i : ℤ, N < i.natAbs → lpOneAlg.toRealSeq a i = 0) :
    ∀ (n : ℕ) (i : ℤ), n * N < i.natAbs → lpOneAlg.toRealSeq (a ^ n) i = 0 := by
  intro n
  induction n with
  | zero => exact fun i hi => by rw [pow_zero]; exact band_one i (by simpa using hi)
  | succ n ih =>
    intro i hi
    rw [pow_succ]
    exact band_mul (n * N) N _ a ih ha i (by rwa [Nat.succ_mul] at hi)

end Complete

end RadiiPolynomial.Fourier
