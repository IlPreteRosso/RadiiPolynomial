import RadiiPolynomial.Applications.Fourier.Semilinear

/-!
# The first-order family `λ_k = i k` as a specialization of the semilinear consumer

The symbol `ikSymbol k = i k` on the bilateral geometric carrier `lpOneAlg ℤ (geomFiberZ ℂ ν)`:
head bound `N` (`headBound_ikSymbol`), the tail inverse `tailInv N ikSymbol` with
`‖tailInv N ikSymbol k‖ = 1_{|k| > N} / |k| ≤ 1/(N + 1)` (the first-tail bound) and two-ray
monotone moduli from `max (N + 1) 1` (`K₀ = 1`), the tail column in closed form for every
coefficient, the exact window `N + m + 1` of `‖DG(ā) − B₀‖` and the Γ majorant with
`C = 1/(N + 1)`.

The first-tail bound `1/(N + 1)`, `K₀ = 1` and the window `N + m + 1` belong to this family only:
the general-symbol statements of `Applications/Fourier/Semilinear.lean` carry the window
`B + max (N + 1) K₀` and the uniform bound `C` of the tail diagonal. The Γ majorant is not the
exact window norm.
-/

noncomputable section

namespace RadiiPolynomial.Fourier.Semilinear

/-- The first-order Fourier symbol `k ↦ i k`. -/
def ikSymbol (k : ℤ) : ℂ :=
    Complex.I * (k : ℂ)

section

/-- The first-order symbol has magnitude `|k|`. -/
theorem norm_ikSymbol (k : ℤ) :
    ‖ikSymbol k‖ = (k.natAbs : ℝ) := by
  rw [ikSymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]

/-- The first-order symbol vanishes only at `k = 0`. -/
theorem ikSymbol_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ikSymbol k ≠ 0 := by
  intro h
  have hn := norm_ikSymbol k
  rw [h, norm_zero] at hn
  exact hk (Int.natAbs_eq_zero.mp (by exact_mod_cast hn.symm))

/-- The head bound of the first-order symbol is `N`. -/
theorem headBound_ikSymbol (N : ℕ) :
    headBound N ikSymbol = (N : ℝ) := by
  unfold headBound
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k hk => ?_
    rw [norm_ikSymbol]
    exact_mod_cast mem_winZ.mp hk
  · have h := Finset.le_sup' (fun k => ‖ikSymbol k‖)
      (mem_winZ.mpr (show ((N : ℤ)).natAbs ≤ N from (Int.natAbs_natCast N).le))
    rw [norm_ikSymbol] at h
    exact (congrArg (fun n : ℕ => (n : ℝ)) (Int.natAbs_natCast N)).symm.trans_le h

/-- The tail inverse of the first-order symbol has modulus `1_{|k| > N} / |k|`. -/
theorem norm_tailInv_ikSymbol (N : ℕ) (k : ℤ) :
    ‖tailInv N ikSymbol k‖ = if k.natAbs ≤ N then 0 else (k.natAbs : ℝ)⁻¹ := by
  unfold tailInv
  by_cases hk : k.natAbs ≤ N
  · rw [ite_eq_left (mem_winZ.mpr hk), ite_eq_left hk, norm_zero]
  · rw [ite_eq_right (fun h => hk (mem_winZ.mp h)), ite_eq_right hk, norm_inv, norm_ikSymbol]

/-- The first-tail bound `‖tailInv N ikSymbol k‖ ≤ 1/(N + 1)` (first-order family only). -/
theorem norm_tailInv_ikSymbol_le (N : ℕ) :
    ∀ k, ‖tailInv N ikSymbol k‖ ≤ 1 / ((N : ℝ) + 1) := by
  intro k
  rw [norm_tailInv_ikSymbol]
  split_ifs with hk
  · positivity
  · rw [one_div]
    apply inv_anti₀ (by positivity)
    exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hk))

/-- The first-order tail inverse is two-ray nonincreasing from `max (N + 1) 1` (`K₀ = 1`). -/
theorem tailInv_ikSymbol_hmono (N : ℕ) :
    ∀ n : ℕ, max (N + 1) 1 ≤ n →
      ‖tailInv N ikSymbol ((n : ℤ) + 1)‖ ≤ ‖tailInv N ikSymbol (n : ℤ)‖ ∧
        ‖tailInv N ikSymbol (-((n : ℤ) + 1))‖ ≤ ‖tailInv N ikSymbol (-(n : ℤ))‖ := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  simp only [norm_tailInv_ikSymbol, Int.natAbs_neg, Int.natAbs_natCast,
    show ((n : ℤ) + 1).natAbs = n + 1 by omega,
    ite_eq_right (show ¬ n ≤ N by omega), ite_eq_right (show ¬ n + 1 ≤ N by omega)]
  constructor <;> apply inv_anti₀ hn0 <;> exact_mod_cast (Nat.le_succ n)

/-- The first-order tail inverse inverts the symbol off the head window. -/
theorem tailInv_ikSymbol_mul_self (N : ℕ) :
    ∀ k : ℤ, N < k.natAbs → tailInv N ikSymbol k * ikSymbol k = 1 :=
  tailInv_mul_self N ikSymbol fun k hk =>
    ikSymbol_ne_zero fun h0 => by rw [h0, Int.natAbs_zero] at hk; exact Nat.not_lt_zero N hk

end

section
variable {ν : PosReal}

/-- The first-order tail column in closed form, for every coefficient `c`. -/
theorem tailCol_tailInv_ikSymbol_coeff (N m : ℕ) (c : lpOneAlg ℤ (geomFiberZ ℂ ν)) (j : ℤ) :
    tailCol m (tailInv N ikSymbol) c j =
      (∑ i ∈ winZ m, (if N < (j + i).natAbs then ((j + i).natAbs : ℝ)⁻¹ else 0) *
        ‖lpOneAlg.toRealSeq c i‖ * (ν : ℝ) ^ (j + i).natAbs) / (ν : ℝ) ^ j.natAbs := by
  simp only [tailCol, norm_tailInv_ikSymbol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hk : (j + i).natAbs ≤ N
  · rw [ite_eq_left hk, ite_eq_right (show ¬ N < (j + i).natAbs by omega)]
  · rw [ite_eq_right hk, ite_eq_left (lt_of_not_ge hk)]

end

section
variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The exact window `N + m + 1` of the first-order family (`K₀ = 1`), explicit form, under `P M = M`
and the band `m` of `β`. -/
theorem norm_fderiv_sub_modelDeriv_eq_sup'_first (N m : ℕ) (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : lpOneAlg ℤ (geomFiberZ ℂ ν)) (hPM : (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L M = M)
    (hβ : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq (beta τ Φ abar) i = 0) :
    ‖(fderiv ℂ (precondMap N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) τ Φ : lpOneAlg ℤ (geomFiberZ ℂ ν) → lpOneAlg ℤ (geomFiberZ ℂ ν)) abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) - (modelDeriv N M ikSymbol τ Φ abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))‖ =
      (winZ (N + m + 1)).sup' (winZ_nonempty _)
        (fun j => headCol N M (beta τ Φ abar) j + tailCol m (tailInv N ikSymbol) (beta τ Φ abar) j) := by
  rw [norm_fderiv_sub_modelDeriv_eq_sup'_explicit N m 1 M ikSymbol (tailInv N ikSymbol)
    (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) τ Φ abar hβ hPM (tailInv_head_zero N ikSymbol)
    (tailInv_ikSymbol_hmono N), window_eq_of_le N m 1 (by omega)]

/-- The Γ majorant of the first-order family, with the first-tail bound `C = 1/(N + 1)`. Not the exact
window norm. -/
theorem norm_fderiv_sub_modelDeriv_le_gamma_first (N : ℕ) (M : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) (τ : ℂ)
    (Φ : MvPolynomial (Fin 1) ℂ) (abar : lpOneAlg ℤ (geomFiberZ ℂ ν)) :
    ‖(fderiv ℂ (precondMap N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1)) (norm_tailInv_ikSymbol_le N) τ Φ : lpOneAlg ℤ (geomFiberZ ℂ ν) → lpOneAlg ℤ (geomFiberZ ℂ ν)) abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) - (modelDeriv N M ikSymbol τ Φ abar : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))‖ ≤
      (‖M ∘L (lpOneAlg.headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν) (winZ N) : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν)) ∘L (gammaDiag N : lpOneAlg ℤ (geomFiberZ ℂ ν) →L[ℂ] lpOneAlg ℤ (geomFiberZ ℂ ν))‖ + 1 / ((N : ℝ) + 1)) * ‖(beta τ Φ abar : lpOneAlg ℤ (geomFiberZ ℂ ν))‖ :=
  norm_fderiv_sub_modelDeriv_le_gamma N M ikSymbol (tailInv N ikSymbol) (1 / ((N : ℝ) + 1))
    (norm_tailInv_ikSymbol_le N) τ Φ abar

end

end RadiiPolynomial.Fourier.Semilinear

end
