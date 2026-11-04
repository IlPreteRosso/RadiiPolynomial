import RadiiPolynomial.Examples.Fourier.Exponential.Numbers
import RadiiPolynomial.Examples.Fourier.Exponential.Algebra
import RadiiPolynomial.Core.Theorem
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.FiniteBlockTransport
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The exponential Fourier consumer: the certificate on `ℓ¹_{6/5}`

The state space is the registered bilateral algebra `X = lpOneAlg ℤ (geomFiberZ ℂ ν)`, `ν = 6/5`
(`NormedCommRing`, `NormedAlgebra ℂ`, `NormOneClass`, `CompleteSpace` by instance search), and the
map is the family map `F̃(u) = −u + Λ(P_e u + a (e^(P_e u) − 1))` of `Algebra.lean` at `a = 51/50`.
On it:

* the approximate inverse `A = M_H − Q_H` is the finite matrix `lpOneAlg.finMatrixCLM` of the
  head data (`WeightedLp/Compatibility/FiniteBlockTransport`: no column bound) minus the
  library tail projection; the approximate derivative `A†` is `DF̃(ū)` with `e^ū` replaced by
  the finite Taylor approximation `Ē`;
* the four bounds: `Y₀ = ‖A F̄‖ + a ‖A Λ‖ δ` and `Z₁ = a ‖A Λ‖ δ` carry the enclosure radius
  `δ ≥ ‖e^ū − Ē‖` of the finite-Taylor contract (`Analysis/Norm/Exponential`:
  `norm_taylorTerm_sub_le`, `norm_exp_sub_sum_le`, `tsum_pow_div_factorial_tail_le`); `Z₀` is the
  head column sums of `I − A A†` (library `finsum_norm_le_of_cols`, `norm_headProj`) plus the tail
  `λ₁₁ (1 + a ‖Ē‖)` (`norm_tailProj_diagCLM_apply_le`); `Z₂ = a ‖A Λ‖ e` from the
  derivative-difference bound `norm_exp_sub_exp_le` (`‖ū‖ + r₁ ≤ 1`);
* injectivity of `A` from the library head-injectivity service
  `eq_zero_of_mem_of_norm_sub_comp_lt_one` on the finite-dimensional head range;
* the Core radii polynomial theorem `general_radii_polynomial_theorem_nondegenerate_local`, applied
  directly on `X` (real scalars by `restrictScalars`), at `r₀ = 10⁻⁵` and `r₁ = 1/100`;
* evenness and reality of the zero from the family symmetries and uniqueness.
-/

open scoped ComplexConjugate Nat

noncomputable section

namespace FourierExponential

open RadiiPolynomial lpOneAlg Numbers Metric

/-! ### A. The space and the data bridge -/

/-- The weight `ν = 6/5`. -/
def ν₆₅ : PosReal := ⟨6 / 5, by norm_num⟩

theorem coe_ν₆₅ : (ν₆₅ : ℝ) = 6 / 5 := rfl

instance fact_one_le_ν₆₅ : Fact (1 ≤ (ν₆₅ : ℝ)) := ⟨by rw [coe_ν₆₅]; norm_num⟩

/-- The state space `ℓ¹_{6/5}(ℤ; ℂ)`, the registered algebra. -/
abbrev X := lpOneAlg ℤ (geomFiberZ ℂ ν₆₅)

/-- The unit atom `e_k`. -/
abbrev e (k : ℤ) : X := single k (1 : ℂ)

/-- `Λ = diag(1/(1+k²))` on `X`. -/
local notation "Λ" => Family.Lam ν₆₅

/-- The reflection `(𝐑 x)_k = x_(−k)` on `X`. -/
local notation "𝐑" => Family.R ν₆₅

/-- The even part `P_e = (1 + 𝐑)/2` on `X`. -/
local notation "Pₑ" => Family.Pe ν₆₅

theorem weight_eq (k : ℤ) :
    FiberTrivialization.weight (E := geomFiberZ ℂ ν₆₅) k = ((nuQ ^ k.natAbs : ℚ) : ℝ) := by
  rw [geomFiberZ_weight, coe_ν₆₅, nuQ]; push_cast; ring

theorem qabs_eq (q : ℚ) : qabs q = |q| := by
  unfold qabs; split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.1 h)).symm

theorem norm_ratCast (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = ((qabs q : ℚ) : ℝ) := by
  rw [qabs_eq, Rat.cast_abs, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mem_idxH {k : ℤ} : k ∈ idxH ↔ -10 ≤ k ∧ k ≤ 10 := by
  simp only [idxH, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨(k + 10).toNat, by omega, by omega⟩

theorem mem_idxK {k : ℤ} : k ∈ idxK ↔ -12 ≤ k ∧ k ≤ 12 := by
  simp only [idxK, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨(k + 12).toNat, by omega, by omega⟩

theorem mem_idxUK {k : ℤ} : k ∈ idxUK ↔ -22 ≤ k ∧ k ≤ 22 := by
  simp only [idxUK, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨(k + 22).toNat, by omega, by omega⟩

theorem nodup_idxH : idxH.Nodup := by decide
theorem nodup_idxK : idxK.Nodup := by decide
theorem nodup_idxUK : idxUK.Nodup := by decide

/-- The head `H = {−10, …, 10}`. -/
abbrev H : Finset ℤ := idxH.toFinset

theorem mem_H {k : ℤ} : k ∈ H ↔ -10 ≤ k ∧ k ≤ 10 := by
  rw [List.mem_toFinset, mem_idxH]

theorem ubarQ_eq_zero {k : ℤ} (h : ¬(-10 ≤ k ∧ k ≤ 10)) : ubarQ k = 0 := by
  simp only [ubarQ, ite_eq_right h]

theorem PQ_eq_zero (n : ℕ) {k : ℤ} (h : ¬(-12 ≤ k ∧ k ≤ 12)) : PQ n k = 0 := by
  simp only [PQ, ite_eq_right h]

theorem EQ_eq_zero {k : ℤ} (h : ¬(-12 ≤ k ∧ k ≤ 12)) : EQ k = 0 := by
  simp only [EQ, PQ_eq_zero _ h]; simp

/-- The rational sum over a duplicate-free list is the finite sum over its set. -/
theorem cast_qsum {l : List ℤ} (hl : l.Nodup) (f : ℤ → ℚ) :
    ((qsum l f : ℚ) : ℝ) = ∑ k ∈ l.toFinset, ((f k : ℚ) : ℝ) := by
  rw [qsum, ← List.sum_toFinset _ hl, Rat.cast_sum]

theorem cast_qsum_ℂ {l : List ℤ} (hl : l.Nodup) (f : ℤ → ℚ) :
    ((qsum l f : ℚ) : ℂ) = ∑ k ∈ l.toFinset, ((f k : ℚ) : ℂ) := by
  rw [qsum, ← List.sum_toFinset _ hl, Rat.cast_sum]

/-- **The element with rational coefficients** `f` on the modes of `l`. -/
def fvec (f : ℤ → ℚ) (l : List ℤ) : X := ∑ k ∈ l.toFinset, single k ((f k : ℚ) : ℂ)

theorem toRealSeq_fvec (f : ℤ → ℚ) (l : List ℤ) (k : ℤ) :
    toRealSeq (fvec f l) k = if k ∈ l then ((f k : ℚ) : ℂ) else 0 := by
  rw [fvec, toRealSeq_finset_sum]
  simp only [toRealSeq_single]
  rw [Finset.sum_ite_eq]
  simp only [List.mem_toFinset]

/-- **The norm bridge**: an element with rational coefficients `f` on `l` and `0` off `l` has
norm `∑_(k ∈ l) |f k| ν^|k|`. -/
theorem norm_eq_qsum {x : X} {l : List ℤ} (hl : l.Nodup) {f : ℤ → ℚ}
    (hin : ∀ k ∈ l, toRealSeq x k = ((f k : ℚ) : ℂ)) (hout : ∀ k ∉ l, toRealSeq x k = 0) :
    ‖x‖ = ((qsum l fun k => qabs (f k) * nuQ ^ k.natAbs : ℚ) : ℝ) := by
  rw [norm_eq_tsum, tsum_eq_sum (s := l.toFinset) fun k hk => by
    rw [norm_eq_abs_toReal_mul_weight, hout k (by simpa using hk), norm_zero, zero_mul],
    cast_qsum hl]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [norm_eq_abs_toReal_mul_weight, hin k (by simpa using hk), norm_ratCast, weight_eq]
  push_cast; ring

/-- **The head-sum bridge**: the fibre norms over the head of an element whose head coefficients
are rational. -/
theorem sum_norm_apply_eq_qsum {x : X} {f : ℤ → ℚ}
    (hin : ∀ k ∈ idxH, toRealSeq x k = ((f k : ℚ) : ℂ)) :
    ∑ k ∈ H, ‖x k‖ = ((qsum idxH fun k => qabs (f k) * nuQ ^ k.natAbs : ℚ) : ℝ) := by
  rw [cast_qsum nodup_idxH]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [norm_eq_abs_toReal_mul_weight, hin k (by simpa using hk), norm_ratCast, weight_eq]
  push_cast; ring

/-! ### B. The centre, the Taylor terms and `Ē` -/

/-- The centre `ū`. -/
def ubar : X := fvec ubarQ idxH

/-- The rounded Taylor terms `P_n`. -/
def Pv (n : ℕ) : X := fvec (PQ n) idxK

/-- The enclosure centre `Ē = ∑_(n ≤ 12) P_n`. -/
def Ebar : X := fvec EQ idxK

theorem toRealSeq_ubar (k : ℤ) : toRealSeq ubar k = ((ubarQ k : ℚ) : ℂ) := by
  rw [ubar, toRealSeq_fvec]
  split_ifs with h
  · rfl
  · rw [ubarQ_eq_zero (fun hh => h (mem_idxH.2 hh)), Rat.cast_zero]

theorem toRealSeq_Pv (n : ℕ) (k : ℤ) : toRealSeq (Pv n) k = ((PQ n k : ℚ) : ℂ) := by
  rw [Pv, toRealSeq_fvec]
  split_ifs with h
  · rfl
  · rw [PQ_eq_zero n (fun hh => h (mem_idxK.2 hh)), Rat.cast_zero]

theorem toRealSeq_Ebar (k : ℤ) : toRealSeq Ebar k = ((EQ k : ℚ) : ℂ) := by
  rw [Ebar, toRealSeq_fvec]
  split_ifs with h
  · rfl
  · rw [EQ_eq_zero (fun hh => h (mem_idxK.2 hh)), Rat.cast_zero]

theorem Ebar_eq_sum : Ebar = ∑ n ∈ Finset.range 13, Pv n := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_finset_sum, toRealSeq_Ebar]
  simp only [toRealSeq_Pv, EQ]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Rat.cast_sum]

theorem Pv_zero : Pv 0 = 1 := by
  refine ext_toRealSeq (funext fun k => ?_)
  rw [toRealSeq_Pv, one_eq_single_zero, toRealSeq_single]
  by_cases hk : -12 ≤ k ∧ k ≤ 12
  · rw [check_P0 k (mem_idxK.2 hk), deltaQ]
    split_ifs <;> simp
  · rw [PQ_eq_zero 0 hk, ite_eq_right (by omega), Rat.cast_zero]

/-- `‖ū‖ ≤ m`. -/
theorem norm_ubar_le : ‖ubar‖ ≤ (mC : ℝ) := by
  rw [norm_eq_qsum nodup_idxH (f := ubarQ) (fun k _ => toRealSeq_ubar k) fun k hk => by
    rw [toRealSeq_ubar, ubarQ_eq_zero (fun hh => hk (mem_idxH.2 hh)), Rat.cast_zero]]
  exact_mod_cast check_normU

/-- `‖Ē‖ ≤ E`. -/
theorem norm_Ebar_le : ‖Ebar‖ ≤ (EC : ℝ) := by
  rw [norm_eq_qsum nodup_idxK (f := EQ) (fun k _ => toRealSeq_Ebar k) fun k hk => by
    rw [toRealSeq_Ebar, EQ_eq_zero (fun hh => hk (mem_idxK.2 hh)), Rat.cast_zero]]
  exact_mod_cast check_normE

/-- Convolution against a finitely supported element with rational coefficients. -/
theorem toRealSeq_mul_fvec (x : X) (f : ℤ → ℚ) (l : List ℤ) (k : ℤ) :
    toRealSeq (x * fvec f l) k = ∑ i ∈ l.toFinset, toRealSeq x (k - i) * ((f i : ℚ) : ℂ) := by
  rw [toRealSeq_mul_eq_finsum x (fvec f l) k l.toFinset fun i hi => by
    rw [toRealSeq_fvec, ite_eq_right (by simpa using hi)]]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [toRealSeq_fvec, ite_eq_left (by simpa using hi)]

theorem toRealSeq_mul_Pv (x : X) (n : ℕ) (k : ℤ) :
    toRealSeq (x * Pv n) k = ∑ i ∈ idxK.toFinset, toRealSeq x (k - i) * ((PQ n i : ℚ) : ℂ) :=
  toRealSeq_mul_fvec x (PQ n) idxK k

/-- The one-step Taylor defect element. -/
theorem norm_taylor_step_le (n : ℕ) (hn : n < 12) :
    ‖((n : ℂ) + 1)⁻¹ • (ubar * Pv n) - Pv (n + 1)‖ ≤ (rhoC n : ℝ) := by
  have hcoef : ∀ k, toRealSeq (((n : ℂ) + 1)⁻¹ • (ubar * Pv n) - Pv (n + 1)) k =
      ((tdefQ n k : ℚ) : ℂ) := fun k => by
    rw [toRealSeq_sub, Pi.sub_apply, toRealSeq_smul, Pi.smul_apply, smul_eq_mul,
      toRealSeq_mul_Pv, toRealSeq_Pv, tdefQ, convQ, Rat.cast_sub, Rat.cast_div,
      cast_qsum_ℂ nodup_idxK]
    simp only [toRealSeq_ubar]
    push_cast
    ring
  have hout : ∀ k ∉ idxUK, tdefQ n k = 0 := fun k hk => by
    rw [mem_idxUK] at hk
    rw [tdefQ, convQ, qsum, PQ_eq_zero _ (by omega), List.sum_eq_zero, zero_div, sub_zero]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
    rw [mem_idxK] at hi
    rw [ubarQ_eq_zero (by omega), zero_mul]
  rw [norm_eq_qsum nodup_idxUK (f := tdefQ n) (fun k _ => hcoef k) fun k hk => by
    rw [hcoef, hout k hk, Rat.cast_zero]]
  have h : rhoPartQ n ≤ rhoC n := by
    by_cases h6 : n < 6
    · exact check_rho_0 n (List.mem_range.2 h6)
    · exact check_rho_1 n (List.mem_map.2 ⟨n - 6, List.mem_range.2 (by omega), by omega⟩)
  exact_mod_cast h

/-! ### C. The operators at `ν = 6/5`: the symbol bridge, the centre is even and real -/

theorem lamQ_pos (k : ℤ) : 0 < lamQ k := by unfold lamQ; positivity

theorem lamQ_le_tail {k : ℤ} (hk : ¬(-10 ≤ k ∧ k ≤ 10)) : lamQ k ≤ 1 / 122 := by
  unfold lamQ
  have h : (11 : ℚ) ≤ |(k : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (show (11 : ℤ) ≤ |k| by rw [le_abs]; omega)
  have hsq : (121 : ℚ) ≤ (k : ℚ) ^ 2 := by rw [← sq_abs]; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The symbol is the rational mirror `lamQ`. -/
theorem lam_eq (k : ℤ) : Family.lam k = ((lamQ k : ℚ) : ℂ) := by
  rw [Family.lam, lamQ]; push_cast; rfl

theorem norm_lam (k : ℤ) : ‖Family.lam k‖ = ((lamQ k : ℚ) : ℝ) := by
  rw [lam_eq, norm_ratCast, qabs_eq, abs_of_pos (lamQ_pos k)]

theorem refl_ubar : 𝐑 ubar = ubar := ext_toRealSeq (funext fun k => by
  rw [toRealSeq_refl, toRealSeq_ubar, toRealSeq_ubar]
  by_cases hk : -10 ≤ k ∧ k ≤ 10
  · rw [check_even k (mem_idxH.2 hk)]
  · rw [ubarQ_eq_zero (by omega), ubarQ_eq_zero hk])

theorem Pe_ubar : Pₑ ubar = ubar := Family.Pe_of_refl ν₆₅ refl_ubar

theorem coeffConj_ubar : coeffConj ubar = ubar :=
  ext_toRealSeq (funext fun k => by rw [toRealSeq_coeffConj, toRealSeq_ubar, map_ratCast])

/-! ### D. The approximate inverse `A = M_H − Q_H` -/

theorem LC_nonneg : (0 : ℚ) ≤ LC := le_trans (by norm_num) check_L_tail

/-- **The head matrix** `M_H`, the transported finite matrix of the head data. -/
def Mop : X →L[ℂ] X := lpOneAlg.finMatrixCLM H fun i j => ((MQ i j : ℚ) : ℂ)

theorem toRealSeq_Mop (y : X) (k : ℤ) :
    toRealSeq (Mop y) k =
      if k ∈ idxH then ∑ j ∈ H, ((MQ k j : ℚ) : ℂ) * toRealSeq y j else 0 := by
  rw [Mop, toRealSeq_finMatrixCLM]
  simp only [List.mem_toFinset]

/-- **The approximate inverse** `A = M_H − Q_H` (head matrix, minus the identity on the tail). -/
def Aop : X →L[ℂ] X := Mop - tailProj (𝕜 := ℂ) H

theorem toRealSeq_Aop (y : X) (k : ℤ) :
    toRealSeq (Aop y) k =
      if k ∈ idxH then ∑ j ∈ H, ((MQ k j : ℚ) : ℂ) * toRealSeq y j else -toRealSeq y k := by
  rw [Aop, sub_apply, toRealSeq_sub, Pi.sub_apply, toRealSeq_Mop,
    toRealSeq_tailProj]
  by_cases hk : k ∈ idxH
  · rw [ite_eq_left hk, ite_eq_left (by simpa using hk), sub_zero, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right (by simpa using hk), zero_sub, ite_eq_right hk]

/-- `Q_H A = −Q_H`: on the tail, `A` is minus the identity. -/
theorem tailProj_Aop (y : X) : tailProj (𝕜 := ℂ) H (Aop y) = -tailProj (𝕜 := ℂ) H y :=
  ext_toRealSeq (funext fun k => by
    rw [toRealSeq_tailProj, toRealSeq_Aop, toRealSeq_neg, Pi.neg_apply, toRealSeq_tailProj]
    by_cases hk : k ∈ idxH
    · rw [ite_eq_left (by simpa using hk), ite_eq_left (by simpa using hk), neg_zero]
    · rw [ite_eq_right (by simpa using hk), ite_eq_right hk, ite_eq_right (by simpa using hk)])

/-- The head matrix on an atom: the `m`-th column of `M` on the head, `0` for `m ∉ H`. -/
theorem toRealSeq_Mop_single (m k : ℤ) :
    toRealSeq (Mop (e m)) k = if k ∈ idxH ∧ m ∈ idxH then ((MQ k m : ℚ) : ℂ) else 0 := by
  rw [toRealSeq_Mop]
  simp only [toRealSeq_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', List.mem_toFinset]
  split_ifs <;> simp_all

/-- **The `A Λ` bound** `‖A Λ w‖ ≤ L ‖w‖` (library column-norm bound `norm_le_of_cols`). -/
theorem norm_Aop_Lam_le (w : X) : ‖Aop (Λ w)‖ ≤ (LC : ℝ) * ‖w‖ := by
  refine norm_le_of_cols (Aop ∘L Λ) (fun m => ?_) w
  rw [ContinuousLinearMap.comp_apply, Family.Lam_single, mul_one, single_smul, map_smul, Aop,
    sub_apply, tailProj_single, norm_smul, norm_lam, weight_eq]
  by_cases hm : m ∈ idxH
  · rw [ite_eq_left (List.mem_toFinset.2 hm), sub_zero,
      norm_eq_qsum nodup_idxH (f := fun k => MQ k m)
        (fun k hk => by rw [toRealSeq_Mop_single, ite_eq_left ⟨hk, hm⟩])
        fun k hk => by rw [toRealSeq_Mop_single, ite_eq_right fun h => hk h.1]]
    have h := check_L_cols m hm
    rw [lColQ] at h
    exact_mod_cast h
  · have h0 : Mop (e m) = 0 := ext_toRealSeq (funext fun k => by
      rw [toRealSeq_Mop_single, ite_eq_right fun h => hm h.2, toRealSeq_zero, Pi.zero_apply])
    rw [ite_eq_right (fun h => hm (List.mem_toFinset.1 h)), h0, zero_sub, norm_neg, norm_single,
      norm_one, one_mul, weight_eq]
    have h1 := lamQ_le_tail (k := m) (fun hh => hm (mem_idxH.2 hh))
    have h2 : lamQ m * nuQ ^ m.natAbs ≤ LC * nuQ ^ m.natAbs :=
      mul_le_mul_of_nonneg_right (h1.trans check_L_tail) (pow_nonneg (by norm_num [nuQ]) _)
    exact_mod_cast h2

/-! ### E. The map, its derivative, the approximate derivative -/

/-- The parameter `a = 51/50` in `ℂ`. -/
def aC : ℂ := ((aQ : ℚ) : ℂ)

theorem norm_aC : ‖aC‖ = ((aQ : ℚ) : ℝ) := by
  rw [aC, norm_ratCast, qabs_eq, abs_of_pos (by norm_num [aQ])]

theorem conj_aC : conj aC = aC := by rw [aC, map_ratCast]

/-- **The symmetrized zero-finding map** `F̃(u) = −u + Λ(P_e u + a (e^(P_e u) − 1))` at
`ν = 6/5`, `a = 51/50` (the family map `Family.Ftil`). -/
def Ftil (u : X) : X := Family.Ftil ν₆₅ aC u

/-- The derivative `DF̃(u) = −1 + Λ (P_e + a e^(P_e u) P_e)`. -/
def DFtil (u : X) : X →L[ℂ] X := Family.DFtil ν₆₅ aC u

/-- The approximate derivative `A† = −1 + Λ (P_e + a Ē P_e)` (`e^ū` replaced by `Ē`). -/
def Adag : X →L[ℂ] X := -1 + Λ ∘L (Pₑ + aC • (mulLeftCLM (𝕜 := ℂ) Ebar ∘L Pₑ))

theorem Ftil_apply (u : X) : Ftil u = -u + Λ (Pₑ u + aC • (NormedSpace.exp (Pₑ u) - 1)) := rfl

theorem hasFDerivAt_Ftil (u : X) : HasFDerivAt Ftil (DFtil u) u :=
  Family.hasFDerivAt_Ftil ν₆₅ aC u

theorem Adag_apply (h : X) : Adag h = -h + Λ (Pₑ h + aC • (Ebar * Pₑ h)) := rfl

theorem DFtil_apply (u h : X) :
    DFtil u h = -h + Λ (Pₑ h + aC • (NormedSpace.exp (Pₑ u) * Pₑ h)) := rfl

/-! ### F. The enclosure of `e^ū` and the residual `Y₀` -/

/-- **The enclosure of the exponential of the centre**: `‖e^ū − Ē‖ ≤ δ` (the finite-Taylor
contract of `Analysis/Norm/Exponential` with the certified one-step defects). -/
theorem norm_exp_ubar_sub_Ebar : ‖NormedSpace.exp ubar - Ebar‖ ≤ (deltaC : ℝ) := by
  have hterm := NormHelpers.norm_taylorTerm_sub_le ℂ (x := ubar) (P := Pv) (m := (mC : ℝ))
    (ρ := fun n => (rhoC n : ℝ)) (ε := fun n => (epsQ n : ℝ)) (J := 12) norm_ubar_le Pv_zero
    (by simp [epsQ]) (fun n hn => norm_taylor_step_le n hn)
    (fun n _ => by rw [epsQ]; push_cast; rfl)
  have h := NormHelpers.norm_exp_sub_sum_le ℂ 12 norm_ubar_le hterm
  rw [← Ebar_eq_sum] at h
  have hm0 : (0 : ℝ) ≤ mC := by norm_num [mC]
  have ht := NormHelpers.tsum_pow_div_factorial_tail_le (m := (mC : ℝ)) 12 hm0 (by norm_num [mC])
  have htq : ((mC : ℝ)) ^ (12 + 1) / ((12 + 1)! : ℝ) * (((12 : ℕ) : ℝ) + 2) /
      (((12 : ℕ) : ℝ) + 2 - mC) = (tailQ : ℝ) := by
    rw [tailQ]; push_cast; norm_num [Nat.factorial]; ring
  have hsum : ∑ n ∈ Finset.range (12 + 1), (epsQ n : ℝ) =
      ((((List.range 13).map epsQ).sum : ℚ) : ℝ) := by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Rat.cast_sum]
  have hd : ((((List.range 13).map epsQ).sum : ℚ) : ℝ) + (tailQ : ℝ) ≤ (deltaC : ℝ) := by
    exact_mod_cast check_delta
  rw [hsum] at h
  rw [mul_div_assoc] at htq
  linarith

/-- The rational residual `F̄ = −ū + Λ(ū + a (Ē − 1))`. -/
def Fbar : X := -ubar + Λ (ubar + aC • (Ebar - 1))

theorem toRealSeq_Fbar (k : ℤ) : toRealSeq Fbar k = ((FbarQ k : ℚ) : ℂ) := by
  rw [Fbar, toRealSeq_add, Pi.add_apply, toRealSeq_neg, Pi.neg_apply, Family.toRealSeq_Lam,
    toRealSeq_add, Pi.add_apply, toRealSeq_smul, Pi.smul_apply, toRealSeq_sub, Pi.sub_apply,
    one_eq_single_zero, toRealSeq_single, toRealSeq_ubar, toRealSeq_Ebar, FbarQ, deltaQ, lam_eq,
    aC, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem FbarQ_eq_zero {k : ℤ} (hk : ¬(-12 ≤ k ∧ k ≤ 12)) : FbarQ k = 0 := by
  rw [FbarQ, ubarQ_eq_zero (by omega), EQ_eq_zero hk, deltaQ, ite_eq_right (by omega)]; ring

theorem Ftil_ubar : Ftil ubar = Fbar + aC • Λ (NormedSpace.exp ubar - Ebar) := by
  rw [Ftil_apply, Pe_ubar, Fbar, ← map_smul, add_assoc, ← map_add]
  congr 2
  rw [smul_sub, smul_sub, smul_sub]; abel

/-- **The `Y₀` bound** `‖A F̃(ū)‖ ≤ ‖A F̄‖ + a ‖A Λ‖ δ ≤ Y₀`. -/
theorem Y0_bound : ‖Aop (Ftil ubar)‖ ≤ (Y0c : ℝ) := by
  have hAF : ∀ k, toRealSeq (Aop Fbar) k = ((AFQ k : ℚ) : ℂ) := fun k => by
    rw [toRealSeq_Aop, AFQ]
    split_ifs with h1 h2 h2
    · rw [cast_qsum_ℂ nodup_idxH]
      exact Finset.sum_congr rfl fun j _ => by rw [toRealSeq_Fbar]; push_cast; ring
    · exact absurd (mem_idxH.1 h1) h2
    · exact absurd (mem_idxH.2 h2) h1
    · rw [toRealSeq_Fbar]; push_cast; ring
  have hAFout : ∀ k ∉ idxK, AFQ k = 0 := fun k hk => by
    rw [mem_idxK] at hk
    rw [AFQ, ite_eq_right (by omega), FbarQ_eq_zero hk, neg_zero]
  have h1 : ‖Aop Fbar‖ ≤ (YAC : ℝ) := by
    rw [norm_eq_qsum nodup_idxK (f := AFQ) (fun k _ => hAF k) fun k hk => by
      rw [hAF, hAFout k hk, Rat.cast_zero]]
    exact_mod_cast check_Y
  have h2 : ‖Aop (aC • Λ (NormedSpace.exp ubar - Ebar))‖ ≤ (aQ : ℝ) * (LC * deltaC) := by
    rw [map_smul, norm_smul, norm_aC]
    refine mul_le_mul_of_nonneg_left ((norm_Aop_Lam_le _).trans ?_) (by norm_num [aQ])
    exact mul_le_mul_of_nonneg_left norm_exp_ubar_sub_Ebar (by exact_mod_cast LC_nonneg)
  rw [Ftil_ubar, map_add]
  have h3 : (YAC : ℝ) + aQ * (LC * deltaC) ≤ Y0c := by
    have := check_Y0; rw [mul_assoc] at this; exact_mod_cast this
  linarith [norm_add_le (Aop Fbar) (Aop (aC • Λ (NormedSpace.exp ubar - Ebar)))]

/-! ### G. The `Z₀` bound: head columns plus the tail -/

theorem cast_deltaQ (m j : ℤ) : ((deltaQ m j : ℚ) : ℂ) = if j = m then 1 else 0 := by
  rw [deltaQ]; split_ifs with h1 h2 h2 <;> simp_all

theorem toRealSeq_Adag_single (m j : ℤ) : toRealSeq (Adag (e m)) j = ((adagQ m j : ℚ) : ℂ) := by
  rw [Adag_apply, Family.Pe_single, mul_smul_comm, mul_add]
  simp only [toRealSeq_add, toRealSeq_neg, toRealSeq_smul, Family.toRealSeq_Lam, Pi.add_apply,
    Pi.neg_apply, Pi.smul_apply, toRealSeq_mul_single, toRealSeq_Ebar, toRealSeq_single,
    smul_eq_mul]
  rw [adagQ]
  push_cast
  rw [cast_deltaQ, cast_deltaQ, lam_eq, aC, sub_neg_eq_add]
  split_ifs <;> ring

/-- The operator `T = I − A A†` whose norm is `Z₀`. -/
abbrev T : X →L[ℂ] X := ContinuousLinearMap.id ℂ X - Aop ∘L Adag

theorem toRealSeq_T_single (m k : ℤ) (hk : k ∈ idxH) :
    toRealSeq (T (e m)) k = ((TQ m k : ℚ) : ℂ) := by
  rw [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    toRealSeq_sub, Pi.sub_apply, toRealSeq_Aop, ite_eq_left hk, toRealSeq_single, TQ, Rat.cast_sub,
    cast_qsum_ℂ nodup_idxH, cast_deltaQ]
  simp only [toRealSeq_Adag_single, Rat.cast_mul]

theorem adagQ_eq_zero {m j : ℤ} (hm : ¬(-22 ≤ m ∧ m ≤ 22)) (hj : -10 ≤ j ∧ j ≤ 10) :
    adagQ m j = 0 := by
  rw [adagQ, deltaQ, deltaQ, ite_eq_right (by omega), ite_eq_right (by omega),
    EQ_eq_zero (by omega),
    EQ_eq_zero (by omega)]
  ring

theorem TQ_eq_zero {m k : ℤ} (hm : ¬(-22 ≤ m ∧ m ≤ 22)) (hk : -10 ≤ k ∧ k ≤ 10) :
    TQ m k = 0 := by
  rw [TQ, deltaQ, ite_eq_right (by omega), qsum, List.sum_eq_zero, sub_zero]
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hq
  rw [adagQ_eq_zero hm (mem_idxH.1 hj), mul_zero]

theorem nuQ_pow_nonneg (n : ℕ) : (0 : ℚ) ≤ nuQ ^ n := pow_nonneg (by norm_num [nuQ]) _

theorem ZHC_nonneg : (0 : ℚ) ≤ ZHC := by norm_num [ZHC]

/-- The head part of every column: `∑_(k ∈ H) |T_km| ν^|k| ≤ Z_H ν^|m|`. -/
theorem z0Col_le (m : ℤ) :
    ((qsum idxH fun k => qabs (TQ m k) * nuQ ^ k.natAbs : ℚ) : ℝ) ≤
      (ZHC : ℝ) * ((nuQ ^ m.natAbs : ℚ) : ℝ) := by
  by_cases hm : -22 ≤ m ∧ m ≤ 22
  · have h : z0ColQ m ≤ ZHC * nuQ ^ m.natAbs := by
      by_cases h0 : m ≤ -8
      · exact check_Z0_cols_0 m (List.mem_map.2 ⟨(m + 22).toNat, List.mem_range.2 (by omega),
          by omega⟩)
      · by_cases h1 : m ≤ 7
        · exact check_Z0_cols_1 m (List.mem_map.2 ⟨(m + 7).toNat, List.mem_range.2 (by omega),
            by omega⟩)
        · exact check_Z0_cols_2 m (List.mem_map.2 ⟨(m - 8).toNat, List.mem_range.2 (by omega),
            by omega⟩)
    exact_mod_cast h
  · have h0 : (qsum idxH fun k => qabs (TQ m k) * nuQ ^ k.natAbs) = 0 := by
      rw [qsum, List.sum_eq_zero]
      intro q hq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
      rw [TQ_eq_zero hm (mem_idxH.1 hk), qabs_eq, abs_zero, zero_mul]
    rw [h0, Rat.cast_zero]
    exact mul_nonneg (by exact_mod_cast ZHC_nonneg) (by exact_mod_cast nuQ_pow_nonneg _)

theorem head_col_le (m : ℤ) :
    ∑ k ∈ H, ‖(T (e m)) k‖ ≤ (ZHC : ℝ) * FiberTrivialization.weight (E := geomFiberZ ℂ ν₆₅) m := by
  rw [sum_norm_apply_eq_qsum (f := TQ m) fun k hk => toRealSeq_T_single m k hk, weight_eq]
  exact z0Col_le m

theorem norm_V_le (h : X) : ‖Pₑ h + aC • (Ebar * Pₑ h)‖ ≤ (1 + (aQ : ℝ) * EC) * ‖h‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_aC]
  have h1 := Family.norm_Pe_le ν₆₅ h
  have h2 : ‖Ebar * Pₑ h‖ ≤ (EC : ℝ) * ‖h‖ :=
    (norm_mul_le _ _).trans (mul_le_mul norm_Ebar_le h1 (norm_nonneg _) (by norm_num [EC]))
  have ha : (0 : ℝ) ≤ aQ := by norm_num [aQ]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

/-- The head and the tail parts add up: `P_H y + Q_H y = y` (`Q_H = 1 − P_H`). -/
theorem headProj_add_tailProj_apply (y : X) :
    headProj (𝕜 := ℂ) H y + tailProj (𝕜 := ℂ) H y = y := by
  rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, add_sub_cancel]

/-- **The `Z₀` bound** `‖I − A A†‖ ≤ Z_H + λ₁₁ (1 + a ‖Ē‖) ≤ Z₀`. -/
theorem Z0_bound : ‖ContinuousLinearMap.id ℂ X - Aop ∘L Adag‖ ≤ (Z0c : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num [Z0c]) fun h => ?_
  have hhead : ‖headProj (𝕜 := ℂ) H (T h)‖ ≤ (ZHC : ℝ) * ‖h‖ := by
    rw [norm_headProj]
    exact finsum_norm_le_of_cols T H id head_col_le h
  have htail : tailProj (𝕜 := ℂ) H (T h) =
      tailProj (𝕜 := ℂ) H (Λ (Pₑ h + aC • (Ebar * Pₑ h))) := by
    rw [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_sub, tailProj_Aop, Adag_apply, map_add, map_neg]
    abel
  have hlam : ∀ w : X, ‖tailProj (𝕜 := ℂ) H (Λ w)‖ ≤ (1 / 122 : ℝ) * ‖w‖ := fun w =>
    norm_tailProj_diagCLM_apply_le H Family.lam 1 Family.norm_lam_le (by norm_num)
      (fun k hk => by
        rw [norm_lam]
        exact (Rat.cast_le (K := ℝ).2 (lamQ_le_tail (fun hh => hk (mem_H.2 hh)))).trans_eq
          (by norm_num)) w
  have ht : ‖tailProj (𝕜 := ℂ) H (T h)‖ ≤ (1 / 122 : ℝ) * ((1 + (aQ : ℝ) * EC) * ‖h‖) := by
    rw [htail]
    exact (hlam _).trans (mul_le_mul_of_nonneg_left (norm_V_le h) (by norm_num))
  have hZ : (ZHC : ℝ) + 1 / 122 * (1 + (aQ : ℝ) * (EC : ℝ)) ≤ (Z0c : ℝ) := by
    have h := Rat.cast_le (K := ℝ).2 check_Z0
    push_cast at h
    linarith
  have hn := norm_nonneg h
  show ‖T h‖ ≤ _
  calc ‖T h‖ = ‖headProj (𝕜 := ℂ) H (T h) + tailProj (𝕜 := ℂ) H (T h)‖ := by
        rw [headProj_add_tailProj_apply]
    _ ≤ ‖headProj (𝕜 := ℂ) H (T h)‖ + ‖tailProj (𝕜 := ℂ) H (T h)‖ := norm_add_le _ _
    _ ≤ (ZHC : ℝ) * ‖h‖ + 1 / 122 * ((1 + (aQ : ℝ) * EC) * ‖h‖) := add_le_add hhead ht
    _ ≤ (Z0c : ℝ) * ‖h‖ := by nlinarith

/-! ### H. The `Z₁` and `Z₂` bounds -/

theorem norm_Aop_Lam_smul_mul_le (w h : X) :
    ‖Aop (Λ (aC • (w * Pₑ h)))‖ ≤ (aQ : ℝ) * LC * ‖w‖ * ‖h‖ := by
  refine (norm_Aop_Lam_le _).trans ?_
  rw [norm_smul, norm_aC]
  have hL : (0 : ℝ) ≤ LC := by exact_mod_cast LC_nonneg
  have ha : (0 : ℝ) ≤ aQ := by norm_num [aQ]
  have hm : ‖w * Pₑ h‖ ≤ ‖w‖ * ‖h‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (Family.norm_Pe_le ν₆₅ h) (norm_nonneg _))
  have := mul_le_mul_of_nonneg_left hm (mul_nonneg hL ha)
  nlinarith [this]

theorem DFtil_sub_DFtil_ubar (c h : X) :
    (DFtil c - DFtil ubar) h =
      Λ (aC • ((NormedSpace.exp (Pₑ c) - NormedSpace.exp ubar) * Pₑ h)) := by
  rw [sub_apply, DFtil_apply, DFtil_apply, Pe_ubar, sub_mul, smul_sub,
    map_sub, map_add, map_add, map_smul, map_smul]
  abel

theorem Adag_sub_DFtil_ubar (h : X) :
    (Adag - DFtil ubar) h = Λ (aC • ((Ebar - NormedSpace.exp ubar) * Pₑ h)) := by
  rw [sub_apply, Adag_apply, DFtil_apply, Pe_ubar, sub_mul, smul_sub,
    map_sub, map_add, map_add, map_smul, map_smul]
  abel

/-- **The `Z₁` bound** `‖A (A† − DF̃(ū))‖ ≤ a ‖A Λ‖ δ ≤ Z₁` (the enclosure error at the centre). -/
theorem Z1_bound : ‖Aop ∘L (Adag - DFtil ubar)‖ ≤ (Z1c : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num [Z1c]) fun h => ?_
  rw [ContinuousLinearMap.comp_apply, Adag_sub_DFtil_ubar]
  refine (norm_Aop_Lam_smul_mul_le _ _).trans ?_
  have hd : ‖Ebar - NormedSpace.exp ubar‖ ≤ (deltaC : ℝ) := by
    rw [norm_sub_rev]; exact norm_exp_ubar_sub_Ebar
  have hZ : (aQ : ℝ) * LC * deltaC ≤ Z1c := by exact_mod_cast check_Z1
  have hL : (0 : ℝ) ≤ (aQ : ℝ) * LC := mul_nonneg (by norm_num [aQ]) (by exact_mod_cast LC_nonneg)
  have := mul_le_mul_of_nonneg_left hd hL
  have hn := norm_nonneg h
  nlinarith

/-- **The `Z₂` bound** on `B̄(ū, r)`, `r ≤ r₁`: `‖A (DF̃(c) − DF̃(ū))‖ ≤ a ‖A Λ‖ e r ≤ Z₂ r`
(the derivative-difference bound `norm_exp_sub_exp_le`, `‖ū‖ + r ≤ 1`). -/
theorem Z2_bound {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ r1) {c : X} (hc : c ∈ closedBall ubar r) :
    ‖Aop ∘L (DFtil c - DFtil ubar)‖ ≤ (Z2c : ℝ) * r := by
  rw [mem_closedBall, dist_eq_norm] at hc
  have hPe : ‖Pₑ c - ubar‖ ≤ r := by
    rw [← Pe_ubar, ← map_sub]; exact (Family.norm_Pe_le ν₆₅ _).trans hc
  have hexp : ‖NormedSpace.exp (Pₑ c) - NormedSpace.exp ubar‖ ≤ Real.exp 1 * r := by
    refine (NormHelpers.norm_exp_sub_exp_le (c := ubar) hPe
      (by rw [sub_self, norm_zero]; exact hr0)).trans ?_
    have h1 : ‖ubar‖ + r ≤ 1 := by
      have := Rat.cast_le (K := ℝ).2 check_mr1
      push_cast at this
      linarith [norm_ubar_le]
    exact mul_le_mul (Real.exp_le_exp.2 h1) hPe (norm_nonneg _) (Real.exp_pos _).le
  have he : Real.exp 1 ≤ (eC : ℝ) := by
    have := Real.exp_one_lt_d9; rw [eC]; push_cast; linarith
  have hZ : (aQ : ℝ) * LC * eC ≤ Z2c := by exact_mod_cast check_Z2
  have hL : (0 : ℝ) ≤ (aQ : ℝ) * LC := mul_nonneg (by norm_num [aQ]) (by exact_mod_cast LC_nonneg)
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num [Z2c]) hr0) fun h => ?_
  rw [ContinuousLinearMap.comp_apply, DFtil_sub_DFtil_ubar]
  refine (norm_Aop_Lam_smul_mul_le _ _).trans ?_
  have h1 : (aQ : ℝ) * LC * ‖NormedSpace.exp (Pₑ c) - NormedSpace.exp ubar‖ ≤
      (aQ : ℝ) * LC * (eC * r) :=
    mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_right he hr0)) hL
  have hn := norm_nonneg h
  have h2 : (aQ : ℝ) * LC * (eC * r) ≤ Z2c * r := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hZ hr0
  nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) hn]

/-! ### I. Injectivity of `A` (the library head-injectivity service) -/

theorem Mop_headProj (y : X) : Mop (headProj (𝕜 := ℂ) H y) = Mop y :=
  ext_toRealSeq (funext fun k => by
    rw [toRealSeq_Mop, toRealSeq_Mop]
    split_ifs
    · exact Finset.sum_congr rfl fun j hj => by rw [toRealSeq_headProj, ite_eq_left hj]
    · rfl)

/-- The head defect `P_H − M_H (P_H A† P_H)` has norm at most `Z_H` (the head columns of `Z₀`). -/
theorem norm_head_defect_le :
    ‖headProj (𝕜 := ℂ) H - Mop ∘L (headProj (𝕜 := ℂ) H ∘L Adag ∘L headProj (𝕜 := ℂ) H)‖ ≤
      (ZHC : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by exact_mod_cast ZHC_nonneg) fun x => ?_
  refine norm_le_of_cols _ (fun m => ?_) x
  rw [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Mop_headProj, weight_eq,
    headProj_single]
  by_cases hm : m ∈ idxH
  · rw [ite_eq_left (List.mem_toFinset.2 hm)]
    have hcoef : ∀ k, toRealSeq (e m - Mop (Adag (e m))) k =
        if k ∈ idxH then ((TQ m k : ℚ) : ℂ) else 0 := fun k => by
      split_ifs with hk
      · rw [← toRealSeq_T_single m k hk, sub_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, toRealSeq_sub,
          toRealSeq_sub, Pi.sub_apply, Pi.sub_apply, toRealSeq_Mop, toRealSeq_Aop, ite_eq_left hk,
          ite_eq_left hk]
      · rw [toRealSeq_sub, Pi.sub_apply, toRealSeq_Mop, ite_eq_right hk, toRealSeq_single,
          ite_eq_right (fun h => hk (by rw [h]; exact hm)), sub_zero]
    rw [norm_eq_qsum nodup_idxH (f := TQ m) (fun k hk => by rw [hcoef, ite_eq_left hk])
      fun k hk => by rw [hcoef, ite_eq_right hk]]
    exact z0Col_le m
  · rw [ite_eq_right (fun h => hm (List.mem_toFinset.1 h))]
    simp only [map_zero, sub_zero, norm_zero]
    exact mul_nonneg (by exact_mod_cast ZHC_nonneg) (by exact_mod_cast nuQ_pow_nonneg _)

/-- **`A` is injective**: `A x = 0` kills the tail and leaves `M_H x = 0` on the finite head;
the head defect `‖P_H − M_H K‖ ≤ Z_H < 1` and the library service
`eq_zero_of_mem_of_norm_sub_comp_lt_one` give `x = 0`. -/
theorem Aop_injective : Function.Injective Aop := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have htail : ∀ k ∉ idxH, toRealSeq x k = 0 := fun k hk => by
    have h := congrArg (fun y => toRealSeq y k) hx
    simp only [toRealSeq_Aop, ite_eq_right hk, toRealSeq_zero, Pi.zero_apply] at h
    exact neg_eq_zero.1 h
  have hPx : headProj (𝕜 := ℂ) H x = x := ext_toRealSeq (funext fun k => by
    rw [toRealSeq_headProj]
    split_ifs with hk
    · rfl
    · rw [htail k (by simpa using hk)])
  have hQx : tailProj (𝕜 := ℂ) H x = 0 := by
    rw [tailProj_eq_one_sub, sub_apply, one_apply_eq_self, hPx, sub_self]
  have hMx : Mop x = 0 := by
    have h : Aop x = Mop x - tailProj (𝕜 := ℂ) H x := rfl
    rw [hQx, sub_zero] at h
    rw [← h, hx]
  have hlt : ‖headProj (𝕜 := ℂ) H - Mop ∘L (headProj (𝕜 := ℂ) H ∘L Adag ∘L
      headProj (𝕜 := ℂ) H)‖ < 1 :=
    norm_head_defect_le.trans_lt (by exact_mod_cast check_ZH)
  exact WeightedLp.eq_zero_of_mem_of_norm_sub_comp_lt_one
    (LinearMap.range (headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν₆₅) H).toLinearMap)
    (fun v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact DFunLike.congr_fun (isIdempotentElem_headProj (𝕜 := ℂ) (G := geomFiberZ ℂ ν₆₅) H).eq w)
    (fun v _ => ⟨Adag (headProj (𝕜 := ℂ) H v), rfl⟩) hlt ⟨x, hPx⟩ hMx

/-! ### J. The Core radii polynomial theorem on `ℓ¹_{6/5}` -/

/-- **The radii polynomial theorem applied on `ℓ¹_{6/5}`** at a radius `0 < r ≤ r₁` with
`p(r) < 0`: the Core local nondegenerate face with the four bounds of this file. -/
theorem exponential_radii {r : ℝ} (hr0 : 0 < r) (hr : r ≤ r1)
    (hrad : (Z2c : ℝ) * r ^ 2 - (1 - Z0c - Z1c) * r + Y0c < 0) :
    ∃ u ∈ ball ubar r, Ftil u = 0 ∧ ((DFtil u).restrictScalars ℝ).IsInvertible ∧
      ∀ v ∈ closedBall ubar r, Ftil v = 0 → v = u :=
  general_radii_polynomial_theorem_nondegenerate_local (E := X) (F := X) (f := Ftil)
    (Df := fun x => (DFtil x).restrictScalars ℝ) (xBar := ubar)
    (A := Aop.restrictScalars ℝ) (A_dagger := Adag.restrictScalars ℝ)
    (Y₀ := Y0c) (Z₀ := Z0c) (Z₁ := Z1c) (Z₂ := fun _ => (Z2c : ℝ)) (r₀ := r) hr0 Y0_bound
    (by
      change ‖(ContinuousLinearMap.id ℂ X - Aop ∘L Adag).restrictScalars ℝ‖ ≤ _
      rw [ContinuousLinearMap.norm_restrictScalars]; exact Z0_bound)
    (by
      change ‖(Aop ∘L (Adag - DFtil ubar)).restrictScalars ℝ‖ ≤ _
      rw [ContinuousLinearMap.norm_restrictScalars]; exact Z1_bound)
    (fun c hc => by
      change ‖(Aop ∘L (DFtil c - DFtil ubar)).restrictScalars ℝ‖ ≤ _
      rw [ContinuousLinearMap.norm_restrictScalars]; exact Z2_bound hr0.le hr hc)
    (fun x _ => ((hasFDerivAt_Ftil x).restrictScalars ℝ).hasFDerivWithinAt)
    (by unfold generalRadiiPolynomial; exact hrad) Aop_injective

theorem r0_le_r1 : (r0 : ℝ) ≤ r1 := by norm_num [r0, r1]

/-- **The enclosure**: the zero lies in the open ball of radius `r₀`, its derivative is
invertible, and it is the only zero in the closed ball of radius `r₁ = 1/100`. -/
theorem exponential_l1_enclosure : ∃ u ∈ ball ubar (r0 : ℝ), Ftil u = 0 ∧
    ((DFtil u).restrictScalars ℝ).IsInvertible ∧
      ∀ v ∈ closedBall ubar (r1 : ℝ), Ftil v = 0 → v = u := by
  obtain ⟨u₀, hu₀, hF₀, hinv, -⟩ :=
    exponential_radii (r := r0) (by norm_num [r0]) r0_le_r1 (by exact_mod_cast check_radii_r0)
  obtain ⟨u₁, -, -, -, huniq⟩ :=
    exponential_radii (r := r1) (by norm_num [r1]) le_rfl (by exact_mod_cast check_radii_r1)
  have h01 : u₀ = u₁ := huniq u₀ (closedBall_subset_closedBall r0_le_r1
    (ball_subset_closedBall hu₀)) hF₀
  refine ⟨u₀, hu₀, hF₀, hinv, fun v hv hFv => ?_⟩
  rw [h01]; exact huniq v hv hFv

/-! ### K. Symmetry: evenness and reality of the zero -/

/-- **The certified coefficient zero**: in the open ball of radius `r₀`, even, real, and the only
zero of `F̃` in the closed ball of radius `r₁`. -/
theorem exponential_l1_solution : ∃ u ∈ ball ubar (r0 : ℝ), Ftil u = 0 ∧ 𝐑 u = u ∧
    coeffConj u = u ∧ ∀ v ∈ closedBall ubar (r1 : ℝ), Ftil v = 0 → v = u := by
  obtain ⟨u, hu, hFu, -, huniq⟩ := exponential_l1_enclosure
  refine ⟨u, hu, hFu, Family.refl_of_Ftil_eq_zero ν₆₅ aC hFu, ?_, huniq⟩
  refine huniq _ ?_ ?_
  · rw [mem_closedBall, dist_eq_norm, ← coeffConj_ubar, ← map_sub, LinearIsometryEquiv.norm_map,
      ← dist_eq_norm]
    exact closedBall_subset_closedBall r0_le_r1 (ball_subset_closedBall hu)
  · change Family.Ftil ν₆₅ aC (coeffConj u) = 0
    rw [Family.Ftil_coeffConj ν₆₅ aC conj_aC, show Family.Ftil ν₆₅ aC u = 0 from hFu, map_zero]

end FourierExponential

end
