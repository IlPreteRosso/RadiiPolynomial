import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The one-sided cosine carrier: symmetric extension, restriction, reflected product

The book's cosine problems (Chapter 13, (13.11)–(13.12)) store an even Fourier series
`u = a₀ + 2 Σ_{k≥1} a_k cos(k L y)` by its one-sided coefficients `(a_k)_{k≥0}` and measure
them in the UNNORMALIZED one-sided norm `‖a‖ = Σ_{k≥0} |a_k| νᵏ`, the norm of `l1Weighted ν`.
The product is the extended (reflected) convolution: extend `a`, `b` evenly to `ℤ`, convolve
in the bilateral algebra `l1Chebyshev ν`, keep the nonnegative modes. This file realizes that
carrier interface on the library's spaces.

This is not the library's normalized storage. The bordered carrier `l1Bordered ν`
(`Chebyshev/Bordered.lean`) weights mode `n ≥ 1` by `2νⁿ`; `nonnegRestrict` maps the
flip-fixed subalgebra `symmetricSubalgebra ν` of `l1Chebyshev ν`, where the product is
submultiplicative, isometrically into it. Here the weights are `νⁿ`, the doubling of the
nonzero modes is not counted, and the product pays a constant: `‖a ⋆ b‖ ≤ C₂ ‖a‖ ‖b‖`
with `C₂ = 1 + 2ν⁻²`, which is exact (for `1 ≤ ν`, `C₂ ≤ 3`, below the constant `4` printed
in (13.12)).

Main declarations:
* `l1Chebyshev.natEmbed` (declared in `Chebyshev/Symmetrize.lean`) — the ℕ-supported embedding
  `ℓ¹_ν(ℕ) → ℓ¹_ν(ℤ)`, an isometry.
* `OneSided.symExt` — the symmetric extension `(E a)_k = a_{|k|}`, defined as
  `symmetrize_CLM ∘L natEmbed`, with `‖E a‖ ≤ 2‖a‖` inherited from `symmetrize_CLM_norm_le`.
* `OneSided.restr` — restriction to the nonnegative modes, defined as
  `borderedToWeighted ∘L nonnegRestrictCLM ν`, with the sharp bound `‖restr x‖ ≤ ‖x‖`
  (`norm_restr_le`, proved directly; the composite's inherited bound is `2`), and the section
  identities `restr ∘ E = id`, `E ∘ restr = id` on symmetric elements.
* `OneSided.cosMul` — the reflected product `a ⋆ b = restr (E a · E b)` as a continuous
  bilinear map; commutative, associative, with unit the zero atom `e₀`.
* `OneSided.cosMul₃` — the trilinear map `(a, b, c) ↦ (a ⋆ b) ⋆ c`.
* `OneSided.opNorm_cosMul_eq : ‖cosMul‖ = C₂` and `OneSided.opNorm_cosMul₃_eq :
  ‖cosMul₃‖ = C₃` with `C₃ = max(1 + 3t, 1 + 2t + 2t²)`, `t = ν⁻²`; the upper bounds come from
  atom bounds through the curried column principle (`lpOneAlg.opNorm_le_of_cols₂/₃`), the lower
  bounds from the atoms `(1, 1)`, `(1, 1, 1)` and `(1, 1, 2)`.

Not a normed ring. The product `⋆` is a continuous algebra multiplication with constant `C₂`,
NOT a `NormedRing` multiplication: `‖e₁ ⋆ e₁‖ = ν² + 2 > ν² = ‖e₁‖²`
(`norm_cosMul_single_self`). No `Mul` instance is declared on `l1Weighted ν` for it; the
product `*` of `l1Weighted ν` remains the Taylor (Cauchy) product.

Hypotheses on `ν`. The embedding, the symmetric extension and the restriction exist for every
`ν : PosReal`. The hypothesis `1 ≤ ν` enters only with the bilateral multiplication (it is the
`Fact` that makes `l1Chebyshev ν` a Banach algebra): at `symExt_mem_symmetricSubalgebra` and
in the product section. The constants are stated for every `ν`, with `1 ≤ ν` as an explicit
hypothesis where it is used (`t_le_one`, `C₂_le_three`, `C₃_le_five`, and the private real
estimates behind the trilinear atom bound).

Instance path. With the pinned Mathlib, `Norm` on the three-level type of `cosMul₃` does not
synthesize at the default `maxSynthPendingDepth` (Mathlib itself builds with 3). The two
statements that mention `‖cosMul₃‖` (`opNorm_cosMul₃_le`, `opNorm_cosMul₃_eq`) are therefore
declared under `set_option maxSynthPendingDepth 2 in`, and a consumer who writes `‖cosMul₃‖`
must repeat exactly that option at its own declaration. No shortcut instance and no
operator-norm alias is exported.

Scope. Everything is parameterized by `ν` and by arbitrary coefficients; no example data and
no numerical values of the constants appear. The consumers are the Chapter-13-type cosine
problems; their cube-shaped faces (such as `‖restr (E a ^ 3)‖ ≤ C₃ ‖a‖³`) follow from
`norm_cosMul₃_le` and belong with those consumers. Nothing here concerns the book's printed
constants `Z^(2)`, `Z^(3)`.

Placement. Namespace `RadiiPolynomial.l1Chebyshev.OneSided`, so that `restr`, `t`, `C₂`, `C₃`
do not become ambient names; the ℕ-supported embedding `l1Chebyshev.natEmbed` is declared with
`symmetrize` (`Chebyshev/Symmetrize.lean`).
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

namespace OneSided

variable {ν : PosReal}

/-! ### One-sided atoms -/

/-- Coefficients of a one-sided atom. -/
private theorem toSeq_lpSingle (n : ℕ) (x : ℝ) (m : ℕ) :
    l1Weighted.toSeq (lpOneAlg.single n x : l1Weighted ν) m = if m = n then x else 0 := by
  show lpOneAlg.toRealSeq (lpOneAlg.single n x : l1Weighted ν) m = _
  exact lpOneAlg.toRealSeq_single n x m

/-- The one-sided norm of an atom: `‖single n x‖ = |x| νⁿ`. -/
private theorem norm_lpSingle (n : ℕ) (x : ℝ) :
    ‖(lpOneAlg.single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [← l1Weighted.single_eq_lpOneAlg_single, l1Weighted.norm_single]

/-! ### The symmetric extension -/

/-- **The symmetric extension** `E : ℓ¹_ν(ℕ) → ℓ¹_ν(ℤ)`, `(E a)_k = a_{|k|}`: the ℕ-supported
embedding followed by the library's symmetrization, `symmetrize_CLM ∘L natEmbed`. Its bound
`‖E a‖ ≤ 2‖a‖` is inherited from `symmetrize_CLM_norm_le` and `norm_natEmbed`. -/
def symExt : l1Weighted ν →L[ℝ] l1Chebyshev ν := symmetrize_CLM ∘L natEmbed

/-- The symmetric extension is the symmetrization of the ℕ-supported embedding. -/
theorem symExt_apply (a : l1Weighted ν) : symExt a = symmetrize (natEmbed a) := rfl

/-- Coefficients of the symmetric extension: `(E a)_k = a_{|k|}`. -/
@[simp] theorem symExt_toSeq (a : l1Weighted ν) (k : ℤ) :
    toSeq (symExt a) k = l1Weighted.toSeq a k.natAbs := by
  rw [symExt_apply, symmetrize_toSeq, natEmbed_toSeq_natCast]

/-- `‖E a‖ ≤ 2‖a‖`, from `symmetrize_CLM_norm_le` and the isometry `norm_natEmbed`. -/
theorem norm_symExt_le (a : l1Weighted ν) : ‖symExt a‖ ≤ 2 * ‖a‖ := by
  rw [← norm_natEmbed a]
  exact symmetrize_CLM.le_of_opNorm_le symmetrize_CLM_norm_le (natEmbed a)

/-- `‖E‖ ≤ 2`. -/
theorem opNorm_symExt_le : ‖(symExt : l1Weighted ν →L[ℝ] l1Chebyshev ν)‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two norm_symExt_le

/-- The symmetric extension is symmetric. -/
theorem isSymmetric_symExt (a : l1Weighted ν) : (symExt a).IsSymmetric :=
  symmetrize_isSymmetric _

/-- For `1 ≤ ν`, the symmetric extension lands in the flip-fixed Chebyshev algebra. -/
theorem symExt_mem_symmetricSubalgebra [Fact (1 ≤ (ν : ℝ))] (a : l1Weighted ν) :
    symExt a ∈ symmetricSubalgebra ν :=
  mem_symmetricSubalgebra.mpr (isSymmetric_symExt a)

/-- The zero atom extends to the bilateral unit. -/
theorem symExt_single_zero : symExt (lpOneAlg.single 0 1 : l1Weighted ν) = 1 := by
  rw [lpOneAlg.one_eq_single_zero]
  exact lpOneAlg.ext_toRealSeq (funext fun k => by
    show toSeq _ k = toSeq _ k
    rw [symExt_toSeq, toSeq_lpSingle, toSeq_single]
    simp only [Int.natAbs_eq_zero])

/-- A positive atom extends to the two bilateral atoms at `±i`. -/
theorem symExt_single (i : ℕ) (hi : 0 < i) :
    symExt (lpOneAlg.single i 1 : l1Weighted ν) = single (i : ℤ) 1 + single (-(i : ℤ)) 1 :=
  lpOneAlg.ext_toRealSeq (funext fun k => by
    show toSeq _ k = toSeq _ k
    rw [symExt_toSeq, toSeq_lpSingle, toSeq_add, toSeq_single, toSeq_single]
    split_ifs <;> (try norm_num) <;> omega)

/-! ### From the bordered carrier to the one-sided carrier -/

/-- The one-sided fiber is dominated by the bordered fiber (`pow_le_borderedWeight`). -/
private theorem fiber_bordered_le (a : l1Bordered ν) (n : ℕ) :
    |lpOneAlg.toRealSeq a n| * (ν : ℝ) ^ n ≤ ‖a n‖ := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight a n]
  simp only [WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν n) (abs_nonneg _)

/-- The coefficients of a bordered element have finite one-sided norm. -/
private theorem borderedToWeighted_mem (a : l1Bordered ν) :
    l1Weighted.Mem ν (fun n => lpOneAlg.toRealSeq a n) := by
  rw [l1Weighted.mem_iff]
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    (fiber_bordered_le a) (lpOneAlg.summable_norm a)

/-- The coefficient identity from the bordered to the one-sided carrier, as an element. -/
private def borderedToWeightedFun (a : l1Bordered ν) : l1Weighted ν :=
  l1Weighted.mk (fun n => lpOneAlg.toRealSeq a n) (borderedToWeighted_mem a)

/-- `borderedToWeightedFun` does not increase the norm. -/
private theorem norm_borderedToWeightedFun_le (a : l1Bordered ν) :
    ‖borderedToWeightedFun a‖ ≤ ‖a‖ := by
  rw [l1Weighted.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  exact (l1Weighted.summable_weighted _).tsum_le_tsum (fiber_bordered_le a)
    (lpOneAlg.summable_norm a)

/-- The identity on coefficients from the bordered carrier `l1Bordered ν` (weights `1`,
`2νⁿ`) to the one-sided carrier `l1Weighted ν` (weights `νⁿ`); norm at most `1` by
`pow_le_borderedWeight`. -/
def borderedToWeighted : l1Bordered ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := borderedToWeightedFun
      map_add' := fun a b => l1Weighted.ext fun n => by
        show lpOneAlg.toRealSeq (a + b) n = lpOneAlg.toRealSeq a n + lpOneAlg.toRealSeq b n
        exact congr_fun (lpOneAlg.toRealSeq_add a b) n
      map_smul' := fun r a => l1Weighted.ext fun n => by
        show lpOneAlg.toRealSeq (r • a) n = r * lpOneAlg.toRealSeq a n
        exact congr_fun (lpOneAlg.toRealSeq_smul r a) n }
    1 (fun a => by rw [one_mul]; exact norm_borderedToWeightedFun_le a)

/-- Coefficients of `borderedToWeighted`: the identity. This is the explicit-rewrite form in
`l1Weighted.toSeq`; it is not a simp rule, because `l1Weighted.toSeq_apply` rewrites its
left-hand side first. The simp rule is `borderedToWeighted_apply`. -/
theorem borderedToWeighted_toSeq (a : l1Bordered ν) (n : ℕ) :
    l1Weighted.toSeq (borderedToWeighted a) n = lpOneAlg.toRealSeq a n := rfl

/-- Coefficients of `borderedToWeighted`, the computation rule for the coefficient arrow
(normalized form; the structural API): the simp rule, stated in the simp-normal form that
`l1Weighted.toSeq_apply` produces. -/
@[simp] theorem borderedToWeighted_apply (a : l1Bordered ν) (n : ℕ) :
    ((borderedToWeighted a).toLp n : ℝ) = lpOneAlg.toRealSeq a n := by
  simpa only [l1Weighted.toSeq_apply] using borderedToWeighted_toSeq a n

/-- `‖borderedToWeighted a‖ ≤ ‖a‖`. -/
theorem norm_borderedToWeighted_le (a : l1Bordered ν) : ‖borderedToWeighted a‖ ≤ ‖a‖ :=
  norm_borderedToWeightedFun_le a

/-! ### Restriction to the nonnegative modes -/

/-- **Restriction to the nonnegative modes**, `ℓ¹_ν(ℤ) → ℓ¹_ν(ℕ)`, `(restr x)_n = x_n`: the
library's `nonnegRestrictCLM` into the bordered carrier followed by `borderedToWeighted`. The
composite's inherited bound is `2`; the sharp bound `‖restr x‖ ≤ ‖x‖` is `norm_restr_le`. -/
def restr : l1Chebyshev ν →L[ℝ] l1Weighted ν := borderedToWeighted ∘L nonnegRestrictCLM ν

/-- Coefficients of the restriction. This is the explicit-rewrite form in `l1Weighted.toSeq`;
it is not a simp rule, because `l1Weighted.toSeq_apply` rewrites its left-hand side first. The
simp rule is `restr_apply`. -/
theorem restr_toSeq (x : l1Chebyshev ν) (n : ℕ) :
    l1Weighted.toSeq (restr x) n = toSeq x n := by
  show lpOneAlg.toRealSeq (nonnegRestrict x) n = _
  rw [nonnegRestrict_toSeq]
  rfl

/-- Coefficients of the restriction, the computation rule for the coefficient arrow
(normalized form; the structural API): the simp rule, stated in the simp-normal form that
`l1Weighted.toSeq_apply` produces. -/
@[simp] theorem restr_apply (x : l1Chebyshev ν) (n : ℕ) :
    ((restr x).toLp n : ℝ) = toSeq x n := by
  simpa only [l1Weighted.toSeq_apply] using restr_toSeq x n

/-- The one-sided norm of the restriction is the sum of the nonnegative-mode fiber norms. -/
theorem norm_restr_eq_tsum (x : l1Chebyshev ν) : ‖restr x‖ = ∑' n : ℕ, ‖x (n : ℤ)‖ := by
  rw [l1Weighted.norm_eq_tsum]
  exact tsum_congr fun n => by rw [restr_toSeq, norm_fiber_natCast]

/-- `‖restr x‖ ≤ ‖x‖`, directly from `norm_restr_eq_tsum` (the nonnegative modes are a
sub-sum of the bilateral norm). -/
theorem norm_restr_le (x : l1Chebyshev ν) : ‖restr x‖ ≤ ‖x‖ := by
  rw [norm_restr_eq_tsum, lpOneAlg.norm_eq_tsum]
  exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm x) (fun _ => norm_nonneg _)
    Nat.cast_injective

/-- `‖restr‖ ≤ 1`. -/
theorem opNorm_restr_le : ‖(restr : l1Chebyshev ν →L[ℝ] l1Weighted ν)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => (norm_restr_le x).trans_eq
    (one_mul _).symm

/-- `restr ∘ E = id`. -/
theorem restr_symExt (a : l1Weighted ν) : restr (symExt a) = a :=
  l1Weighted.ext fun n => by rw [restr_toSeq, symExt_toSeq, Int.natAbs_natCast]

/-- `E ∘ restr = id` on symmetric elements. -/
theorem symExt_restr {x : l1Chebyshev ν} (hx : x.IsSymmetric) : symExt (restr x) = x :=
  lpOneAlg.ext_toRealSeq (funext fun k => by
    show toSeq _ k = toSeq _ k
    rw [symExt_toSeq, restr_toSeq]
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · rw [show ((k.natAbs : ℕ) : ℤ) = -k by omega]
      exact hx k)

/-- A nonnegative bilateral atom restricts to the one-sided atom. -/
theorem restr_single_natCast (n : ℕ) (x : ℝ) :
    restr (single (ν := ν) (n : ℤ) x) = l1Weighted.single n x :=
  l1Weighted.ext fun m => by
    rw [restr_toSeq, toSeq_single, l1Weighted.single_toSeq]
    simp only [Nat.cast_inj]

/-- A negative bilateral atom restricts to zero. -/
theorem restr_single_negSucc (n : ℕ) (x : ℝ) :
    restr (single (ν := ν) (Int.negSucc n) x) = 0 :=
  l1Weighted.ext fun m => by
    rw [restr_toSeq, toSeq_single, l1Weighted.zero_toSeq, ite_eq_right (by omega)]

/-- A bilateral atom restricts to the one-sided atom at `m.toNat`, or to `0` if `m < 0`. -/
theorem restr_single_int (m : ℤ) (x : ℝ) :
    restr (single (ν := ν) m x) = if 0 ≤ m then l1Weighted.single m.toNat x else 0 := by
  rcases m with n | n
  · rw [Int.ofNat_eq_natCast, restr_single_natCast, ite_eq_left (by omega), Int.toNat_natCast]
  · rw [restr_single_negSucc, ite_eq_right (by omega)]

/-- The one-sided norm of a restricted bilateral unit atom: `ν^m` if `0 ≤ m`, else `0`. -/
theorem norm_restr_single (m : ℤ) :
    ‖restr (single (ν := ν) m 1)‖ = if 0 ≤ m then (ν : ℝ) ^ m.toNat else 0 := by
  rw [restr_single_int]
  split_ifs
  · rw [l1Weighted.norm_single, abs_one, one_mul]
  · exact norm_zero

/-! ### The constants -/

/-- `t = ν⁻²`, the parameter of the constants `OneSided.C₂` and `OneSided.C₃`. -/
def t (ν : PosReal) : ℝ := ((ν : ℝ) ^ 2)⁻¹

/-- The bilinear constant `C₂ = 1 + 2t = 1 + 2ν⁻²` of the reflected product on the one-sided
norm `Σ_{k≥0} |a_k| νᵏ` (`opNorm_cosMul_eq`). -/
def C₂ (ν : PosReal) : ℝ := 1 + 2 * t ν

/-- The trilinear constant `C₃ = max(1 + 3t, 1 + 2t + 2t²)` of the iterated reflected product
on the one-sided norm (`opNorm_cosMul₃_eq`). -/
def C₃ (ν : PosReal) : ℝ := max (1 + 3 * t ν) (1 + 2 * t ν + 2 * (t ν) ^ 2)

/-- `0 < t`. -/
theorem t_pos (ν : PosReal) : 0 < t ν := inv_pos.mpr (pow_pos ν.2 2)

/-- `t ≤ 1` for `1 ≤ ν`. -/
theorem t_le_one (hν : 1 ≤ (ν : ℝ)) : t ν ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ hν)

/-- `0 ≤ C₂`. -/
theorem C₂_nonneg (ν : PosReal) : 0 ≤ C₂ ν := by
  have := t_pos ν; unfold C₂; linarith

/-- `1 ≤ C₂`. -/
theorem one_le_C₂ (ν : PosReal) : 1 ≤ C₂ ν := by
  have := t_pos ν; unfold C₂; linarith

/-- `C₂ ≤ 3` for `1 ≤ ν`. -/
theorem C₂_le_three (hν : 1 ≤ (ν : ℝ)) : C₂ ν ≤ 3 := by
  have := t_le_one hν; unfold C₂; linarith

/-- `C₂ ≤ C₃`. -/
theorem C₂_le_C₃ (ν : PosReal) : C₂ ν ≤ C₃ ν := by
  have := t_pos ν; unfold C₂ C₃; exact le_max_of_le_left (by linarith)

/-- `0 ≤ C₃`. -/
theorem C₃_nonneg (ν : PosReal) : 0 ≤ C₃ ν := (C₂_nonneg ν).trans (C₂_le_C₃ ν)

/-- `C₃ ≤ 5` for `1 ≤ ν`. -/
theorem C₃_le_five (hν : 1 ≤ (ν : ℝ)) : C₃ ν ≤ 5 := by
  have h0 := t_pos ν
  have h1 := t_le_one hν
  unfold C₃
  exact max_le (by linarith) (by nlinarith)

/-- The crossover: `C₃ = 1 + 3t` iff `t ≤ 1/2`. -/
theorem C₃_eq_left_iff : C₃ ν = 1 + 3 * t ν ↔ t ν ≤ 1 / 2 := by
  have ht := t_pos ν
  unfold C₃
  rw [max_eq_left_iff]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The crossover in `ν`: `t ≤ 1/2` iff `2 ≤ ν²`. -/
theorem t_le_half_iff : t ν ≤ 1 / 2 ↔ 2 ≤ (ν : ℝ) ^ 2 := by
  unfold t
  have h := inv_le_comm₀ (pow_pos ν.2 2) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h
  exact h

/-! ### Real helpers (private) -/

/-- `posPow ν m = ν^m` for `m ≥ 0` and `0` for `m < 0`: the one-sided norm of the restricted
bilateral unit atom at `m`. -/
private def posPow (ν : PosReal) (m : ℤ) : ℝ := if 0 ≤ m then (ν : ℝ) ^ m.toNat else 0

/-- `norm_restr_single` in `posPow` form. -/
private theorem norm_restr_single_eq_posPow (m : ℤ) :
    ‖restr (single (ν := ν) m 1)‖ = posPow ν m :=
  norm_restr_single m

/-- `posPow ν m = 0` for `m < 0`. -/
private theorem posPow_of_neg {m : ℤ} (h : m < 0) : posPow ν m = 0 := by
  unfold posPow; rw [ite_eq_right (by omega)]

/-- `posPow ν m ≤ νˢ` for `m ≤ s` (`1 ≤ ν`). -/
private theorem posPow_le (hν : 1 ≤ (ν : ℝ)) {m : ℤ} {s : ℕ} (h : m ≤ s) :
    posPow ν m ≤ (ν : ℝ) ^ s := by
  unfold posPow; split_ifs
  · exact pow_le_pow_right₀ hν (by omega)
  · exact pow_nonneg ν.2.le _

/-- `νᵉ ≤ t νˢ` for `e + 2 ≤ s` (`1 ≤ ν`). -/
private theorem pow_le_t_mul (hν : 1 ≤ (ν : ℝ)) {e s : ℕ} (h : e + 2 ≤ s) :
    (ν : ℝ) ^ e ≤ t ν * (ν : ℝ) ^ s := by
  rw [t, inv_mul_eq_div]
  refine (le_div_iff₀ (pow_pos ν.2 2)).mpr ?_
  exact (le_of_eq (pow_add (ν : ℝ) e 2).symm).trans (pow_le_pow_right₀ hν h)

/-- `νᵉ ≤ t² νˢ` for `e + 4 ≤ s` (`1 ≤ ν`). -/
private theorem pow_le_t_sq_mul (hν : 1 ≤ (ν : ℝ)) {e s : ℕ} (h : e + 4 ≤ s) :
    (ν : ℝ) ^ e ≤ t ν ^ 2 * (ν : ℝ) ^ s := by
  rw [t, inv_pow, inv_mul_eq_div, ← pow_mul]
  refine (le_div_iff₀ (pow_pos ν.2 4)).mpr ?_
  exact (le_of_eq (pow_add (ν : ℝ) e 4).symm).trans (pow_le_pow_right₀ hν h)

/-- `posPow ν m ≤ t νˢ` for `m < 0` or `m + 2 ≤ s` (`1 ≤ ν`). -/
private theorem posPow_le_t (hν : 1 ≤ (ν : ℝ)) {m : ℤ} {s : ℕ} (h : m < 0 ∨ m + 2 ≤ s) :
    posPow ν m ≤ t ν * (ν : ℝ) ^ s := by
  unfold posPow; split_ifs with hm
  · exact pow_le_t_mul hν (by omega)
  · exact mul_nonneg (t_pos ν).le (pow_nonneg ν.2.le _)

/-- `posPow ν m ≤ t² νˢ` for `m < 0` or `m + 4 ≤ s` (`1 ≤ ν`). -/
private theorem posPow_le_t_sq (hν : 1 ≤ (ν : ℝ)) {m : ℤ} {s : ℕ} (h : m < 0 ∨ m + 4 ≤ s) :
    posPow ν m ≤ t ν ^ 2 * (ν : ℝ) ^ s := by
  unfold posPow; split_ifs with hm
  · exact pow_le_t_sq_mul hν (by omega)
  · exact mul_nonneg (pow_nonneg (t_pos ν).le 2) (pow_nonneg ν.2.le _)

/-- The real core of the trilinear atom bound: for positive `i, j, k`, `s = i + j + k` and
`1 ≤ ν`, the eight restricted modes `±i ± j ± k` have total one-sided weight at most
`C₃ ν · νˢ` (case table in `norm_cosMul₃_single_le`). -/
private theorem eight_terms_le (hν : 1 ≤ (ν : ℝ)) (i j k : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hk : 0 < k) :
    posPow ν ((i : ℤ) + j + k) + posPow ν ((i : ℤ) + j - k) + posPow ν ((i : ℤ) - j + k)
      + posPow ν ((i : ℤ) - j - k) + posPow ν (-(i : ℤ) + j + k) + posPow ν (-(i : ℤ) + j - k)
      + posPow ν (-(i : ℤ) - j + k) + posPow ν (-(i : ℤ) - j - k)
      ≤ C₃ ν * ((ν : ℝ) ^ i * (ν : ℝ) ^ j * (ν : ℝ) ^ k) := by
  have hs : (ν : ℝ) ^ i * (ν : ℝ) ^ j * (ν : ℝ) ^ k = (ν : ℝ) ^ (i + j + k) := by
    rw [← pow_add, ← pow_add]
  rw [hs]
  have hp : 0 ≤ (ν : ℝ) ^ (i + j + k) := pow_nonneg ν.2.le _
  have ht := (t_pos ν).le
  have hL : (1 + 3 * t ν) * (ν : ℝ) ^ (i + j + k) ≤ C₃ ν * (ν : ℝ) ^ (i + j + k) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  have hR : (1 + 2 * t ν + 2 * t ν ^ 2) * (ν : ℝ) ^ (i + j + k)
      ≤ C₃ ν * (ν : ℝ) ^ (i + j + k) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hp
  have e1 : posPow ν ((i : ℤ) + j + k) ≤ (ν : ℝ) ^ (i + j + k) := posPow_le hν (by omega)
  have e8 : posPow ν (-(i : ℤ) - j - k) = 0 := posPow_of_neg (by omega)
  by_cases hI : i + j + k ≤ 2 * i
  · have e2 : posPow ν ((i : ℤ) + j - k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e3 : posPow ν ((i : ℤ) - j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e5 : posPow ν (-(i : ℤ) + j + k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e4 : posPow ν ((i : ℤ) - j - k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e6 : posPow ν (-(i : ℤ) + j - k) = 0 := posPow_of_neg (by omega)
    have e7 : posPow ν (-(i : ℤ) - j + k) = 0 := posPow_of_neg (by omega)
    linarith
  by_cases hJ : i + j + k ≤ 2 * j
  · have e2 : posPow ν ((i : ℤ) + j - k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e5 : posPow ν (-(i : ℤ) + j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e3 : posPow ν ((i : ℤ) - j + k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e6 : posPow ν (-(i : ℤ) + j - k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e4 : posPow ν ((i : ℤ) - j - k) = 0 := posPow_of_neg (by omega)
    have e7 : posPow ν (-(i : ℤ) - j + k) = 0 := posPow_of_neg (by omega)
    linarith
  by_cases hK : i + j + k ≤ 2 * k
  · have e3 : posPow ν ((i : ℤ) - j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e5 : posPow ν (-(i : ℤ) + j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e2 : posPow ν ((i : ℤ) + j - k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e7 : posPow ν (-(i : ℤ) - j + k) ≤ t ν ^ 2 * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t_sq hν (by omega)
    have e4 : posPow ν ((i : ℤ) - j - k) = 0 := posPow_of_neg (by omega)
    have e6 : posPow ν (-(i : ℤ) + j - k) = 0 := posPow_of_neg (by omega)
    linarith
  · have e2 : posPow ν ((i : ℤ) + j - k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e3 : posPow ν ((i : ℤ) - j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e5 : posPow ν (-(i : ℤ) + j + k) ≤ t ν * (ν : ℝ) ^ (i + j + k) :=
      posPow_le_t hν (by omega)
    have e4 : posPow ν ((i : ℤ) - j - k) = 0 := posPow_of_neg (by omega)
    have e6 : posPow ν (-(i : ℤ) + j - k) = 0 := posPow_of_neg (by omega)
    have e7 : posPow ν (-(i : ℤ) - j + k) = 0 := posPow_of_neg (by omega)
    linarith

/-- Triangle inequality through `restr`. -/
private theorem norm_restr_add_le_of {x y : l1Chebyshev ν} {a b : ℝ} (hx : ‖restr x‖ ≤ a)
    (hy : ‖restr y‖ ≤ b) : ‖restr (x + y)‖ ≤ a + b := by
  rw [map_add]; exact (norm_add_le _ _).trans (add_le_add hx hy)

/-- The one-sided norm of a finitely supported element as a finite sum. -/
private theorem norm_eq_sum_of_support (x : l1Weighted ν) (s : Finset ℕ)
    (h : ∀ n ∉ s, l1Weighted.toSeq x n = 0) :
    ‖x‖ = ∑ n ∈ s, |l1Weighted.toSeq x n| * (ν : ℝ) ^ n := by
  rw [l1Weighted.norm_eq_tsum]
  exact tsum_eq_sum fun n hn => by rw [h n hn, abs_zero, zero_mul]

/-! ### The reflected product -/

section Product

variable [Fact (1 ≤ (ν : ℝ))]

/-- **The reflected product** `a ⋆ b = restr (E a · E b)` on the one-sided carrier, as a
continuous bilinear map: the bilateral multiplication `ContinuousLinearMap.mul` of
`l1Chebyshev ν`, precomposed with `symExt` in both slots and postcomposed with `restr`. It is
NOT the Taylor product `*` of `l1Weighted ν`. -/
def cosMul : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν :=
  ContinuousLinearMap.compL ℝ (l1Weighted ν) (l1Chebyshev ν) (l1Weighted ν) restr ∘L
    (ContinuousLinearMap.mul ℝ (l1Chebyshev ν)).bilinearComp symExt symExt

/-- The reflected product is the restricted bilateral product of the symmetric extensions. -/
theorem cosMul_apply (a b : l1Weighted ν) : cosMul a b = restr (symExt a * symExt b) := rfl

/-- Coefficients of the reflected product: the book's extended convolution (Chapter 13,
between (13.11) and (13.12)), `(a ⋆ b)_k = Σ_{j ∈ ℤ} a_{|k−j|} b_{|j|}` for `k ≥ 0`, in the
library's convolution order `∑' j, x (k - j) * y j`. -/
theorem cosMul_toSeq (a b : l1Weighted ν) (k : ℕ) :
    l1Weighted.toSeq (cosMul a b) k
      = ∑' j : ℤ, l1Weighted.toSeq a (k - j).natAbs * l1Weighted.toSeq b j.natAbs := by
  rw [cosMul_apply, restr_toSeq, toSeq_mul_tsum]
  exact tsum_congr fun j => by rw [symExt_toSeq, symExt_toSeq]

/-- The reflected product is commutative. -/
theorem cosMul_comm (a b : l1Weighted ν) : cosMul a b = cosMul b a := by
  rw [cosMul_apply, cosMul_apply, mul_comm]

/-- The zero atom is a left unit of the reflected product. -/
theorem cosMul_one_left (b : l1Weighted ν) : cosMul (lpOneAlg.single 0 1) b = b := by
  rw [cosMul_apply, symExt_single_zero, one_mul, restr_symExt]

/-- The zero atom is a right unit of the reflected product. -/
theorem cosMul_one_right (a : l1Weighted ν) : cosMul a (lpOneAlg.single 0 1) = a := by
  rw [cosMul_comm, cosMul_one_left]

/-- The iterated reflected product is the restricted triple bilateral product. -/
theorem cosMul_cosMul (a b c : l1Weighted ν) :
    cosMul (cosMul a b) c = restr (symExt a * symExt b * symExt c) := by
  rw [cosMul_apply, cosMul_apply,
    symExt_restr ((isSymmetric_symExt a).mul (isSymmetric_symExt b))]

/-- The reflected product is associative. -/
theorem cosMul_assoc (a b c : l1Weighted ν) :
    cosMul (cosMul a b) c = cosMul a (cosMul b c) := by
  rw [cosMul_cosMul, cosMul_apply a, cosMul_apply b,
    symExt_restr ((isSymmetric_symExt b).mul (isSymmetric_symExt c)), mul_assoc]

/-- The trilinear map `(a, b, c) ↦ (a ⋆ b) ⋆ c`. -/
def cosMul₃ : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν :=
  (ContinuousLinearMap.compL ℝ (l1Weighted ν) (l1Weighted ν)
    (l1Weighted ν →L[ℝ] l1Weighted ν) cosMul).comp cosMul

/-- `cosMul₃ a b c = (a ⋆ b) ⋆ c`. -/
theorem cosMul₃_apply (a b c : l1Weighted ν) : cosMul₃ a b c = cosMul (cosMul a b) c := rfl

/-- `cosMul₃ a b c` is the restricted triple bilateral product. -/
theorem cosMul₃_eq (a b c : l1Weighted ν) :
    cosMul₃ a b c = restr (symExt a * symExt b * symExt c) := by
  rw [cosMul₃_apply, cosMul_cosMul]

/-! ### Bilinear atoms and the constant `C₂` -/

/-- The product of two positive atoms: the four bilateral modes `±i ± j`, restricted. -/
theorem cosMul_single_single (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    cosMul (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single j 1)
      = restr (single ((i : ℤ) + j) 1 + single ((i : ℤ) - j) 1
          + single (-(i : ℤ) + j) 1 + single (-(i : ℤ) - j) 1) := by
  rw [cosMul_apply, symExt_single i hi, symExt_single j hj]
  congr 1
  simp only [add_mul, mul_add, lpOneAlg.single_mul_single, mul_one, sub_eq_add_neg]
  abel

/-- The bilinear atom bound: `‖eᵢ ⋆ eⱼ‖ ≤ C₂ νⁱ νʲ`. -/
theorem norm_cosMul_single_single_le (i j : ℕ) :
    ‖cosMul (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single j 1)‖
      ≤ C₂ ν * ((ν : ℝ) ^ i * (ν : ℝ) ^ j) := by
  have hν : 1 ≤ (ν : ℝ) := Fact.out
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [cosMul_one_left, norm_lpSingle, abs_one, one_mul, pow_zero, one_mul]
    exact le_mul_of_one_le_left (pow_nonneg ν.2.le _) (one_le_C₂ ν)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [cosMul_one_right, norm_lpSingle, abs_one, one_mul, pow_zero, mul_one]
    exact le_mul_of_one_le_left (pow_nonneg ν.2.le _) (one_le_C₂ ν)
  rw [cosMul_single_single i j hi hj]
  refine (norm_restr_add_le_of (norm_restr_add_le_of (norm_restr_add_le_of
    (norm_restr_single_eq_posPow _).le (norm_restr_single_eq_posPow _).le)
    (norm_restr_single_eq_posPow _).le) (norm_restr_single_eq_posPow _).le).trans ?_
  rw [← pow_add]
  have h1 : posPow ν ((i : ℤ) + j) ≤ (ν : ℝ) ^ (i + j) := posPow_le hν (by omega)
  have h2 : posPow ν ((i : ℤ) - j) ≤ t ν * (ν : ℝ) ^ (i + j) := posPow_le_t hν (by omega)
  have h3 : posPow ν (-(i : ℤ) + j) ≤ t ν * (ν : ℝ) ^ (i + j) := posPow_le_t hν (by omega)
  have h4 : posPow ν (-(i : ℤ) - j) = 0 := posPow_of_neg (by omega)
  unfold C₂
  linarith

/-- `‖a ⋆ b‖ ≤ C₂ ‖a‖ ‖b‖`, from the atom bound by `lpOneAlg.norm_le_of_cols₂`. -/
theorem norm_cosMul_le (a b : l1Weighted ν) : ‖cosMul a b‖ ≤ C₂ ν * ‖a‖ * ‖b‖ :=
  lpOneAlg.norm_le_of_cols₂ cosMul (fun i j => by
    rw [WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight, mul_assoc]
    exact norm_cosMul_single_single_le i j) a b

/-- `‖⋆‖ ≤ C₂`. -/
theorem opNorm_cosMul_le : ‖(cosMul : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν)‖
    ≤ C₂ ν :=
  lpOneAlg.opNorm_le_of_cols₂ cosMul (C₂_nonneg ν) (fun i j => by
    rw [WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight, mul_assoc]
    exact norm_cosMul_single_single_le i j)

/-- `eᵢ ⋆ eᵢ = e_{2i} + 2 e₀` for `i ≥ 1`. -/
theorem cosMul_single_self (i : ℕ) (hi : 0 < i) :
    cosMul (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single i 1)
      = l1Weighted.single (2 * i) 1 + (2 : ℝ) • l1Weighted.single 0 1 := by
  rw [cosMul_single_single i i hi hi, map_add, map_add, map_add, restr_single_int,
    restr_single_int, restr_single_int, restr_single_int,
    ite_eq_left (show (0 : ℤ) ≤ (i : ℤ) + i by omega), ite_eq_left (show (0 : ℤ) ≤ (i : ℤ) - i by omega),
    ite_eq_left (show (0 : ℤ) ≤ -(i : ℤ) + i by omega),
    ite_eq_right (show ¬ (0 : ℤ) ≤ -(i : ℤ) - i by omega),
    add_zero, show ((i : ℤ) + i).toNat = 2 * i by omega, show ((i : ℤ) - i).toNat = 0 by omega,
    show (-(i : ℤ) + i).toNat = 0 by omega, add_assoc, two_smul]

/-- `‖eᵢ ⋆ eᵢ‖ = ν^{2i} + 2` for `i ≥ 1`: the ratio to `νⁱ νⁱ` is `1 + 2tⁱ ≤ C₂` (equality at
`i = 1`); at `ν < 1` (`t > 1`) the same formula is unbounded in `i`, which is why the product
needs `1 ≤ ν`; it exceeds `1`, so `⋆` is not a `NormedRing` multiplication. -/
theorem norm_cosMul_single_self (i : ℕ) (hi : 0 < i) :
    ‖cosMul (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single i 1)‖
      = (ν : ℝ) ^ (2 * i) + 2 := by
  have h2i : 2 * i ≠ 0 := by omega
  rw [cosMul_single_self i hi, norm_eq_sum_of_support _ {0, 2 * i} (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [l1Weighted.add_toSeq, l1Weighted.smul_toSeq, l1Weighted.single_toSeq,
      l1Weighted.single_toSeq, ite_eq_right hn.2, ite_eq_right hn.1, mul_zero, add_zero]),
    Finset.sum_pair (Ne.symm h2i)]
  simp only [l1Weighted.add_toSeq, l1Weighted.smul_toSeq, l1Weighted.single_toSeq,
    ite_eq_right (Ne.symm h2i), ite_eq_right h2i, ↓reduceIte]
  norm_num
  ring

/-- Sharpness witness for `C₂`: `‖e₁ ⋆ e₁‖ = ν² + 2`. -/
private theorem norm_cosMul_e1_e1 :
    ‖cosMul (lpOneAlg.single 1 1 : l1Weighted ν) (lpOneAlg.single 1 1)‖ = (ν : ℝ) ^ 2 + 2 :=
  norm_cosMul_single_self 1 one_pos

/-- **The exact bilinear operator norm**: `‖⋆‖ = C₂ = 1 + 2ν⁻²`; the lower bound is the atom
`(1, 1)` through `lpOneAlg.cols_le_opNorm₂`. -/
theorem opNorm_cosMul_eq :
    ‖(cosMul : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν)‖ = C₂ ν := by
  refine le_antisymm opNorm_cosMul_le ?_
  have h := lpOneAlg.cols_le_opNorm₂
    (cosMul : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ] l1Weighted ν) 1 1
  rw [WeightedScalar.fiberTrivialization_weight, pow_one, norm_cosMul_e1_e1] at h
  have hν2 : 0 < (ν : ℝ) ^ 2 := pow_pos ν.2 2
  have hC : C₂ ν = ((ν : ℝ) ^ 2 + 2) / (ν : ℝ) ^ 2 := by
    unfold C₂ t
    field_simp
  rw [hC]
  exact (div_le_iff₀ hν2).mpr (by nlinarith)

/-! ### Trilinear atoms and the constant `C₃` -/

/-- The triple product of three positive atoms: the eight bilateral modes `±i ± j ± k` (sign
patterns in the order `+++`, `++−`, `+−+`, `+−−`, `−++`, `−+−`, `−−+`, `−−−`), restricted. -/
theorem cosMul₃_single (i j k : ℕ) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    cosMul₃ (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single j 1) (lpOneAlg.single k 1)
      = restr (single ((i : ℤ) + j + k) 1 + single ((i : ℤ) + j - k) 1
          + single ((i : ℤ) - j + k) 1 + single ((i : ℤ) - j - k) 1
          + single (-(i : ℤ) + j + k) 1 + single (-(i : ℤ) + j - k) 1
          + single (-(i : ℤ) - j + k) 1 + single (-(i : ℤ) - j - k) 1) := by
  rw [cosMul₃_eq, symExt_single i hi, symExt_single j hj, symExt_single k hk]
  congr 1
  simp only [add_mul, mul_add, lpOneAlg.single_mul_single, mul_one, sub_eq_add_neg]
  abel

/-- The trilinear atom bound: `‖(eᵢ ⋆ eⱼ) ⋆ eₖ‖ ≤ C₃ νⁱ νʲ νᵏ`.

Case table for positive `i, j, k`, `s = i + j + k`; the restricted mode `m` contributes `ν^m`
if `m ≥ 0` and `0` otherwise (`norm_restr_single`); `h1`: `ν^{s−2a} ≤ t νˢ` (`1 ≤ a`,
`2a ≤ s`), `h2`: `ν^{2a−s} ≤ t² νˢ` (`2 ≤ s − a`), `h3`: `1 ≤ t² νˢ` (`2a = s`, `2 ≤ a`),
`h4`: at most one position `a` has `s ≤ 2a`.

| mode | signs | value | bound (no `a` with `s ≤ 2a`) | bound (`a₀ = i` has `s ≤ 2i`) |
|---|---|---|---|---|
| `i+j+k` | +++ | `s` | `νˢ` | `νˢ` |
| `i+j−k` | ++− | `s−2k` | `t νˢ` (h1) | `t νˢ` (h1) |
| `i−j+k` | +−+ | `s−2j` | `t νˢ` (h1) | `t νˢ` (h1) |
| `−i+j+k` | −++ | `s−2i` | `t νˢ` (h1) | `≤ 0`: `0`, or `1 ≤ t² νˢ` if `2i = s` (h3) |
| `i−j−k` | +−− | `2i−s` | `< 0`: `0` | `t² νˢ` (h2) |
| `−i+j−k` | −+− | `2j−s` | `< 0`: `0` | `< 0`: `0` (h4) |
| `−i−j+k` | −−+ | `2k−s` | `< 0`: `0` | `< 0`: `0` (h4) |
| `−i−j−k` | −−− | `−s` | `0` | `0` |
| total | | | `1 + 3t` | `1 + 2t + 2t²` |

(`a₀ = j` or `a₀ = k` permute the table.) A zero index reduces to the bilinear bound through
the unit `e₀` and `C₂ ≤ C₃`. -/
theorem norm_cosMul₃_single_le (i j k : ℕ) :
    ‖cosMul₃ (lpOneAlg.single i 1 : l1Weighted ν) (lpOneAlg.single j 1) (lpOneAlg.single k 1)‖
      ≤ C₃ ν * ((ν : ℝ) ^ i * (ν : ℝ) ^ j * (ν : ℝ) ^ k) := by
  have hν : 1 ≤ (ν : ℝ) := Fact.out
  have hC := C₂_le_C₃ ν
  have hw : ∀ a b : ℕ, 0 ≤ (ν : ℝ) ^ a * (ν : ℝ) ^ b := fun a b =>
    mul_nonneg (pow_nonneg ν.2.le _) (pow_nonneg ν.2.le _)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [cosMul₃_apply, cosMul_one_left, pow_zero, one_mul]
    exact (norm_cosMul_single_single_le j k).trans (mul_le_mul_of_nonneg_right hC (hw j k))
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [cosMul₃_apply, cosMul_one_right, pow_zero, mul_one]
    exact (norm_cosMul_single_single_le i k).trans (mul_le_mul_of_nonneg_right hC (hw i k))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cosMul₃_apply, cosMul_one_right, pow_zero, mul_one]
    exact (norm_cosMul_single_single_le i j).trans (mul_le_mul_of_nonneg_right hC (hw i j))
  rw [cosMul₃_single i j k hi hj hk]
  refine le_trans ?_ (eight_terms_le hν i j k hi hj hk)
  refine norm_restr_add_le_of (norm_restr_add_le_of (norm_restr_add_le_of
    (norm_restr_add_le_of (norm_restr_add_le_of (norm_restr_add_le_of (norm_restr_add_le_of
    (norm_restr_single_eq_posPow _).le (norm_restr_single_eq_posPow _).le)
    (norm_restr_single_eq_posPow _).le) (norm_restr_single_eq_posPow _).le)
    (norm_restr_single_eq_posPow _).le) (norm_restr_single_eq_posPow _).le)
    (norm_restr_single_eq_posPow _).le) (norm_restr_single_eq_posPow _).le

/-- `‖(a ⋆ b) ⋆ c‖ ≤ C₃ ‖a‖ ‖b‖ ‖c‖`, from the atom bound by `lpOneAlg.norm_le_of_cols₃`. -/
theorem norm_cosMul₃_le (a b c : l1Weighted ν) :
    ‖cosMul₃ a b c‖ ≤ C₃ ν * ‖a‖ * ‖b‖ * ‖c‖ :=
  lpOneAlg.norm_le_of_cols₃ cosMul₃ (fun i j k => by
    rw [WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact (norm_cosMul₃_single_le i j k).trans_eq (by ring)) a b c

/-- Sharpness witness for the branch `1 + 3t` of `C₃`: `‖(e₁ ⋆ e₁) ⋆ e₁‖ = ν³ + 3ν` (modes
`3, 1, 1, −1, 1, −1, −1, −3`, so the restriction is `e₃ + 3e₁`). -/
private theorem norm_cosMul₃_e1_e1_e1 :
    ‖cosMul₃ (lpOneAlg.single 1 1 : l1Weighted ν) (lpOneAlg.single 1 1) (lpOneAlg.single 1 1)‖
      = (ν : ℝ) ^ 3 + 3 * ν := by
  rw [cosMul₃_single 1 1 1 one_pos one_pos one_pos]
  have h3 : (3 : ℤ).toNat = 3 := rfl
  simp only [map_add, restr_single_int]
  norm_num [h3]
  rw [norm_eq_sum_of_support _ {1, 3} (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [l1Weighted.add_toSeq, l1Weighted.single_toSeq, ite_eq_right hn.1, ite_eq_right hn.2]
    norm_num), Finset.sum_pair (by norm_num)]
  simp only [l1Weighted.add_toSeq, l1Weighted.single_toSeq]
  norm_num
  ring

/-- Sharpness witness for the branch `1 + 2t + 2t²` of `C₃`: `‖(e₁ ⋆ e₁) ⋆ e₂‖ = ν⁴ + 2ν² + 2`
(modes `4, 0, 2, −2, 2, −2, 0, −4`, so the restriction is `e₄ + 2e₂ + 2e₀`). -/
private theorem norm_cosMul₃_e1_e1_e2 :
    ‖cosMul₃ (lpOneAlg.single 1 1 : l1Weighted ν) (lpOneAlg.single 1 1) (lpOneAlg.single 2 1)‖
      = (ν : ℝ) ^ 4 + 2 * (ν : ℝ) ^ 2 + 2 := by
  have h4 : (4 : ℤ).toNat = 4 := rfl
  have h2 : (2 : ℤ).toNat = 2 := rfl
  rw [cosMul₃_single 1 1 2 one_pos one_pos two_pos]
  simp only [map_add, restr_single_int]
  norm_num [h4, h2]
  rw [norm_eq_sum_of_support _ {0, 2, 4} (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [l1Weighted.add_toSeq, l1Weighted.single_toSeq, ite_eq_right hn.1, ite_eq_right hn.2.1,
      ite_eq_right hn.2.2]
    norm_num)]
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [l1Weighted.add_toSeq, l1Weighted.single_toSeq]
  norm_num
  ring

set_option maxSynthPendingDepth 2 in
/-- `‖cosMul₃‖ ≤ C₃`, from the atom bound by `lpOneAlg.opNorm_le_of_cols₃`.

Stated with `set_option maxSynthPendingDepth 2 in`: without it `Norm` does not synthesize on
the three-level type (see the module docstring); a consumer restating it repeats that
option. -/
theorem opNorm_cosMul₃_le : ‖(cosMul₃ : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ]
    l1Weighted ν →L[ℝ] l1Weighted ν)‖ ≤ C₃ ν :=
  lpOneAlg.opNorm_le_of_cols₃ cosMul₃ (C₃_nonneg ν) (fun i j k => by
    rw [WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact (norm_cosMul₃_single_le i j k).trans_eq (by ring))

set_option maxSynthPendingDepth 2 in
/-- **The exact trilinear operator norm**: `‖cosMul₃‖ = C₃ = max(1 + 3t, 1 + 2t + 2t²)`; the
lower bounds are the atoms `(1, 1, 1)` and `(1, 1, 2)` through `lpOneAlg.cols_le_opNorm₃`.
Stated with `set_option maxSynthPendingDepth 2 in` (as `opNorm_cosMul₃_le`). -/
theorem opNorm_cosMul₃_eq : ‖(cosMul₃ : l1Weighted ν →L[ℝ] l1Weighted ν →L[ℝ]
    l1Weighted ν →L[ℝ] l1Weighted ν)‖ = C₃ ν := by
  refine le_antisymm opNorm_cosMul₃_le ?_
  have h111 := lpOneAlg.cols_le_opNorm₃ (cosMul₃ (ν := ν)) 1 1 1
  have h112 := lpOneAlg.cols_le_opNorm₃ (cosMul₃ (ν := ν)) 1 1 2
  simp only [WeightedScalar.fiberTrivialization_weight, pow_one] at h111 h112
  rw [norm_cosMul₃_e1_e1_e1] at h111
  rw [norm_cosMul₃_e1_e1_e2] at h112
  have hp3 : 0 < (ν : ℝ) ^ 3 := pow_pos ν.2 3
  have hp4 : 0 < (ν : ℝ) ^ 4 := pow_pos ν.2 4
  have eL : (1 + 3 * t ν) * (ν : ℝ) ^ 3 = (ν : ℝ) ^ 3 + 3 * ν := by
    unfold t; field_simp
  have eR : (1 + 2 * t ν + 2 * t ν ^ 2) * (ν : ℝ) ^ 4 = (ν : ℝ) ^ 4 + 2 * (ν : ℝ) ^ 2 + 2 := by
    unfold t; field_simp
  unfold C₃
  refine max_le (le_of_mul_le_mul_right ?_ hp3) (le_of_mul_le_mul_right ?_ hp4)
  · rw [eL]; nlinarith
  · rw [eR]; nlinarith

end Product

end OneSided

end l1Chebyshev

end RadiiPolynomial
