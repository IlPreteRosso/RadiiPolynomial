import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.LiftBound
import RadiiPolynomial.Algebra.Convolution.Ring
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The row-bounded convolution product on `WeightedLp M E p`

On an additive monoid `M` with a chosen frame `[FiberTrivialization 𝕜 M E]` of derived weight
`m = FiberTrivialization.weight`, the *ratio row* at `n` is the family
`r_n(a, b) = m_n / (m_a m_b)` on the addition fibre `addFiber n = {(a, b) | a + b = n}`. For a
carrier exponent `1 ≤ p ≤ ∞` and its Hölder conjugate `q`, the supplied bound
`RowBound m q K` (every row in `ℓ^q(addFiber n)` with norm at most `K`) gives the bounded bilinear
convolution `convCLM h : X →L[𝕜] X →L[𝕜] X`, `X = WeightedLp M E p`, with

* the coefficient computation `coeff (convCLM h x y) = coeff x ⋆ᵣ₊ coeff y` (Mathlib's
  additive-index ring convolution) and absolutely convergent fibre series
  (`summable_norm_coeff_mul`);
* the bounds `‖convCLM h‖ ≤ K` and `‖convCLM h x y‖ ≤ K ‖x‖ ‖y‖` in the physical norm (no
  renormalization; `K` is an upper bound, not the product norm);
* the atom computation `convCLM h (single a r) (single b s) = single (a + b) (r * s)` and, for
  `p ≠ ∞`, determination by the unit atoms (`eq_convCLM_of_single`), so the product does not
  depend on the bound witness;
* the algebra contract: the two-sided unit `single 0 1`, commutativity over a commutative index
  and, for `p ≠ ∞`, associativity, proved from the atoms by density of the finite atom span
  (no reciprocal-mass summability and no Fubini step);
* the coherence `convCLM h a x = symbolAction₀ hC b x` with the ℓ¹ symbol action of
  `Module.lean` whenever `rawSymbol b = coeff a` (additive commutative group index).

At `p = q = 2` the row condition is `∑_{a + b = n} (m_n / (m_a m_b))² ≤ K²` with summable rows,
in the amplitude convention `‖x‖² = ∑ |x_n|² m_n²` of the library (the mass weight is `ω = m²`).
`RowBound.of_tsum_rpow_le` produces it from summable `q`-th powers at finite `q`, and
`RowBound.mul_submul` transfers it from a positive weight `w` to `w · u` for every positive
submultiplicative factor `u`.

## Scope of the hypotheses

The row bound is a sufficient condition, not a characterization of bounded convolution
products. The product uses neither submultiplicativity of `m` (on the one-point index the weight
`m_0 = 1/2` has `K = 2` and `m_0 > m_0²`) nor unit normalization (`single 0 1` is a unit; it has
norm one only when `m_0 = 1`) nor reciprocal-mass summability `∑ m_n⁻² < ∞`: the weight
`m_n = (1 + |n|)² 2ⁿ` on `ℤ` has exactly the ratio rows of `(1 + |n|)²`, since the character `2ⁿ`
cancels in every ratio, while `m_{-N}⁻² = 4^N / (1 + N)⁴` is not summable and the state equal
to `1` on the negative integers lies in `ℓ²_m` but not in unweighted `ℓ¹`. The embedding
`ℓ²_m → ℓ¹` is therefore a separate service, not a premise of the algebra. For a separable
polynomial amplitude `m_n = ∏_j (1 + |n_j|)^α` on `ℤ^d` the row condition at `p = 2` holds for
`α > 1/2` (mass exponent `2α > 1`) with `K = (2^{2α} (2ζ(2α) − 1))^{d/2}` (a mathematical remark,
not formalized here; the consumer `Examples/Fourier/Duffing/Polynomial` proves its own coarse
`K = 10` at `d = 1`, `α = 2`).

## Role of this product

The carrier definition does not select a convolution product on an arbitrary state
`X = ℓ^p_m`. A separately proved bounded self-product may equip a chosen framed state with an
explicit algebra service. Over ℝ or ℂ, the normalized positive-block example excludes a bounded
convolution self-product on the bilateral geometric ℓ² state `m_n = ν^|n|`. This state also fails
the sufficient row condition: its row at `n` contains `|n| + 1` unit ratios (failure of the sufficient
test alone is not the nonexistence proof). The admissible polynomial ℓ² states satisfy the row
condition. Coefficient algebra, state and operator image remain different roles even when two
roles use the same carrier. No `Mul` or `NormedRing` instance is installed on `WeightedLp`: a
`K`-bounded multiplication is not the contractive multiplication of a normed ring.

## Proof

One Hölder step on each fibre (`lp.holderL` with exponents `(q, p)` and target `1`, applied to the
ratio row and the fibre product `(a, b) ↦ ‖x a‖ ‖y b‖`, through the pointwise identity
`r_n(a, b) ‖x a‖ ‖y b‖ = m_n ‖coeff x a * coeff y b‖`), then one aggregation step: the fibre
products lie in `ℓ^p(M)` with norm at most `‖x‖ ‖y‖` (for `p < ∞` by the fibre decomposition
`sigmaAddFiberEquiv : (Σ n, addFiber n) ≃ M × M`, for `p = ∞` by the uniform bound). No
cancellation, commutativity or decidable equality of `M` is used by the estimate. Scalar
convergence of the fibre series uses a complete scalar field.
-/

open scoped ENNReal NNReal DiscreteConvolution
open _root_.DiscreteConvolution (addFiber mem_addFiber addRingConvolution_apply
  single_addRingConvolution addRingConvolution_single addRingConvolution_comm)
open RadiiPolynomial.DiscreteConvolution (sigmaAddFiberEquiv addFiberEquiv
  single_addRingConvolution_single)

noncomputable section

namespace RadiiPolynomial.WeightedLp

/-! ### Ratio rows and the supplied row bound -/

section Rows

variable {M : Type*} [AddMonoid M] (w : M → ℝ)

/-- The ratio row at `n`: `r_n(a, b) = w_n / (w_a w_b)` on the fibre `a + b = n`. -/
def ratioRow (n : M) (ab : addFiber n) : ℝ := w n / (w ab.1.1 * w ab.1.2)

/-- The supplied row bound: every ratio row lies in `ℓ^q(addFiber n)` with norm at most `K`. -/
structure RowBound (q : ℝ≥0∞) (K : ℝ) : Prop where
  mem : ∀ n, Memℓp (ratioRow w n) q
  le : ∀ n, ‖(⟨ratioRow w n, mem n⟩ : lp (fun _ : addFiber n => ℝ) q)‖ ≤ K

variable {w}

/-- A row bound is nonnegative (read off the row at `0`). -/
theorem RowBound.nonneg {q : ℝ≥0∞} {K : ℝ} (h : RowBound w q K) : 0 ≤ K :=
  (lp.norm_nonneg' _).trans (h.le 0)

/-- **The finite-exponent producer**: summable `q`-th powers of the rows with sums at most `K^q`
give the row bound (`0 < q.toReal`, i.e. `q ≠ 0, ∞`; positive weight). At `q = 2` this is the
summable ratio-square row condition `∑_{a + b = n} (w_n / (w_a w_b))² ≤ K²`. -/
theorem RowBound.of_tsum_rpow_le {q : ℝ≥0∞} (hq : 0 < q.toReal) (hw : ∀ m, 0 < w m)
    {K : ℝ} (hK : 0 ≤ K)
    (hs : ∀ n, Summable fun ab : addFiber n => ratioRow w n ab ^ q.toReal)
    (hle : ∀ n, ∑' ab : addFiber n, ratioRow w n ab ^ q.toReal ≤ K ^ q.toReal) :
    RowBound w q K := by
  have hnorm (n : M) (ab : addFiber n) : ‖ratioRow w n ab‖ = ratioRow w n ab :=
    Real.norm_of_nonneg (div_nonneg (hw n).le (mul_pos (hw _) (hw _)).le)
  exact ⟨fun n => memℓp_gen ((hs n).congr fun ab => by rw [hnorm]), fun n =>
    lp.norm_le_of_tsum_le hq hK ((tsum_congr fun ab => by
      rw [hnorm]).trans_le (hle n))⟩

/-- The ratio-row comparison: a row bound of `v` is a row bound of a positive weight `w` whose
every ratio row is dominated by the ratio row of `v` (`q ≠ 0`). -/
private theorem RowBound.of_ratioRow_le {v : M → ℝ} {q : ℝ≥0∞} {K : ℝ} (hq : q ≠ 0)
    (hw : ∀ m, 0 < w m) (hle : ∀ n (ab : addFiber n), ratioRow w n ab ≤ ratioRow v n ab)
    (h : RowBound v q K) : RowBound w q K := by
  have hnn (n : M) (ab : addFiber n) : 0 ≤ ratioRow w n ab :=
    div_nonneg (hw n).le (mul_pos (hw _) (hw _)).le
  have hn (n : M) (ab : addFiber n) : ‖ratioRow w n ab‖ ≤ ‖ratioRow v n ab‖ := by
    rw [Real.norm_of_nonneg (hnn n ab)]
    exact (hle n ab).trans (le_abs_self _)
  refine ⟨fun n => (h.mem n).mono' (hn n), fun n => (lp.norm_mono hq ?_).trans (h.le n)⟩
  exact fun ab => hn n ab

/-- **Transfer by a submultiplicative factor**: a row bound of a positive weight `w` is a row
bound, at the same `q ≠ 0` and `K`, of `w · u` for every positive submultiplicative factor `u`
(`u (i + j) ≤ u i u j`), since every ratio row of `w · u` is dominated by that of `w`. -/
theorem RowBound.mul_submul {u : M → ℝ} {q : ℝ≥0∞} {K : ℝ} (hq : q ≠ 0) (hw : ∀ m, 0 < w m)
    (hu : ∀ m, 0 < u m) (hsub : ∀ i j, u (i + j) ≤ u i * u j)
    (h : RowBound w q K) : RowBound (fun m => w m * u m) q K := by
  refine RowBound.of_ratioRow_le hq (fun m => mul_pos (hw m) (hu m)) (fun n ab => ?_) h
  obtain ⟨⟨i, j⟩, hij⟩ := ab
  have hn : i + j = n := (mem_addFiber).1 hij
  simp only [ratioRow]
  have hun : u n ≤ u i * u j := hn ▸ hsub i j
  have hW : 0 ≤ w n * (w i * w j) := by have := hw n; have := hw i; have := hw j; positivity
  have h1 := hw i; have h2 := hw j; have h3 := hu i; have h4 := hu j
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hun hW]

end Rows

/-! ### Aggregation over the fibre decomposition of `M × M` (frame-free) -/

section Aggregation

variable {M : Type*} [AddMonoid M] {E F : M → Type*} [∀ m, NormedAddCommGroup (E m)]
  [∀ m, NormedAddCommGroup (F m)] {p : ℝ≥0∞}

/-- The fibre product `(a, b) ↦ ‖x a‖ ‖y b‖` on `addFiber n`. -/
private def fiberProd (x : WeightedLp M E p) (y : WeightedLp M F p) (n : M) (ab : addFiber n) :
    ℝ :=
  ‖x ab.1.1‖ * ‖y ab.1.2‖

private theorem fiberProd_nonneg (x : WeightedLp M E p) (y : WeightedLp M F p) (n : M)
    (ab : addFiber n) : 0 ≤ fiberProd x y n ab :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem norm_fiberProd_rpow (x : WeightedLp M E p) (y : WeightedLp M F p) (n : M)
    (ab : addFiber n) (r : ℝ) :
    ‖fiberProd x y n ab‖ ^ r = ‖x ab.1.1‖ ^ r * ‖y ab.1.2‖ ^ r := by
  rw [Real.norm_of_nonneg (fiberProd_nonneg x y n ab), fiberProd,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- The product `‖x a‖^p ‖y b‖^p` is summable over the fibre decomposition `Σ n, addFiber n`. -/
private theorem summable_sigma_rpow (hp : 0 < p.toReal) (x : WeightedLp M E p)
    (y : WeightedLp M F p) :
    Summable fun s : (Σ n : M, addFiber n) => ‖x s.2.1.1‖ ^ p.toReal * ‖y s.2.1.2‖ ^ p.toReal :=
  (sigmaAddFiberEquiv.summable_iff
    (f := fun ij : M × M => ‖x ij.1‖ ^ p.toReal * ‖y ij.2‖ ^ p.toReal)).2
    (((lp.memℓp x).summable hp).mul_of_nonneg ((lp.memℓp y).summable hp)
      (fun _ => by positivity) fun _ => by positivity :)

/-- `∑' n, ∑' (a, b) ∈ addFiber n, ‖x a‖^p ‖y b‖^p = (‖x‖ ‖y‖)^p`. -/
private theorem tsum_tsum_fiber_rpow (hp : 0 < p.toReal) (x : WeightedLp M E p)
    (y : WeightedLp M F p) :
    ∑' n : M, ∑' ab : addFiber n, ‖x ab.1.1‖ ^ p.toReal * ‖y ab.1.2‖ ^ p.toReal =
      (‖x‖ * ‖y‖) ^ p.toReal := by
  have he : ∑' s : (Σ n : M, addFiber n), ‖x s.2.1.1‖ ^ p.toReal * ‖y s.2.1.2‖ ^ p.toReal =
      ∑' ij : M × M, ‖x ij.1‖ ^ p.toReal * ‖y ij.2‖ ^ p.toReal :=
    sigmaAddFiberEquiv.tsum_eq (fun ij : M × M => ‖x ij.1‖ ^ p.toReal * ‖y ij.2‖ ^ p.toReal)
  refine ((summable_sigma_rpow hp x y).tsum_sigma.symm.trans he).trans ?_
  rw [Real.mul_rpow (lp.norm_nonneg' x) (lp.norm_nonneg' y), lp.norm_rpow_eq_tsum hp x,
    lp.norm_rpow_eq_tsum hp y]
  exact (((lp.memℓp x).summable hp).tsum_mul_tsum ((lp.memℓp y).summable hp)
    (((lp.memℓp x).summable hp).mul_of_nonneg ((lp.memℓp y).summable hp)
      (fun _ => by positivity) fun _ => by positivity :)).symm

variable [Fact (1 ≤ p)]

private theorem memℓp_fiberProd (x : WeightedLp M E p) (y : WeightedLp M F p) (n : M) :
    Memℓp (fiberProd x y n) p := by
  rcases p.dichotomy with rfl | hp
  · exact memℓp_infty_iff.2 ⟨‖x‖ * ‖y‖, by
      rintro _ ⟨ab, rfl⟩
      exact (Real.norm_of_nonneg (fiberProd_nonneg x y n ab)).le.trans
        (mul_le_mul (norm_apply_le_norm x _) (norm_apply_le_norm y _) (norm_nonneg _)
          (norm_nonneg _))⟩
  · exact memℓp_gen <| ((summable_sigma_rpow (zero_lt_one.trans_le hp) x y).sigma_factor n).congr
      fun ab => (norm_fiberProd_rpow x y n ab _).symm

/-- The `n`-th fibre product as an element of `ℓ^p(addFiber n, ℝ)`. -/
private def fiberProdLp (x : WeightedLp M E p) (y : WeightedLp M F p) (n : M) :
    lp (fun _ : addFiber n => ℝ) p :=
  ⟨fiberProd x y n, memℓp_fiberProd x y n⟩

/-- **Aggregation**: `n ↦ ‖fiberProdLp x y n‖` lies in `ℓ^p(M)` with norm at most `‖x‖ ‖y‖`. -/
private theorem fiberProd_norm (x : WeightedLp M E p) (y : WeightedLp M F p) :
    ∃ h : Memℓp (fun n => ‖fiberProdLp x y n‖) p,
      ‖(⟨_, h⟩ : lp (fun _ : M => ℝ) p)‖ ≤ ‖x‖ * ‖y‖ := by
  have hxy : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  rcases p.dichotomy with rfl | hp
  · have hle : ∀ n, ‖fiberProdLp x y n‖ ≤ ‖x‖ * ‖y‖ := fun n =>
      lp.norm_le_of_forall_le hxy fun ab =>
        (Real.norm_of_nonneg (fiberProd_nonneg x y n ab)).le.trans
          (mul_le_mul (norm_apply_le_norm x _) (norm_apply_le_norm y _) (norm_nonneg _)
            (norm_nonneg _))
    have hmem : Memℓp (fun n => ‖fiberProdLp x y n‖) ∞ :=
      memℓp_infty_iff.2 ⟨‖x‖ * ‖y‖, by
        rintro _ ⟨n, rfl⟩
        exact (Real.norm_of_nonneg (lp.norm_nonneg' _)).le.trans (hle n)⟩
    exact ⟨hmem, lp.norm_le_of_forall_le hxy fun n =>
      (Real.norm_of_nonneg (lp.norm_nonneg' _)).le.trans (hle n)⟩
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    have hrow : ∀ n, ‖‖fiberProdLp x y n‖‖ ^ p.toReal =
        ∑' ab : addFiber n, ‖x ab.1.1‖ ^ p.toReal * ‖y ab.1.2‖ ^ p.toReal := fun n => by
      rw [norm_norm, lp.norm_rpow_eq_tsum hp0]
      exact tsum_congr fun ab => norm_fiberProd_rpow x y n ab _
    have hmem : Memℓp (fun n => ‖fiberProdLp x y n‖) p :=
      memℓp_gen <| (summable_sigma_rpow hp0 x y).sigma.congr fun n => (hrow n).symm
    exact ⟨hmem, lp.norm_le_of_tsum_le hp0 hxy
      ((tsum_congr hrow).trans (tsum_tsum_fiber_rpow hp0 x y)).le⟩

end Aggregation

/-! ### The convolution estimate -/

section Estimate

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddMonoid M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞}

/-- The pointwise identity `r_n(a, b) ‖x a‖ ‖y b‖ = m_n ‖coeff x a * coeff y b‖`. -/
private theorem ratioRow_mul_fiberProd (x y : WeightedLp M E p) (n : M) (ab : addFiber n) :
    ratioRow (FiberTrivialization.weight (E := E)) n ab * fiberProd x y n ab =
      FiberTrivialization.weight (E := E) n * ‖coeff x ab.1.1 * coeff y ab.1.2‖ := by
  rw [fiberProd, norm_apply_eq, norm_apply_eq, norm_mul, ratioRow]
  have h1 := FiberTrivialization.weight_ne_zero (E := E) ab.1.1
  have h2 := FiberTrivialization.weight_ne_zero (E := E) ab.1.2
  field_simp

/-- The multiplication family of the Hölder step on the fibre `addFiber n`. -/
private def mulFamily (n : M) : addFiber n → ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  fun _ => ContinuousLinearMap.mul ℝ ℝ

private theorem norm_mulFamily_le (n : M) (ab : addFiber n) :
    ‖mulFamily n ab‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  rw [NNReal.coe_one]; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ

variable [Fact (1 ≤ p)] {q : ℝ≥0∞} [p.HolderConjugate q] {K : ℝ}

/-- **The convolution estimate**: under a row bound at the Hölder conjugate exponent, every
fibre series of coordinate products converges absolutely, and the transported convolution lies
in `ℓ^p` with norm at most `K ‖x‖ ‖y‖`. -/
private theorem conv_bound (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) :
    (∀ n, Summable fun ab : addFiber n => ‖coeff x ab.1.1 * coeff y ab.1.2‖) ∧
    ∃ hm : Memℓp (fun n => FiberTrivialization.equiv (E := E) n ((coeff x ⋆ᵣ₊ coeff y) n)) p,
      ‖(⟨_, hm⟩ : WeightedLp M E p)‖ ≤ K * ‖x‖ * ‖y‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let row : ∀ n, lp (fun _ : addFiber n => ℝ) q := fun n =>
    ⟨ratioRow (FiberTrivialization.weight (E := E)) n, h.mem n⟩
  let H : ∀ n, lp (fun _ : addFiber n => ℝ) 1 := fun n =>
    lp.holderL (p := q) (q := p) 1 (mulFamily n) (norm_mulFamily_le n) (row n)
      (fiberProdLp x y n)
  have hH : ∀ n ab, H n ab =
      FiberTrivialization.weight (E := E) n * ‖coeff x ab.1.1 * coeff y ab.1.2‖ := fun n ab =>
    ratioRow_mul_fiberProd x y n ab
  have hHnn : ∀ n ab, ‖H n ab‖ = H n ab := fun n ab => Real.norm_of_nonneg <| by
    rw [hH]; exact mul_nonneg (FiberTrivialization.weight_nonneg n) (norm_nonneg _)
  have hHsum : ∀ n, Summable fun ab => ‖H n ab‖ := fun n => by
    simpa using (lp.memℓp (H n)).summable (by simp)
  have hHnorm : ∀ n, ‖H n‖ = ∑' ab, ‖H n ab‖ := fun n => by
    simpa using lp.norm_eq_tsum_rpow (by simp) (H n)
  have hHle : ∀ n, ‖H n‖ ≤ K * ‖fiberProdLp x y n‖ := fun n =>
    ((ContinuousLinearMap.le_opNorm₂ _ _ _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (lp.norm_holderL_le 1 (mulFamily n) (norm_mulFamily_le n) |>.trans (by simp))
        (h.le n) (lp.norm_nonneg' _) zero_le_one) (lp.norm_nonneg' _))).trans_eq (by ring)
  have hsum : ∀ n, Summable fun ab : addFiber n => ‖coeff x ab.1.1 * coeff y ab.1.2‖ := fun n =>
    ((hHsum n).mul_left (FiberTrivialization.weight (E := E) n)⁻¹).congr fun ab => by
      rw [hHnn, hH, ← mul_assoc, inv_mul_cancel₀ (FiberTrivialization.weight_ne_zero n), one_mul]
  have hout : ∀ n, ‖FiberTrivialization.equiv (E := E) n ((coeff x ⋆ᵣ₊ coeff y) n)‖ ≤
      K * ‖fiberProdLp x y n‖ := fun n => by
    refine le_trans ?_ (hHle n)
    rw [FiberTrivialization.norm_equiv_apply, addRingConvolution_apply, hHnorm, mul_comm]
    refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hsum n))
      (FiberTrivialization.weight_nonneg n)).trans_eq ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun ab => by rw [hHnn, hH]
  obtain ⟨hN, hNle⟩ := fiberProd_norm x y
  let N : lp (fun _ : M => ℝ) p := ⟨_, hN⟩
  have hK0 := h.nonneg
  refine ⟨hsum, (hN.const_mul K).mono hout, ?_⟩
  refine (lp.norm_mono exponent_ne_zero (y := K • N) fun n => (hout n).trans_eq ?_).trans ?_
  · rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg
      (mul_nonneg hK0 (lp.norm_nonneg' _))]
  · rw [lp.norm_const_smul exponent_ne_zero, Real.norm_of_nonneg hK0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hNle hK0

/-- **Absolute convergence of the coefficient series**: under a row bound, every fibre series
`∑ (a, b) ∈ addFiber n, coeff x a * coeff y b` converges absolutely. -/
theorem summable_norm_coeff_mul (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) (n : M) :
    Summable fun ab : addFiber n => ‖coeff x ab.1.1 * coeff y ab.1.2‖ :=
  (conv_bound h x y).1 n

/-- The transported convolution of two states, before bundling. -/
private def conv (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) : WeightedLp M E p :=
  ⟨_, (conv_bound h x y).2.fst⟩

private theorem coeff_conv (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) : coeff (conv h x y) = coeff x ⋆ᵣ₊ coeff y :=
  funext fun n => coeff_mk_equiv _ _ n

private theorem norm_conv_le (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) : ‖conv h x y‖ ≤ K * ‖x‖ * ‖y‖ :=
  (conv_bound h x y).2.snd

end Estimate

/-! ### The bounded bilinear product -/

section Product

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddMonoid M]
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [p.HolderConjugate q]
  {K : ℝ}

private theorem summable_coeff_mul (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (x y : WeightedLp M E p) (n : M) :
    Summable fun ab : addFiber n => coeff x ab.1.1 * coeff y ab.1.2 :=
  (summable_norm_coeff_mul h x y n).of_norm

/-- The convolution as a bilinear map. -/
private def convLM (h : RowBound (FiberTrivialization.weight (E := E)) q K) :
    WeightedLp M E p →ₗ[𝕜] WeightedLp M E p →ₗ[𝕜] WeightedLp M E p :=
  LinearMap.mk₂ 𝕜 (conv h)
    (fun x x' y => ext_coeff <| funext fun n => by
      simp only [coeff_conv, coeff_add, Pi.add_apply, addRingConvolution_apply, add_mul]
      exact (summable_coeff_mul h x y n).tsum_add (summable_coeff_mul h x' y n))
    (fun c x y => ext_coeff <| funext fun n => by
      simp only [coeff_conv, coeff_smul, Pi.smul_apply, smul_eq_mul, addRingConvolution_apply,
        mul_assoc]
      exact tsum_mul_left)
    (fun x y y' => ext_coeff <| funext fun n => by
      simp only [coeff_conv, coeff_add, Pi.add_apply, addRingConvolution_apply, mul_add]
      exact (summable_coeff_mul h x y n).tsum_add (summable_coeff_mul h x y' n))
    (fun c x y => ext_coeff <| funext fun n => by
      simp only [coeff_conv, coeff_smul, Pi.smul_apply, smul_eq_mul, addRingConvolution_apply,
        mul_left_comm _ c]
      exact tsum_mul_left)

/-- **The row-bounded convolution product** `convCLM h : X →L[𝕜] X →L[𝕜] X` on
`X = WeightedLp M E p`, for a row bound `h` of the frame weight at the Hölder conjugate
exponent `q` of `p`. -/
def convCLM (h : RowBound (FiberTrivialization.weight (E := E)) q K) :
    WeightedLp M E p →L[𝕜] WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  (convLM h).mkContinuous₂ K fun x y => by
    simpa only [convLM, LinearMap.mk₂_apply] using norm_conv_le h x y

variable (h : RowBound (FiberTrivialization.weight (E := E)) q K)

/-- **The coefficient computation**: the coordinates of the product are Mathlib's
additive-index ring convolution of the coordinates,
`coeff (convCLM h x y) n = ∑' (a, b) ∈ addFiber n, coeff x a * coeff y b`. -/
theorem coeff_convCLM (x y : WeightedLp M E p) :
    coeff (convCLM h x y) = coeff x ⋆ᵣ₊ coeff y :=
  coeff_conv h x y

/-- `‖convCLM h‖ ≤ K`. -/
theorem norm_convCLM_le : ‖convCLM (p := p) h‖ ≤ K :=
  LinearMap.mkContinuous₂_norm_le _ h.nonneg _

/-- `‖convCLM h x y‖ ≤ K ‖x‖ ‖y‖`. -/
theorem norm_convCLM_apply_le (x y : WeightedLp M E p) : ‖convCLM h x y‖ ≤ K * ‖x‖ * ‖y‖ :=
  norm_conv_le h x y

/-- **The atom computation**: `convCLM h (single a r) (single b s) = single (a + b) (r * s)`. -/
theorem convCLM_single_single [DecidableEq M] (a b : M) (r s : 𝕜) :
    convCLM h (single (E := E) (p := p) a r) (single b s) = single (a + b) (r * s) :=
  ext_coeff <| by rw [coeff_convCLM, coeff_single, coeff_single, coeff_single,
    single_addRingConvolution_single]

/-- **Determination by the unit atoms** (`p ≠ ∞`): a bounded bilinear map with
`B (single a 1) (single b 1) = single (a + b) 1` is the convolution product. In particular the
product does not depend on the row-bound witness. -/
theorem eq_convCLM_of_single [DecidableEq M] (hp : p ≠ ∞)
    {B : WeightedLp M E p →L[𝕜] WeightedLp M E p →L[𝕜] WeightedLp M E p}
    (hB : ∀ a b : M, B (single a 1) (single b 1) = single (a + b) 1) : B = convCLM h :=
  ext_single hp fun a => ext_single hp fun b => by rw [hB, convCLM_single_single, mul_one]

/-- The atom `single 0 1` is a left unit. -/
theorem convCLM_unit_left [DecidableEq M] (x : WeightedLp M E p) :
    convCLM h (single 0 1) x = x :=
  ext_coeff <| by rw [coeff_convCLM, coeff_single, single_addRingConvolution]

/-- The atom `single 0 1` is a right unit. -/
theorem convCLM_unit_right [DecidableEq M] (x : WeightedLp M E p) :
    convCLM h x (single 0 1) = x :=
  ext_coeff <| by rw [coeff_convCLM, coeff_single, addRingConvolution_single]

/-- **Associativity** (`p ≠ ∞`): the two bracketings are continuous and agree on the atoms, which
span a dense subspace. -/
theorem convCLM_assoc (hp : p ≠ ∞) (x y z : WeightedLp M E p) :
    convCLM h (convCLM h x y) z = convCLM h x (convCLM h y z) := by
  classical
  have hz (a b : M) : convCLM h (convCLM h (single a 1) (single b 1)) =
      (convCLM h (single a 1)).comp (convCLM h (single b 1)) :=
    ext_single hp fun c => by
      rw [ContinuousLinearMap.comp_apply]
      simp only [convCLM_single_single, add_assoc, mul_one]
  have hy (a : M) (z : WeightedLp M E p) :
      ((convCLM h).flip z).comp (convCLM h (single a 1)) =
        (convCLM h (single a 1)).comp ((convCLM h).flip z) :=
    ext_single hp fun b => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      exact DFunLike.congr_fun (hz a b) z
  have hx : ((convCLM h).flip z).comp ((convCLM h).flip y) = (convCLM h).flip (convCLM h y z) :=
    ext_single hp fun a => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      exact DFunLike.congr_fun (hy a z) y
  exact DFunLike.congr_fun hx x

end Product

section Commutative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommMonoid M]
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [p.HolderConjugate q]
  {K : ℝ} (h : RowBound (FiberTrivialization.weight (E := E)) q K)

/-- **Commutativity** over a commutative index. -/
theorem convCLM_comm (x y : WeightedLp M E p) : convCLM h x y = convCLM h y x :=
  ext_coeff <| by rw [coeff_convCLM, coeff_convCLM, addRingConvolution_comm]

end Commutative

/-! ### Coherence with the ℓ¹ symbol action -/

section Coherence

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M : Type*} [AddCommGroup M]
  {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [p.HolderConjugate q]
  {K : ℝ} {v : M → ℝ} [PosWeight v] {C : ℝ}

/-- **Coherence of the product with the symbol action**: on a state `a` whose coordinates are the
raw coefficients of an ℓ¹_v symbol `b`, left multiplication by `a` is the operator series
`symbolAction₀ hC b` of the moderate symbol action. No state is required to lie in ℓ¹_v. -/
theorem convCLM_eq_symbolAction₀ (h : RowBound (FiberTrivialization.weight (E := E)) q K)
    (hC : Moderate (FiberTrivialization.weight (E := E)) v C) {a : WeightedLp M E p}
    {b : lpOneAlg M (WeightedScalar 𝕜 v)} (hb : rawSymbol b = coeff a) (x : WeightedLp M E p) :
    convCLM h a x = symbolAction₀ hC b x := by
  refine ext_coeff (funext fun n => ?_)
  rw [coeff_convCLM, symbolAction₀_apply, coeff_symbolSeries, hb, addRingConvolution_apply,
    ← ((Equiv.subLeft n).trans (addFiberEquiv n)).tsum_eq]
  exact tsum_congr fun l => by
    show coeff a (n - (n - l)) * coeff x (n - l) = coeff a l * coeff x (n - l)
    rw [sub_sub_cancel]

end Coherence

end RadiiPolynomial.WeightedLp

end
