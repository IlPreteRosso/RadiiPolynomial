import RadiiPolynomial.source.lpSpace.CauchyProduct
import RadiiPolynomial.source.lpSpace.lpWeighted
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# From Coefficient Space to Analytic Functions

Bridges the coefficient space ℓ¹_ν to analytic functions via power series evaluation.

## Main Results

* `l1Weighted.toPowerSeries`: Embedding ℓ¹_ν ↪ ℝ⟦X⟧
* `l1Weighted.eval`: Evaluation at points in the disk |z| ≤ ν
* `l1Weighted.eval_mul`: Evaluation is a ring homomorphism (Mertens' theorem)
-/

open scoped BigOperators NNReal ENNReal Topology
open RadiiPolynomial

noncomputable section

variable {ν : PosReal}

namespace l1Weighted

private abbrev seq (a : l1Weighted ν) := l1Weighted.toSeq a

/-! ## Formal Power Series Embedding -/

def toPowerSeries (a : l1Weighted ν) : PowerSeries ℝ :=
  PowerSeries.mk (seq a)

@[simp]
theorem coeff_toPowerSeries (a : l1Weighted ν) (n : ℕ) :
    (PowerSeries.coeff n) (toPowerSeries a) = seq a n :=
  PowerSeries.coeff_mk n _

theorem coeff_mul_eq_cauchyProduct (a b : l1Weighted ν) (n : ℕ) :
    (PowerSeries.coeff n) (toPowerSeries a * toPowerSeries b) =
    CauchyProduct (seq a) (seq b) n := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_toPowerSeries, CauchyProduct.apply]

/-! ## Analytic Evaluation -/

private lemma norm_term_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]; gcongr

theorem summable_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => seq a n * z ^ n :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simp only [Real.norm_eq_abs]; exact norm_term_le hz n

private theorem summable_norm_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => ‖seq a n * z ^ n‖ :=
  (l1Weighted.summable_weighted a).of_norm_bounded fun n => by
    simp only [Real.norm_eq_abs, abs_abs]; exact norm_term_le hz n

/-- Evaluate an ℓ¹_ν sequence as a power series at z ∈ ℝ. -/
def eval (a : l1Weighted ν) (z : ℝ) : ℝ :=
  ∑' n, seq a n * z ^ n

/-- eval(a, 0) = a₀. -/
theorem eval_at_zero (a : l1Weighted ν) : eval a 0 = seq a 0 := by
  unfold eval
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- The multiplicative identity evaluates to 1 (constant function). Needed for the
analytic interpretation of constant polynomials in the f-F bridge. -/
@[simp] theorem eval_one (z : ℝ) : eval (1 : l1Weighted ν) z = 1 := by
  unfold eval
  rw [tsum_eq_single 0]
  · rw [show seq (1 : l1Weighted ν) 0 = 1 from l1Weighted.one_toSeq_zero]; simp
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show seq (1 : l1Weighted ν) (m + 1) = 0 from l1Weighted.one_toSeq_succ m]; ring

/-- Evaluation respects negation. -/
@[simp] theorem eval_neg (a : l1Weighted ν) (z : ℝ) :
    eval (-a) z = -eval a z := by
  show ∑' n, seq (-a) n * z^n = -∑' n, seq a n * z^n
  simp_rw [show ∀ n, seq (-a) n = -seq a n from l1Weighted.neg_toSeq a, neg_mul]
  exact tsum_neg

/-- The zero element evaluates to zero. -/
@[simp] theorem eval_zero (z : ℝ) : eval (0 : l1Weighted ν) z = 0 := by
  show ∑' n, seq (0 : l1Weighted ν) n * z^n = 0
  simp_rw [show ∀ n, seq (0 : l1Weighted ν) n = 0 from fun n => l1Weighted.zero_toSeq n,
    zero_mul]
  exact tsum_zero

/-- Evaluation of a `single` is the corresponding monomial: `eval (δ_n · x) z = x · z^n`.

This is the **monomial side** of the algebra-hom `evalAlgHom z hz` — it says
`eval` sends the canonical generators `δ_n` of the additive monoid algebra
`R[ℕ]` (here `l1Weighted ν`) to the monomials `z^n` of the polynomial algebra `R[z]`.
Combined with `single_mul` (`δ_m * δ_n = δ_{m+n}`), this is the data of `eval` as
the unique algebra hom that lifts the monoid hom `n ↦ z^n` (universal property of
the monoid algebra). The tsum collapses to a single term because `single n x` has
support `{n}`. -/
@[simp] theorem eval_single (n : ℕ) (x z : ℝ) :
    l1Weighted.eval (l1Weighted.single (ν := ν) n x) z = x * z^n := by
  unfold eval
  rw [tsum_eq_single n (fun k hk => by
    rw [show seq (l1Weighted.single (ν := ν) n x) k = 0
        from l1Weighted.single_toSeq_of_ne n k x hk]; ring)]
  rw [show seq (l1Weighted.single (ν := ν) n x) n = x
      from l1Weighted.single_toSeq_same n x]

/-- eval is additive. -/
theorem eval_add (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (a + b) z = eval a z + eval b z := by
  show ∑' n, seq (a + b) n * z ^ n = (∑' n, seq a n * z ^ n) + ∑' n, seq b n * z ^ n
  simp_rw [show ∀ n, seq (a + b) n = seq a n + seq b n from l1Weighted.add_toSeq a b, add_mul]
  exact (summable_eval a hz).tsum_add (summable_eval b hz)

/-- eval respects subtraction. -/
theorem eval_sub (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (a - b) z = eval a z - eval b z := by
  show ∑' n, seq (a - b) n * z ^ n = (∑' n, seq a n * z ^ n) - ∑' n, seq b n * z ^ n
  simp_rw [show ∀ n, seq (a - b) n = seq a n - seq b n from l1Weighted.sub_toSeq a b, sub_mul]
  exact (summable_eval a hz).tsum_sub (summable_eval b hz)

/-- eval respects scalar multiplication. -/
theorem eval_smul (r : ℝ) (a : l1Weighted ν) (z : ℝ) :
    eval (r • a) z = r * eval a z := by
  show ∑' n, seq (r • a) n * z ^ n = r * ∑' n, seq a n * z ^ n
  simp_rw [show ∀ n, seq (r • a) n = r * seq a n from l1Weighted.smul_toSeq r a, mul_assoc]
  rw [tsum_mul_left]

/-! ## Continuity bundling: `eval` as a CLM

For `|z| ≤ ν`, pointwise evaluation is a continuous linear map `l1Weighted ν →L[ℝ] ℝ`,
even *before* knowing it's an algebra hom. The opnorm bound `‖eval(·, z)‖ ≤ 1` follows
from `|eval a z| ≤ ∑' n, |a_n|·ν^n = ‖a‖`. This bundling is independent of `eval_mul`
(which is the multiplicative property), so it can be used as a building block in the
density-based proof of Mertens without circularity.

`evalAlgHom z hz` (defined further down) is the upgrade that adds the algebra-hom
structure once `eval_mul` is established. -/

/-- Pointwise evaluation `a ↦ eval a z` as a continuous ℝ-linear map (no
multiplicativity assumed). The opnorm bound is 1: `|eval a z| ≤ ‖a‖`. -/
def eval_CLM (z : ℝ) (hz : |z| ≤ ν) : l1Weighted ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => eval a z
      map_add' := fun a b => eval_add a b hz
      map_smul' := fun r a => eval_smul r a z }
    1
    (fun a => by
      show ‖eval a z‖ ≤ 1 * ‖a‖
      rw [one_mul, l1Weighted.norm_eq_tsum]
      unfold eval
      refine (norm_tsum_le_tsum_norm (summable_norm_eval a hz)).trans ?_
      refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eval a hz)
        (l1Weighted.summable_weighted a)
      simp only [Real.norm_eq_abs]; exact norm_term_le hz n)

@[simp] theorem eval_CLM_apply (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    eval_CLM z hz a = eval a z := rfl

/-- Continuity of pointwise evaluation as a function on `l1Weighted ν`. Reusable for
density / limit arguments where the algebra-hom structure is not yet available. -/
lemma continuous_eval (z : ℝ) (hz : |z| ≤ ν) :
    Continuous (fun a : l1Weighted ν => eval a z) :=
  (eval_CLM z hz).continuous

/-- The pointwise evaluation bound: `|eval a z| ≤ ‖a‖_ν` on the disk of convergence.
Repackages `eval_CLM`'s opnorm bound as a direct estimate, useful for trajectory
bounds in the f-F bridge (see `IVP/Bridge.lean`). -/
lemma abs_eval_le (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    |eval a z| ≤ ‖a‖ := by
  have h_le : ‖eval_CLM z hz a‖ ≤ ‖eval_CLM z hz‖ * ‖a‖ := (eval_CLM z hz).le_opNorm a
  have h_opn : ‖eval_CLM z hz‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have : ‖eval_CLM z hz a‖ ≤ ‖a‖ :=
    h_le.trans (mul_le_of_le_one_left (norm_nonneg _) h_opn)
  show |eval a z| ≤ _
  rw [show |eval a z| = ‖eval_CLM z hz a‖ from rfl]
  exact this

/-! ## Density-based proof of Mertens' theorem

`eval_mul` (below) is proved by a density argument reflecting the interpretation
of `l1Weighted ν` as the weighted Banach completion of the finite-support
additive monoid algebra `ℝ[ℕ]`:

1. **Monomial side** (`single_mul`, `eval_single`): the identity holds on the
   generators `δ_m, δ_n` by direct computation —
   `eval(δ_m · δ_n) z = eval(δ_{m+n}) z = z^{m+n} = z^m · z^n
                      = eval(δ_m) z · eval(δ_n) z`.

2. **Linearity side** (`eval_finset_sum`, `eval_double_finset_sum`): `eval`
   distributes over finite sums, so the monomial identity propagates to
   finite linear combinations. With `trunc_eq_sum` (in `lpWeighted.lean`),
   `trunc N a` is exactly such a finite sum — this gives `eval_mul_trunc`.

3. **Density side** (`tendsto_trunc`, `continuous_eval`): truncations converge
   in the ℓ¹ norm; `eval` is continuous (via `eval_CLM`); multiplication is
   continuous on the Banach algebra. The product-eval identity is preserved
   under the limit, giving `eval_mul`.

The hard summability content of Mertens is encapsulated in `tendsto_trunc`
(tail tsum → 0) and the Banach-algebra continuity of multiplication (norm
submultiplicativity); the body of `eval_mul_trunc` is finite-sum algebra and
`eval_mul` itself is a clean limit-passing argument. No direct invocation of
Mathlib's `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`.

**Performance note**: the limit step uses `Tendsto.mul` on `l1Weighted ν`
directly (which uses only `ContinuousMul`), NOT the more idiomatic-looking
`Continuous.comp continuous_mul`. The latter forces Lean to synthesize the
product uniform structure on `l1Weighted ν × l1Weighted ν`, which times out
(`Lean.Parser.Tactic.refine` ~4.5s, exceeds 200k heartbeats). The
`Tendsto.mul`-based formulation is ~1500× faster. -/

/-- `eval` distributes over finite sums. -/
lemma eval_finset_sum {ι : Type*} (s : Finset ι) (f : ι → l1Weighted ν)
    {z : ℝ} (hz : |z| ≤ ν) :
    eval (∑ i ∈ s, f i) z = ∑ i ∈ s, eval (f i) z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s _ ih =>
    rw [Finset.sum_cons, eval_add _ _ hz, ih, Finset.sum_cons]

/-- `eval` distributes over double finite sums. -/
lemma eval_double_finset_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → κ → l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval (∑ i ∈ s, ∑ j ∈ t, f i j) z = ∑ i ∈ s, ∑ j ∈ t, eval (f i j) z := by
  rw [eval_finset_sum _ _ hz]
  exact Finset.sum_congr rfl fun i _ => eval_finset_sum _ _ hz

/-! ## Mertens' Theorem -/

/-- Multiplicativity of `eval` on **truncations**: the finite-N step of the
density-based proof of Mertens. Both sides are finite sums of monomials, and
the identity is `single_mul` + `eval_single` + `pow_add`. Extracted as a
separate lemma so the rewrite chain doesn't compound with the limit-passing
elaboration (typeclass synthesis on `l1Weighted ν × l1Weighted ν` product
uniform structure) inside `eval_mul`. -/
lemma eval_mul_trunc (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) (N : ℕ) :
    eval (l1Weighted.trunc N a) z * eval (l1Weighted.trunc N b) z =
    eval (l1Weighted.trunc N a * l1Weighted.trunc N b) z := by
  rw [l1Weighted.trunc_eq_sum N a, l1Weighted.trunc_eq_sum N b, Finset.sum_mul_sum,
      eval_finset_sum _ _ hz, eval_finset_sum _ _ hz, Finset.sum_mul_sum,
      eval_double_finset_sum _ _ _ hz]
  apply Finset.sum_congr rfl
  rintro i -
  apply Finset.sum_congr rfl
  rintro j -
  rw [l1Weighted.single_mul, eval_single, eval_single, eval_single, pow_add]
  ring

-- ARCHIVED: classical Cauchy-product proof (kept for reference).
-- Replaced 2026-04-29 by the density-based proof below. Equivalent statement;
-- the classical version threads `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
-- and explicit antidiagonal index manipulation, while the density version
-- factors through the categorical structure (monomial → finite sum → limit).
-- See `exterior/tmp/eval_mul_density/eval_mul_density.tex` for the full
-- classical-math write-up of both versions and the performance pitfall.
--
-- theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
--     eval a z * eval b z = eval (a * b) z := by
--   unfold eval
--   rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
--     (summable_norm_eval a hz) (summable_norm_eval b hz)]
--   congr 1; ext n
--   simp only [seq, l1Weighted.toSeq_mul, CauchyProduct.apply, Finset.sum_mul]
--   apply Finset.sum_congr rfl
--   intro ⟨k, l⟩ hkl
--   simp only [Finset.mem_antidiagonal] at hkl
--   rw [mul_mul_mul_comm, ← pow_add, hkl]

/-- **Mertens' theorem** for `l1Weighted ν`: pointwise evaluation is multiplicative.

Density-based proof:
- **Truncation step** (`eval_mul_trunc`): identity holds on finite-support
  truncations by elementary monomial algebra (`single_mul` + `eval_single`).
- **Limit step**: `Tendsto.mul` on `l1Weighted ν` (Banach algebra continuity)
  + `tendsto_trunc` (density) + `continuous_eval` give `Tendsto` of both sides
  to the desired limits; `tendsto_nhds_unique` concludes.

Performance note: the proof uses `Tendsto.mul` directly on `l1Weighted ν`
rather than `Continuous.comp continuous_mul` because the latter forces Lean
to synthesize the product uniform structure on `l1Weighted ν × l1Weighted ν`,
which times out (200k heartbeats). The `Tendsto.mul` form uses only the
`ContinuousMul (l1Weighted ν)` instance — ~1500× faster. -/
theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z * eval b z = eval (a * b) z := by
  have hmul : Filter.Tendsto (fun N => l1Weighted.trunc N a * l1Weighted.trunc N b)
      Filter.atTop (𝓝 (a * b)) :=
    (l1Weighted.tendsto_trunc a).mul (l1Weighted.tendsto_trunc b)
  have hLHS : Filter.Tendsto
      (fun N => eval (l1Weighted.trunc N a * l1Weighted.trunc N b) z)
      Filter.atTop (𝓝 (eval (a * b) z)) :=
    ((continuous_eval z hz).tendsto _).comp hmul
  have hRHS : Filter.Tendsto
      (fun N => eval (l1Weighted.trunc N a) z * eval (l1Weighted.trunc N b) z)
      Filter.atTop (𝓝 (eval a z * eval b z)) :=
    (((continuous_eval z hz).tendsto _).comp (l1Weighted.tendsto_trunc a)).mul
      (((continuous_eval z hz).tendsto _).comp (l1Weighted.tendsto_trunc b))
  exact tendsto_nhds_unique hRHS (hLHS.congr (fun N => (eval_mul_trunc a b hz N).symm))

/-! ## Evaluation as Algebra Homomorphism

For `|z| ≤ ν`, pointwise evaluation `a ↦ eval a z` is a ring (in fact ℝ-algebra)
homomorphism `l1Weighted ν → ℝ`. Mertens' theorem (`eval_mul`) is what makes this
a *ring* hom — Cauchy product becomes ordinary product. ℝ-linearity (`eval_smul`)
makes it an algebra hom.

Bundling this gives `evalAlgHom z hz`, which composes cleanly with `MvPolynomial.aeval`
via `MvPolynomial.comp_aeval_apply`. This is what makes the Mertens-recursive bridge
`eval_evalBanach` (in `CompPoly.lean`) a one-liner.
-/

/-- Pointwise evaluation `a ↦ eval a z` as an ℝ-algebra homomorphism, valid on the
disk of convergence `|z| ≤ ν`. Mertens makes this a ring hom; ℝ-linearity of `eval`
makes it an algebra hom. -/
def evalAlgHom (z : ℝ) (hz : |z| ≤ ν) : l1Weighted ν →ₐ[ℝ] ℝ where
  toFun a := eval a z
  map_one' := eval_one z
  map_mul' a b := (eval_mul a b hz).symm
  map_zero' := eval_zero z
  map_add' a b := eval_add a b hz
  commutes' r := by
    show eval (algebraMap ℝ (l1Weighted ν) r) z = algebraMap ℝ ℝ r
    rw [l1Weighted.algebraMap_apply, eval_smul, eval_one, mul_one]
    rfl

@[simp] theorem evalAlgHom_apply (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    evalAlgHom z hz a = eval a z := rfl

/-- The ℝ-algebra hom `evalAlgHom` restricted to ℚ scalars. Used to compose with
`MvPolynomial.aeval` (which is over the ℚ base ring) in the Mertens-recursive bridge. -/
def evalAlgHomQ (z : ℝ) (hz : |z| ≤ ν) : l1Weighted ν →ₐ[ℚ] ℝ :=
  (evalAlgHom z hz).restrictScalars ℚ

@[simp] theorem evalAlgHomQ_apply (z : ℝ) (hz : |z| ≤ ν) (a : l1Weighted ν) :
    evalAlgHomQ z hz a = eval a z := rfl

/-! ## Term-by-term Differentiation

The proof of `hasDerivAt_eval` follows the same density skeleton as `eval_mul`:

1. **Monomial side** (`hasDerivAt_eval_single`): the derivative of
   `eval (single n x) z = x · z^n` at `t` is `n · x · t^(n-1)` — direct
   application of Mathlib's `hasDerivAt_pow` to a constant multiple.
2. **Linearity / finite-sum side**: `HasDerivAt` is linear, so for any
   finite linear combination of monomials (i.e., any `trunc N a`), the
   derivative is the corresponding finite sum of monomial derivatives.
3. **Density / uniform-limit side**: pass to the limit using the
   Weierstrass M-test (the bounding series `Σ n · |a_n| · ν'^(n-1)` is
   summable on any `ν' < ν` strictly inside the disk of convergence).

Mathlib packages steps 2–3 in a single combinator,
`hasDerivAt_tsum_of_isPreconnected`, which the proof below invokes
directly. The summability-bound work is encapsulated in
`summable_diff_bound`. We do not refactor the proof to use our toolkit
explicitly because the analytic content (the Weierstrass M-test bound)
is exactly what Mathlib's combinator handles, and re-routing through
`tendsto_trunc` would not shorten the proof. -/

/-- **Monomial side** of the density-based reading of `hasDerivAt_eval`.
Derivative of a single monomial `eval (single n x) z = x · z^n` at `t`. -/
lemma hasDerivAt_eval_single (n : ℕ) (x : ℝ) (t : ℝ) :
    HasDerivAt (fun z => l1Weighted.eval (l1Weighted.single (ν := ν) n x) z)
      ((n : ℝ) * x * t ^ (n - 1)) t := by
  have h_eq : (fun z => l1Weighted.eval (l1Weighted.single (ν := ν) n x) z) =
              fun z => x * z ^ n :=
    funext fun z => eval_single n x z
  rw [h_eq]
  have h := (hasDerivAt_pow n t).const_mul x
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Summability of the bounding sequence `n · |a_n| · ν'^(n-1)` for `ν' < ν`.
Used as the uniform bound for term-by-term differentiation of `eval` on `(-ν', ν')`.
The `n = 0` term vanishes; the shifted sum equals the absolute eval of `derivShift a` at `ν'`. -/
private theorem summable_diff_bound (a : l1Weighted ν) {ν' : ℝ}
    (hν' : ν' < (ν : ℝ)) (hν'_pos : 0 < ν') :
    Summable fun n : ℕ => |seq a n| * (n : ℝ) * ν' ^ (n - 1) := by
  have hν'_abs : |ν'| < (ν : ℝ) := by rwa [abs_of_pos hν'_pos]
  -- The shifted sequence: m ↦ |a_{m+1}| · (m+1) · ν'^m = |toSeq (derivShift a) m| · ν'^m
  have h_shifted : Summable fun m : ℕ => |seq a (m + 1)| * ((m : ℝ) + 1) * ν' ^ m := by
    refine (l1Omega.summable_abs_eval (derivShift a) hν'_abs).congr fun m => ?_
    rw [show |ν'|^m = ν'^m from by rw [abs_of_pos hν'_pos]]
    rw [derivShift_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (m : ℝ) + 1)]
    ring
  -- Match: original n=0 term is 0, original n=m+1 term equals shifted m
  rw [show (fun n : ℕ => |seq a n| * (n : ℝ) * ν' ^ (n - 1)) =
      (fun n : ℕ => match n with
        | 0 => 0
        | m + 1 => |seq a (m + 1)| * ((m : ℝ) + 1) * ν' ^ m) from by
    ext n; cases n with
    | zero => simp
    | succ m => simp only [Nat.succ_sub_one, Nat.cast_succ]]
  exact (summable_nat_add_iff (k := 1)).mp (by simpa using h_shifted)

/-- Term-by-term differentiation of `eval` strictly inside the disk of convergence:
`d/dt (Σ a_n t^n) = Σ (n+1) · a_{n+1} · t^n` for `|t| < ν`. Expressed via `derivShift`. -/
theorem hasDerivAt_eval (a : l1Weighted ν) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (l1Weighted.eval a) (l1Omega.eval (derivShift a) t) t := by
  -- Pick ν' ∈ (|t|, ν)
  obtain ⟨ν', hν'_lt_t, hν'_lt_ν⟩ : ∃ ν' : ℝ, |t| < ν' ∧ ν' < (ν : ℝ) :=
    ⟨(|t| + (ν : ℝ)) / 2, by linarith [abs_nonneg t], by linarith [ν.2]⟩
  have hν'_pos : (0 : ℝ) < ν' := lt_of_le_of_lt (abs_nonneg t) hν'_lt_t
  rw [abs_lt] at hν'_lt_t
  have h_t_mem : t ∈ Set.Ioo (-ν') ν' := ⟨hν'_lt_t.1, hν'_lt_t.2⟩
  have h_zero_mem : (0 : ℝ) ∈ Set.Ioo (-ν') ν' := ⟨by linarith, hν'_pos⟩
  -- HasDerivAt for each term
  have h_g_hasDeriv : ∀ n : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => seq a n * y^n) (seq a n * (n : ℝ) * y^(n - 1)) y := by
    intro n y
    have h := (hasDerivAt_pow n y).const_mul (seq a n)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  -- Uniform bound on (-ν', ν')
  have h_g_bound : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-ν') ν',
      ‖seq a n * (n : ℝ) * y^(n - 1)‖ ≤ |seq a n| * (n : ℝ) * ν'^(n - 1) := by
    intro n y hy
    have hy_abs : |y| ≤ ν' := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        show |((n : ℝ))| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    exact pow_le_pow_left₀ (abs_nonneg _) hy_abs _
  -- Pointwise summability at y = 0
  have h_g_summable_zero : Summable fun n : ℕ => seq a n * (0 : ℝ)^n := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := fun h => hn (by simp [h])
    simp [zero_pow this]
  -- Apply Mathlib's hasDerivAt_tsum_of_isPreconnected
  have h_main := hasDerivAt_tsum_of_isPreconnected
    (summable_diff_bound a hν'_lt_ν hν'_pos)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y _ => h_g_hasDeriv n y)
    h_g_bound h_zero_mem h_g_summable_zero h_t_mem
  -- Σ' n, seq a n * n * t^(n-1) = l1Omega.eval (derivShift a) t
  have h_summable : Summable fun n : ℕ => seq a n * (n : ℝ) * t^(n - 1) := by
    refine Summable.of_norm_bounded
      (g := fun n => |seq a n| * (n : ℝ) * ν'^(n - 1))
      (summable_diff_bound a hν'_lt_ν hν'_pos)
      (fun n => h_g_bound n t h_t_mem)
  have h_deriv_eq :
      (∑' n, seq a n * (n : ℝ) * t^(n - 1)) =
        l1Omega.eval (derivShift a) t := by
    rw [l1Omega.eval]
    -- The n=0 term is 0; for n=m+1, it is `(m+1) * a_{m+1} * t^m`.
    rw [h_summable.tsum_eq_zero_add]
    simp only [Nat.zero_sub, pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_add]
    refine tsum_congr fun m => ?_
    rw [derivShift_apply]
    push_cast
    ring
  change HasDerivAt (fun z => ∑' n, seq a n * z ^ n) (l1Omega.eval (derivShift a) t) t
  rw [← h_deriv_eq]
  exact h_main

end l1Weighted

end
