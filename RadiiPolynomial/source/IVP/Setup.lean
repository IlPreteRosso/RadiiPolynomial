import RadiiPolynomial.source.BlockDiag.Concrete
import RadiiPolynomial.source.lpSpace.OmegaWeighted
import RadiiPolynomial.source.lpSpace.lpWeightedDeriv

/-!
# Generic IVP Map Infrastructure

Equation-independent definitions and lemmas for IVP zero-finding problems.
Parameterized by a nonlinearity `φ : XL1 ν L → Fin L → l1Weighted ν`.

## The IVP Zero-Finding Problem

Given an ODE system `ẋ = f(x)` with `x(0) = x₀`, the Taylor coefficient
zero-finding map is:
```
  F(a)_l_0     = a_{l,0} - (x₀)_l
  F(a)_l_{k+1} = (k+1) · a_{l,k+1} - φ_l(a)_k
```
where `φ` encodes `f` at the sequence level (Cauchy products for nonlinear terms).

The composed map `G = A ∘ F : XL1 → XL1` (with `A` the approximate inverse) is
the Newton-like map for the radii polynomial theorem.

## What This File Provides (equation-independent)

1. `ivpCoeffs` — the F coefficient formula
2. `ivpMap` — the composed map G = A.action(F)
3. `fderiv_ivpMap_coeff_at` — chain rule for G coefficients
4. `ivp_Y₀_le`, `ivp_Z₁_le`, `ivp_Z₂_le` — generic bounds for the radii polynomial
5. `ivpTail` + `ivpFinCorrection` — decomposition for differentiability
6. `differentiable_ivpMap` — G is differentiable (from φ differentiability)
7. `fderiv_ivpMap_tail` — fderiv of G on tail modes

## What Stays Equation-Specific

- `f` definition (the polynomial vector field, e.g. `f` in `Example83.Algebra`)
- `differentiable_f_component` (typically `fun_prop`)
- Fderiv structure of `f` (via `auto_poly_fderiv`)
- ℚ mirrors and bridges
-/

open scoped BigOperators Topology
open RadiiPolynomial

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-! ## 1. IVP Coefficient Formula -/

/-- IVP zero-finding coefficients (Ref: Eq. 8.15, p.195):
`F(a)_l_0 = a_{l,0} - x_{0,l}` and `F(a)_l_{k+1} = (k+1)·a_{l,k+1} - φ_l(a)_k`.
The factor `(k+1)` means `F(a) ∈ (ℓ¹_ω)^L` rather than `(ℓ¹_ν)^L`
(Proposition 10.1.1), where `ω_k = ν^{k+1}/(k+1)`. -/
def ivpCoeffs (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (a : XL1 ν L) (l : Fin L) (n : ℕ) : ℝ :=
  match n with
  | 0 => l1Weighted.toSeq (a l) 0 - x₀ l
  | n + 1 => ((n : ℝ) + 1) * l1Weighted.toSeq (a l) (n + 1) -
      l1Weighted.toSeq (φ a l) n

/-! ## 2. Composed Map G = A.action(ivpCoeffs) -/

/-- The composed map G = A ∘ F : XL1 → XL1.
Defined at the coefficient level: `A.action` applied to `ivpCoeffs`.
The caller provides `hmem` proving ℓ¹_ν membership of each component.

In practice, `hmem` follows from the tail structure: when `A.tailDiag = 1/n`,
the tail term `(1/n)((n)a_n - φ_{n-1}) = a_n - φ_{n-1}/n` is ℓ¹_ν-summable.
This is equation-specific (depends on the tail structure of A). -/
def ivpMap (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (a : XL1 ν L) : XL1 ν L := fun l =>
  l1Weighted.mk (A.action (ivpCoeffs φ x₀ a) l) (hmem a l)

omit [NeZero L] in
/-- G at the coefficient level. -/
lemma ivpMap_coeff (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (a : XL1 ν L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (ivpMap A φ x₀ hmem a l) n =
      A.action (ivpCoeffs φ x₀ a) l n := by
  simp [ivpMap, l1Weighted.mk]; rfl

/-! ## 3. Tail Decomposition -/

/-- The "tail" part of G: `a l - shiftDivN_CLM(φ(a) l)`.
On modes n > N, this equals G exactly (up to the finite block structure of A).
Manifestly differentiable when φ is differentiable. -/
def ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (a : XL1 ν L) : XL1 ν L := fun l =>
  a l - shiftDivN_CLM (φ a l)

omit [NeZero L] in
lemma differentiable_ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l)) :
    Differentiable ℝ (ivpTail φ) := by
  intro a; apply differentiableAt_pi.mpr; intro l
  show DifferentiableAt ℝ (fun a : XL1 ν L => a l - shiftDivN_CLM (φ a l)) a
  have h1 : DifferentiableAt ℝ (fun a : XL1 ν L => a l) a :=
    differentiableAt_pi.mp differentiableAt_id l
  exact h1.sub (shiftDivN_CLM.differentiableAt.comp a (hφ l a))

/-! ## 4. Fderiv on Tail Modes -/

omit [NeZero L] in
/-- Extract component `l` from `fderiv ℝ F a h` when `F : XL1 → XL1`.
Built on Mathlib's `fderiv_apply`. -/
private lemma fderiv_apply_component {F : XL1 ν L → XL1 ν L} {a : XL1 ν L}
    (hF : DifferentiableAt ℝ F a) (h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ F a h) l = (fderiv ℝ (fun x => F x l) a) h := by
  rw [fderiv_apply hF l]; rfl

omit [NeZero L] in
/-- Fderiv of ivpTail at `ā` applied to `h`:
`(fderiv(ivpTail)(ā)(h)) l = h l - shiftDivN_CLM((fderiv(φ·l)(ā))(h))`.
Used for Z₁ bound (tail difference = shiftDivN of Dφ). -/
lemma fderiv_ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ (ivpTail φ) ā h) l =
      h l - shiftDivN_CLM ((fderiv ℝ (fun a => φ a l) ā) h) := by
  rw [fderiv_apply_component (differentiable_ivpTail φ hφ ā) h l]
  exact (((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin L => l1Weighted ν) l).hasFDerivAt).sub
    (shiftDivN_CLM.hasFDerivAt.comp ā (hφ l ā).hasFDerivAt)).fderiv ▸ by simp

/-! ## 5. Generic Z₁ Tail Bound

For the Z₁ bound, the difference `composedApprox.toCLM - fderiv G ā` satisfies:
- On finite modes (n ≤ N): zero (by construction of composedApprox)
- On tail modes (n > N): equals `shiftDivN_CLM(Dφ(h) l)` (since composedApprox tail = id)

The per-component norm is then bounded by `ν/(N+1) * ‖Dφ(h) l‖` via `shiftDivN_tailTsum_le_div`.

This section provides the generic Z₁ component bound, parameterized by:
- `hfin`: finite modes agree (equation-specific, from composedApprox construction)
- `htail_diff`: tail difference = shiftDivN(Dφ) (from `fderiv_ivpTail`)
- `hcomp_tail`: composedApprox tail = identity -/

/-- Generic Z₁ per-component bound.
Given that finite modes cancel and the tail difference is `shiftDivN(Dφ(h) l)`,
the component norm is bounded by `ν/(N+1) * ‖Dφ(h) l‖`. -/
private lemma Z₁_component_le
    (composedApprox : SystemBlockDiagData L N)
    (G : XL1 ν L → XL1 ν L) (ā : XL1 ν L)
    (Dφ : XL1 ν L → Fin L → l1Weighted ν)
    -- Finite modes: composedApprox = fderiv G on n ≤ N
    (hfin : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n = 0)
    -- Tail: difference = shiftDivN(Dφ)
    (htail : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) n)
    (h : XL1 ν L) (l : Fin L) :
    ‖((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l‖ ≤
      (ν : ℝ) / ((N : ℝ) + 1) * ‖Dφ h l‖ := by
  -- Step 1: finite part = 0 → norm = tail tsum starting at N+1
  rw [l1Weighted.norm_eq_tailTsum_of_fin_zero _ (N + 1)
    (fun n hn => hfin h l n (by omega))]
  -- Step 2: rewrite tail terms using htail
  have htail' : ∀ n, |l1Weighted.toSeq
      (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) (n + (N + 1))| =
      |l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) (n + (N + 1))| :=
    fun n => congrArg (|·|) (htail h l (n + (N + 1)) (by omega))
  simp_rw [htail', shiftDivN_CLM_apply]
  -- Step 3: apply shiftDivN_tailTsum_le_div
  exact shiftDivN_tailTsum_le_div (Dφ h l) N

/-- **Generic Z₁ bound**: `‖composedApprox.toCLM - fderiv G ā‖ ≤ Z₁`.
Chains `Z₁_component_le` with per-component Dφ norm bound.

The caller provides:
- `hfin`: finite modes agree (from composedApprox = fderiv G on n ≤ N)
- `htail`: tail difference = shiftDivN(Dφ)
- `hDφ`: per-component `‖Dφ(h) l‖ ≤ K * ‖h‖`
- `hZ₁`: `ν/(N+1) * K ≤ Z₁` -/
lemma ivp_Z₁_le
    (composedApprox : SystemBlockDiagData L N)
    (G : XL1 ν L → XL1 ν L) (ā : XL1 ν L)
    (Dφ : XL1 ν L → Fin L → l1Weighted ν)
    (hfin : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n = 0)
    (htail : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) n)
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ : ∀ h : XL1 ν L, ∀ l : Fin L, ‖Dφ h l‖ ≤ K * ‖h‖)
    {Z₁ : ℝ} (hZ₁ : (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁) :
    ‖composedApprox.toCLM (ν := ν) - fderiv ℝ G ā‖ ≤ Z₁ := by
  have hν : (0 : ℝ) ≤ (ν : ℝ) / ((N : ℝ) + 1) := div_nonneg ν.coe_nonneg (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (mul_nonneg hν hK) hZ₁)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (le_trans (mul_nonneg hν hK) hZ₁)
    (norm_nonneg _))).mpr fun l => ?_
  calc ‖((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l‖
      ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖Dφ h l‖ := Z₁_component_le composedApprox G ā Dφ hfin htail h l
    _ ≤ (ν : ℝ) / ((N : ℝ) + 1) * (K * ‖h‖) := mul_le_mul_of_nonneg_left (hDφ h l) hν
    _ ≤ Z₁ * ‖h‖ := by nlinarith [norm_nonneg h]

/-! ## 6. Generic Y₀ Bound

The Y₀ bound `‖G(ā)‖ ≤ C` reduces to:
1. `G(ā) = A.toCLM(F_abar)` where `F_abar = ofCoeff(ivpCoeffs ā)`
2. `norm_toCLM_apply_le` reduces `‖A.toCLM(F_abar)‖` to per-component finite sums
3. `finsum_bound` closes each component sum

The generic lemma packages step 1 (ivpMap → A.toCLM connection) so the caller
just provides: ℚ bridge, support bound, A data bridges, and per-component bounds. -/

omit [NeZero L] in
/-- **Generic Y₀ bound**: `‖ivpMap A φ x₀ hmem ā‖ ≤ C`.

Reduces to per-component finite sums of `|A.action(ivpCoeffs ā) l n| * ν^n`,
which the caller closes via `finsum_bound using systemBlockDiagActionEval`.

Takes:
- `S`: support bound for `ivpCoeffs φ x₀ ā` (typically `2*N+1` for degree-2 φ)
- `hsupport`: `ivpCoeffs` vanishes beyond S
- `hmem_coeff`: membership proof for `ofCoeff`
- `hcoeff_eq`: G(ā) = A.action(ivpCoeffs ā) at the sequence level
- `hcomp`: per-component bound (user closes with `finsum_bound`) -/
lemma ivp_Y₀_le
    (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (ā : XL1 ν L) (S : ℕ) (hSN : N ≤ S)
    -- Support bound: ivpCoeffs vanishes beyond S
    (hsupport : ∀ l : Fin L, ∀ n, S < n → ivpCoeffs φ x₀ ā l n = 0)
    {C : ℝ} (hC : 0 ≤ C)
    -- Per-component bound (closed by finsum_bound using systemBlockDiagActionEval)
    (hcomp : ∀ l : Fin L,
      ∑ n ∈ Finset.Icc 0 S,
        |A.action (ivpCoeffs φ x₀ ā) l n| * (ν : ℝ) ^ n ≤ C) :
    ‖ivpMap A φ x₀ hmem ā‖ ≤ C := by
  -- Step 1: ‖G(ā)‖ = sup_l ‖G(ā) l‖ where G(ā) l = l1Weighted.mk(A.action(...))
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun l => ?_
  -- Step 2: ‖G(ā) l‖ = finite sum (support bound from A.toCLM_support)
  rw [l1Weighted.norm_eq_Icc_sum_of_support (ivpMap A φ x₀ hmem ā l) S
    (fun n hn => by
      simp only [ivpMap, l1Weighted.mk_apply]
      rw [SystemBlockDiagData.action_tail _ _ _ _ (by omega : N < n)]
      rw [hsupport l n hn, mul_zero])]
  -- Step 3: rewrite toSeq to A.action
  simp_rw [show ∀ n, l1Weighted.toSeq (ivpMap A φ x₀ hmem ā l) n =
    A.action (ivpCoeffs φ x₀ ā) l n from fun n => by simp [ivpMap, l1Weighted.mk]; rfl]
  exact hcomp l

/-! ## 7. Differentiability of IVP Coefficients

Each `ivpCoeffs φ x₀ · j k` is differentiable, and the fderiv difference at two
points yields the shifted Dφ difference pattern:
- k = 0: difference = 0 (affine in a, constant fderiv)
- k = n + 1: difference = −(Dφ_diff l h)_n -/

omit [NeZero L] in
/-- `ivpCoeffs φ x₀ · j k` is differentiable for all k. -/
lemma differentiable_ivpCoeffs (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (j : Fin L) (k : ℕ) :
    Differentiable ℝ (fun a : XL1 ν L => ivpCoeffs φ x₀ a j k) := by
  simp only [ivpCoeffs]
  cases k with
  | zero =>
    exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j).differentiable)).sub (differentiable_const _)
  | succ n =>
    exact (differentiable_const _ |>.mul
      ((l1Weighted.toSeq_CLM (n + 1)).differentiable.comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j).differentiable))).sub
      ((l1Weighted.toSeq_CLM n).differentiable.comp (hφ j))

omit [NeZero L] in
/-- The derivative of the initial-condition row selects the zeroth coefficient. -/
lemma fderiv_ivpCoeffs_zero_apply (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ) (a h : XL1 ν L) (j : Fin L) :
    (fderiv ℝ (fun x => ivpCoeffs φ x₀ x j 0) a) h =
      l1Weighted.toSeq (h j) 0 := by
  rw [show (fun x : XL1 ν L => ivpCoeffs φ x₀ x j 0) =
      fun x => l1Weighted.toSeq (x j) 0 - x₀ j from funext fun _ => rfl,
    fderiv_sub_const,
    show (fun x : XL1 ν L => l1Weighted.toSeq (x j) 0) =
      ⇑((l1Weighted.toSeq_CLM (ν := ν) 0).comp
        (ContinuousLinearMap.proj j)) from rfl,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rfl

omit [NeZero L] in
/-- The derivative of a positive IVP row is its diagonal linear term minus `Dφ`. -/
lemma fderiv_ivpCoeffs_succ_apply (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (a h : XL1 ν L) (j : Fin L) (n : ℕ)
    (hφ : DifferentiableAt ℝ (fun x => φ x j) a) :
    (fderiv ℝ (fun x => ivpCoeffs φ x₀ x j (n + 1)) a) h =
      ((n : ℝ) + 1) * l1Weighted.toSeq (h j) (n + 1) -
        l1Weighted.toSeq ((fderiv ℝ (fun x => φ x j) a) h) n := by
  have hfd : HasFDerivAt (fun x : XL1 ν L => ivpCoeffs φ x₀ x j (n + 1))
      (((n : ℝ) + 1) • ((l1Weighted.toSeq_CLM (n + 1)).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin L => l1Weighted ν) j)) -
        (l1Weighted.toSeq_CLM (ν := ν) n).comp
          (fderiv ℝ (fun x => φ x j) a)) a := by
    show HasFDerivAt (fun x => ((n : ℝ) + 1) *
      l1Weighted.toSeq (x j) (n + 1) - l1Weighted.toSeq (φ x j) n) _ a
    exact (((l1Weighted.toSeq_CLM (n + 1)).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin L => l1Weighted ν) j)).hasFDerivAt.const_mul
          ((n : ℝ) + 1)).sub
      ((l1Weighted.toSeq_CLM n).hasFDerivAt.comp a hφ.hasFDerivAt)
  rw [hfd.fderiv]
  rfl

omit [NeZero L] in
/-- Fderiv difference of `ivpCoeffs` at two points: only the φ-fderiv difference survives.
The linear part `(k+1) * toSeq(a j)(k+1)` has constant fderiv (cancels in difference). -/
private lemma fderiv_ivpCoeffs_diff (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (c ā h : XL1 ν L) (j : Fin L) (k : ℕ) :
    (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j k) c) h -
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j k) ā) h =
      if k = 0 then 0
      else -(l1Weighted.toSeq ((fderiv ℝ (fun x => φ x j) c -
              fderiv ℝ (fun x => φ x j) ā) h) (k - 1)) := by
  cases k with
  | zero =>
    simp only [ite_true]
    rw [fderiv_ivpCoeffs_zero_apply φ x₀ c h j,
      fderiv_ivpCoeffs_zero_apply φ x₀ ā h j, sub_self]
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    rw [fderiv_ivpCoeffs_succ_apply φ x₀ c h j n (hφ j c),
      fderiv_ivpCoeffs_succ_apply φ x₀ ā h j n (hφ j ā)]
    simp only [sub_apply, l1Weighted.sub_toSeq]; ring

omit [NeZero L] in
/-- Chain rule: `toSeq(fderiv(ivpMap A φ x₀) a h l) n = fderiv(a ↦ A.action(F a) l n) a h`.
Used for Z₁ finite-mode cancellation and Z₂ factorization. -/
lemma fderiv_ivpMap_coeff_at
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (hG_diff : Differentiable ℝ (ivpMap A φ x₀ hmem))
    (a h : XL1 ν L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq ((fderiv ℝ (ivpMap A φ x₀ hmem) a h) l) n =
      (fderiv ℝ (fun a => A.action (ivpCoeffs φ x₀ a) l n) a) h := by
  rw [fderiv_apply_component (hG_diff a) h l]
  show l1Weighted.toSeq_CLM (ν := ν) n ((fderiv ℝ (fun x => ivpMap A φ x₀ hmem x l) a) h) = _
  rw [← ContinuousLinearMap.comp_apply (l1Weighted.toSeq_CLM (ν := ν) n),
    ← ContinuousLinearMap.fderiv (l1Weighted.toSeq_CLM (ν := ν) n),
    ← fderiv_comp a (l1Weighted.toSeq_CLM (ν := ν) n).differentiableAt
      ((differentiableAt_pi.mp (hG_diff a)) l),
    show (l1Weighted.toSeq_CLM (ν := ν) n ∘ fun x => ivpMap A φ x₀ hmem x l) =
      fun x => A.action (ivpCoeffs φ x₀ x) l n from funext fun x => ivpMap_coeff A φ x₀ hmem x l n]

/-! ## 8. Generic Z₂ Bound

The Z₂ bound `‖fderiv(ivpMap) c - fderiv(ivpMap) ā‖ ≤ Z₂ * r` for c ∈ B(ā, r) follows from:
1. **Chain rule** via `fderiv_ivpMap_coeff_at`: reduces to `A.action(fderiv_diff(F))`
2. **Factorization**: `fderiv_diff(G)(h) = A.toCLM(w)` where w is shifted Dφ difference
3. **w norm bound** via `norm_mk_shift_neg_le`: `‖w‖ ≤ C·ν·‖c-ā‖·‖h‖`
4. **Block norm bound**: `‖A.toCLM(w) l‖ ≤ restricted_norm(l) * ‖w‖`
5. **Evaluation** (caller): `C·ν·restricted_norm(l) ≤ Z₂_val` via `native_decide` -/

lemma ivp_Z₂_le
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (ā : XL1 ν L)
    (hG_diff : Differentiable ℝ (ivpMap A φ x₀ hmem))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (active : Finset (Fin L))
    (hzero : ∀ (c : XL1 ν L) (h : XL1 ν L) (j : Fin L), j ∉ active →
      (fderiv ℝ (fun x => φ x j) c - fderiv ℝ (fun x => φ x j) ā) h = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hDφ_diff : ∀ (c : XL1 ν L) (h : XL1 ν L) (l : Fin L),
      ‖(fderiv ℝ (fun x => φ x l) c - fderiv ℝ (fun x => φ x l) ā) h‖ ≤
        C * ‖c - ā‖ * ‖h‖)
    {Z₂_val : ℝ} (hZ₂_nn : 0 ≤ Z₂_val)
    (hcomp_le : ∀ l : Fin L,
      C * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
        if l ∈ active then A.tailBound else 0) ≤ Z₂_val)
    {r : ℝ} (c : XL1 ν L) (hc : c ∈ Metric.closedBall ā r) :
    ‖fderiv ℝ (ivpMap A φ x₀ hmem) c - fderiv ℝ (ivpMap A φ x₀ hmem) ā‖ ≤ Z₂_val * r := by
  set G := ivpMap A φ x₀ hmem
  suffices h : ‖fderiv ℝ G c - fderiv ℝ G ā‖ ≤ Z₂_val * ‖c - ā‖ from
    h.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hc) hZ₂_nn)
  set F := ivpCoeffs φ x₀
  have hF_diff : ∀ j k, Differentiable ℝ (fun a : XL1 ν L => F a j k) :=
    fun j k => differentiable_ivpCoeffs φ x₀ hφ j k
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hZ₂_nn (norm_nonneg _))
  intro h'
  rw [sub_apply]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hZ₂_nn
    (norm_nonneg _)) (norm_nonneg _))).mpr fun l => ?_
  -- Construct w: shifted Dφ difference
  have hmem_w : ∀ j : Fin L, l1Weighted.Mem ν
      (fun n => if n = 0 then (0 : ℝ) else
        -l1Weighted.toSeq (((fderiv ℝ (fun x => φ x j) c -
          fderiv ℝ (fun x => φ x j) ā) h')) (n - 1)) := by
    intro j; rw [l1Weighted.mem_iff]
    exact (l1Weighted.summable_shifted_weighted
      ((fderiv ℝ (fun x => φ x j) c -
        fderiv ℝ (fun x => φ x j) ā) h')).of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _))
      (fun n => by split_ifs with h0 <;> simp only [abs_neg, abs_zero, zero_mul, le_refl,
        mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _)])
  set w : XL1 ν L := fun j => l1Weighted.mk _ (hmem_w j)
  have hcd : ∀ j k, (fderiv ℝ (fun a => F a j k) c) h' -
      (fderiv ℝ (fun a => F a j k) ā) h' = toCoeff (ν := ν) w j k := fun j k => by
    rw [fderiv_ivpCoeffs_diff φ x₀ hφ c ā h' j k]
    show _ = l1Weighted.toSeq (w j) k; simp [w]
  -- Factorization: (diff G h') l = A.toCLM(w) l
  have hseq : ∀ n, l1Weighted.toSeq (fderiv ℝ G c h' l - fderiv ℝ G ā h' l) n =
      l1Weighted.toSeq (A.toCLM (ν := ν) w l) n := fun n => by
    rw [l1Weighted.sub_toSeq, fderiv_ivpMap_coeff_at A φ x₀ hmem hG_diff c h' l n,
      fderiv_ivpMap_coeff_at A φ x₀ hmem hG_diff ā h' l n]
    change _ = toCoeff (ν := ν) (A.toCLM (ν := ν) w) l n
    rw [SystemBlockDiagData.toCoeff_toCLM]
    by_cases hn : n ≤ N
    · rw [A.fderiv_action_fin F (fun j k => hF_diff j k) l n hn c h',
        A.fderiv_action_fin F (fun j k => hF_diff j k) l n hn ā h']
      simp only [SystemBlockDiagData.action_finite _ _ _ _ hn,
        ← Finset.sum_sub_distrib, ← mul_sub]; simp_rw [hcd]
    · push Not at hn
      simp_rw [show (fun a => A.action (ivpCoeffs φ x₀ a) l n) =
          fun a => A.tailDiag l n * ivpCoeffs φ x₀ a l n from
        funext fun a => SystemBlockDiagData.action_tail _ _ _ _ hn]
      have hd := fun a => ((hF_diff l n a).hasFDerivAt.const_mul (A.tailDiag l n)).fderiv
      rw [hd c, hd ā]
      simp only [smul_apply, smul_eq_mul, ← mul_sub, hcd,
        SystemBlockDiagData.action_tail _ _ _ _ hn]
  rw [show ((fderiv ℝ G c h' - fderiv ℝ G ā h') : XL1 ν L) l = A.toCLM (ν := ν) w l from by
    show (fderiv ℝ G c h') l - (fderiv ℝ G ā h') l = _; exact l1Weighted.ext hseq]
  have hw_zero : ∀ j, j ∉ active → w j = 0 := fun j hj => l1Weighted.ext fun k => by
    show (if k = 0 then (0 : ℝ) else _) = 0
    simp only [hzero c h' j hj, l1Weighted.zero_toSeq, neg_zero, ite_self]
  have hw_norm : ‖w‖ ≤ C * (ν : ℝ) * ‖c - ā‖ * ‖h'‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hC (PosReal.coe_nonneg _)) (norm_nonneg _)) (norm_nonneg _))).mpr fun j =>
      (l1Weighted.norm_mk_shift_neg_le _ (hmem_w j)).trans
        (mul_le_mul_of_nonneg_left (hDφ_diff c h' j) (PosReal.coe_nonneg _)) |>.trans_eq (by ring)
  -- Assembly
  set R := (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
    if l ∈ active then A.tailBound else 0
  refine (A.norm_toCLM_component_le_restricted w l active hw_zero).trans
    ((mul_le_mul_of_nonneg_left hw_norm (add_nonneg
      (Finset.sum_nonneg fun j _ => blockEntryNorm_nonneg A.finBlock l j)
      (by split <;> [exact A.tailBound_nonneg_at l; exact le_refl _]))).trans ?_)
  rw [show R * (C * ↑ν * ‖c - ā‖ * ‖h'‖) = C * ↑ν * R * ‖c - ā‖ * ‖h'‖ from by ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hcomp_le l) (norm_nonneg _)) (norm_nonneg _)

/-! ## 9. IVP Map Decomposition and Differentiability

When the approximate inverse has IVP tail structure `A.tailDiag l n = 1/n` for `n > N`,
the composed map `ivpMap A φ x₀` decomposes as:

  G = ivpTail + ivpFinCorrection

where:
- `ivpTail φ a l = a l - shiftDivN_CLM(φ a l)` (manifestly differentiable)
- `ivpFinCorrection` is supported on modes 0..N (differentiable by finite support)

This gives generic differentiability of `ivpMap` and the fderiv coefficient chain rule. -/

omit [NeZero L] in
/-- ℓ¹ membership for `ivpMap` when `A.tailDiag = 1/n` on tail modes.
The tail term `(1/n)((n)·a_n - φ_{n-1}) = a_n - φ_{n-1}/n` is bounded by
`|a_n| + |φ_{n-1}|`, hence ℓ¹-summable. -/
lemma ivpMap_mem_of_tailDiag_inv
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (a : XL1 ν L) (l : Fin L) :
    l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l) :=
  l1Weighted.mem_of_eventually_le_add_shift _ (a l) (φ a l) N fun n hn => by
    rw [SystemBlockDiagData.action_tail _ _ _ _ hn, htail l n hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ivpCoeffs, Nat.add_sub_cancel]
    rw [show (1 : ℝ) / (↑(m + 1) : ℝ) = ((m : ℝ) + 1)⁻¹ from by push_cast; exact one_div _]
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [abs_mul, abs_inv, abs_of_nonneg hpos.le, inv_mul_le_iff₀ hpos]
    exact ((abs_sub _ _).trans (by rw [abs_mul, abs_of_nonneg hpos.le])).trans
      (by nlinarith [abs_nonneg (l1Weighted.toSeq (φ a l) m),
        Nat.cast_nonneg (α := ℝ) m])

omit [NeZero L] in
/-- On tail modes (n > N), `ivpMap` agrees with `ivpTail` when `A.tailDiag = 1/n`. -/
private lemma ivpMap_tail_eq_ivpTail
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (a : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action (ivpCoeffs φ x₀ a) l n =
      l1Weighted.toSeq (ivpTail φ a l) n := by
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn, htail l n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [ivpCoeffs, ivpTail, l1Weighted.sub_toSeq,
    shiftDivN_CLM_apply, shiftDivN_succ_mode]
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp; push_cast; ring

/-- The finite correction sequence: `A.action(F a) - ivpTail`.
Zero for n > N by `ivpMap_tail_eq_ivpTail`. -/
private def ivpCorrectionSeq
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (a : XL1 ν L) (l : Fin L) (n : ℕ) : ℝ :=
  A.action (ivpCoeffs φ x₀ a) l n - l1Weighted.toSeq (ivpTail φ a l) n

omit [NeZero L] in
private lemma ivpCorrectionSeq_zero_tail
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (a : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    ivpCorrectionSeq A φ x₀ a l n = 0 := by
  simp only [ivpCorrectionSeq, ivpMap_tail_eq_ivpTail A φ x₀ htail a l n hn, sub_self]

/-- The finite correction: `ivpMap - ivpTail`, supported on modes 0..N. -/
def ivpFinCorrection
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (a : XL1 ν L) : XL1 ν L := fun l =>
  l1Weighted.mk (ivpCorrectionSeq A φ x₀ a l) (by
    rw [l1Weighted.mem_iff]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) fun n hn => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp [ivpCorrectionSeq_zero_tail A φ x₀ htail a l n (by omega)])

omit [NeZero L] in
/-- `ivpMap = ivpTail + ivpFinCorrection`. -/
lemma ivpMap_eq_tail_plus_correction
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (a : XL1 ν L) (l : Fin L) :
    ivpMap A φ x₀ hmem a l =
      ivpTail φ a l + ivpFinCorrection A φ x₀ htail a l := by
  apply l1Weighted.ext; intro n
  simp only [l1Weighted.add_toSeq, ivpFinCorrection, l1Weighted.mk_apply, ivpCorrectionSeq,
    ivpTail, l1Weighted.sub_toSeq, shiftDivN_CLM_apply]
  show A.action (ivpCoeffs φ x₀ a) l n = _; ring

omit [NeZero L] in
/-- Each coefficient of the finite correction is differentiable in `a`. -/
private lemma differentiable_ivpCorrectionSeq_fin
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (l : Fin L) (k : Fin (N + 1)) :
    Differentiable ℝ (fun a : XL1 ν L => ivpCorrectionSeq A φ x₀ a l k) := by
  simp only [ivpCorrectionSeq]
  exact (A.differentiable_action_fin (ivpCoeffs φ x₀)
    (fun j k => differentiable_ivpCoeffs φ x₀ hφ j ↑k) l ↑k (by omega)).sub
    (fun a => ((l1Weighted.toSeq_CLM (ν := ν) ↑k).differentiableAt.comp a
      (differentiableAt_pi.mp differentiableAt_id l)).sub
      ((l1Weighted.toSeq_CLM (ν := ν) ↑k).differentiableAt.comp a
        (shiftDivN_CLM.differentiableAt.comp a (hφ l a))))

omit [NeZero L] in
/-- The finite correction is differentiable. -/
lemma differentiable_ivpFinCorrection
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l)) :
    Differentiable ℝ (ivpFinCorrection A φ x₀ htail) := by
  intro a; apply differentiableAt_pi.mpr; intro l
  exact l1Weighted.differentiable_mk_of_finSupp
    (fun a => ivpCorrectionSeq A φ x₀ a l) N
    (fun a n hn => ivpCorrectionSeq_zero_tail A φ x₀ htail a l n hn)
    _ (fun k => differentiable_ivpCorrectionSeq_fin A φ x₀ hφ l k) a

omit [NeZero L] in
/-- The IVP composed map is differentiable (decomposition: `ivpTail + ivpFinCorrection`). -/
lemma differentiable_ivpMap
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l)) :
    Differentiable ℝ (ivpMap A φ x₀ hmem) := by
  have hdecomp : ivpMap A φ x₀ hmem = fun a l =>
      ivpTail φ a l + ivpFinCorrection A φ x₀ htail a l :=
    funext fun a => funext fun l => ivpMap_eq_tail_plus_correction A φ x₀ htail hmem a l
  rw [hdecomp]
  exact (differentiable_ivpTail φ hφ).add (differentiable_ivpFinCorrection A φ x₀ htail hφ)

omit [NeZero L] in
/-- Fderiv of `ivpFinCorrection` vanishes on tail modes (n > N). -/
lemma fderiv_ivpFinCorrection_zero_tail
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq ((fderiv ℝ (ivpFinCorrection A φ x₀ htail) ā h) l) n = 0 := by
  rw [fderiv_apply_component (differentiable_ivpFinCorrection A φ x₀ htail hφ ā) h l]
  exact l1Weighted.fderiv_mk_of_finSupp_toSeq_tail
    (fun a => ivpCorrectionSeq A φ x₀ a l) N
    (fun a m hm => ivpCorrectionSeq_zero_tail A φ x₀ htail a l m hm)
    _ (fun k => differentiable_ivpCorrectionSeq_fin A φ x₀ hφ l k) ā h n hn

omit [NeZero L] in
/-- Fderiv of `ivpMap` on tail modes equals fderiv of `ivpTail`.
Used for Z₁: the tail difference reduces to `shiftDivN(Dφ)`. -/
lemma fderiv_ivpMap_tail
    (A : SystemBlockDiagData L N)
    (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (↑n : ℝ))
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      l1Weighted.Mem ν (A.action (ivpCoeffs φ x₀ a) l))
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq ((fderiv ℝ (ivpMap A φ x₀ hmem) ā h) l) n =
      l1Weighted.toSeq ((fderiv ℝ (ivpTail φ) ā h) l) n := by
  have hdecomp : ivpMap A φ x₀ hmem = fun a l =>
      ivpTail φ a l + ivpFinCorrection A φ x₀ htail a l :=
    funext fun a => funext fun l => ivpMap_eq_tail_plus_correction A φ x₀ htail hmem a l
  have hfadd : fderiv ℝ (ivpMap A φ x₀ hmem) ā = fderiv ℝ (ivpTail φ) ā +
      fderiv ℝ (ivpFinCorrection A φ x₀ htail) ā := by
    rw [hdecomp]; exact fderiv_add (differentiable_ivpTail φ hφ ā)
      (differentiable_ivpFinCorrection A φ x₀ htail hφ ā)
  rw [hfadd]; simp only [add_apply, Pi.add_apply, l1Weighted.add_toSeq,
    fderiv_ivpFinCorrection_zero_tail A φ x₀ htail hφ ā h l n hn, add_zero]

end IVP

/-! ## CLM Operator Norm Bound for shiftDivN

Exposed here (rather than in `OmegaWeighted.lean`) because the `Norm` instance for
`ContinuousLinearMap` requires the operator-norm imports available in this file. -/

namespace l1Weighted

variable {ν : PosReal}

/-- Operator norm bound: `‖S_{/n}‖ ≤ ν` (shift-divide by n). -/
private lemma norm_shiftDivN_CLM_le : ‖shiftDivN_CLM (ν := ν)‖ ≤ (ν : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (le_of_lt ν.prop) _

end l1Weighted
