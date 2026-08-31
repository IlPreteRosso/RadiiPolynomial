import RadiiPolynomial.Core.Transport
import RadiiPolynomial.Core.AffineZ2
import RadiiPolynomial.Examples.PowerSeries.Example77.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered

/-!
# κ-transport toy instance: Example 7.7's equation at ν = 2

The B side is `l1Weighted ν₂` at ν₂ = 2 — the same parameterized zero-finding
problem `x² = c` as Example 7.7, but posed at a weight in the `Fact (1 < ν)`
regime where the bordered↔U transport stack exists (no production example
lives there natively: Ex77 has ν = 1/4, Ex81 ν = 1, Ex83 ν = 0.15, Ex245 is
scalar; Example1421 is the ν = 2 production instance). Data is chosen so the
four bounds are exact one-mode arithmetic: `x̄ = (3/4)·1`, `c = (5/9)·1`,
`A = (2/3)·id`, `A† = (3/2)·id`, giving `Y₀ = 1/216, Z₀ = Z₁ = 0, Z₂ ≡ 4/3`.

The transported certificate goes through `borderedTU_equiv` at price
κ ≤ 8/3: **accept** at r = 1/16 (margin ≈ 84% > 62.5%), **refuse** at
r = 1/2 (margin ≈ 32%). The `gateQ` runs at the end include the same
decision on the real certified numbers of Ex81 and Ex83 under a
hypothetical κ = 8/3.
-/

namespace KappaToy

open RadiiPolynomial Metric ContinuousLinearMap
open RadiiPolynomial.l1Weighted (leftMul leftMul_smul smul_id_eq_leftMul norm_one_eq)

noncomputable section

def ν₂ : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1:ℝ) < (ν₂ : ℝ)) := ⟨by rw [show ((ν₂ : ℝ)) = 2 from rfl]; norm_num⟩
instance : Fact ((1:ℝ) ≤ (ν₂ : ℝ)) := ⟨by rw [show ((ν₂ : ℝ)) = 2 from rfl]; norm_num⟩

def c : l1Weighted ν₂ := (5/9 : ℝ) • 1
def xBar : l1Weighted ν₂ := (3/4 : ℝ) • 1
def f : l1Weighted ν₂ → l1Weighted ν₂ := Example77.F_sub_const c
def A : l1Weighted ν₂ →L[ℝ] l1Weighted ν₂ := (2/3 : ℝ) • ContinuousLinearMap.id ℝ _
def Adag : l1Weighted ν₂ →L[ℝ] l1Weighted ν₂ := (3/2 : ℝ) • ContinuousLinearMap.id ℝ _

lemma leftMul_one : leftMul (1 : l1Weighted ν₂) = ContinuousLinearMap.id ℝ _ := by
  ext1 x; simp

lemma fderiv_at_xBar :
    fderiv ℝ f xBar = (3/2 : ℝ) • ContinuousLinearMap.id ℝ (l1Weighted ν₂) := by
  rw [show f = Example77.F_sub_const c from rfl, Example77.fderiv_F_sub_const,
    show xBar = (3/4 : ℝ) • 1 from rfl, leftMul_smul, leftMul_one, smul_smul]
  norm_num

lemma f_xBar : f xBar = (1/144 : ℝ) • 1 := by
  show Example77.sq xBar - c = _
  rw [show Example77.sq xBar = xBar * xBar from rfl,
    show xBar = (3/4 : ℝ) • 1 from rfl, show c = (5/9 : ℝ) • 1 from rfl,
    smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, ← sub_smul]
  norm_num

lemma hY₀ : ‖A (f xBar)‖ ≤ (1/216 : ℝ) := by
  rw [f_xBar,
    show A ((1/144 : ℝ) • 1) = (2/3 : ℝ) • ((1/144 : ℝ) • (1 : l1Weighted ν₂)) from rfl,
    smul_smul, norm_smul, Real.norm_eq_abs, norm_one_eq]
  norm_num

lemma hZ₀ : ‖ContinuousLinearMap.id ℝ (l1Weighted ν₂) - A.comp Adag‖ ≤ (0 : ℝ) := by
  have hAA : A.comp Adag = ContinuousLinearMap.id ℝ (l1Weighted ν₂) := by
    rw [show A = (2/3 : ℝ) • ContinuousLinearMap.id ℝ (l1Weighted ν₂) from rfl,
      show Adag = (3/2 : ℝ) • ContinuousLinearMap.id ℝ (l1Weighted ν₂) from rfl,
      smul_comp, comp_smul, ContinuousLinearMap.id_comp, smul_smul,
      show (2/3 : ℝ) * (3/2) = 1 from by norm_num, one_smul]
  rw [hAA, sub_self, norm_zero]

lemma hZ₁ : ‖A.comp (Adag - fderiv ℝ f xBar)‖ ≤ (0 : ℝ) := by
  rw [fderiv_at_xBar,
    show Adag = (3/2 : ℝ) • ContinuousLinearMap.id ℝ (l1Weighted ν₂) from rfl,
    sub_self, ContinuousLinearMap.comp_zero, norm_zero]

lemma hAnorm : ‖A‖ ≤ (2/3 : ℝ) := by
  rw [show A = (2/3 : ℝ) • ContinuousLinearMap.id ℝ (l1Weighted ν₂) from rfl,
    norm_smul, Real.norm_eq_abs, show |(2/3 : ℝ)| = 2/3 from by norm_num]
  linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := l1Weighted ν₂)]

lemma hZ₂ (r : ℝ) (hr : 0 ≤ r) : ∀ c' ∈ Metric.closedBall xBar r,
    ‖A.comp (fderiv ℝ f c' - fderiv ℝ f xBar)‖ ≤ (fun _ : ℝ => (4/3 : ℝ)) r * r := by
  intro c' hc'
  have h : ‖A.comp (fderiv ℝ f c' - fderiv ℝ f xBar)‖ ≤ |(2 : ℝ)| * ‖A‖ * r :=
    RadiiPolynomial.Z₂_ball_bound_of_affine_leftMul
      (Example77.fderiv_F_sub_const_affine c) A xBar c' hc'
  rw [show |(2 : ℝ)| = 2 from by norm_num] at h
  have hmul : ‖A‖ * r ≤ (2/3 : ℝ) * r := mul_le_mul_of_nonneg_right hAnorm hr
  show ‖A.comp (fderiv ℝ f c' - fderiv ℝ f xBar)‖ ≤ (4/3 : ℝ) * r
  linarith [h, hmul]

lemma hdiff : Differentiable ℝ f := Example77.differentiable_F_sub_const c

lemma hAinj : Function.Injective A := by
  intro x y h
  have h' : (2/3 : ℝ) • x = (2/3 : ℝ) • y := h
  have h2 := congrArg (fun v => (3/2 : ℝ) • v) h'
  simpa [smul_smul, show (3/2 : ℝ) * (2/3) = 1 from by norm_num] using h2

/-! ## §5 The transported certificate and the two gate verdicts -/

def u : l1Weighted ν₂ ≃L[ℝ] l1Bordered ν₂ := (borderedTU_equiv (ν := ν₂)).symm

def F' : l1Bordered ν₂ → l1Bordered ν₂ := fun b => u (f (u.symm b))

lemma hsquare : ∀ x, F' (u x) = u (f x) := fun x => by
  rw [show F' (u x) = u (f (u.symm (u x))) from rfl,
    ContinuousLinearEquiv.symm_apply_apply]

lemma hα : ‖(u : l1Weighted ν₂ →L[ℝ] l1Bordered ν₂)‖ ≤ (8/3 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun b => ?_)
  rw [show (u : l1Weighted ν₂ →L[ℝ] l1Bordered ν₂) b = borderedFromU b from rfl]
  have h := borderedFromU_norm_le (ν := ν₂) b
  have hval : 2 * ((ν₂ : ℝ)) ^ 2 / (((ν₂ : ℝ)) ^ 2 - 1) = 8/3 := by
    rw [show ((ν₂ : ℝ)) = 2 from rfl]; norm_num
  rw [hval] at h
  exact h

lemma hβ : ‖((u.symm : l1Bordered ν₂ →L[ℝ] l1Weighted ν₂))‖ ≤ (1 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun a => ?_)
  rw [show (u.symm : l1Bordered ν₂ →L[ℝ] l1Weighted ν₂) a = borderedToU a from rfl,
    one_mul]
  exact borderedToU_norm_le a

/-- **ACCEPT.** At radius 1/16 the B-side margin (≈ 84%) clears the κ = 8/3
threshold (κ−1)/κ = 62.5%, so the certificate transports: a unique zero of the
conjugated map `F'` in the bordered Chebyshev ball of radius 1/16 around the
transported candidate — proved without re-running any bound on the C side. -/
theorem transported_existsUnique :
    ∃! bTilde ∈ Metric.closedBall (u xBar) (1/16 : ℝ), F' bTilde = 0 := by
  refine transport_radii_polynomial_of_margin
    (Y₀ := 1/216) (Z₀ := 0) (Z₁ := 0) (Z₂ := fun _ => (4/3 : ℝ))
    (r₀ := 1/16) (r₁ := 1/16) (α := 8/3) (β := 1)
    u u hsquare hα hβ (by norm_num) (by norm_num) (by norm_num)
    hY₀ hZ₀ hZ₁ (hZ₂ (1/16) (by norm_num)) hdiff ?_ hAinj
  norm_num [generalRadiiPolynomial]

/-- The B-side certificate is also valid at the larger radius 1/2 … -/
theorem bside_accepts_half :
    generalRadiiPolynomial (1/216) 0 0 (fun _ => (4/3 : ℝ)) (1/2) < 0 := by
  norm_num [generalRadiiPolynomial]

/-- **REJECT.** … but at 1/2 the margin (≈ 32%) is below (κ−1)/κ = 62.5%: the
transported polynomial is positive, so transport refuses to certify there —
the price identity says reproving natively is the only route at this radius. -/
theorem gate_rejects_half :
    0 < (8/3 : ℝ) * 1 * generalRadiiPolynomial (1/216) 0 0 (fun _ => (4/3 : ℝ)) (1/2)
      + ((8/3 : ℝ) * 1 - 1) * (1/2) := by
  norm_num [generalRadiiPolynomial]

end

/-! ## §6 The ℚ gate: the reuse-or-reprove decision procedure

`gateQ` is the entire decision procedure: given the B-side certificate numbers
and the transport price κ = αβ, one rational-arithmetic check decides whether
the transported certificate closes. `gateQ_sound` connects a `true` verdict to
the hypothesis of `transport_radii_polynomial_of_margin`. -/

def gateQ (Y₀ Z₀ Z₁ Z₂ r₀ κ : ℚ) : Bool :=
  decide (κ * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + (κ - 1) * r₀ < 0)

theorem gateQ_sound {Y₀ Z₀ Z₁ Z₂ r₀ α β : ℚ}
    (h : gateQ Y₀ Z₀ Z₁ Z₂ r₀ (α * β) = true) :
    (α : ℝ) * (β : ℝ) *
        generalRadiiPolynomial (Y₀ : ℝ) (Z₀ : ℝ) (Z₁ : ℝ) (fun _ => (Z₂ : ℝ)) (r₀ : ℝ)
      + ((α : ℝ) * (β : ℝ) - 1) * (r₀ : ℝ) < 0 := by
  have hq : ((α * β) * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + ((α * β) - 1) * r₀ : ℚ) < 0 :=
    of_decide_eq_true h
  have hR : (((α * β) * (Z₂ * r₀^2 - (1 - Z₀ - Z₁) * r₀ + Y₀) + ((α * β) - 1) * r₀ : ℚ) : ℝ)
      < 0 := by exact_mod_cast hq
  push_cast at hR
  simp only [generalRadiiPolynomial]
  linarith [hR]

-- Toy at r = 1/16 (margin ≈ 84% > 62.5%): the gate ACCEPTS.
example : gateQ (1/216) 0 0 (4/3) (1/16) (8/3) = true := by native_decide
-- Toy at r = 1/2 (margin ≈ 32% < 62.5%): the gate REJECTS.
example : gateQ (1/216) 0 0 (4/3) (1/2) (8/3) = false := by native_decide

/- Production certificate data under a HYPOTHETICAL κ = 8/3 price (no transport
equivalence exists at their weights — Ex81 has ν = 1, Ex83 ν = 0.15, both
outside the `Fact (1 < ν)` regime; these runs are the gate as pure arithmetic
on real certified numbers). Ex81 (margin 67.2%) would clear the 62.5% bar;
Ex83 (margin 0.94%) would not. -/
example : gateQ (3/1000000) 0 (396482/7983360) (110916221/39916800) (1/10) (8/3) = true := by
  native_decide
example : gateQ (44/100000) (37/1000000000000000) (30/100) (49/10) (64/100000) (8/3) = false := by
  native_decide

end KappaToy
