import RadiiPolynomial.Applications.IVP.Chebyshev
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Tactic.AutoPolyFDeriv
import RadiiPolynomial.Algebra.Polynomial
import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Numbers

/-!
# Example 14.2.1 — Chebyshev IVP: u' = u(u-1)

Scalar IVP with Chebyshev basis: u̇ = u(u-1), u(-1) = 1/2.
Same ODE as Example 8.1 (Taylor) — the book's own twin pair — now verified on
[-1,1] with Chebyshev expansion at ν = 2, N = 40.

## The nonlinearity reads only non-negative modes

The book's convolution (Eq. 14.10) is bilateral with the SYMMETRIC extension
`ã_{-k} = ã_k` of the one-sided storage. On the bilateral carrier `XCheb` the
correct φ is therefore NOT the plain ring product of the stored element (whose
negative modes are zero, not symmetric): we first apply the symmetrization
`S(h)_k = h_{|k|}` — which reads only non-negative modes — and then multiply:

  `φ(a) = S(a) * S(a) - S(a)`,   `‖S‖ ≤ 2`.

Reading only non-negative modes is also what keeps the Z₁ bound finite: the
composed approximation acts as the identity on negative modes, so any
derivative coupling from negative input modes would be entirely
unpreconditioned (leakage ε ≈ 0.73, killing the certificate); with `S` those
columns vanish and ε ≈ 0.0034. Zeros of G still have vanishing negative modes
(pass-through), and on such elements φ agrees with the book's Eq. 14.11.
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap RadiiPolynomial ChebyshevIVP

noncomputable section

namespace Example1421

/-! ## 1. Parameters -/

abbrev N : ℕ := 40
abbrev L : ℕ := 1
instance : NeZero L := ⟨by decide⟩
abbrev ν_q : ℚ := 2
def ν_val : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1 : ℝ) ≤ (ν_val : ℝ)) := ⟨by rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num⟩
instance : Fact ((1 : ℝ) < (ν_val : ℝ)) := ⟨by rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num⟩

lemma ν_val_eq_q : (ν_val : ℝ) = ((ν_q : ℚ) : ℝ) := by
  rw [show ((ν_val : ℝ)) = 2 from rfl]; norm_num

/-- Initial value u(-1) = 1/2. -/
def p₀ : Fin L → ℝ := fun _ => 1/2

/-! ## 2. The symmetrization operator S

`S(h)_k = h_{|k|}`: symmetric output, reads only non-negative input modes.
The construction lives in the library (`l1Chebyshev.symmetrize`, promoted from
this example 2026-08-25); `S`/`Ssym` remain as the example's local notation. -/

/-- The symmetrized element (library `l1Chebyshev.symmetrize`). -/
abbrev Ssym : l1Chebyshev ν_val → l1Chebyshev ν_val := l1Chebyshev.symmetrize

/-- The symmetrization as a CLM, `‖S‖ ≤ 2` (library `l1Chebyshev.symmetrize_CLM`). -/
abbrev S : l1Chebyshev ν_val →L[ℝ] l1Chebyshev ν_val := l1Chebyshev.symmetrize_CLM

@[simp] lemma Ssym_toSeq (a : l1Chebyshev ν_val) (k : ℤ) :
    l1Chebyshev.toSeq (Ssym a) k = l1Chebyshev.toSeq a (k.natAbs : ℤ) :=
  l1Chebyshev.symmetrize_toSeq a k

@[simp] lemma S_apply (a : l1Chebyshev ν_val) : S a = Ssym a := rfl

lemma norm_Ssym_le (a : l1Chebyshev ν_val) : ‖Ssym a‖ ≤ 2 * ‖a‖ :=
  l1Chebyshev.symmetrize_norm_le a

lemma norm_S_le : ‖(S : l1Chebyshev ν_val →L[ℝ] l1Chebyshev ν_val)‖ ≤ 2 :=
  l1Chebyshev.symmetrize_CLM_norm_le

/-! ## 3. The nonlinearity φ(a) = S(a)·S(a) − S(a) and its derivative -/

/-- Coefficient-level nonlinearity: the folded (physical Chebyshev) version of
u ↦ u² − u, implemented as the bilateral product of symmetrized inputs. -/
def phi (a : XCheb ν_val L) (l : Fin L) : l1Chebyshev ν_val :=
  S (a l) * S (a l) - S (a l)

@[simp] lemma leftMul_apply' (a h : l1Chebyshev ν_val) :
    l1Chebyshev.leftMul a h = a * h := rfl

/-- Squaring on the Chebyshev algebra: derivative is `2•leftMul x`. -/
lemma hasFDerivAt_sq_cheb (x : l1Chebyshev ν_val) :
    HasFDerivAt (fun y : l1Chebyshev ν_val => y * y)
      ((2 : ℝ) • l1Chebyshev.leftMul x) x := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) x).mul' (hasFDerivAt_id x)
  have heq : (_root_.id x • ContinuousLinearMap.id ℝ (l1Chebyshev ν_val)
      + MulOpposite.op (_root_.id x) • ContinuousLinearMap.id ℝ (l1Chebyshev ν_val))
      = (2 : ℝ) • l1Chebyshev.leftMul x := by
    ext1 h'
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, id_eq, smul_eq_mul, op_smul_eq_mul,
      leftMul_apply']
    rw [mul_comm h' x, two_smul]
  rw [heq] at h
  exact h

/-- The scalar-map derivative of q(y) = y·y − y. -/
lemma hasFDerivAt_q (x : l1Chebyshev ν_val) :
    HasFDerivAt (fun y : l1Chebyshev ν_val => y * y - y)
      ((2 : ℝ) • l1Chebyshev.leftMul x - ContinuousLinearMap.id ℝ _) x :=
  (hasFDerivAt_sq_cheb x).sub (hasFDerivAt_id x)

/-- Component projection composed with S. -/
def SP (l : Fin L) : XCheb ν_val L →L[ℝ] l1Chebyshev ν_val :=
  S.comp (ContinuousLinearMap.proj l)

@[simp] lemma SP_apply (l : Fin L) (a : XCheb ν_val L) : SP l a = Ssym (a l) := rfl

/-- Derivative of φ in the l-th component:
`Dφ(a)h = 2·S(a l)·S(h l) − S(h l)`. -/
lemma hasFDerivAt_phi (a : XCheb ν_val L) (l : Fin L) :
    HasFDerivAt (fun x => phi x l)
      (((2 : ℝ) • l1Chebyshev.leftMul (S (a l))
        - ContinuousLinearMap.id ℝ _).comp (SP l)) a := by
  have hq := hasFDerivAt_q (S (a l))
  have hcomp := hq.comp a (SP l).hasFDerivAt
  exact hcomp

lemma differentiable_phi (l : Fin L) : Differentiable ℝ (fun x => phi x l) :=
  fun a => (hasFDerivAt_phi a l).differentiableAt

/-- The Dφ direction map used in Z-bounds: `Dφ(a)(h)ₗ = 2·S(aₗ)·S(hₗ) − S(hₗ)`. -/
def Dphi (a : XCheb ν_val L) (h : XCheb ν_val L) (l : Fin L) : l1Chebyshev ν_val :=
  (2 : ℝ) • (S (a l) * S (h l)) - S (h l)

lemma fderiv_phi_apply (a h : XCheb ν_val L) (l : Fin L) :
    fderiv ℝ (fun x => phi x l) a h = Dphi a h l := by
  rw [(hasFDerivAt_phi a l).fderiv]
  show (2 : ℝ) • l1Chebyshev.leftMul (S (a l)) (Ssym (h l))
      - Ssym (h l) = _
  simp [Dphi]

/-- The K-bound: `‖Dφ(a)h‖ ≤ (2‖S(aₗ)‖ + 1)·2·‖h‖` componentwise. -/
lemma norm_Dphi_le (a h : XCheb ν_val L) (l : Fin L) :
    ‖Dphi a h l‖ ≤ (2 * ‖S (a l)‖ + 1) * (2 * ‖h‖) := by
  have hSh : ‖S (h l)‖ ≤ 2 * ‖h‖ := by
    refine le_trans (norm_Ssym_le (h l)) ?_
    have : ‖h l‖ ≤ ‖h‖ := norm_le_pi_norm h l
    linarith
  have hmul : ‖S (a l) * S (h l)‖ ≤ ‖S (a l)‖ * ‖S (h l)‖ := norm_mul_le _ _
  have h1 : ‖Dphi a h l‖ ≤ 2 * ‖S (a l) * S (h l)‖ + ‖S (h l)‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_smul]
    simp
  have h2 : 2 * ‖S (a l) * S (h l)‖ + ‖S (h l)‖
      ≤ 2 * (‖S (a l)‖ * ‖S (h l)‖) + ‖S (h l)‖ := by
    nlinarith [norm_nonneg (S (h l))]
  have h3 : 2 * (‖S (a l)‖ * ‖S (h l)‖) + ‖S (h l)‖
      = (2 * ‖S (a l)‖ + 1) * ‖S (h l)‖ := by ring
  have h4 : (2 * ‖S (a l)‖ + 1) * ‖S (h l)‖ ≤ (2 * ‖S (a l)‖ + 1) * (2 * ‖h‖) := by
    have hpos : (0 : ℝ) ≤ 2 * ‖S (a l)‖ + 1 := by positivity
    exact mul_le_mul_of_nonneg_left hSh hpos
  linarith

/-! ## 4. Data bundle -/

/-- The bundled numerical data for the standard Chebyshev IVP pipeline. -/
def data : ChebyshevIVP.StdChebIVPData ν_val L N where
  A_col := A_col
  DF_col := DF_col
  abar_Q := fun _ => abar_0
  ν_q := ν_q
  hν := ν_val_eq_q
  habar_size := fun _ => by native_decide

end Example1421
