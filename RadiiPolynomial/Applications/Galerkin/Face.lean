import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Galerkin
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Bounds
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev

/-!
# The polynomial Galerkin face

For a polynomial system `f : Fin L → CompPoly L`, evaluated componentwise in a normed commutative
real algebra `R` by `u ↦ fun l => (f l).evalBanach u` (the system map of
`CompPoly.hasFDerivAt_system`), this file builds the composite face
`polyFace L₀ Λ π ι f x = L₀ x + Λ (π (fun l => (f l).evalBanach (ι x)))`: a continuous linear
part `L₀`, a lift `ι` into `R^L`, the polynomial evaluation, a projection `π` and an outer
continuous linear map `Λ`. Its derivative is `DpolyFace`, built from the syntactic Jacobian
`CompPoly.jacCLM` (`hasFDerivAt_polyFace`).

The derivative difference is controlled by the centred majorant
`CompPoly.derivativeCentredBound` (`norm_gradCLM_sub_le_centred`, `norm_jacCLM_sub_le_centred`,
`norm_DpolyFace_sub_le`), with no global Lipschitz hypothesis.

On the Galerkin space `E ν N L = Fin L → FνN ν N`, the componentwise lift `I` (the even padding
`ιN`) and projection `Pi'` (the truncation `πN`) are contractions (`norm_I_le`, `norm_Pi'_le`; `I` is
isometric, `norm_I_apply`) into and out of
`(symmetricSubalgebra ν)^L`; `norm_fderiv_galerkinFace_sub_le` is the resulting `Z₂`-shaped
bound `‖DF c − DF x̄‖ ≤ ‖Λ‖ M` on the ball `B̄_r(x̄)`.
-/

noncomputable section

open scoped BigOperators

namespace RadiiPolynomial

namespace Galerkin

open MvPolyBridge

/-! ### The sandwiched polynomial map on any normed commutative real algebra -/

section PolyDeriv

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {L : ℕ}

/-- Generic Galerkin face: for any lift `ι` and projection `π`, the sandwiched polynomial
map `π ∘ (u ↦ (l ↦ (f l).evalBanach u)) ∘ ι` has derivative `π ∘ jacCLM f (ι x) ∘ ι`. -/
theorem hasFDerivAt_sandwich {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ι : X →L[ℝ] (Fin L → R)) (π : (Fin L → R) →L[ℝ] Y) (f : Fin L → CompPoly L) (x : X) :
    HasFDerivAt (π ∘ (fun u l => (f l).evalBanach u) ∘ ι)
      (π.comp ((CompPoly.jacCLM f (ι x)).comp ι)) x :=
  π.hasFDerivAt.comp x ((CompPoly.hasFDerivAt_system f (ι x)).comp x ι.hasFDerivAt)

end PolyDeriv

/-! ### The Galerkin space and its lift and projection -/

section Derivative

open l1Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N L : ℕ}

/-- Subtype bridge to the bilateral face: on flip-fixed inputs the coercion of `gradCLM` is the
stored-coefficient derivative `CompPoly.Chebyshev.derivative` of the bilateral algebra (whose
symmetrization is then the identity). -/
theorem coe_gradCLM (p : CompPoly L) (a h : Fin L → symmetricSubalgebra ν) :
    ((CompPoly.gradCLM p a h : symmetricSubalgebra ν) : l1Chebyshev ν) =
      CompPoly.Chebyshev.derivative p (fun i => (a i : l1Chebyshev ν))
        (fun i => (h i : l1Chebyshev ν)) := by
  rw [CompPoly.Chebyshev.derivative_apply, CompPoly.gradCLM_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [symmetrize_eq_self_of_isSymmetric _ (h i).2, CompPoly.Chebyshev.eval]
  congr 1
  refine (CompPoly.map_evalBanach (symmetricSubalgebra ν).val (p.pderiv i) a).trans ?_
  congr 1
  funext j
  exact (symmetrize_eq_self_of_isSymmetric _ (a j).2).symm

/-- The Galerkin space `E := (FνN)^L`. -/
abbrev E (ν : PosReal) (N L : ℕ) := Fin L → FνN ν N

/-- Componentwise lift `I : E → (symmetricSubalgebra ν)^L`. -/
def I : E ν N L →L[ℝ] (Fin L → symmetricSubalgebra ν) :=
  ContinuousLinearMap.pi fun l => (ιN (ν := ν) (N := N)).toContinuousLinearMap.comp
    (ContinuousLinearMap.proj l)

/-- Componentwise projection `Π : (symmetricSubalgebra ν)^L → E`. -/
def Pi' : (Fin L → symmetricSubalgebra ν) →L[ℝ] E ν N L :=
  ContinuousLinearMap.pi fun l => (πN (ν := ν) (N := N)).comp (ContinuousLinearMap.proj l)

@[simp] theorem I_apply (x : E ν N L) (l : Fin L) : I x l = ιN (x l) := rfl
@[simp] theorem Pi'_apply (a : Fin L → symmetricSubalgebra ν) (l : Fin L) :
    (Pi' a : E ν N L) l = πN (a l) := rfl

/-- The Galerkin map `Π ∘ (u ↦ (l ↦ (f l).evalBanach u)) ∘ I` on `E = (FνN)^L` has derivative
`Π ∘ jacCLM f (I x) ∘ I`, with `jacCLM` the syntactic Jacobian on the flip-fixed algebra. -/
theorem hasFDerivAt_galerkin (f : Fin L → CompPoly L) (x : E ν N L) :
    HasFDerivAt (Pi' (N := N) ∘ (fun u l => (f l).evalBanach u) ∘ I)
      ((Pi' (ν := ν) (N := N) (L := L)).comp ((CompPoly.jacCLM f (I x)).comp I)) x :=
  hasFDerivAt_sandwich (R := symmetricSubalgebra ν) I Pi' f x

theorem fderiv_galerkin (f : Fin L → CompPoly L) (x : E ν N L) :
    fderiv ℝ (Pi' (N := N) ∘ (fun u l => (f l).evalBanach u) ∘ I) x =
      (Pi' (ν := ν) (N := N) (L := L)).comp ((CompPoly.jacCLM f (I x)).comp I) :=
  (hasFDerivAt_galerkin f x).fderiv

end Derivative

/-! ### Centred derivative bounds -/

section Face

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] [NormOneClass R] {L : ℕ}

/-- One component: the centred majorant bounds the gradient difference,
`‖∇p(a) − ∇p(b)‖ ≤ Σᵢ p̂ᵢ(β + δ) − p̂ᵢ(β)` on `‖b i‖ ≤ β i`, `‖a i − b i‖ ≤ δ i`. -/
theorem norm_gradCLM_sub_le_centred (p : CompPoly L) (a b : Fin L → R) (β δ : Fin L → ℝ)
    (hb : ∀ i, ‖b i‖ ≤ β i) (hab : ∀ i, ‖a i - b i‖ ≤ δ i) :
    ‖CompPoly.gradCLM p a - CompPoly.gradCLM p b‖ ≤ CompPoly.derivativeCentredBound p β δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (CompPoly.derivativeCentredBound_nonneg p β δ
    (fun i => (norm_nonneg _).trans (hb i)) (fun i => (norm_nonneg _).trans (hab i))) fun h => ?_
  rw [sub_apply, CompPoly.gradCLM_apply, CompPoly.gradCLM_apply,
    ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  refine (CompPoly.norm_sum_mul_pi_le _ h).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [CompPoly.derivativeCentredBound]
  exact Finset.sum_le_sum fun i _ => CompPoly.norm_evalBanach_sub_le_centred _ a b β δ hb hab

/-- The system: `‖jacCLM f a − jacCLM f b‖ ≤ M` for any `M` dominating every component's
centred majorant. -/
theorem norm_jacCLM_sub_le_centred [NeZero L] (f : Fin L → CompPoly L) (a b : Fin L → R)
    (β δ : Fin L → ℝ) {M : ℝ} (hM : ∀ l, CompPoly.derivativeCentredBound (f l) β δ ≤ M)
    (hb : ∀ i, ‖b i‖ ≤ β i) (hab : ∀ i, ‖a i - b i‖ ≤ δ i) :
    ‖CompPoly.jacCLM f a - CompPoly.jacCLM f b‖ ≤ M := by
  have hM0 : 0 ≤ M := (CompPoly.derivativeCentredBound_nonneg (f 0) β δ
    (fun i => (norm_nonneg _).trans (hb i)) (fun i => (norm_nonneg _).trans (hab i))).trans (hM 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
  have e : (CompPoly.jacCLM f a - CompPoly.jacCLM f b) h l =
      (CompPoly.gradCLM (f l) a - CompPoly.gradCLM (f l) b) h := rfl
  rw [e]
  exact ((CompPoly.gradCLM (f l) a - CompPoly.gradCLM (f l) b).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right
      ((norm_gradCLM_sub_le_centred (f l) a b β δ hb hab).trans (hM l)) (norm_nonneg _))

end Face

/-! ### The general composite face `F = L₀ + Λ ∘ π ∘ (u ↦ (l ↦ (f l).evalBanach u)) ∘ ι` -/

section CompositeFace

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {L : ℕ}
  {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The polynomial composite `x ↦ L₀ x + Λ (π (fun l => (f l).evalBanach (ι x)))`: a continuous
linear part `L₀`, a lift `ι` into `R^L`, the evaluation of any polynomial system `f`, a projection
`π` and an outer continuous linear map `Λ`. -/
def polyFace (L₀ : X →L[ℝ] Z) (Λ : Y →L[ℝ] Z) (π : (Fin L → R) →L[ℝ] Y)
    (ι : X →L[ℝ] (Fin L → R)) (f : Fin L → CompPoly L) (x : X) : Z :=
  L₀ x + Λ (π (fun l => (f l).evalBanach (ι x)))

/-- Its derivative `L₀ + Λ ∘ π ∘ jacCLM f (ι x) ∘ ι`. -/
def DpolyFace (L₀ : X →L[ℝ] Z) (Λ : Y →L[ℝ] Z) (π : (Fin L → R) →L[ℝ] Y)
    (ι : X →L[ℝ] (Fin L → R)) (f : Fin L → CompPoly L) (x : X) : X →L[ℝ] Z :=
  L₀ + Λ.comp (π.comp ((CompPoly.jacCLM f (ι x)).comp ι))

theorem hasFDerivAt_polyFace (L₀ : X →L[ℝ] Z) (Λ : Y →L[ℝ] Z) (π : (Fin L → R) →L[ℝ] Y)
    (ι : X →L[ℝ] (Fin L → R)) (f : Fin L → CompPoly L) (x : X) :
    HasFDerivAt (polyFace L₀ Λ π ι f) (DpolyFace L₀ Λ π ι f x) x :=
  L₀.hasFDerivAt.add (Λ.hasFDerivAt.comp x (hasFDerivAt_sandwich ι π f x))

/-- The linear part cancels in a derivative difference. -/
theorem fderiv_polyFace_sub_apply (L₀ : X →L[ℝ] Z) (Λ : Y →L[ℝ] Z) (π : (Fin L → R) →L[ℝ] Y)
    (ι : X →L[ℝ] (Fin L → R)) (f : Fin L → CompPoly L) (c b h : X) :
    fderiv ℝ (polyFace L₀ Λ π ι f) c h - fderiv ℝ (polyFace L₀ Λ π ι f) b h =
      Λ (π ((CompPoly.jacCLM f (ι c) - CompPoly.jacCLM f (ι b)) (ι h))) := by
  rw [(hasFDerivAt_polyFace L₀ Λ π ι f c).fderiv, (hasFDerivAt_polyFace L₀ Λ π ι f b).fderiv]
  simp only [DpolyFace, add_apply, ContinuousLinearMap.comp_apply,
    sub_apply, map_sub]
  abel

/-- The `Z₂` shape, with no global Lipschitz hypothesis: on the centred ball
`‖ι b i‖ ≤ β i`, `‖ι c i − ι b i‖ ≤ δ i`, `‖DF c − DF b‖ ≤ ‖Λ‖ ‖π‖ M ‖ι‖` for any `M`
dominating the centred majorants of the components. -/
theorem norm_DpolyFace_sub_le [NormOneClass R] [NeZero L] (L₀ : X →L[ℝ] Z) (Λ : Y →L[ℝ] Z)
    (π : (Fin L → R) →L[ℝ] Y) (ι : X →L[ℝ] (Fin L → R)) (f : Fin L → CompPoly L) {c b : X}
    {β δ : Fin L → ℝ} {M : ℝ} (hM : ∀ l, CompPoly.derivativeCentredBound (f l) β δ ≤ M)
    (hb : ∀ i, ‖ι b i‖ ≤ β i) (hcb : ∀ i, ‖ι c i - ι b i‖ ≤ δ i) :
    ‖DpolyFace L₀ Λ π ι f c - DpolyFace L₀ Λ π ι f b‖ ≤ ‖Λ‖ * ‖π‖ * M * ‖ι‖ := by
  rw [DpolyFace, DpolyFace, add_sub_add_left_eq_sub, ← ContinuousLinearMap.comp_sub,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp, mul_assoc, mul_assoc]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_jacCLM_sub_le_centred f (ι c) (ι b) β δ hM hb hcb) (norm_nonneg _)))
      (norm_nonneg _))) (norm_nonneg _))

end CompositeFace

/-! ### The Galerkin instance on `E = (FνN)^L` -/

section Galerkin

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N L : ℕ}

/-- `I` is isometric on `E = (FνN)^L` (sup over components of isometries). -/
theorem norm_I_apply (x : E ν N L) : ‖(I x : Fin L → l1Chebyshev.symmetricSubalgebra ν)‖ = ‖x‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_)
  · rw [I_apply, norm_ιN]
    exact norm_le_pi_norm x l
  · rw [← norm_ιN (ν := ν), ← I_apply]
    exact norm_le_pi_norm (I x) l

theorem norm_I_le : ‖(I : E ν N L →L[ℝ] (Fin L → l1Chebyshev.symmetricSubalgebra ν))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [norm_I_apply, one_mul]

theorem norm_Pi'_le : ‖(Pi' : (Fin L → l1Chebyshev.symmetricSubalgebra ν) →L[ℝ] E ν N L)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => by
      rw [Pi'_apply, one_mul]
      exact (ContinuousLinearMap.le_of_opNorm_le _ norm_πN_le (a l)).trans
        ((one_mul _).le.trans (norm_le_pi_norm a l))

/-- The Galerkin instance of the composite face:
`F = L₀ + Λ ∘ Π ∘ (u ↦ (l ↦ (f l).evalBanach u)) ∘ I` on `E = (FνN)^L`, any `f`. -/
theorem hasFDerivAt_galerkinFace {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L₀ Λ : E ν N L →L[ℝ] Z) (f : Fin L → CompPoly L) (x : E ν N L) :
    HasFDerivAt (polyFace L₀ Λ Pi' I f)
      (L₀ + Λ.comp (Pi'.comp ((CompPoly.jacCLM f (I x)).comp I))) x :=
  hasFDerivAt_polyFace L₀ Λ Pi' I f x

/-- The Galerkin instance on `E = (FνN)^L`: for `F = L₀ + Λ ∘ Π ∘ (u ↦ (l ↦ (f l).evalBanach u)) ∘ I`,
any polynomial system `f` and radii `β ≥ ‖x̄ i‖`, `‖DF c − DF x̄‖ ≤ ‖Λ‖ M` on `B̄_r(x̄)`, where `M`
dominates the centred majorants `derivativeCentredBound (f l) β r`.  No global Lipschitz
hypothesis. -/
theorem norm_fderiv_galerkinFace_sub_le [NeZero L] {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (L₀ Λ : E ν N L →L[ℝ] Z) (f : Fin L → CompPoly L) {xBar : E ν N L} {r : ℝ}
    {β : Fin L → ℝ} (hβ : ∀ i, ‖xBar i‖ ≤ β i) {M : ℝ}
    (hM : ∀ l, CompPoly.derivativeCentredBound (f l) β (fun _ => r) ≤ M) :
    ∀ c ∈ Metric.closedBall xBar r,
      ‖fderiv ℝ (polyFace L₀ Λ Pi' I f) c - fderiv ℝ (polyFace L₀ Λ Pi' I f) xBar‖ ≤ ‖Λ‖ * M := by
  intro c hc
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  have hb : ∀ i, ‖(I xBar : Fin L → l1Chebyshev.symmetricSubalgebra ν) i‖ ≤ β i := fun i => by
    rw [I_apply, norm_ιN]; exact hβ i
  have hcb : ∀ i, ‖(I c : Fin L → l1Chebyshev.symmetricSubalgebra ν) i - I xBar i‖ ≤
      (fun _ => r) i := fun i => by
    rw [I_apply, I_apply, ← map_sub, norm_ιN]; exact (norm_le_pi_norm (c - xBar) i).trans hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (norm_jacCLM_sub_le_centred f _ _ β _ hM hb hcb)
  rw [(hasFDerivAt_polyFace L₀ Λ Pi' I f c).fderiv, (hasFDerivAt_polyFace L₀ Λ Pi' I f xBar).fderiv]
  have h1 : ‖Λ‖ * ‖(Pi' : (Fin L → l1Chebyshev.symmetricSubalgebra ν) →L[ℝ] E ν N L)‖ ≤ ‖Λ‖ := by
    simpa using mul_le_mul_of_nonneg_left (norm_Pi'_le (ν := ν) (N := N) (L := L)) (norm_nonneg Λ)
  exact (norm_DpolyFace_sub_le L₀ Λ Pi' I f hM hb hcb).trans ((mul_le_mul
    (mul_le_mul_of_nonneg_right h1 hM0) norm_I_le (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) hM0)).trans_eq (mul_one _))

end Galerkin

end Galerkin

end RadiiPolynomial

end
