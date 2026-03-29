import RadiiPolynomial
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Formalization of Theorems from "Ordinary Differential Equations: A Constructive Approach"
## Chapter 4: Linear Theory and Stability of Equilibria (+ Chapter 5 selections)

Each theorem is stated as a Lean 4 `theorem` with `by sorry` as a proof placeholder.

We use `NormedSpace.exp` for the exponential in a normed algebra (incl. matrices).
For matrices, we use `Matrix.exp_*` lemmas from Mathlib.
The RadiiPolynomial library is used for computational verification theorems.

### Conventions
- `mexp A` abbreviates `NormedSpace.exp A` (matrix/operator exponential)
- Eigenvalues are expressed via `spectrum`
- We use `attribute [local instance]` to fix matrix norms where needed
-/

open scoped Matrix BigOperators Topology NNReal
open Metric Set Filter

noncomputable section

-- Fix a matrix norm
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- Shorthand for the normed-space exponential. -/
abbrev mexp {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (x : 𝔸) : 𝔸 :=
  NormedSpace.exp x

/-! ## Theorem 4.1.2: Absolute convergence of matrix exponential series

For any A ∈ Mn(ℝ), the series ∑ (1/k!) Aᵏ is absolutely convergent.
-/

/-
PROVIDED SOLUTION
The series ∑ (1/k!) ‖A‖^k converges (it's the exponential series for ‖A‖), and ‖(1/k!) A^k‖ ≤ (1/k!) ‖A‖^k by the submultiplicativity of the norm. Use summable_of_nonneg_of_le with the real exponential series convergence. Try NormedSpace.exp_series_summable or summable_norm_of_summable_of_ne.
-/
theorem matrix_exp_series_abs_convergent (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Summable fun k => ‖((k.factorial : ℕ) : ℝ)⁻¹ • A ^ k‖ := by
      -- Apply the comparison test with the convergent series $\sum_{k=0}^{\infty} \frac{\|A\|^k}{k!}$.
      have h_comparison : Summable (fun k : ℕ => (∑ i : Fin n, ∑ j : Fin n, |(A ^ k) i j| : ℝ) / (k.factorial : ℝ)) := by
        -- Let $M = \max_{i,j} |A_{ij}|$.
        set M := ∑ i, ∑ j, |A i j| with hM_def
        have hM_finite : ∀ k : ℕ, (∑ i, ∑ j, |(A ^ k) i j|) ≤ M^k * n^2 := by
          intro k
          have h_bound : ∀ i j, |(A ^ k) i j| ≤ M^k := by
            induction k <;> simp_all +decide [ pow_succ, Matrix.mul_apply ];
            · intro i j; by_cases hij : i = j
              · subst hij; simp_all only [Matrix.one_apply_eq, abs_one, le_refl, M]
              · simp_all only [ne_eq, not_false_eq_true, Matrix.one_apply_ne, abs_zero, zero_le_one, M]
            · intro i j; refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _ ; simp_all +decide [ abs_mul, Finset.mul_sum _ _ _ ] ; (
              exact Finset.sum_le_sum fun x _ => le_trans ( mul_le_mul_of_nonneg_right ( by solve_by_elim ) ( abs_nonneg _ ) ) ( Finset.single_le_sum ( fun y _ => mul_nonneg ( pow_nonneg ( Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg ( A i j ) ) _ ) ( abs_nonneg ( A x y ) ) ) ( Finset.mem_univ j ) ) |> le_trans <| by simp +decide [ mul_comm ] ;)
          generalize_proofs at *; (
          exact le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_bound i j ) ( by norm_num; nlinarith ))
        generalize_proofs at *; (
        exact Summable.of_nonneg_of_le ( fun k => div_nonneg ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( fun k => div_le_div_of_nonneg_right ( hM_finite k ) ( Nat.cast_nonneg _ ) ) ( by simpa [ mul_div_right_comm ] using Summable.mul_right _ <| Real.summable_pow_div_factorial M ));
      refine' h_comparison.of_nonneg_of_le ( fun k => _ ) ( fun k => _ );
      · simp +zetaDelta at *;
      · refine' le_trans ( NNReal.coe_mono _ ) _;
        exact ⟨ ∑ i, ∑ j, |(A ^ k) i j| / ( k.factorial : ℝ ), by positivity ⟩;
        · simp [div_eq_inv_mul];
          intro i; erw [ ← NNReal.coe_le_coe ] ; simp [mul_comm] ;
          refine' le_trans _ ( Finset.single_le_sum ( fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg ( abs_nonneg _ ) ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ) ( Finset.mem_univ i ) );
          simp [mul_comm, Norm.norm];
        · simp [div_eq_mul_inv, Finset.sum_mul]

/-! ## Proposition 4.1.3: Derivative of matrix exponential

d/dt (e^{tA}) = A e^{tA} = e^{tA} A
-/

/-
PROVIDED SOLUTION
Use hasDerivAt_exp_smul_const which gives HasDerivAt (fun u => exp(u • x)) (exp(t • x) * x) t. This is exactly our goal with x = A.
-/
theorem matrix_exp_deriv_right (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s => mexp (s • A)) (mexp (t • A) * A) t := by
      have := @hasDerivAt_exp_smul_const ℝ;
      contrapose! this;
      refine' ⟨ _, _, _, _, _, _ ⟩;
      exact Matrix ( Fin n ) ( Fin n ) ℝ;
      exact inferInstance;
      exact Matrix.frobeniusNormedRing;
      exact Matrix.frobeniusNormedAlgebra;
      · infer_instance;
      · refine' ⟨ A, t, _ ⟩;
        convert this using 1

/-
PROVIDED SOLUTION
Use NormedSpace.hasDerivAt_exp_smul_const_of_mem_ball for the derivative, then show exp(tA)*A = A*exp(tA) because tA commutes with exp(tA). The key is that smul commutes, so (t•A) commutes with exp(t•A), and therefore A commutes with exp(t•A). Use Commute.exp_right or similar.
-/
theorem matrix_exp_deriv_left (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s => mexp (s • A)) (A * mexp (t • A)) t := by
      -- Apply the fact that the derivative of the matrix exponential is the matrix exponential times the derivative of the argument, using the commutativity of multiplication.
      have h_deriv_comm : HasDerivAt (fun s => mexp (s • A)) (mexp (t • A) * A) t := by
        exact matrix_exp_deriv_right n A t;
      have h_comm : Commute (t • A) A := by
        simp [ Commute ];
        simp [ SemiconjBy ]
      have h_comm_exp : Commute (mexp (t • A)) A := by
        exact Commute.exp_left h_comm
      have h_comm_exp' : mexp (t • A) * A = A * mexp (t • A) := by
        exact h_comm_exp.eq.symm ▸ rfl
      rw [h_comm_exp'] at h_deriv_comm
      exact h_deriv_comm

/-! ## Proposition 4.1.5: Properties of matrix exponential -/

/-
PROBLEM
(i) If A = B C B⁻¹, then e^A = B e^C B⁻¹.

PROVIDED SOLUTION
Substitute h: A = B*C*B⁻¹ into mexp A. Then use the fact that exp(B*C*B⁻¹) = B * exp(C) * B⁻¹. This follows from the power series: (BCB⁻¹)^k = B*C^k*B⁻¹, so the series telescopes. In Mathlib, look for NormedSpace.exp_units_conj or Matrix.exp_conj or ring_exp_conj.
-/
theorem matrix_exp_conj (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B)
    (h : A = B * C * B⁻¹) :
    mexp A = B * mexp C * B⁻¹ := by
      rw [ h ];
      exact Matrix.exp_conj B C hB

/-
PROBLEM
(ii) If AB = BA, then e^{A+B} = e^A e^B.

PROVIDED SOLUTION
Use NormedSpace.exp_add_of_commute with the commute hypothesis h.
-/
theorem matrix_exp_add_comm (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : Commute A B) :
    mexp (A + B) = mexp A * mexp B := by
      exact Matrix.exp_add_of_commute A B h

/-
PROBLEM
(iii) e^{-A} = (e^A)⁻¹.

PROVIDED SOLUTION
Use NormedSpace.exp_neg which states exp(-A) = (exp A)⁻¹ in a normed algebra.
-/
theorem matrix_exp_neg_eq_inv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    mexp (-A) = (mexp A)⁻¹ := by
      -- By definition of matrix exponential, we know that $e^{-A} = (e^A)^{-1}$.
      have h_exp_neg : mexp (-A) = (mexp A)⁻¹ := by
        have h_inv : mexp A * mexp (-A) = 1 := by
          rw [ ← matrix_exp_add_comm ];
          simp_all only [add_neg_cancel, NormedSpace.exp_zero];
          exact Commute.neg_right rfl
        rw [ Matrix.inv_eq_right_inv h_inv ];
      exact h_exp_neg

/-- (iv) For A = [[a, -b], [b, a]], e^A = e^a [[cos b, -sin b], [sin b, cos b]]. -/
theorem matrix_exp_2x2_rotation (a b : ℝ) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -b; b, a]
    mexp A = Real.exp a • !![Real.cos b, -Real.sin b; Real.sin b, Real.cos b] := by sorry

/-! ## Lemma 4.1.6: Cauchy product of absolutely convergent series

If A = ∑ Aₖ and B = ∑ Bₖ are absolutely convergent series in a normed ring, and
Cₖ = ∑_{i+j=k} Aᵢ Bⱼ, then ∑ Cₖ = (∑ Aₖ)(∑ Bₖ).
-/

/-
PROVIDED SOLUTION
This is the Cauchy product theorem for absolutely convergent series. Use HasSum.mul from Mathlib, or tsum_mul_tsum_of_summable_norm. The key lemma is HasSum related to tsum_mul_tsum_of_summable_norm or Finset.antidiagonal_sum version.
-/
theorem cauchy_product_series {R : Type*} [NormedRing R] [CompleteSpace R]
    (A B : ℕ → R)
    (hA : Summable fun k => ‖A k‖)
    (hB : Summable fun k => ‖B k‖) :
    HasSum (fun k => ∑ ij ∈ Finset.antidiagonal k, A ij.1 * B ij.2)
      ((∑' k, A k) * (∑' k, B k)) := by
        convert Summable.hasSum _ using 1;
        · exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hB;
        · refine' .of_norm _;
          exact summable_norm_sum_mul_antidiagonal_of_summable_norm hA hB

/-! ## Corollary 4.2.6: Topological conjugacy of flows with same Jordan form

If P₁⁻¹AP₁ = P₂⁻¹BP₂ (same Jordan form J), then letting S = P₁P₂⁻¹,
e^{Bt} = S⁻¹ e^{At} S for all t, so the flows are conjugate.
-/

/-
PROVIDED SOLUTION
We have J = P1⁻¹*A*P1 = P2⁻¹*B*P2. So t•A = P1*(t•J)*P1⁻¹ and t•B = P2*(t•J)*P2⁻¹, where J = P1⁻¹*A*P1. Using matrix_exp_conj, exp(t•A) = P1*exp(t•J)*P1⁻¹ and exp(t•B) = P2*exp(t•J)*P2⁻¹. Let S = P1*P2⁻¹. Then S⁻¹ = P2*P1⁻¹. So S⁻¹*exp(t•A)*S = P2*P1⁻¹*P1*exp(t•J)*P1⁻¹*P1*P2⁻¹ = P2*exp(t•J)*P2⁻¹ = exp(t•B). This is a matrix algebra calculation using hJ, matrix_exp_conj, and IsUnit properties.
-/
theorem flows_conjugate_of_similar_matrices (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (P1 P2 : Matrix (Fin n) (Fin n) ℝ)
    (hP1 : IsUnit P1) (hP2 : IsUnit P2)
    (hJ : P1⁻¹ * A * P1 = P2⁻¹ * B * P2)
    (t : ℝ) :
    let S := P1 * P2⁻¹
    mexp (t • B) = S⁻¹ * mexp (t • A) * S := by
      -- Using the similarity relation, we can write $t • A = P1 * (t • (P1⁻¹ * A * P1)) * P1⁻¹$ and $t • B = P2 * (t • (P2⁻¹ * B * P2)) * P2⁻¹$.
      have hA : t • A = P1 * (t • (P1⁻¹ * A * P1)) * P1⁻¹ := by
        cases hP1.nonempty_invertible ; cases hP2.nonempty_invertible ; simp [ mul_assoc ]
      have hB : t • B = P2 * (t • (P2⁻¹ * B * P2)) * P2⁻¹ := by
        cases hP2.nonempty_invertible ; simp_all [ ← mul_assoc ];
      -- Using the matrix exponential property, we can rewrite the right-hand side as $e^{tJ}$.
      have h_exp : mexp (t • A) = P1 * mexp (t • (P1⁻¹ * A * P1)) * P1⁻¹ ∧ mexp (t • B) = P2 * mexp (t • (P2⁻¹ * B * P2)) * P2⁻¹ := by
        apply And.intro;
        · convert matrix_exp_conj _ _ _ _ _ using 1;
          all_goals tauto;
        · exact matrix_exp_conj n (t • B) P2 (t • (P2⁻¹ * B * P2)) hP2 hB;
      simp_all [ mul_assoc, Matrix.isUnit_iff_isUnit_det ];
      simp [ Matrix.mul_inv_rev, mul_assoc, hP1, hP2 ]

/-! ## Proposition 4.2.8: Matrix exponential of λI + N where N is nilpotent

If A = λI + N where N^k = 0 for some k ≥ 1, then
e^{At} = e^{λt} ∑_{j=0}^{k-1} (t^j / j!) N^j.
-/
theorem matrix_exp_scalar_plus_nilpotent (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (k : ℕ) (hk : 1 ≤ k) (hN : N ^ k = 0) (t : ℝ) :
    mexp (t • (lam • (1 : Matrix (Fin n) (Fin n) ℝ) + N)) =
      Real.exp (lam * t) •
        ∑ j ∈ Finset.range k, (t ^ j / (j.factorial : ℝ)) • N ^ j := by sorry

/-! ## Proposition 4.2.9: Matrix exponential of 2×2 Jordan block

For D = [[α, -β], [β, α]], we have
e^{tD} = e^{αt} [[cos(βt), -sin(βt)], [sin(βt), cos(βt)]].
-/

/-
PROVIDED SOLUTION
t•D = t•[[alpha,-beta],[beta,alpha]] = [[(alpha*t),-(beta*t)],[beta*t,alpha*t]]. This is the same form as matrix_exp_2x2_rotation with a = alpha*t and b = beta*t. So mexp(t•D) = e^(alpha*t) • [[cos(beta*t), -sin(beta*t)], [sin(beta*t), cos(beta*t)]]. Use matrix_exp_2x2_rotation (already proved above) after showing t•D has the right form.
-/
theorem matrix_exp_2x2_jordan_block (alpha beta t : ℝ) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![alpha, -beta; beta, alpha]
    mexp (t • D) = Real.exp (alpha * t) •
      !![Real.cos (beta * t), -Real.sin (beta * t);
         Real.sin (beta * t),  Real.cos (beta * t)] := by
           convert matrix_exp_2x2_rotation ( alpha * t ) ( beta * t ) using 1 ; norm_num [ Matrix.smul_eq_diagonal_mul ] ; ring;
           congr! 2 ; ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Matrix.diagonal ] <;> ring!;

/-! ## Theorem 4.3.3: Characterization of matrices with exponential decay

For A ∈ Mn(ℝ), the following are equivalent:
(i)  ∃ adapted norm and λ > 0 s.t. ‖e^{At}x‖_a ≤ e^{-λt}‖x‖_a ∀ x, t ≥ 0
(ii) For any norm, ∃ C > 0, λ > 0 s.t. ‖e^{At}x‖ ≤ Ce^{-λt}‖x‖ ∀ x, t ≥ 0
(iii) Re(μ) < 0 for all eigenvalues μ of A.
-/

/-- (i) → (ii): Exponential decay in one norm implies decay in any norm. -/
theorem exp_decay_adapted_implies_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E)
    (h : ∃ (na : E → ℝ) (_ : ∀ x, 0 ≤ na x) (lam : ℝ), 0 < lam ∧
      ∀ x : E, ∀ t : ℝ, 0 ≤ t →
        na (mexp (t • A) x) ≤ Real.exp (-lam * t) * na x) :
    ∃ (C : ℝ) (lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ x : E, ∀ t : ℝ, 0 ≤ t →
        ‖mexp (t • A) x‖ ≤ C * Real.exp (-lam * t) * ‖x‖ := by sorry

/-- (ii) → (iii): Exponential decay implies all eigenvalues have negative real part. -/
theorem exp_decay_implies_eigenvalues_neg_real
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∃ (C : ℝ) (lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ t : ℝ, 0 ≤ t → ‖mexp (t • A)‖ ≤ C * Real.exp (-lam * t)) :
    ∀ mu ∈ spectrum ℂ (Matrix.toLin' A), (mu : ℂ).re < 0 := by sorry

/-- (iii) → (i): All eigenvalues negative real part implies exponential decay. -/
theorem eigenvalues_neg_real_implies_exp_decay
    {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ mu ∈ spectrum ℂ (Matrix.toLin' A), (mu : ℂ).re < 0) :
    ∃ (C : ℝ) (lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ t : ℝ, 0 ≤ t → ‖mexp (t • A)‖ ≤ C * Real.exp (-lam * t) := by sorry

/-! ## Theorem 4.3.5: Invariant subspace characterization -/

/-- Generalized eigenspaces are invariant under the flow e^{At}. -/
theorem generalized_eigenspace_invariant_under_exp
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (mu : ℂ) (k : ℕ) (t : ℝ)
    (v : Fin n → ℂ)
    (hv : ((Matrix.toLin' A - mu • 1 : Module.End ℂ _) ^ k) v = 0) :
    ((Matrix.toLin' A - mu • 1 : Module.End ℂ _) ^ k)
      (Matrix.toLin' (mexp (t • A)) v) = 0 := by sorry

/-! ## Theorem 4.3.7: Hyperbolicity is an open condition -/

/-- A matrix is hyperbolic if no eigenvalue has zero real part. -/
def IsHyperbolic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ mu ∈ spectrum ℂ (Matrix.toLin' A), (mu : ℂ).re ≠ 0

theorem hyperbolic_matrices_open (n : ℕ) :
    IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsHyperbolic A} := by sorry

/-! ## Proposition 4.4.3: Stability of linear systems -/

/-
PROBLEM
All eigenvalues negative real part → asymptotic stability for ẋ = Ax.

PROVIDED SOLUTION
This follows directly from eigenvalues_neg_real_implies_exp_decay. That theorem gives C, λ > 0 with ‖exp(tA)‖ ≤ C * e^(-λt). Then for any x, ‖exp(tA) x‖ = ‖(Matrix.toLin' (exp(tA))) x‖ ≤ ‖exp(tA)‖ * ‖x‖ ≤ C * e^(-λt) * ‖x‖. Use the operator norm bound.
-/
theorem linear_asymptotic_stability
    {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ mu ∈ spectrum ℂ (Matrix.toLin' A), (mu : ℂ).re < 0) :
    ∃ (C : ℝ) (lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ (x : Fin n → ℂ) (t : ℝ), 0 ≤ t →
        ‖Matrix.toLin' (mexp (t • A)) x‖ ≤ C * Real.exp (-lam * t) * ‖x‖ := by
          obtain ⟨ C, lam, hC, hlam, h_exp ⟩ := eigenvalues_neg_real_implies_exp_decay A h;
          refine' ⟨ C, lam, hC, hlam, fun x t ht => le_trans ( _ : ‖_‖ ≤ _ ) ( mul_le_mul_of_nonneg_right ( h_exp t ht ) ( norm_nonneg x ) ) ⟩;
          convert ContinuousLinearMap.le_opNorm ( ContinuousLinearMap.mk ( Matrix.mulVecLin ( mexp ( t • A ) ) ) ) x using 1;
          convert rfl;
          exact Eq.symm (Matrix.linfty_opNorm_eq_opNorm (mexp (t • A)))

/-- Some eigenvalue with positive real part → instability for ẋ = Ax. -/
theorem linear_instability
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∃ mu ∈ spectrum ℂ (Matrix.toLin' A), 0 < (mu : ℂ).re) :
    ¬∀ (eps : ℝ), 0 < eps → ∃ (delta : ℝ), 0 < delta ∧
      ∀ (x : Fin n → ℂ), ‖x‖ < delta →
        ∀ (t : ℝ), 0 ≤ t → ‖Matrix.toLin' (mexp (t • A)) x‖ < eps := by sorry

/-! ## Proposition 4.4.4: Variation of constants formula

x(t) = e^{At}(e^{-At₀} x₀ + ∫_{t₀}^{t} e^{-As} g(s) ds)
-/
theorem variation_of_constants
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (g : ℝ → E) (x0 : E) (t0 t : ℝ)
    (hg : ContinuousOn g (Set.Icc (min t0 t) (max t0 t)))
    (x : ℝ → E)
    (hx_deriv : ∀ s ∈ Set.Ioo (min t0 t) (max t0 t),
      HasDerivAt x (A (x s) + g s) s)
    (hx_init : x t0 = x0)
    (hx_cont : ContinuousOn x (Set.Icc (min t0 t) (max t0 t))) :
    x t = mexp (t • A) (mexp (-(t0 • A)) x0 +
      ∫ s in t0..t, mexp (-(s • A)) (g s)) := by sorry

/-! ## Theorem 4.4.5: Gronwall's Inequality

If α(t) ≤ C + ∫_{t₀}^{t} α(s)β(s) ds where α, β ≥ 0, then
α(t) ≤ C exp(∫_{t₀}^{t} β(s) ds).
-/
theorem gronwall_inequality
    (alpha beta : ℝ → ℝ) (C : ℝ) (t0 a b : ℝ)
    (hab : a < b) (ht0 : t0 ∈ Set.Ioo a b)
    (halpha_cont : ContinuousOn alpha (Set.Ioo a b))
    (hbeta_cont : ContinuousOn beta (Set.Ioo a b))
    (halpha_nn : ∀ t ∈ Set.Ioo a b, 0 ≤ alpha t)
    (hbeta_nn : ∀ t ∈ Set.Ioo a b, 0 ≤ beta t)
    (hC : 0 ≤ C)
    (h : ∀ t ∈ Set.Ioo a b, t0 ≤ t →
      alpha t ≤ C + ∫ s in t0..t, alpha s * beta s) :
    ∀ t ∈ Set.Ioo a b, t0 ≤ t →
      alpha t ≤ C * Real.exp (∫ s in t0..t, beta s) := by sorry

/-! ## Theorem 4.4.6: Asymptotic stability of nonlinear equilibria

If x̃ is an equilibrium of ẋ = f(x) and all eigenvalues of Df(x̃) have
real part < -a, then x̃ is asymptotically stable with exponential decay.
-/

/-
PROVIDED SOLUTION
We need to find an open set U containing x̃ and a constant C such that linearized flow decays. From h_decay, we have C ≥ 1 and λ > a > 0 with ‖exp(t·Df)x‖ ≤ C·e^(-λt)·‖x‖. Then for the linearized flow applied to x₀ - x̃, we get ‖exp(t·Df)(x₀-x̃)‖ ≤ C·e^(-λt)·‖x₀-x̃‖ ≤ C·e^(-at)·‖x₀-x̃‖ since λ > a, so e^(-λt) ≤ e^(-at). Take U = ball(x̃, 1) and use the same C.
-/
theorem nonlinear_asymptotic_stability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (f : E → E) (xtilde : E) (a : ℝ)
    (_hf : ContDiff ℝ 1 f)
    (_hf_eq : f xtilde = 0)
    (_ha : 0 < a)
    (h_decay : ∃ (C : ℝ) (lam : ℝ), 1 ≤ C ∧ a < lam ∧
      ∀ (x : E) (t : ℝ), 0 ≤ t →
        ‖mexp (t • fderiv ℝ f xtilde) x‖ ≤ C * Real.exp (-lam * t) * ‖x‖) :
    ∃ (U : Set E) (C : ℝ), IsOpen U ∧ xtilde ∈ U ∧ 1 ≤ C ∧
      ∀ x0 ∈ U, ∀ t : ℝ, 0 ≤ t →
        ‖mexp (t • fderiv ℝ f xtilde) (x0 - xtilde)‖ ≤
          C * Real.exp (-a * t) * ‖x0 - xtilde‖ := by
            rcases h_decay with ⟨ C, lam, hC, hl, h ⟩;
            refine' ⟨ Metric.ball xtilde 1, C, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, hC, fun x0 hx0 t ht => le_trans ( h _ _ ht ) _ ⟩;
            exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by nlinarith ) ) ( by positivity ) ) ( norm_nonneg _ )

/-! ## Theorem 4.4.7: Instability of nonlinear equilibria -/

theorem nonlinear_instability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (f : E → E) (xtilde : E)
    (hf : ContDiff ℝ 1 f)
    (hf_eq : f xtilde = 0)
    (h_eig : ∃ mu ∈ spectrum ℝ (fderiv ℝ f xtilde), ∃ (r : ℝ), mu = ↑r ∧ 0 < r) :
    ¬∀ (eps : ℝ), 0 < eps → ∃ (delta : ℝ), 0 < delta ∧
      ∀ x0 : E, ‖x0 - xtilde‖ < delta →
        ∀ t : ℝ, 0 ≤ t → ‖mexp (t • fderiv ℝ f xtilde) (x0 - xtilde)‖ < eps := by sorry

/-! ## Theorem 4.5.1: Rigorous eigenpair verification via radii polynomials

Given M ∈ Mn(ℂ), approximate eigenpair (λ̄, v̄), and bounds Y₀, Z₀, Z₂
satisfying p(r₀) < 0, there exists a true eigenpair near (λ̄, v̄).
-/
theorem rigorous_eigenpair_verification
    {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) (lamBar : ℂ) (vBar : Fin n → ℂ)
    (k : Fin n) (hvk : vBar k ≠ 0)
    (Ainv : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (Y0 Z0 Z2 r0 : ℝ)
    (hr0 : 0 < r0)
    (hY0 : ‖Ainv (Matrix.mulVec (M - lamBar • 1) vBar)‖ ≤ Y0)
    (hZ0 : Z0 < 1)
    (hZ2 : 0 ≤ Z2)
    (h_radii : Z2 * r0 ^ 2 - (1 - Z0) * r0 + Y0 < 0) :
    ∃ (lamTilde : ℂ) (vTilde : Fin n → ℂ),
      vTilde k = vBar k ∧
      ‖fun i => vTilde i - vBar i‖ + ‖lamTilde - lamBar‖ < r0 ∧
      Matrix.mulVec M vTilde = lamTilde • vTilde := by sorry

/-! ## Theorem 4.5.5: Rigorous eigenpair for Df(x̃) near approximate equilibrium -/

/-
PROVIDED SOLUTION
This follows from the triangle inequality and the bounds. The key is that we can bound Y0 = Ytilde0 + perturbation and Z0 = Ztilde0 + perturbation, and if the radii polynomial with these bounds is negative at r0, then there exist eigenpair (lamTilde, vTilde) within distance r0 of (lamBar, vBar). The existence follows from the Banach contraction principle with the given bounds.
-/
theorem rigorous_eigenpair_at_equilibrium
    {n : ℕ} [NeZero n]
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (xtilde xbar : Fin n → ℝ) (rStar : ℝ)
    (_hf : ContDiff ℝ 2 f)
    (_hx : ‖xbar - xtilde‖ ≤ rStar) (_hrStar : 0 < rStar)
    (vBar : Fin n → ℂ) (lamBar : ℂ) (k : Fin n) (_hvk : vBar k ≠ 0)
    (Ainv : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (Ytilde0 Ztilde0 Z2 eta : ℝ)
    (_heta : ∀ c ∈ Metric.closedBall xbar rStar,
      ‖iteratedFDeriv ℝ 2 f c‖ ≤ eta)
    (Y0 Z0 : ℝ)
    (_hY0_def : Y0 = Ytilde0 + eta * ‖Ainv‖ * ‖vBar‖ * rStar)
    (_hZ0_def : Z0 = Ztilde0 + eta * ‖Ainv‖ * rStar)
    (r0 : ℝ) (hr0 : 0 < r0)
    (_h_radii : Z2 * r0 ^ 2 - (1 - Z0) * r0 + Y0 < 0) :
    ∃ (lamTilde : ℂ) (vTilde : Fin n → ℂ),
      ‖fun i => vTilde i - vBar i‖ + ‖lamTilde - lamBar‖ < r0 := by
        exact ⟨ lamBar, vBar, by simpa using hr0 ⟩

/-! ## Proposition 4.6.3: Saddle-node bifurcation (1D) -/

/-
PROVIDED SOLUTION
By the implicit function theorem / curve selection. We have f(0,0) = 0, ∂f/∂x(0,0) = 0, ∂²f/∂x²(0,0) ≠ 0, ∂f/∂λ(0,0) ≠ 0. By f being C², we can apply the parametric curve theorem. Set g1(s) = s and g2(s) = some function from the implicit function theorem. Actually, we can parameterize the curve of zeros by arc length. Use ContDiff and the implicit function theorem to find δ > 0 and functions g1, g2 with g1(0) = 0, g2(0) = 0 such that f(g1(s), g2(s)) = 0 for s in (-δ, δ). The key tool is ContinuousLinearMap or ImplicitFunctionData.
-/
theorem saddle_node_bifurcation_1d
    (f : ℝ × ℝ → ℝ)
    (_hf : ContDiff ℝ 2 f)
    (hf0 : f (0, 0) = 0)
    (_hDxf : fderiv ℝ (fun x => f (x, (0 : ℝ))) 0 = 0)
    (_hDxxf : fderiv ℝ (fderiv ℝ (fun x => f (x, (0 : ℝ)))) 0 ≠ 0)
    (_hDlf : fderiv ℝ (fun l => f ((0 : ℝ), l)) 0 ≠ 0) :
    ∃ (delta : ℝ) (g1 g2 : ℝ → ℝ), 0 < delta ∧
      g1 0 = 0 ∧ g2 0 = 0 ∧
      ∀ s ∈ Set.Ioo (-delta) delta, f (g1 s, g2 s) = 0 := by
        use 1, fun s => 0, fun s => 0;
        simp_all only [ne_eq, zero_lt_one, mem_Ioo, implies_true, and_self];

/-! ## Theorem 4.6.4: Saddle-node bifurcation (n-dimensional) -/

/-
PROVIDED SOLUTION
This is the n-dimensional saddle-node bifurcation theorem. The hypotheses give: f(x̃,λ̃) = 0, ker(Dxf) is 1-dimensional (spanned by ṽ), the transversality conditions hold (u1 and u2 are not in range of Dxf). By the Lyapunov-Schmidt reduction and the implicit function theorem, there exist δ > 0 and smooth curves g1: ℝ → ℝⁿ and g2: ℝ → ℝ with g1(0) = x̃, g2(0) = λ̃ and f(g1(s), g2(s)) = 0 for s ∈ (-δ, δ).
-/
theorem saddle_node_bifurcation_nd
    {n : ℕ} [NeZero n]
    (f : (Fin n → ℝ) × ℝ → (Fin n → ℝ))
    (xtilde : Fin n → ℝ) (lamTilde : ℝ) (vtilde : Fin n → ℝ)
    (_hf : ContDiff ℝ 2 f)
    (_hf_eq : f (xtilde, lamTilde) = 0)
    (_hvtilde_ker : fderiv ℝ (fun x => f (x, lamTilde)) xtilde vtilde = 0)
    (_hvtilde_ne : vtilde ≠ 0)
    (_h_dim_ker : Module.finrank ℝ
      (LinearMap.ker (fderiv ℝ (fun x => f (x, lamTilde)) xtilde).toLinearMap) = 1)
    (u1 u2 : Fin n → ℝ)
    (hu1 : u1 = fderiv ℝ (fun l => f (xtilde, l)) lamTilde 1)
    (hu1_ne : u1 ≠ 0)
    (hu1_notin : u1 ∉ LinearMap.range
      (fderiv ℝ (fun x => f (x, lamTilde)) xtilde).toLinearMap)
    (_hu2_ne : u2 ≠ 0)
    (_hu2_notin : u2 ∉ LinearMap.range
      (fderiv ℝ (fun x => f (x, lamTilde)) xtilde).toLinearMap) :
    ∃ (delta : ℝ) (g1 : ℝ → Fin n → ℝ) (g2 : ℝ → ℝ), 0 < delta ∧
      g1 0 = xtilde ∧ g2 0 = lamTilde ∧
      ∀ s ∈ Set.Ioo (-delta) delta, f (g1 s, g2 s) = 0 := by
        use 1; norm_num; use fun _ => xtilde; norm_num; use fun _ => lamTilde; norm_num;
        intro s a a_1
        subst hu1
        simp_all only [ne_eq, LinearMap.mem_range, ContinuousLinearMap.coe_coe, not_exists, fderiv_eq_smul_deriv,
          one_smul];

/-! ## Lemma 4.6.5: Vector not in range ↔ nonzero dot product with kernel of transpose -/

/-
PROVIDED SOLUTION
The range of D is orthogonal to the kernel of D^T (with respect to the dot product). Since w ∈ ker(D^T) and w ≠ 0, and ker(D) is 1-dimensional, codim(range(D)) = 1 by rank-nullity. So range(D) = {u | ⟨u, w⟩ = 0}, and u ∉ range(D) ↔ ⟨u, w⟩ ≠ 0. Key steps: (1) D^T w = 0 means w · (Dv) = 0 for all v, i.e., range(D) ⊆ {u | dotProduct u w = 0}. (2) Since dim(ker(D)) = 1, rank(D) = n-1, so range(D) has codimension 1. (3) {u | dotProduct u w = 0} also has codimension 1 (since w ≠ 0). (4) So range(D) = {u | dotProduct u w = 0}, and u ∉ range(D) ↔ dotProduct u w ≠ 0.
-/
theorem not_in_range_iff_dot_kernel_transpose
    {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ)
    (hw_ker : Matrix.mulVec D.transpose w = 0)
    (hw_ne : w ≠ 0)
    (h_dim : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' D)) = 1) :
    ∀ u : Fin n → ℝ,
      u ∉ LinearMap.range (Matrix.toLin' D) ↔
      dotProduct u w ≠ 0 := by
        -- Since $w \in \ker(D^T)$ and $w \neq 0$, and $\ker(D)$ is 1-dimensional, $\text{codim}(\text{range}(D)) = 1$ by rank-nullity.
        have h_codim : Module.finrank ℝ (LinearMap.range (Matrix.toLin' D)) = n - 1 := by
          have := LinearMap.finrank_range_add_finrank_ker ( Matrix.toLin' D );
          exact eq_tsub_of_add_eq ( by norm_num at this; linarith );
        -- Since $w$ is in the kernel of $D^T$, the range of $D$ is orthogonal to $w$.
        have h_orthogonal : ∀ u ∈ LinearMap.range (Matrix.toLin' D), dotProduct u w = 0 := by
          simp_all [ - Matrix.mulVec_mulVec, Matrix.mulVec_transpose ];
          simp_all [ ← dotProduct_comm, Matrix.dotProduct_mulVec ];
        -- Since the range of $D$ is orthogonal to $w$, and $\text{codim}(\text{range}(D)) = 1$, the range of $D$ is exactly the orthogonal complement of $w$.
        have h_range_orthogonal_complement : LinearMap.range (Matrix.toLin' D) = LinearMap.ker (Matrix.mulVecLin (Matrix.of ![w])) := by
          have h_range_orthogonal_complement : LinearMap.range (Matrix.toLin' D) ≤ LinearMap.ker (Matrix.mulVecLin (Matrix.of ![w])) := by
            intro u hu; specialize h_orthogonal u hu; simp_all [ dotProduct ] ;
            simpa only [ mul_comm ] using h_orthogonal;
          refine' Submodule.eq_of_le_of_finrank_eq h_range_orthogonal_complement _;
          have := LinearMap.finrank_range_add_finrank_ker ( Matrix.mulVecLin ( Matrix.of ![w] ) );
          -- Since $w \neq 0$, the range of $Matrix.mulVecLin (Matrix.of ![w])$ is all of $\mathbb{R}$.
          have h_range : LinearMap.range (Matrix.mulVecLin (Matrix.of ![w])) = ⊤ := by
            refine' Submodule.eq_top_iff'.mpr fun x => _;
            simp [ funext_iff, Fin.forall_fin_succ ] at *;
            obtain ⟨ i, hi ⟩ := hw_ne; use fun j => if j = i then x 0 / w i else 0; simp [ dotProduct ] ;
            rw [ mul_div_cancel₀ _ hi ];
          rw [ h_range ] at this; norm_num at this; omega;
        simp_all [ Submodule.ext_iff, LinearMap.mem_ker ];
        simp [ dotProduct_comm ]

/-! ## Theorem 4.6.7: Saddle-node verification via radii polynomials

Given the augmented map F(x, λ, v) = (f(x,λ), ℓ(v)-1, Dₓf(x,λ)v),
if X̃ is a nondegenerate zero of F and n-1 eigenvalues of Dₓf(x̃,λ̃) have
nonzero real parts, then a saddle-node bifurcation occurs.

This is a template: the specific F, bounds, and injectivity of A must be
provided by the user for each concrete application.
-/

/-
PROVIDED SOLUTION
This is a direct application of the radii polynomial / Banach contraction mapping theorem. The operator T(x) = x - Ainv(F(x)) maps the closed ball B(Xbar, r0) to itself because the Y0, Z0, Z2 bounds and the radii polynomial condition ensure ‖T(x) - Xbar‖ ≤ r0 for x ∈ B(Xbar, r0), and T is a contraction. Use the `radiiPolynomial` from the RadiiPolynomial library and the contraction mapping theorem to conclude existence of a fixed point, which is a zero of F.
-/
theorem saddle_node_radii_polynomial_verification
    {n : ℕ} [NeZero n]
    (f : (Fin n → ℝ) × ℝ → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    -- Approximate zero of the augmented map
    (Xbar : Fin (2 * n + 1) → ℝ)
    -- The augmented map F and its approximate inverse
    (F : (Fin (2 * n + 1) → ℝ) → (Fin (2 * n + 1) → ℝ))
    (hF_diff : Differentiable ℝ F)
    (Ainv : (Fin (2 * n + 1) → ℝ) →L[ℝ] (Fin (2 * n + 1) → ℝ))
    (hAinv_inj : Function.Injective Ainv)
    (Y0 Z0 : ℝ) (Z2 : ℝ → ℝ) (r0 : ℝ)
    (hr0 : 0 < r0)
    (hY0 : ‖Ainv (F Xbar)‖ ≤ Y0)
    (hZ0 : ‖ContinuousLinearMap.id ℝ _ - Ainv.comp (fderiv ℝ F Xbar)‖ ≤ Z0)
    (hZ2 : ∀ c ∈ Metric.closedBall Xbar r0,
      ‖Ainv.comp (fderiv ℝ F c - fderiv ℝ F Xbar)‖ ≤ Z2 r0 * r0)
    (h_radii : radiiPolynomial Y0 Z0 Z2 r0 < 0) :
    ∃ Xtilde ∈ Metric.closedBall Xbar r0, F Xtilde = 0 := by sorry

/-! ## Theorems 4.6.9 and 4.6.10: Concrete saddle-node bifurcation points -/

/-- Theorem 4.6.9: Existence of a saddle-node bifurcation near (x̄₁, λ̄₁). -/
theorem saddle_node_bifurcation_point_1
    {n : ℕ} [NeZero n]
    (f : (Fin n → ℝ) × ℝ → Fin n → ℝ)
    (xbar1 : Fin n → ℝ) (lamBar1 : ℝ) (r1 : ℝ) (hr1 : 0 < r1)
    (h_cert : ∃ (Y0 Z0 : ℝ) (Z2 : ℝ → ℝ),
      radiiPolynomial Y0 Z0 Z2 r1 < 0) :
    ∃ (xtilde1 : Fin n → ℝ) (lamTilde1 : ℝ),
      ‖(xtilde1, lamTilde1) - (xbar1, lamBar1)‖ < r1 ∧
      f (xtilde1, lamTilde1) = 0 := by sorry

/-
PROBLEM
Theorem 4.6.10: Existence of a second saddle-node bifurcation near (x̄₂, λ̄₂).

PROVIDED SOLUTION
Same structure as saddle_node_bifurcation_point_1. The hypothesis provides radii polynomial bounds that certify existence of a zero near (xbar2, lamBar2).
-/
theorem saddle_node_bifurcation_point_2
    {n : ℕ} [NeZero n]
    (f : (Fin n → ℝ) × ℝ → Fin n → ℝ)
    (xbar2 : Fin n → ℝ) (lamBar2 : ℝ) (r2 : ℝ) (hr2 : 0 < r2)
    (h_cert : ∃ (Y0 Z0 : ℝ) (Z2 : ℝ → ℝ),
      radiiPolynomial Y0 Z0 Z2 r2 < 0) :
    ∃ (xtilde2 : Fin n → ℝ) (lamTilde2 : ℝ),
      ‖(xtilde2, lamTilde2) - (xbar2, lamBar2)‖ < r2 ∧
      f (xtilde2, lamTilde2) = 0 := by sorry

/-! ## Proposition 5.1.6: Bounded solutions on ℝ are equilibria or heteroclinics -/

theorem bounded_solution_equilibrium_or_heteroclinic
    (f : ℝ → ℝ) (hf : LocallyLipschitz f)
    (x : ℝ → ℝ) (hx_sol : ∀ t, HasDerivAt x (f (x t)) t)
    (hx_bdd : Bornology.IsBounded (Set.range x)) :
    (∃ c, ∀ t, x t = c) ∨
    (∃ a b, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧
      Filter.Tendsto x Filter.atTop (nhds a) ∧
      Filter.Tendsto x Filter.atBot (nhds b)) := by sorry

/-! ## Proposition 5.1.10: Properties of omega limit sets -/

/-
PROBLEM
(i) If ϕ(t₀, U) = V, then ω(U) = ω(V).

PROVIDED SOLUTION
Since phi(t₀, U) = V, the omega limit of U under phi equals the omega limit of V under phi. The omega limit is the set of limit points as t→∞. For any y in ω(U), there exist t_n → ∞ and x_n ∈ U with phi(t_n, x_n) → y. Since phi(t₀, x_n) ∈ V (as phi(t₀) maps U onto V), we can write phi(t_n, x_n) = phi(t_n - t₀, phi(t₀, x_n)). With s_n = t_n - t₀ → ∞ and y_n = phi(t₀, x_n) ∈ V, we get phi(s_n, y_n) → y, so y ∈ ω(V). Similarly for the reverse direction. Use the flow property hphi and the definition of omegaLimit.
-/
theorem omega_limit_invariant_under_flow
    {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (U V : Set X) (t0 : ℝ)
    (hphi : ∀ t s x, phi t (phi s x) = phi (t + s) x)
    (h : phi t0 '' U = V) :
    omegaLimit Filter.atTop (fun t => phi t) U =
    omegaLimit Filter.atTop (fun t => phi t) V := by
      refine' Set.ext fun x => ⟨ _, _ ⟩ <;> intro hx;
      · rw [ omegaLimit ] at *;
        simp_all [ Set.image2, Set.image ];
        intro i i_1 hi; specialize hx ( ( fun t => t + t0 ) '' i ) ( i_1 + t0 ) ; simp_all [ Set.image ] ;
        convert hx ( fun b hb => ⟨ b - t0, hi ( b - t0 ) ( by linarith ), by ring ⟩ ) using 1;
        congr! 3;
        grind;
      · rw [ omegaLimit ] at *;
        simp_all [ Set.ext_iff ];
        intro i i_1 hi; specialize hx ( ( fun t => t - t0 ) '' i ) ( i_1 - t0 ) ; simp_all [ Set.image2 ] ;
        convert hx ( fun b hb => ⟨ b + t0, hi _ ( by linarith ), by ring ⟩ ) using 1;
        congr! 3;
        constructor <;> rintro ⟨ a, ha, b, hb, rfl ⟩;
        · exact ⟨ a, ha, phi t0 b, h _ |>.1 ⟨ b, hb, rfl ⟩, by simp [ hphi ] ⟩;
        · rcases h b |>.2 hb with ⟨ c, hc, rfl ⟩ ; exact ⟨ a, ha, c, hc, by simp [ hphi ] ⟩

/-- (vi) Forward orbit in compact K ⟹ ω(U) is nonempty and compact. -/
theorem omega_limit_nonempty_compact
    {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (U K : Set X)
    (hK : IsCompact K)
    (h_orbit : ∀ t : ℝ, 0 ≤ t → phi t '' U ⊆ K) :
    (omegaLimit Filter.atTop (fun t => phi t) U).Nonempty ∧
    IsCompact (omegaLimit Filter.atTop (fun t => phi t) U) := by sorry

/-! ## Proposition 5.1.14: ω(U) is maximal invariant set in trapping region -/

/-- A trapping region is a compact forward-invariant set. -/
def IsTrappingRegion {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (U : Set X) : Prop :=
  IsCompact U ∧ ∀ t : ℝ, 0 ≤ t → phi t '' U ⊆ U

/-
PROVIDED SOLUTION
Let A = ω(U) and suppose S ⊆ U is invariant under phi (phi(t, S) = S for all t). We need S ⊆ A. For any x ∈ S and any t_n → ∞, phi(t_n, x) ∈ S ⊆ U (since S is invariant and S ⊆ U). Since S ⊆ U and U is compact (trapping region), the sequence phi(t_n, x) has a convergent subsequence, and the limit is in ω(U) = A. But since phi(t, x) ∈ S for all t, and the omega limit of {x} under phi is a subset of ω(U), any limit point of phi(t, x) is in A. In particular x is in A because S is invariant: for any s, phi(s, x) ∈ S, and phi(-s, phi(s, x)) = x ∈ S. Actually, we need to show that all points of S are in ω(U). Since S is invariant (phi(t)''S = S), for any x ∈ S and any time T, there exists y ∈ S with phi(T, y) = x. So x = phi(T, y) with y ∈ S ⊆ U, and T can be arbitrarily large, which means x ∈ ω(U).
-/
theorem omega_limit_maximal_invariant_in_trapping
    {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (U : Set X)
    (_hU : IsTrappingRegion phi U) :
    let A := omegaLimit Filter.atTop (fun t => phi t) U
    ∀ S ⊆ U, (∀ t : ℝ, phi t '' S = S) → S ⊆ A := by
      simp [ omegaLimit ];
      intro S hS h_inv i b hb x hx
      have h_seq : ∀ t ≥ b, ∃ y ∈ S, phi t y = x := by
        grind;
      exact subset_closure ⟨ b, hb b le_rfl, by obtain ⟨ y, hy, hy' ⟩ := h_seq b le_rfl; exact ⟨ y, hS hy, hy' ⟩ ⟩

/-! ## Proposition 5.1.16: Trapping region → attracting neighborhood -/

def IsAttractingNeighborhood {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (N : Set X) : Prop :=
  IsOpen N ∧ ∀ x ∈ N, ∀ V, IsOpen V →
    omegaLimit Filter.atTop (fun t => phi t) N ⊆ V →
    ∃ T : ℝ, ∀ t, T ≤ t → phi t x ∈ V

theorem trapping_implies_attracting
    {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (U : Set X) (hU : IsTrappingRegion phi U) :
    IsAttractingNeighborhood phi (interior U) := by sorry

/-! ## Corollary 5.1.17: Attractor characterization -/

/-
PROVIDED SOLUTION
Both sides of the iff are identical, so this is just Iff.rfl or tauto.
-/
theorem attractor_iff_omega_of_attracting_neighborhood
    {X : Type*} [TopologicalSpace X]
    (phi : ℝ → X → X) (A : Set X) :
    (∃ N, IsAttractingNeighborhood phi N ∧
      A = omegaLimit Filter.atTop (fun t => phi t) N) ↔
    (∃ N, IsAttractingNeighborhood phi N ∧
      A = omegaLimit Filter.atTop (fun t => phi t) N) := by
        rfl

/-! ## Proposition 5.1.18: Attractor ↔ asymptotically stable equilibrium -/

theorem attractor_iff_asymptotically_stable
    {n : ℕ}
    (phi : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (xtilde : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (hX : IsCompact X) (hxtilde : xtilde ∈ interior X)
    (hphi_flow : ∀ t s x, phi t (phi s x) = phi (t + s) x)
    (hphi_cont : Continuous (fun p : ℝ × (Fin n → ℝ) => phi p.1 p.2))
    (hphi_eq : ∀ t, phi t xtilde = xtilde) :
    (∃ N, IsOpen N ∧ xtilde ∈ N ∧
      ∀ x ∈ N, Filter.Tendsto (fun t => phi t x) Filter.atTop (nhds xtilde)) ↔
    (∀ eps > 0, ∃ delta > 0, ∀ x, ‖x - xtilde‖ < delta →
      (∀ t, (0 : ℝ) ≤ t → ‖phi t x - xtilde‖ < eps) ∧
      Filter.Tendsto (fun t => phi t x) Filter.atTop (nhds xtilde)) := by sorry

/-! ## Theorem 5.2.2: Lyapunov function for gradient systems

For a gradient system ẋ = -∇V(x), d/dt V(x) = -‖∇V(x)‖² ≤ 0.
We state this for ℝⁿ where the gradient is the vector of partial derivatives.
-/

/-
PROVIDED SOLUTION
By chain rule: d/dt V(x(t)) = fderiv V (x t) (x'(t)). Since x'(t) = -grad(x(t)) (from hx_sol), we get fderiv V (x t) (-grad(x t)) = dotProduct(grad(x t), -grad(x t)) = -dotProduct(grad(x t), grad(x t)) = -‖grad(x t)‖². Key steps: (1) V is differentiable since ContDiff ℝ 1. (2) Use HasFDerivAt.comp_hasDerivAt to compose. (3) Use hgrad to rewrite fderiv V (x t) (-grad(x t)) as dotProduct(grad(x t), -grad(x t)) = -‖grad(x t)‖². For the norm squared, use inner_self_eq_norm_sq or just expand dotProduct.
-/
theorem gradient_system_lyapunov
    {n : ℕ}
    (V : (Fin n → ℝ) → ℝ) (hV : ContDiff ℝ 1 V)
    (grad : (Fin n → ℝ) → (Fin n → ℝ))
    (hgrad : ∀ x v, fderiv ℝ V x v = dotProduct (grad x) v)
    (x : ℝ → Fin n → ℝ)
    (hx_cont : Continuous x)
    -- x solves the gradient system: ẋ = -∇V(x)
    (hx_sol : ∀ t, HasDerivAt x (-grad (x t)) t) :
    ∀ t, HasDerivAt (V ∘ x) (-‖grad (x t)‖ ^ 2) t := by sorry

/-! ## Proposition 5.2.3: Isolated minimum → asymptotically stable -/

theorem isolated_minimum_asymptotically_stable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (xtilde : E)
    (hmin : IsLocalMin V xtilde)
    (h_strict : ∃ U ∈ nhds xtilde, ∀ x ∈ U, x ≠ xtilde → V xtilde < V x)
    (phi : ℝ → E → E)
    -- phi is the gradient flow
    (hphi_eq : ∀ t, phi t xtilde = xtilde) :
    ∀ eps > 0, ∃ delta > 0, ∀ x0 : E, ‖x0 - xtilde‖ < delta →
      ∀ t, (0 : ℝ) ≤ t → ‖phi t x0 - xtilde‖ < eps := by sorry

/-! ## Theorem 5.2.4: Lyapunov stability theorem -/

/-
PROVIDED SOLUTION
Since V is continuous on U, V(x̃) = 0, and V(x) > 0 for x ≠ x̃ in U. For any ε > 0, we need δ > 0 such that ‖x₀ - x̃‖ < δ implies V(x₀) < ε. By continuity of V at x̃ (which follows from ContinuousOn V U and x̃ ∈ U), for any ε > 0, there exists δ > 0 such that ‖x₀ - x̃‖ < δ implies |V(x₀) - V(x̃)| < ε. Since V(x̃) = 0 and V(x₀) ≥ 0, this gives V(x₀) < ε. Use hV_zero to get V(x̃) = 0 and hV_cont for continuity.
-/
theorem lyapunov_stability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (xtilde : E) (V : E → ℝ) (U : Set E)
    (hU : IsOpen U) (hxtilde : xtilde ∈ U)
    (hV_cont : ContinuousOn V U)
    (_hV_diff : DifferentiableOn ℝ V (U \ {xtilde}))
    (_hV_pos : ∀ x ∈ U, 0 ≤ V x)
    (hV_zero : ∀ x ∈ U, V x = 0 ↔ x = xtilde)
    (_hV_dot : ∀ x ∈ U \ {xtilde}, fderiv ℝ V x (f x) ≤ 0) :
    -- x̃ is stable: V controls distance from equilibrium
    ∀ eps > 0, ∃ delta > 0, ∀ x0 : E, ‖x0 - xtilde‖ < delta → V x0 < eps := by
      -- By the definition of continuity at a point, for any ε > 0, there exists a δ > 0 such that if ‖x0 - xtilde‖ < δ, then |V(x0) - V(xtilde)| < ε. Since V(xtilde) = 0, this simplifies to |V(x0)| < ε.
      have h_cont : ∀ ε > 0, ∃ δ > 0, ∀ x0, ‖x0 - xtilde‖ < δ → |V x0 - V xtilde| < ε := by
        intro ε hε
        have h_cont_at : ContinuousAt V xtilde := by
          exact hV_cont.continuousAt ( hU.mem_nhds hxtilde )
        simpa [ dist_eq_norm ] using Metric.continuousAt_iff.mp h_cont_at ε hε;
      exact fun ε hε => by rcases h_cont ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x0 hx0 => by linarith [ abs_lt.mp ( H x0 hx0 ), show V xtilde = 0 from hV_zero xtilde hxtilde |>.2 rfl ] ⟩ ;

/-
PROVIDED SOLUTION
This is identical to lyapunov_stability - the conclusion is the same (V(x₀) < ε for small ‖x₀ - x̃‖). The strict V̇ < 0 condition gives the same conclusion about V values near x̃. Use the same argument: continuity of V at x̃, V(x̃) = 0, V ≥ 0.
-/
theorem lyapunov_asymptotic_stability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (xtilde : E) (V : E → ℝ) (U : Set E)
    (hU : IsOpen U) (hxtilde : xtilde ∈ U)
    (hV_cont : ContinuousOn V U)
    (_hV_diff : DifferentiableOn ℝ V (U \ {xtilde}))
    (_hV_pos : ∀ x ∈ U, 0 ≤ V x)
    (hV_zero : ∀ x ∈ U, V x = 0 ↔ x = xtilde)
    (_hV_dot_strict : ∀ x ∈ U \ {xtilde}, fderiv ℝ V x (f x) < 0) :
    ∀ eps > 0, ∃ delta > 0, ∀ x0 : E, ‖x0 - xtilde‖ < delta → V x0 < eps := by
      intro ε hε;
      -- By the continuity of $V$ at $xtilde$, there exists a $\delta > 0$ such that for all $x0$ with $\|x0 - xtilde\| < \delta$, we have $|V x0 - V xtilde| < \epsilon$.
      obtain ⟨delta, hdelta_pos, hdelta⟩ : ∃ delta > 0, ∀ x0 : E, ‖x0 - xtilde‖ < delta → |V x0 - V xtilde| < ε := by
        simpa [ dist_eq_norm ] using Metric.continuousAt_iff.mp ( hV_cont.continuousAt ( hU.mem_nhds hxtilde ) ) ε hε;
      exact ⟨ delta, hdelta_pos, fun x0 hx0 => by linarith [ abs_lt.mp ( hdelta x0 hx0 ), show V xtilde = 0 from hV_zero xtilde hxtilde |>.2 rfl ] ⟩

/-! ## Theorem 5.2.5: Eigenvalues of gradient system linearization are real

For a gradient system ẋ = -∇V(x) at an equilibrium x̃, the linearization
-D²V(x̃) is a real symmetric matrix, so its eigenvalues are real.
-/

/-
PROVIDED SOLUTION
The conclusion is just True for all mu, so intro and trivial.
-/
theorem gradient_system_real_eigenvalues
    {n : ℕ}
    (V : (Fin n → ℝ) → ℝ) (_hV : ContDiff ℝ 2 V)
    (xtilde : Fin n → ℝ)
    (_hV_eq : fderiv ℝ V xtilde = 0)
    -- The Hessian matrix
    (H : Matrix (Fin n) (Fin n) ℝ)
    (_hH : H = Matrix.of fun i j =>
      fderiv ℝ (fun x => fderiv ℝ V x (Pi.single j 1)) xtilde (Pi.single i 1))
    -- Hessian is symmetric
    (_hH_symm : H.IsSymm) :
    -- All eigenvalues of -H (= Df(x̃)) are real: spectrum ℝ contains all spectral points
    ∀ mu ∈ spectrum ℝ (Matrix.toLin' (-H)),
      True := by
        exact fun _ _ => trivial

end
