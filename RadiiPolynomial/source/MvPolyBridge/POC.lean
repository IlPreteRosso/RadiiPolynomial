import RadiiPolynomial.source.MvPolyBridge.Basic
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# MvPolyBridge — Proof of Concept

Testing three layers of the MvPolyBridge design:
1. **evalInBanach basics**: Can `simp` evaluate `aeval` on `C r * (X i - X j)` etc.?
2. **Master bridge**: Can we extract coefficients from `evalInBanach` to ℚ?
3. **pderiv↔fderiv bridge**: Can we connect algebraic `pderiv` to analytic `fderiv`?
-/

open MvPolynomial
open RadiiPolynomial MvPolyBridge
open ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

/-! ## Layer 1: evalInBanach basics

Test whether `simp` can reduce `aeval f p` for concrete MvPolynomials
in the Banach algebra `l1Weighted ν`. -/

section Layer1

variable (a : Fin 3 → l1Weighted ν)

-- Test 1a: aeval on variable
example : evalInBanach (X 0 : MvPolynomial (Fin 3) ℚ) a = a 0 := by
  simp [evalInBanach]

-- Test 1b: aeval on product of variables
example : evalInBanach (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) a = a 0 * a 1 := by
  simp [evalInBanach]

-- Test 1c: aeval on subtraction of variables
example : evalInBanach (X 1 - X 0 : MvPolynomial (Fin 3) ℚ) a = a 1 - a 0 := by
  simp [evalInBanach]

-- Test 1d: aeval on C r — this gives algebraMap ℚ (l1Weighted ν) r
-- The question: does it simplify to (r : ℝ) • 1 or similar?
example : evalInBanach (C (10 : ℚ) : MvPolynomial (Fin 3) ℚ) a =
    algebraMap ℚ (l1Weighted ν) 10 := by
  simp [evalInBanach]

-- Test 1e: The key test — C r * (X i - X j) should become algebraMap(r) * (a i - a j)
-- Can simp close this, or do we need extra lemmas?
example : evalInBanach (C 10 * (X 1 - X 0) : MvPolynomial (Fin 3) ℚ) a =
    algebraMap ℚ (l1Weighted ν) 10 * (a 1 - a 0) := by
  simp [evalInBanach]

-- Test 1f: Can we go further and get (10 : ℝ) • (a 1 - a 0)?
-- Uses ratSmul_eq from LpOneBanachAlgebra.lean to bridge ℚ-smul → ℝ-smul.
example : evalInBanach (C 10 * (X 1 - X 0) : MvPolynomial (Fin 3) ℚ) a =
    (10 : ℝ) • (a 1 - a 0) := by
  simp only [evalInBanach, map_mul, map_sub, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_sub]
  norm_cast

end Layer1

/-! ## Layer 2: Master bridge (coefficient extraction)

Test whether we can prove `toSeq(evalInBanach p a) n = (mvPolyCoeffQ p arrs n : ℝ)`
for simple polynomials. Start with the base cases. -/

section Layer2

-- Test 2a: Variable — evalInBanach (X i) a = a i, so toSeq matches directly
example (a : Fin 3 → l1Weighted ν) (arrs : Fin 3 → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ))
    (n : ℕ) :
    l1Weighted.toSeq (evalInBanach (X 0 : MvPolynomial (Fin 3) ℚ) a) n =
      (mvPolyCoeffQ (X 0) arrs n : ℝ) := by
  simp only [evalInBanach, aeval_X]
  rw [ha]
  -- Need to show: ((arrs 0).getD n 0 : ℝ) = (mvPolyCoeffQ (X 0) arrs n : ℝ)
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, arrayToPowerSeries]
  -- eval₂ of X 0 in PowerSeries should give the 0-th power series
  simp [eval₂_X]

-- Test 2b: Product — the hard case, needs CauchyProduct.ratCast
example (a : Fin 3 → l1Weighted ν) (arrs : Fin 3 → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ))
    (n : ℕ) :
    l1Weighted.toSeq (evalInBanach (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) a) n =
      (mvPolyCoeffQ (X 0 * X 1) arrs n : ℝ) := by
  simp only [evalInBanach, map_mul, aeval_X]
  -- LHS: toSeq(a 0 * a 1) n = CauchyProduct(toSeq(a 0))(toSeq(a 1)) n
  -- RHS: mvPolyCoeffQ(X 0 * X 1) arrs n = coeff n (eval₂ C arrs (X 0 * X 1))
  --     = coeff n (arrs 0 * arrs 1) = CauchyProduct(arrs 0.getD)(arrs 1.getD) n
  -- Bridge: CauchyProduct.ratCast + ha
  show CauchyProduct (l1Weighted.toSeq (a 0)) (l1Weighted.toSeq (a 1)) n = _
  rw [show l1Weighted.toSeq (a 0) = fun k => ((arrs 0).getD k 0 : ℝ) from funext (ha 0),
      show l1Weighted.toSeq (a 1) = fun k => ((arrs 1).getD k 0 : ℝ) from funext (ha 1),
      CauchyProduct.ratCast]
  -- Now need: (CauchyProduct (arrs 0).getD (arrs 1).getD n : ℝ) = (mvPolyCoeffQ ... : ℝ)
  congr 1
  simp only [mvPolyCoeffQ, mvPolyToPowerSeries, arrayToPowerSeries]
  simp [eval₂_X, PowerSeries.coeff_mul]
  -- CauchyProduct vs PowerSeries.coeff of product — should be definitional
  rfl

end Layer2

/-! ## Layer 3: pderiv↔fderiv bridge

The key question: can we prove that `fderiv` of `evalInBanach p` relates to
`pderiv` of `p` evaluated via `evalInBanach`?

Target statement (for simple polynomial on Pi type):
  fderiv ℝ (fun a => evalInBanach p a) ā =
    ∑ i, (leftMul (evalInBanach (pderiv i p) ā)).comp (proj i)

Strategy: prove for base cases (C, X), then for +, *, show induction works. -/

section Layer3

variable (ā : Fin 3 → l1Weighted ν)

-- Test 3a: pderiv computation — does simp handle it?
example : pderiv (0 : Fin 3) (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) = X 1 := by
  rw [MvPolynomial.pderiv_mul]; simp

example : pderiv (1 : Fin 3) (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) = X 0 := by
  rw [MvPolynomial.pderiv_mul]; simp

example : pderiv (2 : Fin 3) (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) = 0 := by
  rw [MvPolynomial.pderiv_mul]; simp

-- Test 3b: fderiv of evalInBanach for X i (variable)
-- evalInBanach (X i) a = a i, so fderiv = proj i
-- Need: show that evalInBanach (X 0) reduces to (· 0), then auto_poly_fderiv
example : fderiv ℝ (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0) a) ā =
    proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) 0 := by
  -- evalInBanach (X 0) a = aeval a (X 0) = a 0
  have : (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0) a) =
      (fun a => a 0) := by ext a; simp [evalInBanach]
  rw [this]
  auto_poly_fderiv

-- Test 3c: fderiv of evalInBanach for X 0 * X 1 (product)
example : fderiv ℝ (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0 * X 1) a) ā =
    (l1Weighted.leftMul (ā 0)).comp (proj 1) +
    (l1Weighted.leftMul (ā 1)).comp (proj 0) := by
  have : (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0 * X 1) a) =
      (fun a => a 0 * a 1) := by ext a; simp [evalInBanach]
  rw [this]
  auto_poly_fderiv

-- Test 3d: The bridge lemma for X 0 * X 1
-- fderiv(evalInBanach p)(ā) = Σ_i leftMul(evalInBanach(pderiv i p) ā) ∘ proj i
example : fderiv ℝ (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0 * X 1) a) ā =
    ∑ i : Fin 3,
      (l1Weighted.leftMul (evalInBanach (pderiv i (X 0 * X 1)) ā)).comp
        (proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) i) := by
  -- Step 1: Simplify evalInBanach to concrete expression
  have hfun : (fun a : Fin 3 → l1Weighted ν => evalInBanach (X 0 * X 1) a) =
      (fun a => a 0 * a 1) := by ext a; simp [evalInBanach]
  rw [hfun]
  -- Step 2: Simplify pderiv i for each i, then evalInBanach
  conv_rhs =>
    arg 2; ext i
    rw [show pderiv i (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) =
      pderiv i (X 0) * X 1 + X 0 * pderiv i (X 1) from MvPolynomial.pderiv_mul]
  -- Step 3: Expand Fin 3 sum and simplify
  rw [Fin.sum_univ_three]
  simp [evalInBanach]
  -- After simp: pderiv side matches fderiv canonical form up to add_comm.
  rw [add_comm]
  auto_poly_fderiv

-- Test 3e: Lorenz component 0 — fderiv of direct definition (already works)
example :
    fderiv ℝ (fun a : Fin 3 → l1Weighted ν =>
      (10 : ℝ) • (a 1 - a 0)) ā =
    (10 : ℝ) • (proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) 1 -
      proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) 0) := by
  auto_poly_fderiv

-- Test 3f: Lorenz component 1 — bilinear terms (already works)
example :
    fderiv ℝ (fun a : Fin 3 → l1Weighted ν =>
      (28 : ℝ) • a 0 - a 1 - a 0 * a 2) ā =
    (28 : ℝ) • proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) 0 -
      proj (R := ℝ) (φ := fun _ : Fin 3 => l1Weighted ν) 1 -
    ((l1Weighted.leftMul (ā 0)).comp (proj 2) +
     (l1Weighted.leftMul (ā 2)).comp (proj 0)) := by
  auto_poly_fderiv

end Layer3

/-! ## Layer 4: Degree-based Z₂ automation

For degree ≤ 2 polynomials, `pderiv i (pderiv j p)` should be constant
(no variables), meaning D²φ is constant → bilinear bound for Z₂. -/

section Layer4

-- Test 4a: second pderiv of X 0 * X 1 is constant
example : pderiv (0 : Fin 3) (pderiv (1 : Fin 3) (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)) =
    C 1 := by
  simp

-- Test 4b: second pderiv of X 0 * X 1 wrt same variable is 0
example : pderiv (0 : Fin 3) (pderiv (0 : Fin 3) (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)) =
    0 := by
  simp

-- Test 4c: second pderiv of linear term C 10 * X 0 is 0
example : pderiv (0 : Fin 3) (pderiv (0 : Fin 3) (C 10 * X 0 : MvPolynomial (Fin 3) ℚ)) =
    0 := by
  simp

-- Test 4d: Lorenz φ₁ = 28*X₀ - X₁ - X₀*X₂ — all second pderivs are constant
-- ∂²φ₁/∂x₀∂x₂ = -1 (from the -X₀*X₂ term)
example : pderiv (0 : Fin 3) (pderiv (2 : Fin 3)
    (C 28 * X 0 - X 1 - X 0 * X 2 : MvPolynomial (Fin 3) ℚ)) = C (-1) := by
  simp

end Layer4
