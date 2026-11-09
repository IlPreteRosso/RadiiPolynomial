import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Numbers

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: the numerical clauses

The third carrier of the same Duffing problem: the combined amplitude weight
`m_n = (6/5)^{|n|} (1 + |n|)²` (mass `ω_n = m_n²`) on `ℓ²(ℤ; ℂ)`, with no renormalization. The
centre `ā` and the head matrix `M` are the shipped exact rational leaf `leaf` of
`Examples/Fourier/Duffing/Numbers.lean`, read through the leaf-parametric mirror of the
rational-leaf adapter `Certification/Fourier/Quadratic.lean` without copies; the finite formulas
of `Polynomial/Numbers.lean` are parameterized by the rational weight `w` (`yTermW`, `zRowW`,
`hRowW`, `aRowW`, `betaBoundW`, …) and evaluated at `wQ n = (6/5)^{|n|} (1 + |n|)²`. The
weight-free tail constants `tailQ = 1/117` and `t2Q = 484/287469` are those of
`Polynomial/Numbers.lean`. Nothing here reads the geometric certified zero.

This module is finite arithmetic only. The bound constants are `Y₀ = 117/500000`, `Z₀ = 1/400`,
`H = 1/200`, `‖2ā‖ ≤ 289/20`, `Z₁ = 1237/10000`, radius `3/10000` and `Z₂ = 42`; `Z₂` comes from
the exact squared row majorant `UsqQ` of `M` and `t2Q` through `4 (UsqQ + t2Q) ≤ Z₂²`
(`CurvCheck`, one `decide +kernel`). Every clause of `Checks` is consumed by
`Combined/Certificate.lean`; the whole bundle is ONE `native_decide`.
-/

namespace FourierDuffing.Combined.Numbers

open FourierDuffing.Numbers RadiiPolynomial.Certification.Fourier.Quadratic

section Formulas

variable (w : ℤ → ℚ)

/-- Squared weighted residual summand at the weight `w`. -/
def yTermW (n : ℤ) : ℚ := cnormSq (leaf.GQ n) * w n ^ 2
def yPartW (k : ℕ) : ℚ := qsum (y0Chunk k) (yTermW w)
def ySquaredW : ℚ := yPartW w 0 + yPartW w 1 + yPartW w 2
/-- Weighted rows/columns of the finite defect `I − M DF` at the weight `w`. -/
def zRowW (i : ℤ) : ℚ := qsum (idx 10) fun j => reim (leaf.EQ i j) * w i / w j
def zColW (j : ℤ) : ℚ := qsum (idx 10) fun i => reim (leaf.EQ i j) * w i / w j
/-- Weighted rows/columns of the composed leakage at the weight `w`. -/
def hRowW (i : ℤ) : ℚ := qsum (leakColsQ 10 7) fun k => reim (leaf.KMQ i k) * w i / w k
def hColW (k : ℤ) : ℚ := qsum (idx 10) fun i => reim (leaf.KMQ i k) * w i / w k
/-- Weighted rows of `M` at the weight `w`. -/
def aRowW (i : ℤ) : ℚ := qsum (idx 10) fun j => reim (leaf.MQ i j) * w i / w j
def UsqW : ℚ := qsum (idx 10) fun i => aRowW w i ^ 2
/-- Weighted `ℓ¹` symbol majorant of `2ā` at the weight `w`. -/
def betaBoundW : ℚ := qsum (idx 10) fun k => 2 * reim (leaf.abarQ k) * w k

end Formulas

/-! ### The combined weight and the formulas at it -/

/-- Combined amplitude weight `(6/5)^{|n|} (1 + |n|)²`; the `ℓ²` mass is its square. -/
def wQ (n : ℤ) : ℚ := (6 / 5 : ℚ) ^ n.natAbs * (1 + (n.natAbs : ℚ)) ^ 2

theorem wQ_pos (n : ℤ) : 0 < wQ n := by unfold wQ; positivity

def ySquaredQ : ℚ := ySquaredW wQ
def zRowQ : ℤ → ℚ := zRowW wQ
def zColQ : ℤ → ℚ := zColW wQ
def hRowQ : ℤ → ℚ := hRowW wQ
def hColQ : ℤ → ℚ := hColW wQ
def aRowQ : ℤ → ℚ := aRowW wQ
def UsqQ : ℚ := UsqW wQ
def betaBoundQ : ℚ := betaBoundW wQ

def Y0Q : ℚ := 117 / 500000
def Z0Q : ℚ := 1 / 400
def HQ : ℚ := 1 / 200
def betaQ : ℚ := 289 / 20
def Z1Q : ℚ := 1237 / 10000
def Z2Q : ℚ := 42
def radiusQ : ℚ := 3 / 10000

def RzQ : ℚ := 13 / 10000
def CzQ : ℚ := 9 / 2000
def RhQ : ℚ := 47 / 10000
def ChQ : ℚ := 51 / 10000

def Y0Check : Prop := ySquaredQ ≤ Y0Q ^ 2

def Z0Check : Prop :=
  (∀ i ∈ idx 10, zRowQ i ≤ RzQ) ∧
  (∀ j ∈ idx 10, zColQ j ≤ CzQ) ∧ RzQ * CzQ ≤ Z0Q ^ 2

def HCheck : Prop :=
  (∀ i ∈ idx 10, hRowQ i ≤ RhQ) ∧
  (∀ k ∈ leakColsQ 10 7, hColQ k ≤ ChQ) ∧ RhQ * ChQ ≤ HQ ^ 2

def BetaCheck : Prop := betaBoundQ ≤ betaQ

def Z1Check : Prop := HQ ^ 2 + (Polynomial.Numbers.tailQ * betaQ) ^ 2 ≤ Z1Q ^ 2

def RadiiCheck : Prop :=
  0 < radiusQ ∧ Z2Q * radiusQ ^ 2 - (1 - Z0Q - Z1Q) * radiusQ + Y0Q < 0

/-- The finite-arithmetic bundle; no semantic assumption is hidden here. -/
def Checks : Prop :=
  Y0Check ∧ Z0Check ∧ HCheck ∧ BetaCheck ∧ Z1Check ∧ RadiiCheck

instance : Decidable Checks := by
  unfold Checks Y0Check Z0Check HCheck BetaCheck Z1Check RadiiCheck
  infer_instance

/-- **The certificate call**: the whole bundle by one `native_decide`. -/
theorem checks : Checks := by native_decide

theorem check_Y0 : Y0Check := checks.1
theorem check_Z0 : Z0Check := checks.2.1
theorem check_H : HCheck := checks.2.2.1
theorem check_beta : BetaCheck := checks.2.2.2.1
theorem check_Z1 : Z1Check := checks.2.2.2.2.1
theorem check_radii : RadiiCheck := checks.2.2.2.2.2

/-- The curvature check `4 (UsqQ + t2Q) ≤ Z₂²`, implying `2 √(UsqQ + t2Q) ≤ Z₂ = 42`. -/
def CurvCheck : Prop := 4 * (UsqQ + Polynomial.Numbers.t2Q) ≤ Z2Q ^ 2

instance : Decidable CurvCheck := by
  unfold CurvCheck
  infer_instance

/-- **The curvature call**: `CurvCheck` by one `decide +kernel`. -/
theorem check_curv : CurvCheck := by decide +kernel

end FourierDuffing.Combined.Numbers
