import RadiiPolynomial.Examples.Fourier.Duffing.Numbers

/-!
# Book §10.1 Helmholtz–Duffing on the polynomial carrier: the numerical clauses

The second carrier of the same Duffing problem: the physical amplitude weight
`m_n = (1 + |n|)²` (mass `ω_n = (1 + |n|)⁴`) on `ℓ²(ℤ; ℂ)`, with no renormalization. The centre
`ā` and the head matrix `M` are the shipped exact rational leaf `leaf` of
`Examples/Fourier/Duffing/Numbers.lean`, read through the leaf-parametric mirror of the
rational-leaf adapter `Certification/Fourier/Quadratic.lean` without copies; only the weight
changes.

This module is finite arithmetic only. The bound constants (`Y₀ = 71/10⁶`, `Z₀ = 1/1000`,
`H = 7/1000`, `‖2ā‖ ≤ 103/10`, tail `≤ 1/117`, `‖A‖ ≤ 11`, `Z₁ = 9/100`, `Z₂ = 220` from the
product bound `κ = 10`, radius `1/10000`) are those of the trial certificate. Every clause of
`Checks` is consumed by `Polynomial/Certificate.lean`; the whole bundle is ONE `native_decide`.
-/

namespace FourierDuffing.Polynomial.Numbers

open FourierDuffing.Numbers RadiiPolynomial.Certification.Fourier.Quadratic

/-- Polynomial amplitude weight `(1 + |n|)²`; the `ℓ²` mass is its square. -/
def weightQ (n : ℤ) : ℚ := (1 + (n.natAbs : ℚ)) ^ 2

/-- Exact squared weighted residual summand, from the shipped preconditioned residual `GQ`. -/
def yTermQ (n : ℤ) : ℚ := cnormSq (leaf.GQ n) * weightQ n ^ 2

/-- The residual support `{|n| ≤ 20}` is covered by the three `Y₀` chunks of the leaf. -/
theorem idx2_eq_chunks : idx2 10 = y0Chunk 0 ++ y0Chunk 1 ++ y0Chunk 2 := by decide +kernel

/-- The three residual chunks of the shipped arithmetic mirror. -/
def yPartQ (k : ℕ) : ℚ := qsum (y0Chunk k) yTermQ

def ySquaredQ : ℚ := yPartQ 0 + yPartQ 1 + yPartQ 2

/-- Weighted rows/columns of the finite defect `I − M DF`. -/
def zRowQ (i : ℤ) : ℚ :=
  qsum (idx 10) fun j => reim (leaf.EQ i j) * weightQ i / weightQ j

def zColQ (j : ℤ) : ℚ :=
  qsum (idx 10) fun i => reim (leaf.EQ i j) * weightQ i / weightQ j

/-- Weighted rows/columns after composing the finite inverse and the leakage. -/
def hRowQ (i : ℤ) : ℚ :=
  qsum (leakColsQ 10 7) fun k => reim (leaf.KMQ i k) * weightQ i / weightQ k

def hColQ (k : ℤ) : ℚ :=
  qsum (idx 10) fun i => reim (leaf.KMQ i k) * weightQ i / weightQ k

/-- Weighted rows/columns of `M`, for its `ℓ²` Schur bound. -/
def aRowQ (i : ℤ) : ℚ :=
  qsum (idx 10) fun j => reim (leaf.MQ i j) * weightQ i / weightQ j

def aColQ (j : ℤ) : ℚ :=
  qsum (idx 10) fun i => reim (leaf.MQ i j) * weightQ i / weightQ j

/-- Fixed-centre weighted-`ℓ¹` symbol majorant of `2ā`. -/
def betaBoundQ : ℚ := qsum (idx 10) fun k => 2 * reim (leaf.abarQ k) * weightQ k

def Y0Q : ℚ := 71 / 10 ^ 6
def Z0Q : ℚ := 1 / 1000
def HQ : ℚ := 7 / 1000
def betaQ : ℚ := 103 / 10
def tailQ : ℚ := 1 / 117
def AQ : ℚ := 11
def Z1Q : ℚ := 9 / 100
def Z2Q : ℚ := 220
def radiusQ : ℚ := 1 / 10000

def RzQ : ℚ := 1 / 2000
def CzQ : ℚ := 3 / 2000
def RhQ : ℚ := 7 / 1000
def ChQ : ℚ := 7 / 1000
def RaQ : ℚ := 25 / 2
def CaQ : ℚ := 193 / 20

def Y0Check : Prop := ySquaredQ ≤ Y0Q ^ 2

def Z0Check : Prop :=
  (∀ i ∈ idx 10, zRowQ i ≤ RzQ) ∧
  (∀ j ∈ idx 10, zColQ j ≤ CzQ) ∧ RzQ * CzQ ≤ Z0Q ^ 2

def HCheck : Prop :=
  (∀ i ∈ idx 10, hRowQ i ≤ RhQ) ∧
  (∀ k ∈ leakColsQ 10 7, hColQ k ≤ ChQ) ∧ RhQ * ChQ ≤ HQ ^ 2

def ACheck : Prop :=
  (∀ i ∈ idx 10, aRowQ i ≤ RaQ) ∧
  (∀ j ∈ idx 10, aColQ j ≤ CaQ) ∧ RaQ * CaQ ≤ AQ ^ 2 ∧ tailQ ≤ AQ

def BetaCheck : Prop := betaBoundQ ≤ betaQ

def Z1Check : Prop := HQ ^ 2 + (tailQ * betaQ) ^ 2 ≤ Z1Q ^ 2

def RadiiCheck : Prop :=
  0 < radiusQ ∧ Z2Q * radiusQ ^ 2 - (1 - Z0Q - Z1Q) * radiusQ + Y0Q < 0

/-- The finite-arithmetic bundle; no semantic assumption is hidden here. -/
def Checks : Prop :=
  Y0Check ∧ Z0Check ∧ HCheck ∧ ACheck ∧ BetaCheck ∧ Z1Check ∧ RadiiCheck

instance : Decidable Checks := by
  unfold Checks Y0Check Z0Check HCheck ACheck BetaCheck Z1Check RadiiCheck
  infer_instance

/-- **The certificate call**: the whole bundle by one `native_decide`. -/
theorem checks : Checks := by native_decide

theorem check_Y0 : Y0Check := checks.1
theorem check_Z0 : Z0Check := checks.2.1
theorem check_H : HCheck := checks.2.2.1
theorem check_A : ACheck := checks.2.2.2.1
theorem check_beta : BetaCheck := checks.2.2.2.2.1
theorem check_Z1 : Z1Check := checks.2.2.2.2.2.1
theorem check_radii : RadiiCheck := checks.2.2.2.2.2.2

end FourierDuffing.Polynomial.Numbers
