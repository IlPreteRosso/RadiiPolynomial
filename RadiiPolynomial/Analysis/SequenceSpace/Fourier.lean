import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Support
import RadiiPolynomial.Analysis.SequenceSpace.Fourier.TailWindow
import RadiiPolynomial.Analysis.SequenceSpace.Fourier.GammaLeakage

/-! Public API for the bilateral geometric carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` on the Fourier
side: the `ℤ`-window and band support facts (`Fourier.Support`: `winZ`, the far-antitone window
maximum principle, the coefficient norm, `band_mul`, `band_pow`) and the exact finite-window
operator norm of the tail-diagonal defect `M P L_b Q + R L_b`, attained as a weighted column
ratio at an atom, with its explicit and joint head-block forms (`Fourier.TailWindow`).

The Γ leakage layer (`Fourier.GammaLeakage`): over a real-scalar field `[NormedAlgebra ℝ 𝕜]`
(the Γ entries `γ_N(k) = ν^{2|k|} / ν^{2(N+1)}` enter through `algebraMap ℝ 𝕜`), the Γ scalar `gammaScalar`,
the head diagonals `gammaDiag` and `gammaInvDiag` with `gammaDiag N ∘L gammaInvDiag N = headProj (winZ N)`, and the
all-coefficient leakage estimates `‖Γ⁺ P L_c Q‖ ≤ ‖c‖`, `‖M P L_c Q‖ ≤ ‖M P Γ‖ ‖c‖`, `‖D_r L_c‖ ≤ C ‖c‖` and the Γ
majorant `‖defect N M r C hr c‖ ≤ (‖M P Γ‖ + C) ‖c‖` (`norm_defect_le_gamma`). The Γ majorant is a universal head
bound; it is not the exact window norm `opNorm_defect_eq_sup'`. -/
