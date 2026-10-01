import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Support
import RadiiPolynomial.Analysis.SequenceSpace.Fourier.TailWindow

/-! Public API for the bilateral geometric carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` on the Fourier
side: the `ℤ`-window and band support facts (`Fourier.Support`: `winZ`, the far-antitone window
maximum principle, the coefficient norm, `band_mul`, `band_pow`) and the exact finite-window
operator norm of the tail-diagonal defect `M P L_b Q + R L_b`, attained as a weighted column
ratio at an atom, with its explicit and joint head-block forms (`Fourier.TailWindow`).
(T39, L002.) -/
