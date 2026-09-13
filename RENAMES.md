# RENAMES — end-consumer interface alignment (TASK 2, 2026-09-13)

Ledger of every renamed, moved, retired, or deleted Lean declaration of the alignment pass.
Convention: `| old | new | file | step | reason |`. "retired" = deleted with a library replacement
named in the reason; "moved" = same name, new file. Certificate axiom sets are frozen in
`tmp/autonomous_agenda_2026_09_13/TASK2_axioms_before.txt` and must reprint byte-identically
except for the label changes listed here. Design: `tmp/autonomous_agenda_2026_09_13/TASK2_design_synthesis.md`.

## Decisions on the design panel's open questions (mine, revertible by the user)
1. Naming: keep the skill's `f`/`F` convention; Ex 8.1/8.3 `f` (coefficient nonlinearity) untouched; Ex 14.2.1's real
   vector field is `IVP.vectorField f_cpoly`; `r_minus` (pipeline root, Numbers layer) and `r₀` (theorem radius) both kept.
2. `compPolyOf%`: literal `f_cpoly` stays the definition; a `rfl` reification witness is added (A4).
3. Ex 14.2.1 function-level theorems: retire only the self-labelled compatibility `main_solution_existsUnique_radius_two`
   (+ `R_traj_le_two`); keep `main_solution_existsUnique`, `_contractive`, `_radius_one`.

## RENAMED
| old | new | file | step | reason |
|---|---|---|---|---|
| `Example1421.Cert.main_existsUnique` | `Example1421.Cert.main_theorem` | `Examples/IVP/Chebyshev/Example1421/Certificate.lean` | E1 | the four-example headline name; now proved by `StdChebIVPData.existsUnique_of_compPoly f_cpoly p₀ … Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg` (finite-block `Z₀`, no differentiability witness). Paper main.tex:1414 cites the old name — RECORDED, not edited |
| `IVP.ivpComposedApprox_eq_fderiv_fin` | `IVP.composedApprox_eq_fderiv_fin` | `Applications/IVP/Taylor/Theorem.lean` | A1 | the `ivp` prefix only existed to pair with the retired `ivpComposedApprox` alias; sole consumer `Applications/IVP/Taylor/Standard.lean` updated |
| `smulCLM`, `smulCLM_apply`, `norm_smulCLM`, `id_eq_smulCLM_one`, `smulCLM_comp`, `smulCLM_sub`, `id_sub_smulCLM`, `smulCLM_injective`, `fderiv_sq_sub_const`, `differentiable_sq_sub_const`, `Z₂_bound_sq_sub_const` (root namespace) | `Example245.*` | `Examples/FiniteDimensional/Example245/Algebra.lean` | A2 | an example file was declaring eleven root-namespace symbols; one consumer (`Example245/Certificate.lean`), so namespaced rather than promoted. `#check smulCLM` now fails at the root |
| `Example245.Cert.ex_f` | `Example245.Cert.f` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | `ex_` prefix dropped; the namespace already says which example |
| `Example245.Cert.ex_xBar` | `Example245.Cert.xBar` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_A` | `Example245.Cert.A` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_A_dag` | `Example245.Cert.A_dag` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_Y₀` | `Example245.Cert.Y₀_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | `*_bound` is the spelling of the other four examples |
| `Example245.Cert.ex_Z₀` | `Example245.Cert.Z₀_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_Z₂` | `Example245.Cert.Z₂_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_r₀` | `Example245.Cert.r₀` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example77.Cert.ν` | `Example77.Cert.ν_q` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | a `def ν : ℚ` shadowed the project-wide weight symbol inside the namespace that also defines `ν_val`; the duplicate commented `-- def ν : ℚ := 1/4` of the alternative parameter set (same value) was deleted |
| `Example77.Cert.Y₀_bnd` | `Example77.Cert.Y₀_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | `*_bound` is the spelling of the other four examples (commented alternative set renamed too) |
| `Example77.Cert.Z₀_bnd` | `Example77.Cert.Z₀_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `Example77.Cert.Z₁_bnd` | `Example77.Cert.Z₁_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `Example77.Cert.Z₂_bnd` | `Example77.Cert.Z₂_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `RadiiPolynomial.IVP.SplitBoundary` (+ `.trace_extension_apply`, `.equiv`, `.equiv_fst`, `.equiv_snd_coe`, `.zeroPart`, `.zeroPart_coe`, `.trace_zeroPart`, `.extension_add_zeroPart`, `.anchoredPrimitive`, `.trace_anchoredPrimitive`, `.fiber_eq_translate_ker`) | `IVP.SplitBoundary` … | `Applications/IVP/Boundary.lean` | H1 | the outer `namespace RadiiPolynomial` wrapper dropped (this module imports only Mathlib, so no `open RadiiPolynomial` is added); zero external consumers, `command grep -rn '^namespace RadiiPolynomial$' Applications/` now empty |
| `RadiiPolynomial.IVP.{taylorBoundaryCharacter, taylorBoundaryCharacter_apply, taylorEndpointCharacter, taylorEndpointCharacter_apply, taylorReborderingDefect, taylorReborderingDefect_apply, norm_taylorReborderingDefect_apply_le, norm_taylorReborderingDefect_le, norm_taylorReborderingDefect, taylorSplitBoundary, taylorSplitBoundary_trace, taylorBoundary_shiftDivN, taylorAnchoredPrimitive, taylorAnchoredPrimitive_coe}` | `IVP.*` | `Applications/IVP/Taylor/Boundary.lean` | H1 | outer wrapper dropped, `open RadiiPolynomial` added |
| `RadiiPolynomial.IVP.{chebyshevBoundary, chebyshevBoundary_apply, chebyshevBoundary_one, chebyshevBoundary_not_multiplicative, chebyshevSplitBoundary, symmetricEndpointCharacter, chebyshevBoundary_factor_symmetric, symmetricEndpointCharacter_comp_joukowskiAevalSymm, abs_chebyshevBoundary_le_norm_of_two_le, chebyshevIntegrateCLM, chebyshevIntegrateCLM_apply, chebyshevAnchoredPrimitive, chebyshevAnchoredPrimitive_zero_boundary, eval_chebyshevAnchoredPrimitive}` | `IVP.*` | `Applications/IVP/Chebyshev/Boundary.lean` | H1 | outer wrapper dropped, `open RadiiPolynomial` added |

## MOVED
| name | from | to | step | reason |
|---|---|---|---|---|
| `IVP.vectorField` | `Applications/IVP/Taylor/Trajectory.lean` | `Applications/IVP/VectorField.lean` (new) | L4 | geometry-free right-hand side; both discretizations' function-space conclusions name it, so it sits below Taylor and Chebyshev. Name, namespace and docstring unchanged; `IVP.banachField` stays in `Trajectory.lean` (it mentions `XL1`) |
| `Example1421.G_diff` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | restated on `ChebyshevIVP.banachField f_cpoly`, proof unchanged (`data.differentiable_G_of_compPoly f_cpoly p₀`); kept for `Examples/Transport/TwinTransport.lean` |
| `IVP.analyticOnNhd_x_analytic` | `Applications/IVP/Taylor/ComplexTime.lean` | `Applications/IVP/Taylor/Analyticity.lean` (new) | H3 | a purely real statement had forced `Example81/Analyticity.lean` to import the complex-time layer; name, namespace, statement and proof unchanged, `ComplexTime.lean` now imports the new module |
| `Example83.Cert.lorenz_analyticOnNhd` | `Examples/IVP/Taylor/Example83/ComplexTime.lean` | `Examples/IVP/Taylor/Example83/Analyticity.lean` (new) | H3 | layer parity with Ex 8.1; names and proofs unchanged |
| `Example83.Cert.lorenz_analytic_existsUnique` | `Examples/IVP/Taylor/Example83/ComplexTime.lean` | `Examples/IVP/Taylor/Example83/Analyticity.lean` (new) | H3 | idem |

## RETIRED (deleted; replacement named)
| old | replacement | file | step | reason |
|---|---|---|---|---|
| `Example1421.hasFDerivAt_sq_cheb` | `CompPoly.Chebyshev.hasFDerivAt_eval` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; the adapter proves `HasFDerivAt` for any `CompPoly` |
| `Example1421.hasFDerivAt_q` | `CompPoly.Chebyshev.hasFDerivAt_eval` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.differentiable_phi` | `ChebyshevIVP.StdChebIVPData.differentiable_G_of_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.fderiv_phi_apply` | `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.norm_Dphi_le` | `CompPoly.Chebyshev.norm_derivative_apply_le` / `ChebyshevIVP.norm_compPolyDerivative_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.norm_S_le` | `l1Chebyshev.symmetrize_CLM_norm_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; bare alias for the library bound |
| `Example1421.norm_Ssym_le` | `l1Chebyshev.symmetrize_norm_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; bare alias for the library bound |
| `Example1421.SP_apply` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; `SP` unfolds by `rfl` |
| `Example77.F_eq` | — | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers; `rfl` |
| `Example77.F_sub_const_eq_fun` | — | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example77.Z₀_structural` | `ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel` | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers; bare alias for the library reduction |
| `Example77.differentiable_sq` | `Example77.hasFDerivAt_sq` (`.differentiableAt`) | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example77.fderiv_sq` | `Example77.hasFDerivAt_sq` (`.fderiv`) | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example245.fderiv_sq` | `Example245.fderiv_sq_sub_const` | `Examples/FiniteDimensional/Example245/Algebra.lean` | D1 | zero consumers |
| `Example245.Cert.ex_A_dag_eq` | — | `Examples/FiniteDimensional/Example245/Certificate.lean` | D1 | zero consumers (`private`) |
| `Example81.f_bridge` | `CompPoly.toSeq_evalBanach` | `Examples/IVP/Taylor/Example81/Algebra.lean` | D1 | zero consumers; one-line application of the library bridge |
| `Example83.f_bridge` | `CompPoly.toSeq_evalBanach` | `Examples/IVP/Taylor/Example83/Algebra.lean` | D1 | zero consumers; one-line application of the library bridge |
| `Example83.G_ā_vec` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers; the Y₀ fold is computed from `F_Q`, not from stored `G(ā)` literals |
| `Example83.G_ā_vec_0` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`; ≈11.6 KB of literals) |
| `Example83.G_ā_vec_1` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`) |
| `Example83.G_ā_vec_2` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`) |
| `Example1421.phi` | `ChebyshevIVP.banachField f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | rfl-equal; every statement of `Certificate.lean`, `Analytic.lean`, `TwinTransport.lean` now reads `data.G (banachField f_cpoly) p₀` |
| `Example1421.Ssym` | `l1Chebyshev.symmetrize` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.S` | `l1Chebyshev.symmetrize_CLM` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias; `Sabar_norm_le` keeps its name and proof shape, its statement now reads `‖l1Chebyshev.symmetrize_CLM (ābar l)‖` |
| `Example1421.Ssym_toSeq` | `l1Chebyshev.symmetrize_toSeq` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.S_apply` | `l1Chebyshev.symmetrize_CLM_apply` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.SP` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | intermediate of the retired CLM-level derivative formula |
| `Example1421.leftMul_apply'` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | intermediate of the retired CLM-level derivative formula |
| `Example1421.derivative_f_cpoly_eq` | `Example1421.Dphi_eq_derivative` (direct proof) | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | the CLM-level identity `derivative (f_cpoly l) a = (2·leftMul(S aₗ) − id) ∘ S ∘ projₗ` is folded into the componentwise `Dphi_eq_derivative` |
| `Example1421.hasFDerivAt_phi` | `ChebyshevIVP.hasFDerivAt_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | adapter proves it for any `CompPoly` system |
| `Example1421.DPhiCLM` | `ChebyshevIVP.compPolyDerivative f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | one derivative name at the CLM level; the example's explicit `Dphi` is reached by the new rfl-backed `compPolyDerivative_apply_eq_Dphi` |
| `Example1421.DPhiCLM_apply` | `Example1421.compPolyDerivative_apply_eq_Dphi` (new) | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | componentwise bridge `compPolyDerivative f_cpoly a h l = Dphi a h l := (Dphi_eq_derivative a h l).symm` |
| `Example1421.hasFDerivAt_Phi` | `ChebyshevIVP.hasFDerivAt_compPoly` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E2 | — |
| `Example1421.compPolyDerivative_eq` | `Example1421.compPolyDerivative_apply_eq_Dphi` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | CLM identity replaced by the componentwise one |
| `Example1421.fderiv_G` | `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly f_cpoly p₀` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | `Certificate.lean`'s `fderiv_toSeq` rewrites with the library lemma directly |
| `Example1421.Cert.f` | `IVP.vectorField f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | rfl-equal; the surviving theorem statements spell the vector field this way (see "Statement wording" below) |
| `Example1421.Cert.hφ_eval` | derived inside `StdChebIVPData.solution_existsUnique_of_compPoly` / `_of_two_le_of_compPoly` / `analytic_solution_existsUnique_of_two_le_of_compPoly` (`CompPoly.Chebyshev.eval_eval`) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | structural obligation, no longer stated per example |
| `Example1421.Cert.f_lipschitzOnWith` | `CompPoly.lipschitzOnWith_evalBanach_pi` inside the faces; the syntactic input was briefly the example lemma `lipschitzBound_f_cpoly` (retired again in round 2: the faces build it internally) : lipschitzBound (X² − X) (fun _ => R) = 2R + 1` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | the faces take `hK` on the syntax |
| `Example1421.Cert.defect_norm_lt_one` | `ChebyshevIVP.StdChebIVPData.defect_finBlockNorm_lt_one_of_radii` (derived inside the faces) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | derived from the four bounds |
| `Example1421.Cert.two_le_ν_val` | inline `by rw [show ((ν_val : ℝ)) = 2 from rfl]` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | private one-liner |
| `Example1421.Cert.main_solution_existsUnique_radius_two` | — (headline is `main_solution_existsUnique_radius_one`) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | self-labelled compatibility statement; companion l.2608 ripple for the docs pass |
| `Example1421.Cert.R_traj_le_two` | — | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | only consumer was `_radius_two` |
| `Example81.Cert.banachField_eq_f` | `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` &co. (the `_of_compPoly` faces supply `rfl` internally) | `Examples/IVP/Taylor/Example81/Analytic.lean` | T1 | private `rfl` bridge; the four function-space theorems now call the L6 faces, which take `f_cpoly` and no `h_phi_eq` |
| `Example83.Cert.banachField_eq_f` | `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` &co. | `Examples/IVP/Taylor/Example83/Analytic.lean` | T1 | idem |
| `IVP.ivpComposedApprox` | `SystemBlockDiagData.composedApprox` | `Operators/BlockDiagonal/Composition.lean` | A1 | compatibility `abbrev` for the pre-refactor Taylor API; all 11 use sites rewritten (`Applications/IVP/Taylor/{Theorem,Standard}.lean`) |
| `IVP.ivpComposedApprox_defect_eq` | `SystemBlockDiagData.composedApprox_defect_eq` | `Operators/BlockDiagonal/Composition.lean` | A1 | wrapper delegating to the `SystemBlockDiagData` lemma |
| `IVP.ivpComposedApprox_toCLM_tail` | `SystemBlockDiagData.composedApprox_toCLM_tail` | `Operators/BlockDiagonal/Composition.lean` | A1 | wrapper delegating to the `SystemBlockDiagData` lemma |
| `Example245.existsUnique` | `general_radii_polynomial_theorem` | `Examples/FiniteDimensional/Example245/Algebra.lean` | A2 | verbatim argument permutation of Thm 7.6.2; `Cert.main_theorem` now calls the abstract theorem directly |
| `KappaToy.f := Example77.F_sub_const c` (and its `Example77.{sq, fderiv_F_sub_const, fderiv_F_sub_const_affine, differentiable_F_sub_const}` uses) | local `KappaToy.{f, hasFDerivAt_f, fderiv_f, fderiv_f_affine}` | `Examples/Transport/KappaToy.lean` | H4 | removes the last Examples→Examples import outside `TwinTransport`; `f` is now `fun a => a * a - c` with its own `auto_hasFDerivAt` derivative (import `Examples.PowerSeries.Example77.Algebra` replaced by `Tactic.AutoPolyFDeriv`) |

## DELETED FILES
| file | step | reason |
|---|---|---|
| `RadiiPolynomial/Examples/IVP/Chebyshev/Example1421/Lambda.lean` (+ its import line in `RadiiPolynomial/Examples.lean`; `Certificate.lean` now imports `…Example1421.Algebra`) | E2 | every declaration retired or moved (see RETIRED/MOVED); Ex 14.2.1 now has exactly Numbers → Algebra → Certificate → Analytic → Analyticity |

## ADDED (library faces, step 2-4)

New declarations, all sorry-free, all printing exactly `propext, Classical.choice, Quot.sound`.
No global instance, no `native_decide`, no new axiom.

| declaration | file | step | role |
|---|---|---|---|
| `ChebyshevIVP.banachField` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 | Chebyshev coefficient nonlinearity of a `CompPoly` system; mirror of `IVP.banachField` |
| `ChebyshevIVP.banachField_apply` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 | `@[simp]` component form (`rfl`) |
| `ChebyshevIVP.StdChebIVPData.defect_finBlockNorm_lt_one_of_radii` | `Applications/IVP/Chebyshev/Standard.lean` | L2 | Chebyshev mirror of the Taylor lemma; derives `‖defect‖ < 1` from the four bounds |
| `ChebyshevIVP.StdChebIVPData.Z₂_le_of_compPoly_max` | `Applications/IVP/Chebyshev/Polynomial.lean` | L3 | `Z₂` socket: syntactic derivative Lipschitz constant plus a `TC` bound gives the ball statement |
| `ChebyshevIVP.StdChebIVPData.existsUnique_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L3 | coefficient-zero face, `Z₀` in finite-block form |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | function-space face, trajectory radius `2(‖ā‖ + r₀)` |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | contractive face at `2 ≤ ν`, radius `‖ā‖ + r₀` |
| `ChebyshevIVP.StdChebIVPData.analytic_solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | same, with `AnalyticOnNhd` for the produced solution only |
| `IVP.StdIVPData.existsUnique_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | L6 | Taylor coefficient-zero face |
| `IVP.StdIVPData.existsUnique_ivpCoeffs_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | L6 | same at the source residual, `Z₀` in finite-block form |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | `φ := banachField φ_cpoly`, `h_phi_eq := rfl` |
| `IVP.StdIVPData.analytic_eq_canonical_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `IVP.StdIVPData.analytic_unique_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `IVP.StdIVPData.analytic_existsUnique_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `Example1421.compPolyDerivative_apply_eq_Dphi` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1 | rfl-backed bridge from the adapter's system derivative to the example's explicit `Dphi` |
| `Example1421.Cert.lipschitzBound_f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | `lipschitzBound (X² − X) (fun _ => R) = 2R + 1`; the one syntactic input of the three function-space theorems and of `Analyticity.lean` |
| `Example81.f_cpoly_reified` | `Examples/IVP/Taylor/Example81/Algebra.lean` | A4 | `f_cpoly 0 = compPolyOf% (fun u : Fin L → ℝ => u 0 * u 0 - u 0) := rfl` — certificate-level consumer of the elaborator (needs `import RadiiPolynomial.Tactic.MakeCompPoly`) |
| `Example1421.f_cpoly_reified` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | A4 | idem, Chebyshev geometry (the reifier is geometry-free, so the same `Fin L → ℝ` lambda is used) |
| `RadiiPolynomial.Gelfand.pointwiseTopology` | `Analysis/SequenceSpace/CharacterTopology.lean` (new) | H2 | carrier-independent topology of pointwise convergence on `A →A[R] B`; the three per-carrier `pointwiseTopology` defs (`TaylorSpectrum`, `LaurentSpectrum`, `PhysicalSpectrum`) are now one-line specializations, each module keeping its own `local instance` |
| `RadiiPolynomial.Gelfand.continuous_character_apply` | `Analysis/SequenceSpace/CharacterTopology.lean` (new) | H2 | the single continuity fact the three modules needed; the three same-named per-carrier theorems keep their names and delegate |
| `KappaToy.hasFDerivAt_f`, `KappaToy.fderiv_f`, `KappaToy.fderiv_f_affine` | `Examples/Transport/KappaToy.lean` | H4 | the toy's own calculus for `a ↦ a·a − c`, replacing the imported Ex 7.7 lemmas |

## RESTATED (same name, statement rewritten through `ChebyshevIVP.banachField`)

`rw` matches syntactically, so the adapter lemmas that inlined
`fun x l => CompPoly.Chebyshev.eval (f l) x` had to be restated for the new faces to
compose. All proofs are unchanged except `ivpCoeffs_abar_eq_cast_of_compPoly`, whose
`simp only` set gained `banachField, CompPoly.Chebyshev.eval` as unfold rules. All six
keep their axiom sets, and Example 14.2.1's `exact`/`have` call sites were accepted
unchanged (defeq).

| declaration | file | step |
|---|---|---|
| `ChebyshevIVP.StdChebIVPData.ivpCoeffs_abar_eq_cast_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.hasFDerivAt_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.hasFDerivAt_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.differentiable_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_fin_toSeq_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_single_fin_eq_cast_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |

## NEW MODULES

| module | imports | wired into |
|---|---|---|
| `Applications/IVP/VectorField.lean` | `Algebra.Polynomial.CompPoly.Core` only | `Taylor/Trajectory.lean`, and both facades `Applications/IVP/Taylor.lean` and `Applications/IVP/Chebyshev.lean` |
| `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` | `Chebyshev.Analyticity`, `Chebyshev.Polynomial`, `IVP.VectorField` | facade `Applications/IVP/Chebyshev.lean` (already imported by the root) |

Import added as a consequence: `Applications/IVP/Taylor/Polynomial.lean` now imports
`Applications/IVP/Taylor/Trajectory.lean`, because `IVP.banachField` lives there and the
Taylor faces state their hypotheses through it. No cycle; the `Applications.IVP.Taylor`
facade consequently also exposes `Trajectory`.

### NEW MODULES (steps 10, H2/H3)

| file | step | role |
|---|---|---|
| `RadiiPolynomial/Applications/IVP/Taylor/Analyticity.lean` | H3 | hosts the moved `IVP.analyticOnNhd_x_analytic`; imported by `Taylor/ComplexTime.lean`, `Example81/Analyticity.lean`, `Example83/Analyticity.lean` and the root import |
| `RadiiPolynomial/Examples/IVP/Taylor/Example83/Analyticity.lean` | H3 | Ex 8.3's real-analyticity theorems, mirroring `Example81/Analyticity.lean`; wired into `Examples.lean` and the `TaylorCertifiedExamples.lean` shim |
| `RadiiPolynomial/Analysis/SequenceSpace/CharacterTopology.lean` | H2 | `Gelfand.pointwiseTopology` / `Gelfand.continuous_character_apply`, imported by `Geometric/Spectrum.lean`, `Chebyshev/LaurentSpectrum.lean`, `Chebyshev/Spectrum/Topology.lean` |

## RESTATED (Example 14.2.1, steps E1–E3; same names, `phi`/`S`/`f` spelled through library names)

Statements are unchanged up to `rfl`-unfolding of the retired aliases; proofs of the
native_decide-bearing declarations are byte-identical in structure (names and native call
counts unchanged: `data`, `Sabar_norm_le`, `Y₀_le`, `Z₀_finBlockNorm_le`, `abar_0_size`,
`TCcolNormQ_le_small`, `colNormQ_le_small`, `rowA0Q_le`).

| declaration | file | change |
|---|---|---|
| `Example1421.Dphi` | `Algebra.lean` | body `(2:ℝ) • (l1Chebyshev.symmetrize_CLM (a l) * l1Chebyshev.symmetrize_CLM (h l)) - l1Chebyshev.symmetrize_CLM (h l)` (was the same through the alias `S`) |
| `Example1421.Dphi_eq_derivative` | `Algebra.lean` | direct proof (`derivative_apply` + `Fin.sum_univ_one` + the two `change`s), no CLM-level intermediate |
| `Example1421.Cert.{Y₀_le, Z₁_le, Z₁_le_semiMajor, Z₂_le}` | `Certificate.lean` | `data.G phi p₀` → `data.G (banachField f_cpoly) p₀`; `Z₂_le` proved by `data.Z₂_le_of_compPoly_max f_cpoly p₀ … TC_norm_le …` with `Z₂_bound = (7/4)·8` |
| `Example1421.Cert.Sabar_norm_le` | `Certificate.lean` | `‖S (ābar l)‖` → `‖l1Chebyshev.symmetrize_CLM (ābar l)‖`; proof shape unchanged (`native_decide` witness `ax_1_3` unchanged) |
| private `Sabar_toSeq`, `S_single_toSeq`, `conv_single_toSeq`, `Dphi_single_toSeq`, `Trow_negSucc_toSeq`, `fderiv_toSeq`, `compPolyDphiQ_eq`, `Trow`, `Trow_eq`, `Z₁_hneg`, `Z₁_htail`, `Z₁_hfin`, `Trow_single_toSeq`, `F_abar_eq`, `Y₀_eval_correct` | `Certificate.lean` | same spelling changes; `fderiv_toSeq` rewrites with `data.fderiv_G_of_compPoly f_cpoly p₀` and `compPolyDerivative_apply_eq_Dphi`; `S_single_toSeq` pins `(ν := ν_val)` on the `single` (the alias used to pin it) |
| `TwinTransport.{twin_transports, twin_scalar_certificate}` | `Examples/Transport/TwinTransport.lean` | `data.G phi p₀` → `data.G (banachField f_cpoly) p₀` (4 sites) |

### Statement wording (the paper and the ground note cite these; statements literally unchanged except for the spelling of the vector field)

| theorem | old spelling | new spelling |
|---|---|---|
| `Example1421.Cert.main_solution_existsUnique` | `ChebyshevIVP.IsSolution f p₀ R_traj g` | `ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj g` |
| `Example1421.Cert.main_solution_existsUnique_contractive` | `… IsSolution f p₀ R_traj_contractive …` | `… IsSolution (IVP.vectorField f_cpoly) p₀ R_traj_contractive …` |
| `Example1421.Cert.main_solution_existsUnique_radius_one` | `… IsSolution f p₀ 1 …` | `… IsSolution (IVP.vectorField f_cpoly) p₀ 1 …` |
| `Example1421.Cert.analytic_solution_existsUnique_radius_one` | `… IsSolution Example1421.Cert.f Example1421.p₀ 1 …` | `… IsSolution (IVP.vectorField Example1421.f_cpoly) Example1421.p₀ 1 …` |
| `Example1421.Cert.main_theorem` (ex `main_existsUnique`) | `data.G phi p₀ xTilde = 0` | `data.G (banachField f_cpoly) p₀ xTilde = 0` |

`Cert.f u l` was by definition `(f_cpoly l).evalBanach u`, which is `IVP.vectorField f_cpoly u l` by `rfl`.

## Audit files synced (E4)

| file | change |
|---|---|
| `tmp/proposal_experiments_2026_09_06/ChebCompPolyExample1421.lean` | `phiPoly_eq_phi` → `phiPoly_eq_banachField` (`= ChebyshevIVP.banachField Example1421.f_cpoly`), `evalBanach_eq_f` → `evalBanach_eq_vectorField`, `fPoly_eq_f` → `fPoly_eq_vectorField`; local `defect_norm_lt_one` now derived by `data.defect_finBlockNorm_lt_one_of_radii`; the Lipschitz input is `CompPoly.lipschitzOnWith_evalBanach_pi f_cpoly 1 (K := 3) (fun l => by simp [CompPoly.lipschitzBound, f_cpoly]; norm_num)` passed directly (defeq to `fPoly` by one delta step) |
| `tmp/proposal_experiments_2026_09_06/checks/cheb_comppoly_promotion_2026_09_12/promoted_axioms.lean` | dropped `Example1421.hasFDerivAt_phi` and `Example1421.Cert.hφ_eval` (retired), `main_existsUnique` → `main_theorem`; `checks/…/before/` and `baseline_axioms.lean` untouched |

## Writeup ripple (filled by the docs pass)

Filled 2026-09-13 by the documentation pass. Every Lean name written into these files was
verified with `command grep -rn "<name>" RadiiPolynomial/` before it was written; no `.lean`
file was touched and no build was run.

| file | what changed |
|---|---|
| `ARCHITECTURE.md` | Directory table: new rows `Analysis/SequenceSpace/CharacterTopology` (`Gelfand.pointwiseTopology`, `Gelfand.continuous_character_apply`) and `Applications/IVP/VectorField.lean` (`IVP.vectorField`); Geometric and Chebyshev rows now say their spectrum modules install the *shared* topology as a `local instance`; the Taylor row gains `Analyticity` (`IVP.analyticOnNhd_x_analytic`, no longer attributed to `ComplexTime`) and the three `StdIVPData.*_of_compPoly` faces; the Chebyshev row gains `ChebyshevIVP.banachField`, `StdChebIVPData.{existsUnique_of_compPoly, Z₂_le_of_compPoly_max, defect_finBlockNorm_lt_one_of_radii}` and the three `AnalyticPolynomial` faces. Import rule 6 records the single surviving `Examples → Examples` edge (`TwinTransport → Example1421/Certificate`). Boundaries: the `IVP.ivpComposedApprox` alias bullet replaced by its dated retirement plus `IVP.composedApprox_eq_fderiv_fin`; example progression is now `Numbers → Algebra → Certificate → Analytic → Analyticity` with "Example 14.2.1 has exactly these five and no `Lambda.lean`" and the per-example strengthenings corrected (`Analyticity` for Ex 8.1/8.3/14.2.1, `ComplexTime` for Ex 8.3 only); the pointwise-topology bullet rewritten around the shared definition; the root-wiring sentence now names `Taylor/{Analytic,Analyticity,ComplexTime}.lean` and why `Analyticity` sits below `ComplexTime`. |
| `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/UBIQUITOUS_LANGUAGE.md` | Trust-surface row: `main_existsUnique` → `main_theorem` (with a dated "was its spelling before 2026-09-13"). Spectrum row and its 2026-09-13 status bullet: the three homeomorphisms now name the shared `Gelfand.pointwiseTopology` of `Analysis/SequenceSpace/CharacterTopology.lean`, and `IVP.analyticOnNhd_x_analytic` is located in `Taylor/Analyticity.lean`. Λ-decomposition row: the example's `DPhiCLM`, `compPolyDerivative_eq`, `fderiv_G` and `Example1421/Lambda.lean` recorded as retired, the library derivative named as `ChebyshevIVP.compPolyDerivative`, the bridge as `Example1421.compPolyDerivative_apply_eq_Dphi`, and the still-live library `Applications/IVP/Chebyshev/Lambda.lean` explicitly distinguished. Derivative-constants row: the "kept as a header" claim about the retired `norm_Dphi_le` corrected. Adapter row: the stale "`f_cpoly` supplies `phi`, `f`, `hφ_eval`, `G_diff`, `fderiv_G`" replaced by the post-alignment interface. New section "End-consumer interface" with six rows: coefficient nonlinearity φ = `banachField f_cpoly` (both geometries), vector field f = `IVP.vectorField f_cpoly`, `_of_compPoly` face, `r_minus` vs `r₀`, `x₀` vs `p₀`, `retract` vs `symmetrize`. |
| `/Users/ilpreterosso/.claude/skills/radii-poly-api-design/SKILL.md` | §9 rewritten: five layers, the explicit "what an example supplies" list, both geometries' `_of_compPoly` entry points, the two derived maps, the syntactic-constant sockets (`CompPoly.normBound`/`lipschitzBound`/`derivativeBound`, `ivp_Dφ_norm_le_of_compPoly`, `Z₂_le_of_compPoly_max`) with the cancellation caveat, and the `f_cpoly_reified` rfl-witness convention. Pattern list: `MvPolyBridge/CompPoly.lean` → `RadiiPolynomial/Algebra/Polynomial/CompPoly/Core.lean`, `source/Tactic/` → `RadiiPolynomial/Tactic/` (and `compPolyOf%` now reifies constants), `IVP/AnalyticGlue` → `Applications/IVP/Taylor/Analytic.lean` with the `banachField_eq_f` obligation recorded as gone. Build hygiene rewritten: the `examples/tests/{easy,hard}` skeleton tree no longer exists; today's layout is the `RadiiPolynomial/Examples.lean` import list. |
| `RadiiPolynomial/tmp/ground_floor/note_ground_floor.tex` | Status flips to production for the spectra/analyticity branch (ellipse contractivity ¶, the `rem:spectop` and physical-classification remarks, the fiber identity, the complex-disc ODE sentence, the cross-geometry verdict, the Taylor and Chebyshev read-back paragraphs). Status ¶ rewritten around three promotions (residual certificate Sept 7, Chebyshev adapter Sept 12, spectra/analyticity Sept 13) and names what is still an experiment. Trust ¶: build count 3,999 → 4,026 jobs, promotion list extended. Production table gains eight rows (shared character topology; disc spectrum + full-disc analyticity; annulus spectrum; physical spectrum, six modules; real-character obstructions; Taylor real analyticity + complex time; Chebyshev read-back analyticity; the four strengthened certificates) and `Example1421.compPolyDerivative_eq` → `compPolyDerivative_apply_eq_Dphi`. Experiment table loses the five promoted rows and gains three new ones (`CoronaDivisionCoproduct.lean`, `SpectralGap.lean`, `tmp/cross_geometry_arrow/FoldedProductRing.lean`). Experiment-checks ¶: 49 modules/6,022 lines → 51/5,239, with the twelve new re-exports explained. Limits ¶: "derives no norm bound from syntax" replaced by the syntactic-constant statement and the Ex 8.1 cancellation exception. |
| `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/tmp/formalization_companion/formalization_companion.tex` | Packaged annulus/ellipse classifications now stated (`LaurentSpectrum.characterEquivAnnulus`, `PhysicalSpectrum.characterEquivEllipse`); "What Lean has" moved to production with the production file names and the shared topology; the `IsAnalyticSolution` paragraph points at the production analyticity theorems. Ex 8.1/8.3 per-example obligations reduced from two to one (`banachField_eq_f` recorded as deleted). Library `Lambda.lean` citation disambiguated by its full path. Ex 14.2.1: bounds sentence `main_existsUnique` → `main_theorem`; the "Example 14.2.1, migrated" paragraph rewritten to the new interface (one polynomial system in, `banachField f_cpoly`, `compPolyDerivative` + `compPolyDerivative_apply_eq_Dphi`, retirement of `DPhiCLM`/`hasFDerivAt_Phi`/`compPolyDerivative_eq`/`fderiv_G` and of `Example1421/Lambda.lean`, `existsUnique_of_compPoly`, `Z₂_le_of_compPoly_max`), and its closing "no norm bound is derived from syntax" replaced. Analytic strengthening paragraph moved to production. "The three per-example obligations" → "The one per-example obligation" (`hφ_eval` and `f_lipschitzOnWith` derived inside the faces; `lipschitzBound_f_cpoly` named). Trust-surface ¶: `main_existsUnique` → `main_theorem`, and the `_radius_two` compatibility sentence replaced by its dated retirement. Transform-map table: spectrum rows "checked experiment" → "production", with a new `characterEquiv*` row. Catalogue: new entries for `Applications/IVP/VectorField.lean`, `Chebyshev/AnalyticPolynomial.lean`, the two `Analyticity.lean` modules, the spectra modules and `CharacterTopology.lean`; the Taylor entry gains `Taylor/Polynomial.lean`'s faces; the example entry records the five layers and the retired radius-two statement. |
| `exterior/paper/v5/main.tex` | One citation token at line 1414: `Example1421.Cert.main_existsUnique` → `main_theorem`. No prose changed. Full audit, including eleven citations checked and left alone, in `tmp/autonomous_agenda_2026_09_13/TASK2_PAPER_CITATIONS.md`. |

Rebuilds (three consecutive `pdflatex -synctex=1 -interaction=nonstopmode` runs each, identical output):
ground note 45 pp / 0 errors / 0 overfull / 0 underfull (was 43 pp, 0 overfull);
companion 57 pp / 0 errors / 0 overfull / 25 underfull (was 56 pp, 0 overfull, 23 underfull);
paper v5 23 pp / 0 errors / 0 overfull / 0 underfull (unchanged).

Acceptance: every RETIRED/RENAMED old name above is absent from the two `.tex` files, the
glossary, `ARCHITECTURE.md`, `SKILL.md` and `main.tex`, except inside dated
"renamed/retired/formerly" notes — `main_existsUnique` (companion, glossary),
`ivpComposedApprox` (ARCHITECTURE), `norm_Dphi_le` (glossary, in the aliases-to-avoid column),
`DPhiCLM`, `hasFDerivAt_Phi`, `compPolyDerivative_eq`, `banachField_eq_f`, `f_lipschitzOnWith`
and `Example1421/Lambda.lean` (companion, glossary, SKILL) — and in this file.
`Applications/IVP/Chebyshev/Lambda.lean` is a live library module and its citations stand.

## Header-diff audit (completeness check, 2026-09-13)
`git diff -U0 -- '*.lean' | grep '^[-+](theorem|lemma|def|…)'`: 70 removed / 58 added declaration header lines. Every removed
header not matched by a RENAMES.md row falls in one of two classes:
- **Pre-TASK-2 removals (2026-09-12 Chebyshev-adapter migration of Example 14.2.1, other session; documented in
  `tmp/proposal_experiments_2026_09_06/CHEB_COMPPOLY_PROMOTION_RESULTS.md`, not in RENAMES.md by design):** `suppWindow`,
  `FCseq_Dphi_single`, `Sabar_support`, `phi_abar_toSeq_nat`, `FAseq_single` (Example1421/Certificate.lean). Uncommitted since, hence visible here.
  The private generic `FAseq_single` in `Applications/IVP/Chebyshev/Polynomial.lean` is a different declaration.
- **Restated / re-homed but still present (header line rewritten, declaration exists — verified `grep -rlw`):** `hasFPowerSeriesAt_eval`
  (Geometric/AnalyticExt.lean, now a corollary of `hasFPowerSeriesOnBall_eval`), `A_norm_le`, `hdiff`, `r₀_pos`, `ν_val_eq_q`, `A_inj`
  (Example245/Certificate.lean, Example77/Certificate.lean, KappaToy.lean — `ex_` prefix drops / H4 local calculus).
No other unaccounted header change. Verdict: RENAMES.md complete for TASK 2.

## Round 2 (R2, 2026-09-13) — review findings applied

Gates: every step built its targets green and reprinted its endpoints byte-identically against
`TASK2_axioms_after_T.txt`; the full 18-endpoint probe is saved as `TASK2_axioms_after_R2.txt`
(byte-identical). Three consecutive full `lake build`s: 4,026 jobs. Backups of every touched file:
`tmp/autonomous_agenda_2026_09_13/backup_task2_R2/`.

### RETIRED (R2; deleted, replacement named)
| old | replacement | file | step | reason |
|---|---|---|---|---|
| `Example1421.Cert.lipschitzBound_f_cpoly` | `IVP.vectorField_lipschitzOnWith` (internal to the faces) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | R2-1 | the three Chebyshev solution faces no longer take `{K} (hK)`; the Lipschitz constant `∑ l, lipschitzBound (f l) R` is chosen inside the face (`R ≥ 0` from `hR`), so the example states no syntactic number. Statements of `main_solution_existsUnique*` and `analytic_solution_existsUnique_radius_one` literally unchanged |
| `Example81.Cert.Df_diff_norm_le` (private) | `IVP.StdIVPData.Z₂_le_of_compPoly` + `CompPoly.norm_fderiv_evalBanach_sub_le_max` | `Examples/IVP/Taylor/Example81/Certificate.lean` | R2-5 | the Lipschitz bound of the derivative is read off the syntax (`derivativeLipschitzBound (X² − X) = 2`, radius-free); `Z₂_le_cert` keeps its name, statement and its single `native_decide` (`…Z₂_le_cert._native.native_decide.ax_1_1`) |
| `Example83.Cert.D₂_lorenz`, `Example83.Cert.hD₂_lorenz`, `Example83.Cert.Df_diff_norm_le` (all private) | `IVP.StdIVPData.Z₂_le_of_compPoly` (`hinactive` for the linear first equation, `hB` with `B = 2`) | `Examples/IVP/Taylor/Example83/Certificate.lean` | R2-5 | idem; the Hessian table and its `pderiv` check are replaced by the syntactic constant, `{1, 2}` active set and the `native_decide` block-norm check unchanged (`…Z₂_le_cert._native.native_decide.ax_1_1`) |
| `Example81.fderiv_G_scalar_tail` | `IVP.StdIVPData.Z₁_le_of_compPoly` / `Z₁_le_exact_of_compPoly` (tail plumbing discharged inside `StdIVPData.Z₁_le`) | `Examples/IVP/Taylor/Example81/Algebra.lean` | R2-6 | zero consumers after `Z₁_le_cert`/`Z₁_le_exact` became one call each; `Df`, `Df_eq_fderiv`, `Df_norm_le` (native-bearing), `Df_eq_leftMul` untouched |
| `Example83.fderiv_G_lorenz_tail` | idem | `Examples/IVP/Taylor/Example83/Algebra.lean` | R2-6 | idem |
| `Example81.Cert.defect_norm_lt_one`, `Example83.Cert.defect_norm_lt_one` (private) | `IVP.StdIVPData.{x_analytic_isAnalyticSolution, analytic_eq_canonical, analytic_unique, analytic_existsUnique}_of_compPoly_of_radii`, `ivpCoeffs_zero_of_compPoly_of_radii` | `Examples/IVP/Taylor/Example8{1,3}/Analytic.lean` | R2-4 | `Z₀ < 1` is derived by the faces from the same five facts `main_theorem` consumes; `xTilde`/`xTilde_ball`/`xTilde_G_zero`/`x_analytic` stay (live consumers: `logistic_analyticOnNhd`, `lorenz_analyticOnNhd`, `lorenz_coefficients_zero`, `lorenz_complex_ivp`). `ComplexTime.lean`'s duplicated `hdefect` derivation resolved the same way (library face) |
| `Example1421.Cert.abar_toSeq_neg`, `Example1421.Cert.abar_norm_component_le` (private) | `ChebyshevIVP.StdChebIVPData.abar_toSeq_negSucc`, `StdChebIVPData.norm_abar_le_norm_symmetrize` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | R2-7 | bundle-level facts (`ā` is one-sided); `abar_norm_le` is now a one-liner through the bundle lemma and `Sabar_norm_le` |

### ADDED (R2; library faces, all sorry-free, axioms exactly `propext, Classical.choice, Quot.sound`)
| declaration | file | step | role |
|---|---|---|---|
| `IVP.vectorField_lipschitzOnWith` | `Applications/IVP/VectorField.lean` (+ import `CompPoly/Bounds`) | R2-1 | `LipschitzOnWith (toNNReal (∑ l, lipschitzBound (f l) R)) (vectorField f) (closedBall 0 R)` for `R ≥ 0`; the internal Lipschitz witness of the Chebyshev solution faces |
| `IVP.StdIVPData.ivpCoeffs_zero_of_compPoly_of_radii` | `Applications/IVP/Taylor/Polynomial.lean` | R2-4 | `G xTilde = 0 → ivpCoeffs … xTilde = 0` with `Z₀ < 1` from the four bounds (consumer: `Example83.Cert.lorenz_coefficients_zero`) |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly_of_radii`, `analytic_eq_canonical_of_compPoly_of_radii`, `analytic_unique_of_compPoly_of_radii`, `analytic_existsUnique_of_compPoly_of_radii` | `Applications/IVP/Taylor/Analytic.lean` (+ import `Taylor/Polynomial`) | R2-4 | the Taylor analytic faces from the bounds; the last two choose the zero via `existsUnique_of_compPoly`; mirror of `Chebyshev/AnalyticPolynomial.lean` |
| `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_sub_le`, `norm_fderiv_evalBanach_sub_le_max` | `Algebra/Polynomial/CompPoly/WeightedL1.lean` | R2-5 | Lipschitz bound of `fderiv (evalBanach p)` in `‖c − a‖` by `derivativeLipschitzBound` (Taylor face of `Chebyshev.norm_derivative_sub_le_of_norm_sub`, no factor 2) |
| `IVP.StdIVPData.Z₂_le_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-5 | Taylor `Z₂` socket on `ivp_Z₂_le`: `(active) (hcomp_le : native block-norm check, first argument) (hr₀) (hinactive) (hB)`; derives differentiability, `0 ≤ B`, `0 ≤ Z₂` |
| `IVP.StdIVPData.Z₁_le`, `Z₁_le_exact` (+ private `composedApprox_sub_fderiv_G_toSeq`) | `Applications/IVP/Taylor/Standard.lean` | R2-6 | generic `Z₁` recipe / exact-column faces with the `hfin`/`htail` plumbing discharged (`composedApprox_toCLM_tail` + `fderiv_G_tail`) |
| `IVP.StdIVPData.Z₁_le_of_compPoly`, `Z₁_le_exact_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-6 | the same at `φ := banachField f_cpoly`; consumers `Example8{1,3}.Cert.Z₁_le_cert`, `Example81.Cert.Z₁_le_exact` (one call each, the example's own `Df`, `Df_eq_fderiv`, `Df_norm_le`) |
| `ChebyshevIVP.StdChebIVPData.abar_toSeq_negSucc`, `norm_abar_le_norm_symmetrize` | `Applications/IVP/Chebyshev/Standard.lean` (+ import `Chebyshev/Evaluation`) | R2-7 | one-sided storage of `ā` and `‖ā l‖ ≤ ‖S(ā l)‖` |
| `Example1421.two_le_ν_val` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | R2-8 | `(2 : ℝ) ≤ ν_val`, replaces three inlined `by rw [show (ν_val : ℝ) = 2 from rfl]` |

### RESTATED (R2; same name, signature changed)
| declaration | file | step | change |
|---|---|---|---|
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_compPoly`, `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` | R2-1 | `{K : NNReal} (hK : …)` removed; conclusions unchanged |
| `ChebyshevIVP.StdChebIVPData.Z₂_le_of_compPoly_max` | `Applications/IVP/Chebyshev/Polynomial.lean` | R2-2 | `hB` quantified over `c ∈ closedBall ā r₀` instead of all `c`; docstring says which radii the constant is taken at (degree ≤ 2 ⇒ radius-free) |
| `IVP.StdIVPData.existsUnique_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-3 | `hZ₀ : Z₀_norm … ≤ Z₀` → `hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀` (matches its sibling and the Chebyshev face); Ex 8.1/8.3 `main_theorem` drop `data.Z₀_le` |
| `IVP.ivp_Z₂_le` | `Applications/IVP/Taylor/Operator.lean` | R2-5 | `c`, `hc` moved before `active`; `hzero` and `hDφ_diff` are stated at the point `c` only (strictly more general; sole other consumer `Theorem.lean` adapted with `fun h j hj => hzero c h j hj`) |
| `RadiiPolynomial.Gelfand.pointwiseTopology` | `Analysis/SequenceSpace/CharacterTopology.lean` | R2-8 | `R` explicit; the three consumers (`Geometric/Spectrum`, `Chebyshev/LaurentSpectrum`, `Chebyshev/Spectrum/Topology`) drop `(R := ℝ)` |
| `Example8{1,3}.Cert.main_theorem`, `ivp_main_theorem`, `Z₁_le_cert`, `Z₂_le_cert`, `Example81.Cert.Z₁_le_exact`, `Example8{1,3}.Cert.{x_analytic_isAnalyticSolution, analytic_eq_canonical, analytic_unique, analytic_existsUnique}`, `Example83.Cert.lorenz_coefficients_zero`, `Example1421.Cert.{main_solution_existsUnique, _contractive, _radius_one, analytic_solution_existsUnique_radius_one, Z₂_le, abar_norm_le}` | examples | R2 | bodies only (proof terms retargeted to the faces; the no-op cast adaptors `Y₀_le.trans (by … exact_mod_cast le_refl _)` and `fun c hc => Z₂_le_cert c hc` dropped); statements unchanged; axiom sets byte-identical |

Docstrings rewritten (R2-8): `Applications/IVP/Taylor/Analytic.lean` module header (three tiers of faces),
`Applications/IVP/Chebyshev/Standard.lean` "Deferred to Example Level" → "Certificate faces",
`Applications/IVP/Chebyshev/Polynomial.lean` "Certificate faces" paragraph + `norm_compPolyDerivative_le`
(system face kept for a future system-level `Z₁` theorem), `Example1421/Certificate.lean` header
(`Z₀_finBlockNorm_le` is the `Z₀` input), `Example1421/Algebra.lean` §4 audit witnesses
(`computed_DF_columns`/`computed_DF_entries`/`rawDerivative_single_eq_dataDF`). Dead imports removed
from `Example1421/Algebra.lean`: `Analysis/SequenceSpace/Chebyshev/Bordered`, `Certification/LeanCertAdapter`,
`Algebra/Polynomial` (build-verified).


## Independent-review fixes (Codex, 2026-09-13)

The four findings in `tmp/autonomous_agenda_2026_09_13/review_codex/REVIEW.md` are resolved.
`MakeCompPoly.lean` now synthesizes the input lambda before reification; the production
polynomial example adds `rationalConstant_reified`, `algebraMapConstant_reified`, and
`affineConstant_reified`. No existing declaration was renamed or removed.

Experimental `BorderedCheb` exports `instCompleteSpace` and `instNormOneClass`; downstream
residual and exact multiplier-norm checks use these instances directly. It remains in tmp.
The three quadratic-bound docstrings now qualify the syntactic AST presentation.
The header audit above corrects the old Example1421 `FAseq_single` removal's classification.

The canonical tracked `.claude/skills/radii-poly-api-design/SKILL.md` now incorporates the
current interface guidance while preserving its original core description and UMP doctrine.
Both `~/.agents/skills/radii-poly-api-design/SKILL.md` and
`~/.claude/skills/radii-poly-api-design/SKILL.md` are byte-identical mirrors of it; this
supersedes the earlier global-Claude-only skill update recorded in the writeup table.

Gates: full build 4,026 jobs; 51/51 experiment checks; frozen 18-endpoint axiom output
byte-identical after the existing label rename; folded consumer/bridge checks and skill
validation pass. No `.tex` or curated-memory edits, commits, or pushes in this correction.
Evidence and Claude handoff: `tmp/autonomous_agenda_2026_09_13/review_fixes_codex/`.
