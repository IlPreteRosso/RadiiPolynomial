# CONTRACT.md digest (v1.2a, 428 lines; `exterior/Unformalization/CONTRACT.md`, as of 2026-10-11)

The contract file is authoritative; this digest says what each section governs and quotes the
operative clause of every ruling. Version history (line 3): v0 (kept at `_records/CONTRACT_v0_fc5bb6e5.md`)
→ v1 = v0 + Codex's seven positions → v1.1 = pilot drafter's mechanics (§6) → v1.2 = pilot checker's
eleven rulings (§7) → v1.2a = trust-boundary wording (Codex C1), freeze inventory incl. per-unit
registry copies (Codex C2), §7.12–15 + tool fixes. §7.16–7.70 and §8 were appended during the waves
and the close-out (2026-10-10/11). Each unit's MANIFEST records `contract_sha256`, and a copy sits in
`_records/<unit>/CONTRACT.frozen.md`.

## §1 Scope and layout
Scope = `API_FILES.txt` (129 files from `_tools/inventory.py`); mirror `<Dir>/<File>.lean` ↦ `<Dir>/<File>.tex` + `.pdf`;
artefacts beside them, never versioned; shared preamble `_common/unformalization.sty`; every companion starts
`\documentclass[11pt]{article}\usepackage{unformalization}`, "no other packages". Pinned library commit (text): `5d0fa4f`.

## §2 Document template (section order fixed)
0 title/author/date + `\unfheader{<source path>}{<pin>}{<project imports>}{<role>}{<importers or "none (facade/leaf)">}`.
1 **Setting**: (a) standing hypotheses = every `variable`/typeclass block as classical assumptions, in file order;
(b) Who-is-who booktabs table "Lean object → symbol used in this companion → meaning … No new symbol without a row."
2 **Body sections mirroring the file**, "titled in words (never a Lean name in a heading)". **Coverage policy** — sidecar
= "the inventory of record, the regex inventory is advisory"; each public authored declaration has "exactly one *primary
exposition*" closed by a `\leanline`. Categories: def/abbrev/structure/class/inductive → Definition; generated declarations
covered by the parent and listed in the index; theorem/lemma → Lemma/Proposition/Theorem/Corollary by weight; named instance →
Fact (structure, operations, compatibility, scope); anonymous/local instance → stated in the section's Setting with span,
"a `local instance` is never turned into a global statement"; `private` → folded into proofs and named in the `\leanline`,
"a *public* helper is never dropped for being a helper"; axiom → Assumption; opaque/unsafe/partial → Definition with the
category; macro/syntax/elab → Convention ("what it does NOT check"); exclusions need a recorded reason.
**Statement discipline**: "Hypotheses are the declaration's EFFECTIVE binders as printed in the sidecar"; "Nothing generalized,
nothing added, nothing dropped"; preserve quantifiers, direction, strictness, empty/finite cases, carrier vs scalar, norm and
topology in force; `PosReal` = positivity only; `noncomputable` is not a hypothesis; exact numerals only with the equality
recorded. **Proof rule**: "the classical exposition of the argument the Lean proof ESTABLISHES"; "`simp` is NOT 'unfold and
compute'"; `rfl` = definitional identity; `ring` = polynomial normalization "never an analytic claim"; one-call proofs explain the
cited theorem; alternative proofs only in a Remark tagged *alternative route (not the formalized one)*. Then `\leanline \lean{…}`
+ `\bookref{…}` "copied, never invented". Design-choice docstrings become Remarks.
3 **Index of declarations**: longtable "Lean name → environment number → one-clause meaning, every public declaration".

## §3 Faithfulness and evidence
Evidence tags for anything not proved in this file (Lean/Mathlib/LeanCert, resolved by a real `#check`, recorded in
`EXTERNAL_RESOLVED.txt`); `\evid{not formalized here}` = "no supporting declaration identified in the audited scope, never a
global absence claim", Remarks only; "A tag never licenses stronger hypotheses than the declaration it names". Established facts
are not relabelled independent proofs. **Trust boundary** sentence distinguishing `decide`, `native_decide`, axioms/`sorry`;
"no axiom audit is claimed otherwise" (Codex C1). Lean names byte-exact in `\lean{…}`, "never inside a section title, never in math
mode. No code blocks … precise binders live in the sidecar, not in the PDF." Numbers copied from source. `\bookref` = attribution,
stated once. Banned words: "novel", "new", "state of the art", "elegant", "trivially", hedges, meta-commentary, line counts, page
targets, speculation. Terminology: `UBIQUITOUS_LANGUAGE.md` authoritative.

## §4 Gates (`_tools/gates.py` v2; `_tools/selftest.py` negative controls must pass)
G0 sidecar · G1 tex · G2 pdf + pdfinfo/pdftotext · G3 log without `!` · G4 no `??` · G5 no overfull > 5 pt ("fix by rewording,
never by font/spacing") · G6 coverage against the ELABORATED sidecar · G7 resolution (exact FQN / unique suffix in file → ALL_FQNS
→ EXTERNAL_RESOLVED; ambiguous and unknown fail). (G8, G9, G10 were added later in the tool: stranded Lean line, tag path = declaring
file, advisory `\leanx` names.) "`_tools/build.py` is fail-closed"; "A regex count is never acceptance evidence".

## §5 Pipeline per unit
"Opus 5.5 drafters and checkers; Haiku 5.5 for recipe-plus-script steps; Fable coordinates; Codex reviews." Drafter → Checker
("read-only: a per-declaration matrix `_records/<unit>/MATRIX_<File>.md` … plus the rendered PDF") → drafter applies findings
("disposition of every finding recorded") → gates → freeze (`_tools/freeze.py <unit>`) → Codex audit of samples "Core (E1),
WeightedL1 (B9), Certification/IVP (D2), Tactic (E4)", expansion by shared defect pattern (B4 first candidate); "Sampling never
means 'Codex audited all 129 files'; no unit is accepted by being named a sample." "No `lake build` … no edit of any `.lean` file,
no edit of anything outside `exterior/Unformalization/`."

## §6 Mechanics learnt from the pilot (E1 Core)
`\lean{…}` "for DECLARATION NAMES only; it is what the gate reads"; `\leanx{…}` for binders/expressions/paths with `\_`; tags
`\evidl{Mathlib}{decl_name}` etc.; `% unf-allow:` "for notation typeset with `\lean` only, never for Mathlib names"; unnameable
instance facts → `\evid{Mathlib}` with the structure in words; Who-is-who = non-floating longtable; index =
`longtable{l p{4.6in}}`; "Imported by" never `Examples/`; "§1"/"§2" docstring labels are internal, "Theorem 7.6.2 in the informal
proof" is a book locator; "The contract, the style file and the tools are FROZEN during a wave; a change is announced in the next
wave's briefs, never applied under a running drafter."

## §7 Rulings 7.1–7.70 (operative clause quoted; source unit in brackets as in the contract)
1. Standing hypotheses vs effective binders [E1]: "The Setting renders each `variable` block *as declared*, and says in the same sentence which statements use it"; "A standing sentence is never stronger than the effective binders of the statements it introduces."
2. Evidence form [E1]: "the name lives inside the tag and is NOT repeated in a `\lean{…}`"; `\evid{Mathlib}` without a name "only for a fact obtained by instance inference".
3. Paths in `\evidl{Lean: …}` "are full paths from the library source root … never abbreviated."
4. Book locators: "docstrings AND `-- eq. …` / `-- Ref: …` line comments … both count; nothing is invented."
5. Severity scale: "ERROR (statement or proof wrong) · MAJOR (hypothesis or route deviation; an extra conclusion inside a statement environment that the declaration does not prove — it moves to a Remark) · EVIDENCE … · MINOR … Every class is fixed before the freeze."
6. Orphans/layout: "`\nopagebreak`, `\pagebreak`, `\clearpage` and moving a paragraph are allowed fixes; font and spacing changes are not; no new packages."
7. Who-is-who threshold: "A row for every symbol used in two or more environments or introduced in a Setting paragraph".
8. Glossary vs source usage: "`UBIQUITOUS_LANGUAGE.md` wins for prose terms"; "acceptance gate", never bare "gate", for `gateQ`; "syntactic Lipschitz constant of \(x\mapsto Q(x)\) on \(\nrm{x}\le R\)".
9. "**Sidecar order** is source order (by span start); matrices follow it."
10. Examples in Remarks: "`Examples/` files may be named as `\fpath{…}` in Remarks without an evidence tag"; never in "Imported by".
11. `ring`/`rfl` wording: "both sides are the same polynomial in … by ring normalization in \(\R\)" / "definitionally equal after unfolding …"; "'Compute' alone is not accepted."
12. Notation declarations (`«term_⋆[_]_»`) "are covered by a **Convention** environment … listed in the index byte-exact inside `\lean{…}`".
13. Export aliases: "cited by its DECLARED name (`Finset.HasMulAntidiagonal.mem_mulAntidiagonal`), which is what `#check` resolves."
14. Other tactic normalizations: `abel` → "by normalization in the additive commutative group …"; `noncomm_ring`; `linarith`/`nlinarith` → "by linear (resp. polynomial) arithmetic over \(\R\) from the listed inequalities"; `omega`; `norm_num` → "by numeral evaluation"; `positivity`; "`simp` is never one of these".
15. Stale docstrings: "the companion follows the source and records the discrepancy neutrally in a Remark; it never repeats the stale claim as fact."
16. Lean core facts "are tagged `\evidl{Lean core}{name}`"; external tags accepted "ONLY from a real `#check` whose module belongs to that package"; elaborator calls in `\leanx` without a tag.
17. Tactic files: a macro-only private theorem "gets its own Lemma"; metaprogram defs → "Definition (algorithm)"; regression `example`s "not results of the file"; Convention paragraphs "**Invocation · Goal · Algorithm · Rule set · Statement discharged · What remains for the user · What is not checked**, in this order."
18. "**Typewriter ligatures** are off"; "a companion adds no local preamble beyond `\newcommand`s for its own symbols."
19. Who-is-who sharpened [A1]: a row "for a symbol defined in one environment and referenced from another, or introduced in a section preamble"; re-bound variables need none; generated twins named in the same `\leanline`; `\leanline` carries `\nopagebreak`.
20. Tags/names [A2]: tag text breaks after `/`; Lean-path tags may use the unique dotted suffix; external tags use "the DECLARED full name"; un-imported Mathlib names in `\leanx` "with 'not imported by this file', never tagged"; homogeneous simp-lemma families "may share ONE environment with numbered items".
21. "**`ContDiff ℝ ⊤`** is the analytic class \(C^\omega\) in this Mathlib"; a docstring saying "smooth" is weaker — state \(C^\omega\), record the discrepancy.
22. Cross-file facts list [B9 draft]: "Facts used from other library files" ((A1), (A2), …), each entry tagged; proofs may cite the label.
23. Short tokens: "`\lean{…}` tokens of two characters or fewer … are invisible to the gate; cite constructors and such names qualified".
24. Tactic fixed fills [E4]: "Goal. None: a term elaborator …", "Statement discharged. None: the output is a value, not a proof"; third-party elaborators as `\leanx{Name}` + `\fpath{LeanCert/Tactic/Verification.lean}` + pinned LeanCert revision (`7f91b6eb`).
25. "**Never parenthesise an `\evidl`**"; an orphaned `\paragraph{Who is who.}` is fixed with `\pagebreak` before it.
26. Small clarifications [B1]: "every Setting carries the one-sentence trust line, also when the file contains no `decide`/`native_decide`/axiom/`sorry`"; local-instance index rows point to their section; module docstring is the role source when ARCHITECTURE.md has no row; long header fields use nested `tabular[t]`.
27. Fact registry [D2]: numbered `longtable` registry (fact / statement / tag); proofs cite "(F24)"; "`\leanx{…}` never sits in math mode either"; sidecar reports `structure`.
28. Locators and long Lean lines [A3]: section-docstring locator attaches to "the declaration whose formula the section docstring quotes, and only to it"; `\leanline` with five or more names in `\newline` groups; `(\lnu)^{L}`, never `\lnu^{L}`.
29. Primes, short names, named local instances [A4]: "only tokens of ≤ 2 characters are invisible"; a named `local instance` in the sidecar is covered by the Setting paragraph's `\leanline`.
30. Trust line, mandatory wording [B1 check; Codex B9]: "`\paragraph{Trust boundary.} Reading this file's source shows no explicit \leanx{decide} or \leanx{native\_decide} invocation, axiom declaration, or admission by \leanx{sorry} or \leanx{admit}; no transitive axiom audit is claimed.`"; a docstring using the word "axiom" is not an axiom declaration; labelled first-use cross-file statements allowed at any use count for one-call proofs.
31. Facts lists at any use count; titles [B9]: "the §7.22 'three or more uses' threshold is withdrawn"; "`\title{Unformalization of \unftitle{RadiiPolynomial.A.B.C}}`"; Mathlib `⨆` on reals "and `0` OTHERWISE (empty OR unbounded)".
32. Local-instance files [A4]: the checker elaborates with `pp.explicit` and records which statements mention the selected instance constants; "the selection selects the same operations" only where a probe or declaration supports it.
33. Tags in lists; private defs [B3]: long tags woven into the sentence with the unique suffix; a private def's omitted section instances count in the Setting; "The external-name registry is now written under an exclusive lock."
34. "**Declaration names are never `\leanx`** … typeset `\lean{FQN}` (or inside `\evidl`)"; authored `alias` → index row to a Remark naming the aliased statement.
35. Enumerate labels print (i), (ii), …; header value column is a breakable `p` column; index rows may use the unique suffix.
36. "**`simp?` probes.** A drafter or checker who must name the lemmas a `simp` call uses runs `simp?` on a scratch file with `lake env lean` from the Lake root (no build)".
37. Lists of objects from other files may stand in the Setting; a file without sections "may be one `\section` with `\subsection`s."
38. "**Continuous vs bounded** (Codex B9): `→L[𝕜]` is CONTINUOUS linear maps … 'bounded' only where a bound is proved; never repair by strengthening the field; a target that is only a topological module gets no norm language."
39. Defaults from B5: "the registry `longtable` (§7.27) is the default form for cross-file facts"; shared private helper → one Remark + mention per using paragraph; overclaiming docstrings recorded neutrally.
40. Private helpers and tags [B2]: "every private helper must ALSO appear in at least one `\leanline`"; "never two `\evidl` tags back to back; never start a line with a long tag; one tag per facts sub-item".
41. Fixed glosses [B4]: `@[instance_reducible]` = "a definition (not an instance) carrying the attribute `instance_reducible`…"; header source path breaks only after `/`.
42. Foreign `X.congr_simp` [B6]: indexed with a row pointing to the Setting's objects list ("generated in this file: congruence lemma of the parent …"); "bounded" docstrings over bare normed fields corrected neutrally.
43. Namespaces named like a carrier [B7]: say once that full names carry no library prefix; "Brief summaries are hints: the drafter follows the source"; unverified instance choices "by instance inference" only.
44. House forms [C1]: "an applied expression is typeset head-first, `\lean{CompPoly.pderiv}\leanx{ 0 d.P}`"; quoted foreign definitions in a `\paragraph`; generated anonymous instance = index row + section paragraph, no `\leanline`.
45. B5 check: registry cells may stack tags; simp inside a private proof over private definitions "may be read from the source instead of probed (say so in the matrix)"; mid-word header breaks cleared by rebuild.
46. Provenance notes [B2]: "promoted from Example 14.2.1" counts as a book locator; repo example by `\fpath`; facts-list items may stack tags.
47. One `decide`; reserved macros; header fields [C3]: "…shows one explicit `\leanx{decide}` invocation, a kernel-checked decision proof in <environment> …"; reserved `\ev`, `\nrm`, `\lnu`, `\abar`, `\diag`, `\Hom`, `\R\N\Q\C\Z`; header fields "use the `\newline` form with `\leanx{\unftitle{Module.Path}}`".
48. More tactic wording [C2]: `linear_combination e` → "by ring normalization in \(R\) of the linear combination \(e\) of the listed identities"; `module`; `push_cast` → "by pushing the coercions inward"; unique suffixes default in object lists.
49. Paths [C1, revised]: tag paths hyphenatable, `\fpath` breakable; "A mid-word break in a path is cosmetic and never a finding"; Mathlib total-derivative convention tagged `\evidl{Mathlib}{fderiv_zero_of_not_differentiableAt}`; G10 also flags registry Mathlib names in `\leanx`.
50. Foreign congr_simp; shared privates [B8]: one "Private steps" Remark per section is acceptable "provided every private helper also appears in at least one `\leanline`"; probes need `Environment.contains n (skipRealize := false)`.
51. Header fields [C3]: §7.47 governs Imports and Imported-by; Role may stay nested `tabular[t]`; "A file wired only at the root is 'imported by the root module `RadiiPolynomial`'".
52. Heads of Who-is-who expressions [C3]: head-first "whatever the head's origin"; "library head in `\leanx` = EVIDENCE; Mathlib/core head = MINOR".
53. Probe recipe without `cd` [C3]: the v4.34.1 `lean` binary with `LEAN_PATH` = root and package build libs "is accepted as equivalent to `lake env lean`".
54. Private declarations used by nothing [C6]: "recorded in a Remark with its own `\leanline`, stating that it is unused."
55. Which `simp` calls need a probe [C6]: "A non-`only` `simp`/`simp_all`/`field_simp` call that discharges or materially transforms the goal is substantive and is probed"; pure unfolds/elementary identities described in words, saying so.
56. Notation-form Who-is-who rows [E3]: infix/arrow-type objects "may stay in `\leanx`".
57. Library history in Remarks [E2]: only "when the module's own text at the pinned revision grounds it"; "Git history is not a source for the companions."
58. Descriptions of external definitions [D1]: "must hold on that definition's whole domain, or be explicitly restricted … A description true only in the assumed case but stated generally is MAJOR."
59. `decide` as a term [D3]: counted "wherever they occur"; "A `decide (p)` used as a Boolean VALUE inside a definition is not a proof".
60. Paths in italic environments [C4]: "`\textup{\fpath{…}}`"; style not changed ("frozen units are not re-rendered").
61. Several decision proofs [close-out]: "counts them … and locates each in one clause …; it never writes 'several'."
62. Grouped definitions: only "one mathematical object split for Lean's sake"; "each name gets its own `\leanline` directly after the environment".
63. Long `\leanline`s: "At most three names per `\leanline`; a longer list is split with `\newline` into groups of at most three"; `\emergencystretch` unchanged.
64. One external registry: "`_sidecar/EXTERNAL_RESOLVED.txt` is the single registry … Rows enter only through `_tools/resolve_external.py` (real `#check`), never by hand"; batched per cited module.
65. "`\unfheader` keeps its fields. External packages a file uses (LeanCert) are named in the trust paragraph with their pinned revision".
66. "`gates.py` prints the G10 advisory … as a `NOTE` line … Notes never fail a gate."
67. Private helpers in a `\leanline`: "G6 coverage counts PUBLIC authored declarations only"; a cited private is allowed and resolved; "No sub-check is added."
68. Brackets in theorem titles: "`\begin{theorem}[{…}]`; plain titles stay unbraced."
69. Core types in the SYNTAX set: type formers "never get a registry row"; "A FACT about them (`Fin.val_lt`, `Finset.sum_le_sum`) is a registry row."
70. Long `\leanx` tokens: "`\leanx` stays unbreakable … broken by hand with `\allowbreak` after `_` or `.`"; `\pagebreak` before an overflowing enumerate.

## §8 Lessons (2026-10-11; "for the next wave or the companion re-pin")
- Every MAJOR came from a property smuggled into a Definition (§7.5) or a route sentence a probe refuted → DRAFTER
  preconditions P1 (move properties out of Definitions), P2 (confirm route sentences; PROBE substantive simp/rw; probes in
  `_records/<unit>/probes/`; "the checker re-probes a sample instead of all"), P3 (§7.58 whole-domain check), P4 (grep unused
  privates, §7.54).
- "Rulings first. §7 (now §7.1–7.70) is closed; a new wave starts from the full §7 in its briefs and a checker raises only points
  that no ruling covers." Half of round-1 findings of waves 2–3 relitigated ruled points.
- Pin: "Companions stay correct AT THEIR PIN; a re-pin pass (new MANIFESTs, line ranges, docstring Remarks turned into history or
  dropped) is a separate campaign on the user's word." (Executed 2026-10-11; result: pin d6fda60 in the headers and MANIFESTs;
  the §1/§8 text still says 5d0fa4f.)

## Rulings by topic (index)
Hypotheses/Setting: 7.1, 7.7, 7.19, 7.26, 7.29, 7.32, 7.33, 7.37 · Evidence/registry: 7.2, 7.3, 7.13, 7.16, 7.20, 7.22, 7.27, 7.31,
7.39, 7.45, 7.46, 7.64, 7.69 · Trust line: 7.26, 7.30, 7.47, 7.59, 7.61, 7.65 · Proof wording/probes: 7.11, 7.14, 7.36, 7.48, 7.53,
7.55 · Names/typesetting: 7.12, 7.23, 7.29, 7.34, 7.44, 7.52, 7.56, 7.63, 7.67, 7.68, 7.70 · Layout: 7.6, 7.18, 7.25, 7.28, 7.35,
7.41, 7.49, 7.60 · Docstrings/history: 7.4, 7.15, 7.21, 7.28, 7.39, 7.42, 7.46, 7.57 · Math semantics: 7.21, 7.31, 7.38, 7.58 ·
Privates/generated: 7.17, 7.34, 7.40, 7.42, 7.50, 7.54, 7.62, 7.67 · Tactic files: 7.17, 7.24 · Header: 7.26, 7.31, 7.35, 7.41,
7.47, 7.51, 7.65 · Severity: 7.5, 7.52, 7.58.
