# Verification scope

This delivery does **not** complete the requested end-to-end Lean formalization.
The PDF addresses every question, including counterexamples to claims that fail
as printed. The Lean file proves 63 component theorems and contains no unfinished
proofs. These are different levels of completion.

## Source papers

- `2025年计算与应用数学.pdf`: six questions, three pages.
- `2025年概率与统计.pdf`: four questions, two pages.

The five source pages were rendered and inspected. No answer keys or direct
solutions were searched. Local Mathlib source was consulted for theorem APIs.

## Question-by-question coverage

| Question | Written solution | Lean verification | Remaining formal work |
|---|---|---|---|
| Applied 1 | Taylor expansion; unique parameters; generic order 3 | Exact coefficient optimization | Taylor/remainder/convergence bridge |
| Applied 2 | Complete sine eigenbasis and inverse spectral radius | Two matrix inverse identities; continuant expansion | Characteristic determinant identification, eigenbasis and spectral radius |
| Applied 3(a) | Distinct-root proof on the real domain (-1,1) | Polynomial root-count implication | Legendre degree/basis and interpolation matrix bridge |
| Applied 3(b,c) | Normal equations, positive definiteness, explicit diagonal and parity | Weight positivity; diagonal-system solution/uniqueness; cancellation algebra | Legendre and integral identities |
| Applied 4 | PCA/SVD construction and optimality | Spectral weight bound | Projection and spectral theorem reduction |
| Applied 5(a) | Positive inverse, bounded-step existence, sup-norm bound | Stencil algebra and norm induction | Sequence-space operators and norms |
| Applied 5(b) | Fourier proof with sharp scalar restriction | Exact scalar stability equivalence | Fourier/Plancherel and grid operator |
| Applied 6(a) | Exact solution | Initial conditions and both derivative equations | No remaining gap in verification of the explicit solution; uniqueness theorem is not formalized |
| Applied 6(b,c,d) | Stability regions, actual-data divergence, unconditional stability | Real factor bounds and explicit recurrence | Complex region and asymptotic power/vector arguments |
| Statistics 1(a) | All sign cases, zero endpoint cases and zero mean | Reflection and zero-mean interval geometry | Normal measures and CDF calculations |
| Statistics 1(b) | Counterexample using length-two intervals | Algebraic contradiction | Expected-length factorization and normal moments |
| Statistics 2 | Mixture interpretation; two injective rules refuting both quantifiers | Pointwise bounds and injectivity | Integration and normal-law example |
| Statistics 3 | Explicit independent two-point construction for every n >= 2 | Support comparisons; complete sine-ratio parameters; finite product nonnegativity, total mass and rectangle independence | Assemble these components into a single random-variable existence theorem with all cyclic comparison probabilities |
| Statistics 4 | Smooth-score no-root counterexample; corrected high-probability proof | Score bounds, mean arithmetic and no-root algebra | C1 proof and event probability; concentration, measurable selection and limits |

## Printed-statement qualifications

- Statistics 1(b): a fixed random coefficient width has expected interval length
  proportional to E|X|. It cannot reproduce the constant length 2 for all sigma.
- Statistics 2: the correct-selection probability is the mixture expectation of
  phi. An injective rule with range entirely above 1/2 defeats the requested
  universal counterexample construction.
- Statistics 4: bounded C1 scores can have no empirical root on a positive-
  probability event. The corrected high-probability statement is proved, with
  global differentiability/bounded derivative or equivalent expectation-level
  conditions clearly stated.
- Applied 3 uses the real associated-Legendre domain. Applied 5 uses supremum
  norms on the infinite grid and records the sampling typo.

## Reproduction

Run `./output/solutions2025/CHECK.ps1` from the existing project, or invoke the
script by absolute path. It uses the project's pinned toolchain and package
cache, then compiles Exam2025.lean and audits every declared theorem.

- Lean: leanprover/lean4:v4.34.0-rc2.
- Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
- `verification.txt`: compiler result and SHA256 of the checked source.
- `axioms.txt`: all 63 theorem dependency reports.
- `Audit.lean`: reproducible dependency queries.
- `numerical_checks.txt`: sanity checks of dice construction and spectral radius.

No custom axioms or proof placeholders are introduced. Standard Lean foundations
may include propext, Classical.choice and Quot.sound. No sorryAx is permitted.

`build_pdf.py` regenerates the PDF using ReportLab and installed Windows fonts.
`inspect_pdf.py` renders all pages with pypdfium2. The final PDF was visually
inspected; font fallbacks were added for missing mathematical glyphs.
