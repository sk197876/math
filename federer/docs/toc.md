# Documentation

This directory documents the Rocq formalisation of Herbert Federer,
*Geometric Measure Theory* (1969). Each Federer section has its own file,
with one entry per numbered item: the formalised assertions, their Rocq
names, hypotheses, corrections of the book and sources. Every mention of a
Rocq file or of a uniquely defined declaration is a link into the sources.

## Chapter 1: Grassmann algebra

Conventions and source scope are preserved in [1.1](chapter1/1.1.md).
Section 1.1 is complete apart from the deliberately deferred 1.1.3;
§§1.2–1.10 are covered with the qualifications
recorded in the individual entries. Questions in 1.8.3–1.8.4 remain questions.

| Section | Printed pages |
| --- | --- |
| [1.1 Tensor products](chapter1/1.1.md) | 8–11 |
| [1.2 Graded algebras](chapter1/1.2.md) | 11–13 |
| [1.3 The exterior algebra of a vectorspace](chapter1/1.3.md) | 13–16 |
| [1.4 Alternating forms and duality](chapter1/1.4.md) | 16–21 |
| [1.5 Interior multiplications](chapter1/1.5.md) | 21–23 |
| [1.6 Simple m-vectors](chapter1/1.6.md) | 23–27 |
| [1.7 Inner products](chapter1/1.7.md) | 27–38 |
| [1.8 Mass and comass](chapter1/1.8.md) | 38–41 |
| [1.9 The symmetric algebra of a vectorspace](chapter1/1.9.md) | 41–43 |
| [1.10 Symmetric forms and polynomial functions](chapter1/1.10.md) | 43–49 |

## Chapter 2: General measure theory

General conventions and earlier verification history are preserved in
[2.1](chapter2/2.1.md); erratum cross-references are in [2.2](chapter2/2.2.md).
Sections 2.1–2.7 and 2.9 are covered as recorded in their entries.
Items 2.8.8–2.8.9 are complete within the requested scope, including
subsidiary assertions and strict-convexity uniqueness, and excluding book
examples. Section 2.10 retains the documented qualifications:
2.10.6, the listed variants of later items, and deferred 2.10.46. Item 2.10.2
is complete, including real-degree Gamma normalization and the actual circle
cutoff counterexample.
The requested last proof is 2.10.48; 2.10.49 is historical discussion and
requires no formalisation. Validation checks the implemented statements;
it does not close these documented coverage gaps.

| Section | Printed pages |
| --- | --- |
| [2.1 Measures and measurable sets](chapter2/2.1.md) | 51–59 |
| [2.2 Borel and Suslin sets](chapter2/2.2.md) | 59–72 |
| [2.3 Measurable functions](chapter2/2.3.md) | 72–80 |
| [2.4 Lebesgue integration](chapter2/2.4.md) | 80–91 |
| [2.5 Linear functionals](chapter2/2.5.md) | 91–114 |
| [2.6 Product measures](chapter2/2.6.md) | 114–121 |
| [2.7 Invariant measures](chapter2/2.7.md) | 121–141 |
| [2.8 Covering theorems](chapter2/2.8.md) (2.8.8–2.8.9 complete within requested scope; book examples excluded) | 141–152 |
| [2.9 Derivates](chapter2/2.9.md) (formalised) | 152–169 |
| [2.10 Carathéodory's construction](chapter2/2.10.md) (through 2.10.48 with the stated qualifications; 2.10.46 deferred) | 169–206 |

The 27 October 2026 release passed the Chapter 2 rebuild, full recursive
kernel check and fresh 15,349-query assumptions audit. Unchanged Chapter 1
artifacts were reused after fingerprint checks. See the
[verification record](verification.txt) and
[machine-readable release report](checkpoints/chapter2-release-validation.json).

## Chapter 3: Rectifiability

[3.1 Differentials and tangents](chapter3/3.1.md), printed pp. 209–241,
is complete. Items **3.1.1–3.1.24 are completed** with their documented conventions,
zero-dimensional qualifications and erratum corrections. Their calculus,
inverse-function, Borel-measurability, partial-derivative, approximate-differential and measurable-section developments
have passed focused compilation, recursive kernel checking and assumptions
audits. The [3.1.4 completion record](checkpoints/3.1.4-validation.json)
records its final build, regression, recursive kernel check and assumptions audit.
The [3.1.5 record](checkpoints/3.1.5-validation.json) covers the subsequent
approximate-to-ordinary differentiability lemma and its punctured-center regression.
The [3.1.6 record](checkpoints/3.1.6-validation.json) covers Rademacher's
theorem, including both zero-dimensional boundaries.
The [3.1.7 record](checkpoints/3.1.7-validation.json) covers approximate
derivatives of Lipschitz maps on measurable domains.
The [3.1.8 record](checkpoints/3.1.8-validation.json) covers finite approximate
growth, the countable Lipschitz decomposition and approximate differentiability.
The [3.1.9 record](checkpoints/3.1.9-validation.json) covers Stepanoff's
theorem without a measurability premise on A.
The commentary in 3.1.10 is recorded. The [3.1.11 record](checkpoints/3.1.11-validation.json) covers higher
calculus, Taylor formulas, jets, coordinate partials and the smooth cutoff.
The [3.1.12 record](checkpoints/3.1.12-validation.json) covers the
Lipschitz-radius packing lemma, including the zero-dimensional case.
The [3.1.13 record](checkpoints/3.1.13-validation.json) covers the smooth
partition of unity on an arbitrary open cover, with its derivative bounds.
The [3.1.14 record](checkpoints/3.1.14-validation.json) covers Whitney's
extension theorem for jets of polynomials on a closed subset of R^m.
The [3.1.15 record](checkpoints/3.1.15-validation.json) covers the
approximation of maps of class k with finitely growing top differential
by maps of class k+1, up to sets of small measure.
The [3.1.16 record](checkpoints/3.1.16-validation.json) covers class-one
approximation under finite approximate growth, with an arbitrary actual domain.
The [3.1.17 record](checkpoints/3.1.17-validation.json) covers the corrected
converse, the nonmeasurable-domain and zero-source counterexamples, and
the zero-target regression.
The [3.1.18 record](checkpoints/3.1.18-validation.json) covers the complete
constant-rank normal form, its fixed smooth charts and both regressions.
The [3.1.19 record](checkpoints/3.1.19-validation.json) covers all submanifold
chart equivalences, actual coordinate homeomorphisms, local retractions,
local compactness and the isolated-point characterization.
The [3.1.20 record](checkpoints/3.1.20-validation.json) covers the full connected
submanifold/retraction equivalence and the erratum-corrected construction.
The [3.1.21 record](checkpoints/3.1.21-validation.json) covers tangent and normal
cones, transport, tangent planes, both bundles and the generic tangent-space
identities; its closing positive-reach paragraph remains a forward reference.
The [3.1.22 record](checkpoints/3.1.22-validation.json) covers relative
differentiation and class, the corrected base-value criterion, all five
submanifold differential criteria and ambient extensions.
The [3.1.23 record](checkpoints/3.1.23-validation.json) covers the complete
controlled supported straightening theorem, including the exact tangent-plane
identity and both Lipschitz bounds.
The [3.1.24 record](checkpoints/3.1.24-validation.json) covers analytic
characterizations, exact composition, general inversion and the scalar
majorant, analytic constant-rank and submanifold charts, root-set alternative
and coordinate series. The [3.1 release](checkpoints/3.1-release-validation.json)
passed its incremental all build, complete recursive kernel check and
dependency assumptions audit. [3.2 Area and coarea of Lipschitzian maps](chapter3/3.2.md) is in progress; items 3.2.1–3.2.39 are complete and validated, with explicit source qualifications and corrections in the section account. The first paragraph of 3.2.40 passed the full validation completed on 3 November 2026; only its Kneser example remains deferred. Items 3.2.41–44 are complete and validated. Items 3.2.46–48 remain pending. Item 3.2.45 is partial outside the current request. Subsections 3.3–3.4 remain pending.
Chapter 3 is exposed through [`Rectifiability.v`](../theories/Rectifiability.v) and tested in
[`DifferentialExamples.v`](../tests/DifferentialExamples.v) and [`InverseFunctionExamples.v`](../tests/InverseFunctionExamples.v).

Before undertaking Chapter 4, the user requests formalisation of
[EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952). This
prerequisite remains pending.

## Maps

- [contents.md](contents.md): each numbered item of the book with the Rocq
files and principal declarations that formalise it. It is generated by
`python3 tools/contents.py`.
- [index.md](index.md): the notions of the book's
index (pp. 672–676) with the declarations that define them.
- [symbols.md](symbols.md): the notations of pp. 669–671 with the declarations
or MathComp notations that express them.
- [divergences.md](divergences.md):
every place where a formal statement or proof departs from Federer's printed
text , with the reason and the declarations.

## Generated documentation

`make doc` runs coqdoc over the library and writes HTML to the build
directory's `html/` (not tracked). This workspace uses
`/opt/rocq/federer-build/html/index.html`; other checkouts default to
`_build/html/index.html` (see the top-level README). It lists the interface modules and, for
each numbered item, the modules and declarations that serve it, with links
to the coqdoc table of contents and the index of identifiers. The pages
show statements and documentation comments; proofs are omitted.

## Records and references

- [bibliography.md](bibliography.md): bibliographical identities of all cited sources.
- [verification.txt](verification.txt): builds, kernel checks and assumption audits.
- [assumptions.log](assumptions.log): the output of `make audit`.
- [toolchain.txt](toolchain.txt): exact toolchain versions.
- [references/README.md](references/README.md): source editions and citation conventions.
- [federer-erratum.tex](references/federer-erratum.tex): the working erratum transcription.

## Maintenance

After changing the formalisation, update the entry of the item in its
section file, record any divergence from Federer's text there and in
[divergences.md](divergences.md), then run `python3 tools/contents.py` and
`python3 tools/linkify_docs.py` (and `python3 tools/divergence_counts.py`
after changing the register). The linkify script links every mentioned
`.v` file and uniquely defined declaration, and repairs declaration links
whose line no longer holds the declaration.

The [full-project validation](checkpoints/2026-11-02-full-validation.json) completed on 3 November 2026: all 7,660 registered modules rebuilt cleanly, complete recursive kernel checking and all 20,465 fresh assumption queries passed without warnings; all 20,393 earlier assumption sets were preserved. This does not extend coverage to unregistered drafts.

Federer 1.1.2 is now complete and validated, including arbitrary finite-family canonical maps and product bases. See [the item record](checkpoints/1.1.2-validation.json).

Federer 1.1.4 is complete and validated, including unrestricted injectivity and the exact finite-factor surjectivity criterion. See [the item record](checkpoints/1.1.4-validation.json).

Federer 2.8.8 is complete and validated within the requested scope, including subsidiary assertions and excluding the book examples. See [the item record](checkpoints/2.8.8-validation.json).

Federer 2.8.9 is complete and validated within the requested scope, including strict-convexity and actual inner-product radial uniqueness. See [the item record](checkpoints/2.8.9-validation.json).

Federer 2.10.2 is complete and validated, including real dimensions and the circle example. See [the item record](checkpoints/2.10.2-validation.json).

Federer 3.2.41 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.41-validation.json).

Federer 3.2.42 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.42-validation.json).

Federer 3.2.43 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.43-validation.json).

Federer 3.2.44 is complete and validated with the scope and qualifications in [its record](checkpoints/3.2.44-validation.json).
