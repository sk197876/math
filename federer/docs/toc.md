# Documentation

These guides document the Rocq formalisation of Herbert Federer,
*Geometric Measure Theory* (1969). Each section guide records its numbered
items, formalised assertions, Rocq names, hypotheses, corrections, and
sources. Rocq files and uniquely defined declarations link to the sources.

## Find a result

| Starting point | Guide |
| --- | --- |
| A chapter or section | The section guides below |
| A numbered item | [Item map](contents.md) |
| A mathematical notion | [Book index](index.md) |
| A printed symbol | [Symbol map](symbols.md) |
| A correction, convention, or changed proof | [Divergences](divergences.md) |
| A cited work or consulted passage | [Bibliography](bibliography.md) and [source guide](references/README.md) |
| A build or audit result | [Verification guide](validation.md) and [checkpoint catalogue](checkpoints/README.md) |
| Documentation tools and editing rules | [Maintenance guide](maintenance.md) |

The section guides distinguish current coverage from dated validation.
Their overviews lead to local contents lists and numbered-item accounts;
supporting notes follow the accounts. The [maintenance guide](maintenance.md#document-structure)
defines this structure.

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

Release dates, rebuilt and reused scope, and the later Chapter 1 and 2
supplements are recorded in the [verification guide](validation.md#chapter-2-release-and-subsequent-supplements).

## Chapter 3: Rectifiability

This checkout records 3.1 and 3.3 as complete with their documented
qualifications. Section 3.2 retains deferred Kneser material in the second
paragraph of 3.2.40 and partial 3.2.45. Section 3.4 records validated work
through 3.4.6; 3.4.7–3.4.12 remain marked pending here. The
[release accounts](validation.md#chapter-3-release-accounts) retain the
individual checks, counts, source corrections, and future obligations.

| Section | Printed pages |
| --- | --- |
| [3.1 Differentials and tangents](chapter3/3.1.md) | 209–241 |
| [3.2 Area and coarea of Lipschitzian maps](chapter3/3.2.md) | 241–287 |
| [3.3 Structure theory](chapter3/3.3.md) | 287–310 |
| [3.4 Some properties of highly differentiable functions](chapter3/3.4.md) | 310–339 |

Chapter 3 is exposed through [`Rectifiability.v`](../theories/Rectifiability.v)
and tested in [`DifferentialExamples.v`](../tests/DifferentialExamples.v)
and [`InverseFunctionExamples.v`](../tests/InverseFunctionExamples.v).

Before Chapter 4, the user requests formalisation of
[EilenbergSteenrod1952](bibliography.md#eilenbergsteenrod1952). This
future prerequisite is recorded in the project plan.

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
text, with the reason and the declarations.

## Generated documentation

See [Rendering the documentation](rendering.md#generated-documentation)
for coqdoc output, its location, and its contents.

## Records and references

The [checkpoint guide](checkpoints/README.md) distinguishes dated historical
progress notes from current coverage and the active work queue.

- [bibliography.md](bibliography.md): bibliographical identities of all cited sources.
- [verification.txt](verification.txt): builds, kernel checks and assumption audits.
- [assumptions.log](assumptions.log): the output of `make audit`.
- [toolchain.txt](toolchain.txt): exact toolchain versions.
- [references/README.md](references/README.md): source editions and citation conventions.
- [federer-erratum.tex](references/federer-erratum.tex): the working erratum transcription.
- [federer-errors.tex](references/federer-errors.tex): the error catalogue, convention qualifications, and published corrections, with their verification status.

- [validation.md](validation.md): release accounts and their recorded scope.
- [rendering.md](rendering.md): coqdoc and Markdown HTML instructions.
- [maintenance.md](maintenance.md): document structure, writing rules, and checks.

## Maintenance

Follow the [maintenance guide](maintenance.md) when changing coverage,
maps, source citations, or navigation. The guide includes the generators
and the command that checks local links, anchors, and declaration lines.

## HTML copies of Markdown

See [the Markdown rendering instructions](rendering.md#html-copies-of-markdown)
for file and batch conversion, offline mathematics, and output paths.
