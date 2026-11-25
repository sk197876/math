# Federer: Geometric Measure Theory in Rocq

This project formalises Herbert Federer's *Geometric Measure Theory*
(1969), following the book's definitions, hypotheses, conventions, and
proofs as closely as possible. The development covers Chapters 1 and 2
with documented qualifications, and Chapter 3, subject to the deferrals
and qualifications in the section guides. All numbered assertions of
3.4.1–3.4.12 are validated. They cover
critical values and sharpness, analytic germs, Noetherianity and unique
factorization, Weierstrass division and preparation, finite analytic
stratification, compact component finiteness, analytic dimension, and the
geometry of regular and singular parts, tangent-hull dimension, and finite
homogeneous polynomial majorants, including their complex analytic
extensions and the required covering and dimension corrections.
The original real auxiliary compact-union assertion of 3.4.8(5) also has a
validated supplement for arbitrary proper ideals.
Formalisation of Chapter 4 begins with §4.1.

## Sources and principles

[Federer1969](docs/bibliography.md#federer1969) is the primary source, read
with [Federer1987Erratum](docs/bibliography.md#federer1987erratum).
The working erratum is transcribed in
[docs/references/federer-erratum.tex](docs/references/federer-erratum.tex).
The [bibliography](docs/bibliography.md) identifies source editions and
supporting papers. The [source guide](docs/references/README.md) records
consulted passages and links the original erratum scan included in the repository.

The development aims to be self-contained, using general topology, set
theory, and scalar algebra as background. External dependencies stay narrow;
the book's mathematical arguments are developed within the project.
Objects are specified by abstract laws or universal properties.
Constructions prove existence, opaque sealed modules hide the witnesses,
and later proofs use the public laws. An axiomatic specification is a
predicate to be proved, not an unproved project axiom.

Every mathematical declaration carries a source comment with the Federer item,
printed page, and a quotation or mathematical paraphrase. All departures from
the printed statements or proof routes are registered in
[docs/divergences.md](docs/divergences.md).

## Coverage and verification

Chapter 1 covers §§1.2–1.10 with the qualifications in the section
guides; 1.1.1, 1.1.2, and 1.1.4 are complete, and 1.1.3 is intentionally
deferred. Chapter 2 reaches the requested last proof, 2.10.48, with its
documented qualifications. Items 2.8.8–2.8.9 exclude book examples;
2.10.46 remains partial and deferred. The complete 2.10.6 comparison and
ratio assembly is proved. The Ward construction cited in 2.10.27 is
intentionally omitted at the user’s request. Item 2.10.49 is a historical remark.

Chapter 3 covers 3.1 and 3.3 with documented qualifications. Section 3.2
retains the deferred second paragraph of 3.2.40. Item 3.2.45 is complete
with its documented source correction, including original exponent
continuity, sharp comparisons, full convex and all-set section inequalities,
and measurable-first-factor product equality. This checkout records all
numbered assertions of 3.4.1–3.4.12 as validated.
The [fresh full-project rebuild, kernel check, and full audit](docs/checkpoints/chapter3-full-validation.json)
after that release passed, preserving every earlier assumption set.
The compact-cover supplement closes the original real
auxiliary proof limit in 3.4.8(5) and has its own validation record.

Chapter 4 is in progress. Items 4.1.1–4.1.27 are complete and validated.
They cover test functions, distributions, differential forms, currents,
Cartesian products, homotopy, cones, joins, oriented simplexes, flat
seminorms and flat chains, smooth and Lipschitz images, flat-current
support laws, convex support hulls, mass approximation, summable form
contractions, smoothing, compact L1 representations, flat cochains,
integral-geometric null support, its null-set corollaries, integral and
real polyhedral chains with simultaneous flat and mass approximation,
rectifiable currents, integral currents and integral flat chains,
Lipschitz images of summable currents with their full-fibre area density,
the signed degree of a Lipschitz map on a bounded set, and the oriented
simplex as the image of the open unit cube.
The documented corrections in 4.1.1, 4.1.7, 4.1.8, 4.1.15, 4.1.17 and
4.1.19, the degree-zero qualification in 4.1.25 and the degenerate-case
univalence qualification in 4.1.27 remain explicit.
Items 4.1.28–4.1.34 remain pending. The
[4.1 guide](docs/chapter4/4.1.md) records coverage and the distinction
between the literal final test topology and its locally convex counterpart.

The [section guides](docs/toc.md) give the precise scope of each item.
The [coverage completion record](docs/checkpoints/coverage-completion.md)
records completion of the proof obligations authorised after the Chapter 3
release and preserves the user’s explicit omissions.
The [latest coverage supplement](docs/checkpoints/3.2.45-sections-supplement-validation.json) passes registered compilation, recursive kernel checking, and a dependency audit.

The [verification guide](docs/validation.md) preserves the detailed release
accounts, test scope, counts, durations, and remaining obligations. The complete
build record is [docs/verification.txt](docs/verification.txt); individual
reports are catalogued under [docs/checkpoints/](docs/checkpoints/README.md).
Only the three permitted MathComp boolp assumptions occur in the recorded
audits. Proof integrity requires ordinary compilation, recursive kernel
checking, and assumptions audits; known Rocq/Coq exploits and unchecked
bypasses are forbidden.

## Documentation and repository layout

Start at **[docs/toc.md](docs/toc.md)**. Each Federer subsection has its own
account in `docs/chapter1/`, `docs/chapter2/`, `docs/chapter3/` or `docs/chapter4/`, with entries for its numbered
items. The maps are:

- [contents.md](docs/contents.md): Federer item numbers to source modules and declarations.
- [index.md](docs/index.md): book index entries to formalised notions.
- [symbols.md](docs/symbols.md): printed notation to formal notation.
- [divergences.md](docs/divergences.md): corrections, conventions and proof departures.
- [bibliography.md](docs/bibliography.md): bibliographical identities of cited sources.

`theories/` contains the library under the `Federer` namespace. `tests/`
contains compiled example suites and the assumptions audit.
`_CoqProject` lists source files, namespaces and compiler flags. `tools/`
contains documentation generators and validation helpers. Generated coqdoc
pages are written to `html/` inside the build directory; build artifacts and
HTML are not tracked.

For HTML copies of the Markdown documentation, use
`python3 docs/md_to_html.py docs/contents.md`. This separate converter
requires Python 3 and Pandoc and renders mathematics as offline MathML.
File and batch usage are described in [the documentation index](docs/toc.md#html-copies-of-markdown).

The [maintenance guide](docs/maintenance.md) defines the shared document
structure, writing rules, and link checks. The [verification guide](docs/validation.md)
separates historical release evidence from current coverage.

## Build environment

Use opam switch **`RP.2026.02.0~9.1~2026.01`** explicitly. The recorded
platform uses Rocq 9.1.0, OCaml 4.14.2, MathComp 2.5.0, MathComp
classical/reals/analysis 1.16.0, finmap 2.2.2, Hierarchy Builder 1.10.2,
Rocq-Elpi 3.3.1 and algebra-tactics 1.2.7. Exact package versions are in
[docs/toolchain.txt](docs/toolchain.txt). GNU Make builds the library;
Python 3 runs the documentation and audit helpers. The source materials are
needed for source consultation, not for compiling the proofs.

Run these commands in the `federer/` folder with your configured opam root.
The [resource guard](docs/resources.md) supports shared build machines.

```sh
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make -j1
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make check
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make audit
```

| Target | Effect |
| --- | --- |
| `make` / `make all` | Generate the Rocq Makefile and compile registered theories and all registered example suites. |
| `make check` | Build as needed, then recursively kernel-check the public chapter interfaces and all registered example suites. |
| `make audit` | Build as needed, then freshly run every `Print Assumptions` query and rewrite `docs/assumptions.log`. |
| `make doc` | Build as needed and generate coqdoc HTML with the project index in `html/`. |
| `make clean` | Remove generated compilation artifacts and HTML. |
| `make prepare-build` | Link sources into the separate build directory and generate its Rocq Makefile, without compiling. |
| `ADOPT=1 make prepare-build` | Take over a build directory owned by another checkout: repoint its source links, keep the artifacts of unchanged sources and drop those of changed or removed modules. |
| `make migrate-build` | Relocate old in-source artifacts, verifying copies and preserving timestamps; retain obsolete outputs separately. |

All these targets run in a separate build directory. The default is
`_build/`. Override it with `BUILD_DIR=/absolute/path` or an ignored
`.build-dir` file. The build tree records which checkout owns its source
links. To build the companion subprojects with their committed load paths,
build Federer with `BUILD_DIR=/opt/rocq/federer-build`.

The build tree contains individual source symlinks, compiled files (`.vo`,
`.vos`, `.vok`, `.glob`, `.aux`), generated Makefiles and dependencies, and
`html/`. Sources and tracked verification records, including
`docs/assumptions.log`, stay in the repository. Migration preserves artifact
timestamps, so stale outputs are still rebuilt normally; relocation is not
a new validation. Old generated Makefiles and artifacts of removed modules
are retained under `previous-build/`, outside the active load paths.

For a focused compilation, use for example
`opam exec --switch=RP.2026.02.0~9.1~2026.01 -- make theories/TensorUP.vo`.
For direct compiler commands, first run `make prepare-build` under the same
switch, then run Rocq from the build directory with the usual relative
`-Q theories Federer -Q tests FedererTests` mappings. The dependency-audit
and coqdoc-index helpers use the same `.build-dir` or environment setting.

The Chapter 2 release rebuild preserves compatible unchanged Chapter 1
artifacts; it does not use an indiscriminate clean. Reused sources,
toolchain and dependency consistency must be checked, and the reuse scope
recorded with the verification results. The normal build also works from
source without another checkout.

For proof development, the project has used Rocq MCP, a local
Rocqet library index and MathComp guidance. The
[development account](docs/validation.md#proof-development-aids) explains
their use within the project's formalisation and validation rules.

## Documentation maintenance

Use the [maintenance guide](docs/maintenance.md) to update maps and check links.
Use the [rendering guide](docs/rendering.md) to generate HTML with mathematics.

## Public snapshot

This snapshot includes the validated sources through 4.1.27 and the
completed coverage supplements. [PUBLIC_SNAPSHOT.json](PUBLIC_SNAPSHOT.json)
records the source revision, validation evidence, and export checks.
