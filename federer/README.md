# Federer: Geometric Measure Theory in Rocq

This project formalises Herbert Federer's *Geometric Measure Theory*
(1969), following the book's definitions, hypotheses, conventions and
proofs as closely as possible. The development covers Chapters 1 and 2
with documented qualifications and is beginning Chapter 3, rectifiability.

## Sources and principles

[Federer1969](docs/bibliography.md#federer1969) is the primary source, read
with [Federer1987Erratum](docs/bibliography.md#federer1987erratum).
The working erratum is transcribed in
[docs/references/federer-erratum.tex](docs/references/federer-erratum.tex).
The [bibliography](docs/bibliography.md) identifies source editions and
supporting papers. The [source guide](docs/references/README.md) records
consulted passages and links the original erratum scan included in the repository.

The development aims to be self-contained, using general topology, set
theory and scalar algebra as background. External dependencies stay narrow;
the book's mathematical arguments are developed within the project.
Objects are specified by abstract laws or universal properties.
Constructions prove existence, opaque sealed modules hide the witnesses,
and later proofs use the public laws. An axiomatic specification is a
predicate to be proved, not an unproved project axiom.

Every mathematical declaration carries a source comment with the Federer item,
printed page and a quotation or mathematical paraphrase. All departures from
the printed statements or proof routes are registered in
[docs/divergences.md](docs/divergences.md).

## Coverage and verification

Chapter 1 covers §§1.2–1.10 with the qualifications in the section accounts;
§1.1 remains partial and 1.1.3 is intentionally left aside. Chapter 2
reaches the requested last proof, **2.10.48**. Sections 2.1–2.7 and 2.9
are covered as documented. Remaining qualifications include examples and the strict-convexity parenthesis in
2.8.8–2.8.9, 2.10.6, the real-degree Gamma normalisation, the printed
circle computation and listed variants. **2.10.46 remains partial and
deferred at the user's request.** Item 2.10.49 is a historical remark
requiring no formalisation. Chapter 2 is therefore not claimed to contain
a proof of every printed mathematical assertion.

The final compact-subset and Suslin inner-approximation results cover the
exact natural-degree Hausdorff normalisation and arbitrary nonnegative
real power gauges with explicit positive coefficients. Detailed statements,
coverage limits and proof accounts belong in the
[section documentation](docs/toc.md).

The **27 October 2026 release passed** the complete Chapter 2 rebuild,
full recursive kernel check and fresh audit of all 15,349 assumption queries.
The rebuild reused compatible unchanged Chapter 1 artifacts from Claude.

The [scheduled full-project validation](docs/checkpoints/2026-10-28-full-validation.json)
completed on **29 October 2026**. It passed a fresh clean rebuild of the
whole registered project, recursive kernel checking and all 15,729
assumptions queries, without warnings or changed assumption sets. Its
snapshot included the partial 3.1.4 checkpoint; later proofs receive
separate focused checks.

[docs/verification.txt](docs/verification.txt) records the actual scope and
outcome of every validation checkpoint. The full dependency report is
[docs/assumptions.log](docs/assumptions.log). Only the three permitted
MathComp classical assumptions may occur: propositional extensionality,
dependent functional extensionality and constructive indefinite description.
There are no admitted proofs, new project axioms or unchecked cast bypasses.
A successful build verifies the implemented statements, not pending passages.

Chapter 3 has completed [3.1.1–3.1.24](docs/chapter3/3.1.md), with the
conventions and qualifications documented there. The completed items passed
focused compilation, regression checks, recursive kernel checking and
assumptions audits. The commentary in 3.1.10 is recorded. The
[3.1 release](docs/checkpoints/3.1-release-validation.json) also passed the
incremental project build, complete recursive kernel check and dependency
assumptions audit. [Subsection 3.2](docs/chapter3/3.2.md) is in progress: items 3.2.1–3.2.39 are complete and validated, with explicit source qualifications and corrections in the section account. Item 3.2.40 remains outside this validated source snapshot; its Kneser example is deferred. Items 3.2.41–3.2.49 remain pending. Subsections 3.3–3.4 remain pending.
Chapter 4 has not begun. Before Chapter 4, the planned
prerequisite is a formalisation of
[EilenbergSteenrod1952](docs/bibliography.md#eilenbergsteenrod1952).

## Documentation and repository layout

Start at **[docs/toc.md](docs/toc.md)**. Each Federer subsection has its own
account in `docs/chapter1/`, `docs/chapter2/` or `docs/chapter3/`, with entries for its numbered
items. The maps are:

- [contents.md](docs/contents.md): Federer item numbers to source modules and declarations.
- [index.md](docs/index.md): book index entries to formalised notions.
- [symbols.md](docs/symbols.md): printed notation to formal notation.
- [divergences.md](docs/divergences.md): corrections, conventions and proof departures.
- [bibliography.md](docs/bibliography.md): bibliographical identities of cited sources.

`theories/` contains the library under the `Federer` namespace. `tests/`
contains ten compiled example suites and the assumptions audit.
`_CoqProject` lists source files, namespaces and compiler flags. `tools/`
contains documentation generators and validation helpers. Generated coqdoc
pages are written to `html/` inside the build directory; build artifacts and
HTML are not tracked.

## Build environment

Use opam switch **`RP.2026.02.0~9.1~2026.01`** explicitly. The recorded
platform uses Rocq 9.1.0, OCaml 4.14.2, MathComp 2.5.0, MathComp
classical/reals/analysis 1.16.0, finmap 2.2.2, Hierarchy Builder 1.10.2,
Rocq-Elpi 3.3.1 and algebra-tactics 1.2.7. Exact package versions are in
[docs/toolchain.txt](docs/toolchain.txt). GNU Make builds the library;
Python 3 runs the documentation and audit helpers. The source materials are
needed for source consultation, not for compiling the proofs.

Run from the repository root, normally with at most two proof workers.
Use your own configured opam root.

```sh
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make -j2
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make check
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make audit
```

| Target | Effect |
| --- | --- |
| `make` / `make all` | Generate the Rocq Makefile and compile registered theories and all ten example suites. |
| `make check` | Build as needed, then recursively kernel-check the public Chapter 1, 2 and developing Chapter 3 interfaces and all ten example suites. |
| `make audit` | Build as needed, then freshly run every `Print Assumptions` query and rewrite `docs/assumptions.log`. |
| `make doc` | Build as needed and generate coqdoc HTML with the project index in `html/`. |
| `make clean` | Remove generated compilation artifacts and HTML. |
| `make prepare-build` | Link sources into the separate build directory and generate its Rocq Makefile, without compiling. |
| `ADOPT=1 make prepare-build` | Take over a build directory owned by another checkout: repoint its source links, keep the artifacts of unchanged sources and drop those of changed or removed modules. |
| `make migrate-build` | Relocate old in-source artifacts, verifying copies and preserving timestamps; retain obsolete outputs separately. |

All these targets run in a separate build directory. The two working
checkouts on this host share `/opt/rocq/federer-build`, selected by the
ignored local file `.build-dir`, and use it in turn. The checkout whose
links the tree holds is recorded in its ownership marker; another checkout
takes it over with `ADOPT=1 make prepare-build` before building, so stored
artifacts of unchanged sources are reused and only changed modules are
recompiled. On this host build directories use group `llm` and setgid
inheritance. Make recipes use `BUILD_UMASK=0002` by default so new outputs
remain readable and writable by the group; use `umask 0002` for direct Rocq
and audit commands as well. Other clones default to `_build/`; override with
`BUILD_DIR=/absolute/path` as an environment variable or a make argument.

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

After changing mathematical coverage, update the section account and maps,
then run:

```sh
python3 tools/contents.py
python3 tools/linkify_docs.py
python3 tools/divergence_counts.py
```

`tools/dependency_audit.py BASE` supports audits of changed dependencies at
ordinary section releases. It does not replace the fresh full audit
requested for this Chapter 2 release.
