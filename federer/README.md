# Federer: Geometric Measure Theory in Rocq

This project formalises Herbert Federer's *Geometric Measure Theory*
(1969), following the book's definitions, hypotheses, conventions, and
proofs as closely as possible. The development covers Chapters 1 and 2
with documented qualifications, and Chapter 3 through subsection 3.3,
subject to the explicit deferrals in 3.2. Subsection 3.4 is in progress:
3.4.1–3.4.6 are validated, including critical values, sharpness, analytic
germs, conditional local algebra and Weierstrass division and preparation.

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
2.10.46 remains partial and deferred. Item 2.10.49 is a historical remark.

Chapter 3 covers 3.1 and 3.3 with documented qualifications. Section 3.2
retains the deferred second paragraph of 3.2.40 and partial 3.2.45. This
checkout records 3.4.1–3.4.6 as validated and later 3.4 items as pending.

The [section guides](docs/toc.md) give the precise scope of each item.
The [verification guide](docs/validation.md) preserves the detailed release
accounts, test scope, counts, dates, and remaining obligations. The complete
build record is [docs/verification.txt](docs/verification.txt); individual
reports are catalogued under [docs/checkpoints/](docs/checkpoints/README.md).
Only the three permitted MathComp boolp assumptions occur in the recorded
audits. Proof integrity requires ordinary compilation, recursive kernel
checking, and assumptions audits; known Rocq/Coq exploits and unchecked
bypasses are forbidden.

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
separates dated release evidence from current coverage.

## Build environment

Use opam switch **`RP.2026.02.0~9.1~2026.01`** explicitly. The recorded
platform uses Rocq 9.1.0, OCaml 4.14.2, MathComp 2.5.0, MathComp
classical/reals/analysis 1.16.0, finmap 2.2.2, Hierarchy Builder 1.10.2,
Rocq-Elpi 3.3.1 and algebra-tactics 1.2.7. Exact package versions are in
[docs/toolchain.txt](docs/toolchain.txt). GNU Make builds the library;
Python 3 runs the documentation and audit helpers. The source materials are
needed for source consultation, not for compiling the proofs.

Run from the repository root. On this shared host, the daytime resource policy
permits up to eight compiler workers with memory-aware admission and a 1.5 GiB
RAM reserve. Between 17:00 and 07:00 Europe/Warsaw, use as many resources as
are useful. Keep registered inputs stable during validation, run the
validation stages sequentially, and avoid overlapping top-level makes.
The manual example below uses two workers.
Use your configured opam root.

```sh
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make -j2
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make check
opam exec --switch=RP.2026.02.0~9.1~2026.01 -- nice -n 10 make audit
```

| Target | Effect |
| --- | --- |
| `make` / `make all` | Generate the Rocq Makefile and compile registered theories and all registered example suites. |
| `make check` | Build as needed, then recursively kernel-check the public Chapter 1, 2 and developing Chapter 3 interfaces and all registered example suites. |
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

## Documentation maintenance

Use the [maintenance guide](docs/maintenance.md) to update maps and check links.
Use the [rendering guide](docs/rendering.md) to generate HTML with mathematics.

## Public snapshot

This snapshot exports the verified source files and current documentation
from revision `b07c257e` of the working formalisation.
The latest mathematical release is 3.4.6; later 3.4 items retain their
pending status. [PUBLIC_SNAPSHOT.json](PUBLIC_SNAPSHOT.json) records the
source revision, validation evidence, exclusions, and export checks.
Agent instructions, memories, restart handoffs, unfinished draft recovery,
local settings, and generated build artifacts are excluded.
