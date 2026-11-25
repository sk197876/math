# Conventions for the subprojects allard1972, DPDRG2018 and DPGPR2026

These rules govern the Rocq formalisations built on top of the Federer
library (`federer1969/`, logical name `Federer`). They cover the material needed
for the anisotropic Michael–Simon inequality of De Philippis, Gennaioli, Pigati and Rindler
(DPGPR 2026, Theorem 1.6), formalised close to the original papers and
with the encapsulation used for Federer's book.

## Layout and logical names

| Folder | Logical name | Tests | Build tree |
| --- | --- | --- | --- |
| `allard1972/` | `Allard` | `AllardTests` | `/opt/rocq/allard1972-build` |
| `DPDRG2018/` | `DPDRG` | `DPDRGTests` | `/opt/rocq/DPDRG2018-build` |
| `DPGPR2026/` | `DPGPR` | `DPGPRTests` | `/opt/rocq/DPGPR2026-build` |

Each folder has `theories/`, `tests/` (with `tests/Assumptions.v`),
`docs/`, `_CoqProject` and `Makefile`. `_CoqProject` maps the Federer
build tree (`-Q /opt/rocq/federer-build/theories Federer`) and the build
trees of the subprojects below it: DPDRG reads Allard; DPGPR reads Allard
and DPDRG. Never import a module of a higher subproject from a lower one.

Add a new file by appending one line to `_CoqProject`
(`echo theories/Name.v >> _CoqProject`); never rewrite the file, since
several workers may append concurrently. The order of lines is irrelevant;
`rocq makefile` computes dependencies.

## Building

Run every Rocq command through `tools/rocq_run.sh` (from the repository
root, or with a relative path from a subproject). It selects the pinned
opam switch, group `llm`, umask 0002 and nice 10, and on weekdays
07:00–17:00 Europe/Warsaw it admits at most two commands at once. Use `-j1`
in that window. Nights (17:00–07:00) and weekends are unrestricted; use at
most `-j2` per worker even then, because several workers share 8 threads
and 15 GiB of RAM.

```sh
cd DPGPR2026
../tools/rocq_run.sh make theories/Name.vo      # focused build
../tools/rocq_run.sh make -j2                   # whole subproject
```

`make` links the sources into the build tree and compiles there; never
compile beside the sources. Build the lower subprojects first when a file
of theirs changed (`cd ../allard1972 && ../tools/rocq_run.sh make`).

For experiments, write scratch files under
`/opt/rocq/<folder>-build/scratch/<your-name>/` and compile them there:

```sh
cd /opt/rocq/DPGPR2026-build && "/path/to/math/tools/rocq_run.sh" \
  rocq compile -Q /opt/rocq/federer-build/theories Federer \
  -Q /opt/rocq/allard1972-build/theories Allard -Q theories DPGPR \
  -w -notation-overridden,-ambiguous-paths,-redundant-canonical-projection,-notation-incompatible-prefix \
  scratch/<your-name>/Probe.v
```

`Check`, `About`, `Print`, `Search` and `Fail` in a scratch file are the
probing tools; a goal can be printed with
`match goal with |- ?G => idtac G end.` Companion builds read the existing
Federer artifacts. Build Federer separately using its [build guide](federer1969/README.md#build-environment).

## Use of the Federer library

- Read `federer1969/docs/symbols.md` (notation → declarations),
  `federer1969/docs/contents.md` (numbered item → files and names) and
  the section accounts `federer1969/docs/chapterN/*.md`, which state the
  qualifications of each formalised item. `docs/divergences.md` records
  corrections of the printed book.
- Use only public interfaces. Never import a module whose name ends in
  `Construction` or `Witness`, or any module that the Federer
  documentation calls private; use the corresponding `Sealed`/interface
  module and the predicate laws.
- Search before proving: `grep -rn` in `federer1969/theories`, or
  `/opt/rocq/federer-build/tooling/rocqet/search --limit 8 "query"`.
- Federer's measure theory, integrals, Lebesgue and Hausdorff measures,
  exponential, logarithm, π and derivatives are its own (MathComp
  analysis is not used for measures or integrals). Work with them.
- Euclidean space is `inner_metric_space (@euclidean_inner_productP R n)`
  over `R : realType`, as in `federer1969/theories/ClosedRectifiableMinkowski.v`;
  linear maps are `Hom X Y` (`Federer.Hom`), the adjoint is `inner_adjoint`,
  the trace of an endomorphism `trace_Hom`. Confirm the details in the
  library before use.

## Encapsulation (as for Federer's book)

Every object whose definition involves a choice (a supremum, an integral
value chosen by description, a basis, an inverse, a limit, a measure
obtained from a representation theorem) is introduced in four layers:

1. `NameUP.v`: a predicate expressing the defining (universal or
   characteristic) property, and the consequences derived from it alone;
2. `NameConstruction.v`: a proof that an object with the property exists;
3. `NameSealed.v`: a `Module Type` signature exposing only the object and
   its laws, and an opaque module `Module Name : NameSignature` choosing
   the witness (see `federer1969/theories/NormOperatorNorm*.v`);
4. `Name.v`: the public interface used by every later file.

Later files import only the interface (and the predicate file), never the
construction. Objects given by an explicit formula in already public
operations (for example the heat kernel p_s(z) = (4πs)^{-n/2} exp(−|z|²/(4s)))
may be ordinary definitions.

## Fidelity to the papers

- Follow the blueprints: `allard1972/blueprint/allard_blueprint.tex`,
  `DPDRG2018/blueprint/dpdrg_blueprint.tex`,
  `DPGPR2026/blueprint/dgpr_blueprint.tex`. Formalise the items on the
  Michael–Simon path (marked MS in the Allard and DPDRG blueprints; all of
  the DPGPR blueprint) with the papers' hypotheses and conclusions. Do not
  weaken a statement or add a hypothesis without recording it in the
  subproject's `docs/divergences.md`, with the reason.
- Name principal results after the source numbering:
  `allard_2_4_1` for Allard 2.4(1), `allard_3_5_1_b` for 3.5(1)(b),
  `ddg_lemma_A_1`, `ddg_lemma_A_2`, `dgpr_lemma_3_1`,
  `dgpr_theorem_1_1_rectifiable`, `dgpr_theorem_1_6`. Name the lemmas of
  the blueprint that are new (marked “new”) descriptively and give the
  blueprint label in the comment.
- Every file starts with a comment naming the source and item; every
  definition and lemma has a comment `Source for [name]: ...` giving the
  paper, item and page (or the blueprint label for new lemmas), in the
  style of the Federer library. Follow the global mathematical-writing
  guide in comments and documentation (British English, Federer's
  notation).

## Soundness

- No `Admitted`, `admit`, `Axiom`, `Abort`, `Show` (in committed files),
  cast bypass, or exploit of Rocq. Unfinished work stays outside
  `_CoqProject` or in scratch files.
- Add each principal theorem to the subproject's `tests/Assumptions.v`
  (`Print Assumptions name.`). Allowed axioms are only
  `boolp.propositional_extensionality`,
  `boolp.functional_extensionality_dep` and
  `boolp.constructive_indefinite_description`, as in Federer.
