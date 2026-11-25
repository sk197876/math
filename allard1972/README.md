# Allard, On the first variation of a varifold

This subproject formalises W. K. Allard, “On the first variation of a
varifold”, *Ann. of Math. (2)* 95 (1972), 417–491,
[doi:10.2307/1970868](https://doi.org/10.2307/1970868)
(bibliography key `Allard1972`). It builds on the Federer library of
[federer1969/](../federer1969/README.md).

The folder [blueprint/](blueprint/) holds the LaTeX blueprint of the
formalisation of the whole paper, sections 2–8. It gives every numbered
item a statement and a proof that cites Federer's book, an earlier item, other
published work, or a new lemma. It records the corrections to Allard's
text and the Federer items beyond the formalised range. Entries marked MS form
the shortest path to the anisotropic Michael–Simon inequality of
[DPGPR2026/](../DPGPR2026/README.md); the remark on that path at the end
of the blueprint lists them. Compile it in that folder:

```sh
pdflatex allard_blueprint && bibtex allard_blueprint && pdflatex allard_blueprint && pdflatex allard_blueprint
```

The Rocq formalisation covers section 2 up to 2.4(1), with the blueprint
lemmas new:grass_compact and new:projection_formula, and, for M = U = R^n,
items 3.1, 3.2(1), 3.5 with blueprint al:3.5:lem, part (b) of 3.5(1) and
the density and tangent plane assertions of the “only if” half of its part
(a), and the blueprint lemmas
new:simple_to_projection and new:density_tangent. The sources are in
[theories/](theories/); [docs/section2.md](docs/section2.md) and
[docs/section3.md](docs/section3.md) map each item to its Rocq declarations,
and [docs/divergences.md](docs/divergences.md) records
the divergences from Allard's text and from the blueprint. Build with
`../tools/rocq_run.sh make -j1`; `../tools/rocq_run.sh make -j1 audit` writes
the axiom audit of [tests/Assumptions.v](tests/Assumptions.v) to
[docs/assumptions.log](docs/assumptions.log).
