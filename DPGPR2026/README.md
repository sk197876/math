# De Philippis, Gennaioli, Pigati and Rindler (2026)

This subproject formalises G. De Philippis, L. Gennaioli, A. Pigati
and F. Rindler, “Scale-invariant bounds on thin sets for measures
satisfying a first-order PDE and the anisotropic Michael–Simon
inequality”, preprint, 28 September 2026,
[arXiv:2609.34573](https://doi.org/10.48550/arXiv.2609.34573). It builds
on the Federer library of [federer/](../federer/README.md), on
Allard's paper ([allard1972/](../allard1972/README.md)) and on Appendix A
of De Philippis, De Rosa and Ghiraldin
([DPDRG2018/](../DPDRG2018/README.md)).

The folder [blueprint/](blueprint/) holds the LaTeX blueprint of the
formalisation of the anisotropic Michael–Simon inequality: Theorem 1.1
for rectifiable sets and Theorem 1.6. It matches every step to Federer,
to Allard 1972, to other cited work, or to a new lemma. Compile it in
that folder:

```sh
pdflatex dgpr_blueprint && bibtex dgpr_blueprint && pdflatex dgpr_blueprint && pdflatex dgpr_blueprint
```

The Rocq formalisation in [theories/](theories/) covers the blueprint
sections on notation and linear algebra, the heat flow, the heat estimates
(the hypotheses (S), the identities, regularity, the heat calculus and
DGPR Lemmas 3.1 and 3.2), the entropy bounds DGPR (4.1) and (4.2),
lem:inner, lem:tube, the compact case, Theorem 1.1 for rectifiable data
(thm:main, `dgpr_theorem_1_1_rectifiable` in
[theories/DgprMainTheorem.v](theories/DgprMainTheorem.v)) and the
varifold section, including the first variation δ_F V as a distribution
and Theorem 1.6, the anisotropic Michael–Simon inequality
(`dgpr_theorem_1_6` in [theories/DgprTheorem16.v](theories/DgprTheorem16.v)).
Both theorems hold with an explicit constant depending only on n, λ and
Λ. The files in [docs/](docs/) map each
blueprint item to its Rocq declarations, and
[docs/divergences.md](docs/divergences.md) records the divergences from
the paper and from the blueprint. Build with
`../tools/rocq_run.sh make -j1`; `../tools/rocq_run.sh make -j1 audit`
writes the axiom audit of [tests/Assumptions.v](tests/Assumptions.v) to
[docs/assumptions.log](docs/assumptions.log).
