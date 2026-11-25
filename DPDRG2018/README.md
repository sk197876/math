# De Philippis, De Rosa and Ghiraldin (2018)

This subproject formalises material from G. De Philippis, A. De Rosa
and F. Ghiraldin, “Rectifiability of varifolds with locally bounded first
variation with respect to anisotropic surface energies”, *Comm. Pure
Appl. Math.* 71 (2018), no. 6, 1123–1148 (bibliography key
`DePhilippis2018`). It builds on the Federer library of
[federer1969/](../federer1969/README.md) and on
[allard1972/](../allard1972/README.md).

The subproject [DPGPR2026/](../DPGPR2026/README.md) needs Appendix A of
the paper, for integrands that do not depend on the point:

- the identification (A.1) of the Grassmannian G(n,d) with the
  orthogonal projections T satisfying T∘T = T, T* = T and trace T = d,
  and the tangent space of G(n,d) at T derived from (A.2);
- Lemma A.1: the derivative at t = 0 of the orthogonal projection onto
  (id + tL)[im T] equals T⊥∘L∘T + (T⊥∘L∘T)*;
- Lemma A.2: the anisotropic first variation formula, with the map B_F
  of (A.5).

The main results of the paper, the rectifiability theorems and the
condition (AC), are not needed.

The folder [blueprint/](blueprint/) holds the LaTeX blueprint of the
formalisation of the whole paper, including the x-dependent versions of
Appendix A and the external dependencies (Preiss 1987, Grafakos,
Gilbarg–Trudinger). Entries marked MS form the path needed by
DPGPR2026. Compile it in that folder:

```sh
pdflatex dpdrg_blueprint && bibtex dpdrg_blueprint && pdflatex dpdrg_blueprint && pdflatex dpdrg_blueprint
```

The Rocq formalisation in [theories/](theories/) covers Appendix A for
Ω = R^n on the path to the Michael–Simon inequality of DPGPR2026: the
tangent spaces of G(n,d) (A.4), Lemma A.1, the map B_F (sealed as for
Federer's book), A.6, A.7, Lemma A.2 (`ddg_lemma_A_2`,
`ddg_lemma_A_2_image`) and its form for integrands not depending on the
point (`ddg_lemma_A_2_constant`).
[docs/appendixA.md](docs/appendixA.md) maps each item to its Rocq
declarations, and [docs/divergences.md](docs/divergences.md) records the
divergences from the paper and from the blueprint. Build with
`../tools/rocq_run.sh make -j1`; `../tools/rocq_run.sh make -j1 audit`
writes the axiom audit of [tests/Assumptions.v](tests/Assumptions.v) to
[docs/assumptions.log](docs/assumptions.log).
