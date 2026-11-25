# Rocq formalisations in geometric measure theory

This repository holds Rocq formalisations of works in geometric measure
theory. Each work has its own subproject folder.

| Folder | Source | State |
| --- | --- | --- |
| [federer1969/](federer1969/README.md) | H. Federer, *Geometric Measure Theory*, Springer, 1969 | Chapters 1–3 and §4.1.1–4.1.27 released |
| [allard1972/](allard1972/README.md) | W. K. Allard, “On the first variation of a varifold”, *Ann. of Math. (2)* 95 (1972), 417–491 | blueprint written; Rocq: 2.2–2.4(1), 3.1, 3.2(1), 3.5 and 3.5(1)(b) |
| [DPDRG2018/](DPDRG2018/README.md) | G. De Philippis, A. De Rosa and F. Ghiraldin, “Rectifiability of varifolds with locally bounded first variation with respect to anisotropic surface energies”, *Comm. Pure Appl. Math.* 71 (2018), 1123–1148 | blueprint written; Rocq: Appendix A (Lemmas A.1, A.2) |
| [DPGPR2026/](DPGPR2026/README.md) | G. De Philippis, L. Gennaioli, A. Pigati and F. Rindler, “Scale-invariant bounds on thin sets for measures satisfying a first-order PDE and the anisotropic Michael–Simon inequality”, arXiv:2609.34573 (2026) | blueprint written; Rocq: Theorem 1.1 for rectifiable sets and Theorem 1.6 (anisotropic Michael–Simon inequality) |

The Federer library (logical name `Federer`) is the common foundation;
the later subprojects build on it. Each subproject keeps its own sources,
documentation and tools, and its own instructions in its folder.

The [public snapshot record](federer1969/PUBLIC_SNAPSHOT.json) gives the source
revision, validation records, and export checks.
