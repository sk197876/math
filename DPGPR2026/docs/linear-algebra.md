# Section 2 of the blueprint: notation and auxiliary linear algebra

This account maps the items of section 2 of
[the blueprint](../blueprint/dgpr_blueprint.tex) to the Rocq declarations
of the subproject. The blueprint works in $\mathbf R^n$ with a fixed
orthonormal basis. The formalisation works in an arbitrary vector space
$V$ over a real field $R$ with an inner product $B$ (Federer's
`is_inner_product`) and a finite basis `e : 'I_n -> V` (`is_basis e`);
the target $W$ of a linear map carries an inner product $C$. Linear maps
are elements of Federer's `Hom V W`. Every choice (a supremum, a map
defined through an eigenbasis) is made in the four layers of
[CONVENTIONS.md](../../CONVENTIONS.md): characteristic property,
construction, sealed module, public interface. Later files use only the
property and the interface.

## mr:notation

| Blueprint | Declarations |
| --- | --- |
| $A \bullet B = \operatorname{trace}(A^* \circ B)$ and $\lvert A\rvert$ on $\operatorname{Hom}(V,W)$ | Federer's `hom_inner`, `hom_norm`, `hom_inner_trace` (1.7.9), used directly |
| $\lvert A\rvert^2 = \sum_j \lvert A(u_j)\rvert^2$ for an orthonormal basis $u$ | [`dgpr_hom_norm_sqr`](../theories/DgprHomNorms.v) |
| $\lVert A\rVert$, $\lVert A\rVert \le \lvert A\rvert \le (\dim V)^{1/2}\lVert A\rVert$, $\lVert A^*\rVert = \lVert A\rVert$ | Federer's `linear_operator_norm`, `hom_operator_norm_comparison`, `linear_operator_adjoint_norm_equal` (1.7.6, 1.7.9) |
| $\lvert A^*\rvert = \lvert A\rvert$ | [`dgpr_hom_norm_adjoint`](../theories/DgprHomNorms.v) |
| $\lvert L \circ A\rvert \le \lVert L\rVert\,\lvert A\rvert$ | [`dgpr_hom_norm_comp_left`](../theories/DgprHomNorms.v) |
| $\lvert A \circ L\rvert \le \lvert A\rvert\,\lVert L\rVert$ | [`dgpr_hom_norm_comp_right`](../theories/DgprHomNorms.v) |
| $\omega \cdot b$ and $(\omega \cdot b) \bullet A = \omega(A^*(b))$ | [`dgpr_rank_one`](../theories/DgprHomNorms.v) (Federer's `hom_with_coefficient`, 1.4.4), `dgpr_rank_oneE`, `dgpr_rank_one_inner` |
| orthonormal expansions, Parseval's identity, quadratic forms in an eigenbasis | [DgprOrthonormalCoordinates.v](../theories/DgprOrthonormalCoordinates.v) |

The rank one map is Federer's declaration under a second name, so that it
can later be identified with Allard's notation 2.3(4).

## def:sv, lem:sv and rem:sv_singular

| Blueprint | Declarations |
| --- | --- |
| characteristic property of $\operatorname{sv}_m(X)$ | [`dgpr_sv_lower_bound`, `is_dgpr_sv`](../theories/DgprSingularValueUP.v) |
| existence | [`dgpr_sv_exists`](../theories/DgprSingularValueConstruction.v) (private) |
| sealed choice | [`DgprSingularValue`](../theories/DgprSingularValueSealed.v) |
| $\operatorname{sv}_m(X)$ | [`dgpr_sv`, `dgpr_svP`, `dgpr_sv_characterisation`, `dgpr_sv_lower`, `dgpr_sv_approximate`](../theories/DgprSingularValue.v) |
| lem:sv(hom) | `dgpr_sv_hom` |
| lem:sv(lip) | `dgpr_sv_lip` |
| lem:sv(rank) | [`dgpr_sv_rank`](../theories/DgprSingularValueRank.v) |
| lem:sv(eigen) | `dgpr_sv_eigen` |
| rem:sv_singular | `dgpr_sv_singular` |

The characteristic property states that $\operatorname{sv}_m(X)$ is the
least upper bound of the numbers $t$ for which some $P \in G(V,m)$
satisfies $t \le \lvert X(v)\rvert$ for all unit vectors $v \in P$. This
equals the supremum over $P$ of the infima of the blueprint and avoids a
nested choice. The Grassmannian is Federer's `G V m`. The definition
requires $1 \le m \le n$, as in mr:notation. The value does not depend
on the basis `e` (`dgpr_sv_basis_independent`).

## def:spectral and lem:spectral

| Blueprint | Declarations |
| --- | --- |
| characteristic property: $\hat\chi(A)(v) = \chi(a)\,v$ whenever $A(v) = a\,v$ | [`is_dgpr_spectral_value`](../theories/DgprSpectralCalculusUP.v) |
| formula in every orthonormal eigenbasis, uniqueness | `dgpr_spectral_value_expansion`, `dgpr_spectral_value_unique` |
| existence from an eigenbasis (Federer 1.7.3) | [`dgpr_spectral_value_exists`](../theories/DgprSpectralCalculusConstruction.v) (private) |
| sealed choice | [`DgprSpectralCalculus`](../theories/DgprSpectralCalculusSealed.v) |
| $\hat\chi(A)$ | [`dgpr_spectral`, `dgpr_spectralP`, `dgpr_spectral_characterisation`, `dgpr_spectral_expansion`](../theories/DgprSpectralCalculus.v) |
| lem:spectral, symmetry | `dgpr_spectral_symmetric` |
| lem:spectral, eigenvalues | `dgpr_spectral_eigenvalue` |
| lem:spectral, $\lvert\hat\chi(A) - \hat\chi(A')\rvert \le L\,\lvert A - A'\rvert$ for a Lipschitz bound $L$ of $\chi$ | `dgpr_spectral_lipschitz` |
| the same with $L = \operatorname{Lip}(\chi)$ of Federer 2.2.7 | `dgpr_spectral_lipschitz_constant` |

The proof of the Lipschitz estimate computes in two orthonormal
eigenbases $u$ of $A$ and $u'$ of $A'$:
$\lvert\hat\chi(A) - \hat\chi(A')\rvert^2 = \sum_{i,j} (\chi(a_i) - \chi(a'_j))^2 (u_i \bullet u'_j)^2$
(`dgpr_spectral_difference_sqr`). This is the blueprint's computation
with the projections $\pi_i$ and $\pi'_j$, since
$\lvert\pi_i \circ \pi'_j\rvert^2 = (u_i \bullet u'_j)^2$.

## lem:trace, lem:hull and lem:barycentre

| Blueprint | Declarations |
| --- | --- |
| lem:trace | [`dgpr_trace_comparison`](../theories/DgprTraceComparison.v), with `dgpr_trace_eigen` |
| lem:hull | [`dgpr_hull_compact`](../theories/DgprConvexHull.v), from Federer's `finite_norm_compact_convex_hull` (2.10.21) and `convex_hull_empty` |
| lem:barycentre, membership | [`dgpr_barycentre`](../theories/DgprBarycentre.v), from Federer's `closed_convex_integral_mean` (2.4.19) |
| lem:barycentre, existence of the integral | `dgpr_barycentre_integrable` (2.4.12), `dgpr_barycentre_exists` |

A finite dimensional normed space is a vector space $V$ with a norm $N$
(`is_real_norm N`) and a finite basis; its metric space is Federer's
`real_norm_metric_space hN`. The measure $\nu$ of lem:barycentre is a
Federer measure over a `choiceType` with `mu setT = m%:E` and `0 < m`.

## mr:functionals

| Blueprint | Declarations |
| --- | --- |
| variation measure $\lVert\Theta\rVert$ and normalised density $\overrightarrow{\Theta}$ of a distribution representable by integration (Federer 4.1.5) | [`dgpr_functional_representation`](../theories/DgprFunctionals.v), from Federer's `finite_distribution_radon_representation` |
| first consequence: $\lVert\Theta\rVert(A) \le \nu(A)$ | `dgpr_variation_dominated`, `dgpr_variation_dominated_integral` |
| second consequence, gauge: $\lVert\Theta\rVert(f) = 0$ | `dgpr_variation_vanishes` |
| second consequence, measure: $\lVert\Theta\rVert(\mathbf R^n \setminus C) = 0$ | `dgpr_variation_null_outside`, `dgpr_functional_null_outside` |

The representation theorem is Federer's, with completeness and
separability of the target derived from a finite basis. The two
consequences are proved for an arbitrary locally compact space $X$, a
Radon measure $\rho$ representing the gauge of $S$ on $\mathscr K(X)^+$
(as the record `is_normalised_distribution_representation` provides), and
a Radon measure $\nu$ over the same $X$. The comparison of open sets uses
`radon_positive_compact_open_content` (Federer 2.5.14) for both measures;
arbitrary sets follow from outer regularity (`radon_outer_formula`,
2.2.5). The condition "$\operatorname{spt} g \cap C = \varnothing$" is
expressed as "$g$ vanishes on an open set containing $C$", which is
equivalent.
