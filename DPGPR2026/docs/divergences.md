# Divergences from the blueprint

Each entry records a statement of the formalisation that differs from the
blueprint (a hypothesis added or dropped, a different formulation), with
the reason. Workers append entries for their items.

## Section 2: notation and auxiliary linear algebra

- **Setting.** The blueprint works in $\mathbf R^n$ with a fixed
  orthonormal basis and in a finite dimensional inner product space $Y$.
  The formalisation works in an arbitrary vector space $V$ with an inner
  product and a finite basis, and in an arbitrary target $W$ with an inner
  product. This is a generalisation; for $\mathbf R^n$ it gives the
  blueprint's statements.
- **def:sv.** The supremum of infima is formalised as the least upper
  bound of the numbers $t$ such that $t \le \lvert X(v)\rvert$ for all
  unit vectors $v$ of some $P \in G(V,m)$. The two numbers coincide. The
  definition carries the hypothesis $1 \le m \le n$ of mr:notation.
- **lem:sv(rank).** The condition $\dim \operatorname{im} X \ge m$ is
  expressed by Federer's `linear_rank_at_least X m` (3.1.18): some $m$
  vectors have linearly independent images.
- **lem:sv(eigen), rem:sv_singular.** The orthonormal basis $u$ may be
  indexed by any finite ordinal; being a basis forces its size to be
  $\dim V$. The eigenvalue condition is stated with Federer's
  `inner_adjoint`.
- **def:spectral, lem:spectral.** $\hat\chi(A)$ is defined for every map
  $\chi : \mathbf R \to \mathbf R$, not only for Lipschitzian maps; the
  definition needs no regularity. The Lipschitz estimate is proved for
  every $L$ with $\lvert\chi(x) - \chi(y)\rvert \le L\,\lvert x - y\rvert$
  (`dgpr_spectral_lipschitz`) and, as stated in the blueprint, with
  $L = \operatorname{Lip}(\chi)$ of Federer 2.2.7 for the real line
  (`dgpr_spectral_lipschitz_constant`). The proof computes in two
  orthonormal eigenbases rather than with the projections $\pi_i$,
  $\pi'_j$; the two computations agree term by term.
- **lem:trace.** The bilinear form $g$ need not be symmetric; only
  $g(v,v) \ge 0$ is assumed. This is a generalisation. The basis
  $\varepsilon$ is any orthonormal basis of $V$.
- **lem:barycentre.** The membership statement `dgpr_barycentre` takes
  the integral $y$ as an argument with the specification
  `is_measure_vector_integral` of Federer 2.4.12, and needs no
  measurability hypothesis. The existence of the integral for a $\nu$
  measurable $f$ is `dgpr_barycentre_exists`. The total mass is
  $m$ with $\nu(\Omega) = m$ and $0 < m$.
- **mr:functionals.** The representation is Federer's 4.1.5 for a
  distribution on an open subset $U$ of $\mathbf R^n$ with values in a
  normed space with a finite basis; the continuous dual of the target and
  its weak topology are parameters, as in Federer's library. The two
  consequences are proved for a Radon measure $\rho$ that represents the
  gauge on $\mathscr K(X)^+$ over a locally compact space $X$, and the
  measure $\nu$ of the first consequence is a Radon measure over the same
  space $X$; for a distribution on $U$ this is the domain $U$ with its
  subspace topology. The first consequence assumes
  $S(\phi) \le \int^* \lvert\phi\rvert \, d\nu$ with Federer's upper
  integral (2.4.2), which is the integral whenever $\lvert\phi\rvert$ is
  $\nu$ summable; the blueprint's two-sided bound implies it. The
  condition "$\operatorname{spt} g \cap C = \varnothing$" is expressed as
  "$g$ vanishes on an open set containing $C$", which is equivalent.
  The specialisation of the general results to the variation measure of
  `dgpr_functional_representation` is made for the second consequence
  (`dgpr_functional_null_outside`). The first consequence is specialised
  to $U = \mathbf R^n$ in `DgprFunctionalsEuclidean.v`
  (`dgpr_dominated_variation`; see the entry below); a proper open
  $U \subset \mathbf R^n$ is not treated, since the deduction uses only
  $U = \mathbf R^n$.

## Section 3: heat kernel and heat extensions

- **Differentiation under the integral sign.** The hypotheses are stated
  pointwise: every integrand f(x, ·) for x near a has a Federer integral
  (2.4.12), every f(·, y) has a differential near a, and
  ‖Df(x, y)(v)‖ ≤ g(y)‖v‖ for a ν summable g and all y (not only ν almost
  all y). The class ∞ statement `dgpr_parameter_integral_smooth` asks for a
  family of integrands closed under partial differentiation with locally
  uniform majorants.
- **def:heat.** The factor (4πs)^{-n/2} is written
  `Num.sqrt (4 * dgpr_pi R * s) ^- n`, which is the same number for
  0 < s. The Borel hypothesis on ν is stated as "every open set is ν
  measurable"; the support hypothesis as
  `measure_almost_everywhere nu [set y | N y <= r]`, that is,
  ν(R^n ∖ B(0, r)) = 0; finiteness as ν(R^n) = m. The finite dimensional
  space Z is replaced by a complete separable normed space (every finite
  dimensional normed space is such, `finite_norm_metric_complete`,
  `finite_norm_metric_separable`), and "f bounded" by ‖f(y)‖ ≤ M for all y.
  The heat extension `dgpr_heat_extension` is defined as the vector
  integral when [y ↦ p_s(x − y) f(y)] is ν summable and 0 otherwise;
  `dgpr_heat_extension_integral` shows the first case always occurs.
- **lem:kernel(1),(2).** Proved through the multivariate Gamma integral of
  Federer 3.2.13 and the dilation law of L^n, not through one-dimensional
  integrals and Fubini's theorem; the statements are unchanged.
- **lem:kernel(3).** Δp_s(z) is the sum over the standard basis of
  D²p_s(z)(e_i, e_i), and ∂_s p_s(z) is the curve derivative of
  [t ↦ p_t(z)] at s (`has_normed_curve_derivative`).
- **lem:kernel(4).** For every j the constant c(n, j) is shown to exist
  (`dgpr_kernel_higher_bound`), and for j = 1, 2 it is c(n,1) = 1/2 and
  c(n,2) = 1 (`dgpr_kernel_first_scaled_bound`,
  `dgpr_kernel_second_scaled_bound`). The bound ‖L‖ ≤ K for the norm of a
  j linear map is stated for j ≤ 2 as |L(v_1, …, v_j)| ≤ K|v_1|⋯|v_j|; for
  general j it is the norm of Federer 3.1.11, p. 219. The polynomials P_j
  of the blueprint's induction are replaced by the graded family
  `dgpr_kernel_graded`, and the norm of D^j p_s(z) is bounded through its
  values on coordinate vectors. s^{-1/2} is written (Num.sqrt s)^{-1}.
- **lem:kernel(5).** D²p_s(z)(v, w) is the differential at z of
  [x ↦ Dp_s(x)(v)], applied to w.
- **lem:heat_extension(1).** Class ∞ is proved for [(s, x) ↦ u(s, x)] on
  {(s, x) : 0 < s} ⊆ R × R^n with the product inner product, and for
  [(t, x) ↦ u(T − t, x)] on Ω_T, through R^{n+1} with time as coordinate 0
  and the isometry `dgpr_time_space_map`; the differentiation under the
  integral sign uses the kernel family `dgpr_kernel_family` (members are
  polynomials in z and s^{-1} times p_s) in place of bounds on all
  derivatives of [(s, z) ↦ p_s(z)]. ∂_s u(s, x) is the curve derivative of
  [t ↦ u(t, x)] at s, and Δu_s(x) is Σ_i D²u_s(x)(e_i, e_i) over the
  standard basis. The formula D^j u_s(x) = ∫ D^j p_s(x − y) f(y) dν y is
  proved for j = 1, 2 as an identity of linear maps and, for every j, for
  the multi-index derivatives D^α of Federer 3.1.11, p. 223
  (`dgpr_heat_extension_multi_partial`), which determine D^j u_s(x).
- **lem:heat_extension(2).** For j = 0, 1, 2 with c(n,0) = 1,
  c(n,1) = 1/2, c(n,2) = 1, stated for the values on vectors as in
  lem:kernel(4); for every j with an existing constant and the norm of
  Federer 3.1.11 (`dgpr_heat_extension_higher_bound`, which assumes
  0 ≤ r). The integral ∫ p_s(x − y)|f(y)| dν y is
  `dgpr_heat_norm_extension s x`, the heat extension of ‖f‖, whose
  integral property is `dgpr_heat_norm_integral`.
- **lem:heat_extension(3).** The first inequality is
  `dgpr_heat_extension_gauss_bound`: the integrals of
  [y ↦ p_s(x − y)‖f(y)‖] and ‖f‖ exist, the first being
  `dgpr_heat_norm_extension s x`; the earlier form
  `dgpr_heat_extension_gauss` assumes them. The lower bound is stated for
  Z = R and a bounded ν measurable f ≥ 0 with integral b.
- **lem:heat_extension(4).** Proved for Z = R and f ≥ 0
  (`dgpr_heat_extension_mass`), which covers the uses in section 4; the
  general case is open.
- **lem:semiconvex.** |grad log u_s(x)| ≤ (2s)^{-1}(|x| + r) is stated as
  |D log u_s(x)(w)| ≤ (2s)^{-1}(|x| + r)|w| for all w, without passing to
  the gradient. D² log u_s(x)(v, v) is the differential at x of
  [y ↦ D log u_s(y)(v)] = [y ↦ Du_s(y)(v)/u_s(y)], applied to v. The
  hypothesis ν(R^n) > 0 is stated as ν(R^n) = m with 0 < m.

## Section 3: classes of maps and integration by parts

- **def:classes.** The bilinear map β of lem:classes(cl:product) is any
  bounded bilinear map between normed spaces (`norm_bounded_bilinear`),
  not only one between finite dimensional spaces. Lip(e|B(x, 1)) is
  expressed through a number L ≥ 0 with |e(y) − e(z)| ≤ L|y − z| for
  y, z ∈ B(x, 1) and |e(x)| + L ≤ c(1 + |x|)^c
  (`dgpr_lipschitz_polynomial_growth`). On Ω_T, differentials are taken
  for the product inner product of R × R^n (Federer 1.7.11).
- **lem:classes.** The spaces Z₁, Z₂, Z₃ are arbitrary normed spaces
  over R, not only finite dimensional ones, and the hypothesis 0 < T is
  not used. Statement (cl:product) is otherwise unchanged
  (`dgpr_classes_product` and its variants on R^n).
- **lem:classes(cl:dt).** Stated for real-valued f only. The derivative
  ∂_t f(t, x) is Df(t, x)(1, 0) for a given field Df of differentials of
  f on Ω_T. The conclusion reads: for t < T the maps [x ↦ f(t, x)] and
  [x ↦ Df(t, x)(1, 0)] are L^n summable, and whenever I(t) and DI(t) are
  their integrals, I is of class 1 on R ∩ {t : t < T} with differential
  [s ↦ s DI(t)] at t. Hence d/dt ∫ f(t, x) dx = ∫ ∂_t f(t, x) dx. The case
  of f with values in a normed space is open.
- **lem:classes(cl:div).** For g : R^n → R^n the hypotheses are weaker
  than class ∞ with Gaussian decay: g is differentiable at every point,
  and for every x there is L ≥ 0 with |g(x)| + L ≤ c exp(−|x|²/c) and
  |Dg(x)(v)| ≤ L|v| for all v. The proof uses the translation invariance
  of L^n (Federer 2.7.16) and dominated convergence (2.4.9) applied to
  difference quotients, in place of Fubini's theorem and the fundamental
  theorem of calculus. div g(x) is the trace of Dg(x) (Federer 1.4.5),
  computed in the standard basis. For real-valued f, Δf(x) is
  Σ_i D²f(x)(ε_i, ε_i), and the identity ∫ Δf dL^n = 0 is stated for any
  field of second differentials of f (`dgpr_classes_laplacian`).
- **lem:ibp** (`dgpr_ibp`). The hypotheses and the conclusion are read
  as follows.
  - "D log ρ has polynomial growth" is
    `dgpr_log_derivative_polynomial_growth`: log ∘ ρ is of class ∞ and for
    each j ≥ 1 there is c with ‖D^j log ρ(x)‖ ≤ c(1 + |x|)^c. That log ∘ ρ
    is of class ∞ follows from the other hypotheses on ρ; it is assumed,
    not proved.
  - D log ρ and D² log ρ enter as any fields Dh, D2h with Dh(x) the
    differential of log ∘ ρ at x and D2h(x) = D² log ρ(x), the latter in
    the space of continuous bilinear maps of Federer 3.1.11.
  - The conclusion states that e is differentiable at L^n almost all
    points and that, for every field De such that De(x) is the
    differential of e at L^n almost all x, both sides of (3.17) are
    integrals of summable functions with a common value a.
- **lem:ibp, proof of the general case** (`dgpr_ibp_fields`). The
  statement is unchanged; the proof differs from the blueprint as follows.
  - ε runs through 1/(k + 2), k ∈ N.
  - The bounds |e_ε(x)| ≤ c(2 + |x|)^c and |De_ε(x)(v)| ≤ c(2 + |x|)^c|v|
    for 0 < ε ≤ 1 are obtained from the mean values of e and of the
    difference quotients of e over B(x, ε), not from the formula
    De_ε = Φ_ε ∗ De. The bound of D²e_ε for fixed ε is obtained from
    D_vD_w e_ε = (D_vD_w Φ_ε) ∗ e (Federer 4.1.2), not from DΦ_ε ∗ De.
  - Rademacher's theorem (Federer 3.1.6) and the convergence
    De_ε(x)(v) → De(x)(v) for L^n almost all x are applied to the
    Lipschitzian maps e ∘ P_k, P_k a nonexpanding retraction of R^n onto
    B(0, k + 1), and transferred to e on U(0, k + 1). The convergence for
    Lipschitzian maps is the library lemma supporting Federer 4.1.25
    (`current_lipschitz_lebesgue_action_smoothing_direction_ae`, from
    4.1.2 and 2.9.9); Lebesgue points of De are not used explicitly.
  - The first case is applied in the form `dgpr_ibp_smooth`, with ρ given
    by the first-order fields H1, H2 described below.
- **lem:ibp, first case of the proof with the blueprint's hypotheses**
  (`dgpr_ibp_smooth_classes`). The hypothesis that e, De, D²e have
  polynomial growth is `dgpr_second_order_polynomial_growth`: e is of
  class ∞ and ‖D^j e(x)‖ ≤ c(1 + |x|)^c for j ≤ 2, with one c; the
  hypotheses on ρ are those of `dgpr_ibp`.
- **lem:ibp, first case of the proof** (`dgpr_ibp_smooth`). This form
  differs from the blueprint as follows.
  - The hypotheses are first and second order: ρ, e and h = log ρ are not
    assumed of class ∞. The condition Dh = D log ρ is stated as
    Dρ(x)(v) = ρ(x) H1(x)(v) with 0 < ρ(x); H2(x)(v)(w) is the
    differential at x of [y ↦ H1(y)(w)], applied to v; E2(x)(v)(w) is the
    differential at x of [y ↦ De(y)(w)], applied to v.
  - The symmetry E2(x)(v)(w) = E2(x)(w)(v) is a hypothesis. It holds for
    e of class 2 by Federer 3.1.11, and it is used, as in the blueprint,
    for div[x ↦ De(x)(e(x))] = D(div e)(e) + trace(De ∘ De).
  - Continuity of [x ↦ H2(x)(v)(w)] is a hypothesis, used only for the
    measurability of the integrand on the left of (3.17).
  - The growth hypotheses are pointwise: ρ(x) ≤ c exp(−|x|²/c), and
    |e(x)|, ‖De(x)‖, ‖E2(x)‖, ‖H1(x)‖ and ‖H2(x)‖ are bounded by
    c(1 + |x|)^c, the norms being those of multilinear maps.
  - The conclusion states that both sides of (3.17) are integrals of
    summable functions with a common value a.

## Geometric lemmas: lem:tube, lem:inner, mr:functionals on R^n

- **lem:tube** (`dgpr_tube_estimate`). The hypothesis 1 ≤ m ≤ n of
  mr:notation is stated as `(0 < m)%N` and `(m <= n)%N`. The function
  dist(·, E) is any d with `is_metric_set_distance E d` (Federer 2.2.10);
  this property determines d. The number γ_s is any g with
  `is_measure_integral` for [x ↦ exp(−d(x)^2/(4s))]; such g exists by
  `dgpr_tube_summable`. The bound is stated in the extended real numbers,
  ((1 + 2 (4π)^(n/2)) s^((n−m)/2))·H^m(E), so that H^m(E) = ∞ is allowed
  (the bound is then trivial). The proof does not use Fubini's theorem
  and the layer-cake formula (eq:tube:layer): it uses a discrete layer
  decomposition with step δ = (s/(2(n−m) + 1))^(1/2), Abel summation and
  comparison with a Gaussian integral over R^(n−m), which gives the same
  constant c(n). The choice of s_0 differs from the blueprint's
  accordingly.
- **lem:inner** (`dgpr_inner_approximation`). The density θ is a total
  function R^n → R, nonnegative on M; only its values on M matter. The
  hypothesis H^m(M) < ∞ is kept but not used. The general statement
  `dgpr_inner_approximation_measure` holds for every finite measure μ
  over R^n for which the Borel sets are measurable and μ(A) = 0 whenever
  H^m(M ∩ A) = 0. The compact sets F_i are the closures of the
  m rectifiable sets of the countable cover (Federer 3.2.14), so
  Kirszbraun's theorem is not needed.
- **mr:functionals, first consequence on R^n** (`dgpr_dominated_variation`,
  `dgpr_dominated_representation`, `dgpr_dominated_finite_variation`).
  The specialisation is made for distributions on the whole of R^n
  (U = R^n). Federer's variation measure ‖S‖ is a measure over the
  current domain `current_domain R n setT`; the Radon measure ν over R^n
  is transported to it by the homeomorphism `euclidean_full_domain_point`,
  and the conclusion reads ‖S‖(A) ≤ ν({x : x ∈ A}) for subsets A of the
  current domain. The hypothesis is one-sided, S(φ) ≤ ∫^* |φ| dν with
  Federer's upper integral (2.4.2); the blueprint's
  |S(φ)| ≤ ∫ |φ| dν implies it. As in `DgprFunctionals.v`, the target Z is
  a normed space with a finite basis.

## Section 4: the hypotheses (S), heated objects, identities and heat operators

- **mr:standing, (S)** (`dgpr_standing`). The distribution Υ is an element
  of `Hom (smooth_test_space hE) R^o` for a space hE of smooth maps
  R^n → Y (Federer 4.1.1). The functional σ is not a separate object: the
  constraint Υ(g) = −σ(Dg) is the assertion that X • Dg is μ summable with
  integral −Υ(g), for every test function g and its differentials Dg.
  "Υ is representable by integration" is replaced by its consequences in
  mr:functionals: the data include a Radon measure ‖Υ‖ (`ups`), whose
  integrals of nonnegative continuous functions with compact support are
  the values of the variation of Federer 4.1.5, with ‖Υ‖(R^n) = δ, and a
  ‖Υ‖ measurable map dΥ (`dups`) with ‖dΥ(z)‖ ≤ 1 for every z and
  Υ(g) = ∫ ⟨g(z), dΥ(z)⟩ d‖Υ‖ z. The derivation of these data from
  Federer's representation theorem (mr:functionals) is not part of (S).
  "Borel measure" is read as: open sets are measurable. The support
  condition on μ is μ almost everywhere |y| ≤ r_0.
- **def:heat_objects.** The objects are total functions on R × R^n; the
  restriction to Ω_T, and to the set where S > 0 and ρ > 0, is expressed
  by the hypothesis t < T of each statement. The heat operators H and
  H_ζ are relations `dgpr_heat_operator NZ f t x h` and
  `dgpr_heat_Hzeta hS NZ f t x h` between f, (t, x) and the value h,
  defined through explicit jets: the time derivative, the values of the
  space differentials D f_t(y) for all y and the values of D² f_t(x).
  The class-2 hypothesis of the blueprint is replaced by the existence of
  such a jet at the point. ζ is S^{−1} times the gradient of the values
  of D S_t(x), which equals grad log S_t(x). I(ρ_t) is the upper integral
  of Federer 2.4.2, so that it is defined without a summability
  hypothesis.
- **lem:identities(div), (divB).** The covectors div W_t(x) and
  div B_t(x) are given by their values: for the values l of D W_t(x),
  ⟨y, div W_t(x)⟩ is the sum of l(ε_i)(ε_i) • y. The proof uses a test
  function equal to [z ↦ p_{T−t}(x − z) y] on an open set containing
  B(0, r_0) (`dgpr_heat_kernel_test`) instead of φ g with a cut-off
  function φ. Class ∞ refers to R × R^n with the product inner product of
  Federer 1.7.11 and the open set Ω_T.
- **lem:identities(bounds)** (`dgpr_identities_bounds`,
  `dgpr_identities_bounds_full`). The inequality ρ ≤ U
  (`dgpr_identities_rho_le_U`) is proved separately in
  `DgprMeasureComparison.v`: `dgpr_integral_measure_comparison` gives
  ∫ f dμ_0 ≤ ∫ f dμ for a nonnegative bounded f whose sublevel sets
  {x : f(x) < c} are μ and μ_0 measurable, when μ_0(A) ≤ μ(A) for every A,
  by bounding f above and below by step functions built on the layers
  {x : jh ≤ f(x) < (j + 1)h}; no such lemma was found in Federer.
- **lem:identities(mass)** (`dgpr_identities_mass`). The integrals are
  with respect to Federer's Lebesgue measure `euclidean_lebesgue_measure`.
- **lem:heat_calculus.** The hypotheses "f, g, φ of class 2" are replaced
  by the relations H_ζ f(t, x) = h (which contain a jet at (t, x)) and
  the values of D f_t(x); the conclusions are the corresponding relations
  for the combined maps. In (product) Z is any normed space; in (square)
  Z is any inner product space and \|D f_t(x)\|² is the sum of
  \|D f_t(x)(ε_i)\|² over the standard basis. In (chain) Φ, Φ' and Φ'' are
  given functions with the derivative relations on (0, ∞), and φ(t, y) > 0
  is assumed for every y.
- **lem:regularity.** The class-∞ assertions are proved for U, W, R, Ψ,
  S, ρ, B, η, κ, q, log S, log ρ and log q (`dgpr_identities_div_smooth`,
  `dgpr_regularity_smooth`, `dgpr_regularity_log_smooth`); the logarithm
  is shown to be of class ∞ on {r : 0 < r} (`dgpr_logarithm_norm_class`).
  The Gaussian decay before T of U, W, R, Ψ and ρ is
  `dgpr_regularity_gaussian_extensions`; it rests on the joint bounds
  `dgpr_backward_heat_joint_bound` of `DgprBackwardHeatDecay.v`:
  ‖D^j F(t, x)‖ ≤ c (1 + |x|)^K u_ν(T − t, x) for t in a compact interval
  J ⊂ (−∞, T), where u_ν is the heat extension of (ν, 1). The exponent K
  is existential and not the exponent 2j of eq:reg:ratio; only the
  polynomial character of the weight is used. The derivatives with
  respect to (t, x) are computed through the coordinate derivatives on
  R^{n+1} and Federer's finite coordinate bound (3.1.11, p. 223), not
  through the reduction of time derivatives to space derivatives of order
  at most 2j. The remaining assertions are proved in `DgprRegularity.v`
  with existential constants: the Gaussian decay before T of S
  (`dgpr_regularity_S_gaussian`), the polynomial growth before T of B, η,
  κ and q (`dgpr_regularity_polynomial`) and of log S, log ρ and log q
  (`dgpr_regularity_log_polynomial`), and the Gaussian decay before T of
  ρ log q and ρ |B|² (`dgpr_regularity_entropy_gaussian`,
  `dgpr_regularity_B2_gaussian`). def:classes asserts only some
  0 < c < ∞, so the exponent 2j and the explicit polynomials of the
  blueprint are not computed. On each strip a ≤ t ≤ b < T, the
  derivatives of U, W, R, Ψ, ρ and S are bounded by weights
  c(1 + |x|)^c φ, with φ equal to U, R, ρ or S (`dgpr_relative_class`,
  `DgprRegularityWeights.v`); products of such weights are weights
  relative to the product of the φ's. The bounds for S^{−1}, ρ^{−1} and
  q^{−1} come from an induction on D(F^{−1}) = −F^{−2} DF, with Federer's
  identification of D^k(Df) with D^{k+1}f, instead of the explicit
  formula of the blueprint. The polynomial growth of |log S|, |log ρ| and
  |log q| uses the lower bound
  (4π(T − a))^{−n/2} · mass · exp(−(|x| + r₀)²/(4(T − b))) of
  lem:heat_extension(3) and the Gaussian decay of U and R. The
  derivatives of (T − t)^{±1/2} are bounded on strips by the same
  induction. The class ∞ and the polynomial growth of ζ are not proved;
  they are not used.
- **Proof of lem:DGPR31, the time derivative of ∫ f_t**
  (`dgpr_heat_integral`, `DgprHeatIntegral.v`). The step
  J'(t) = ∫ H(ρ log q)(t, x) dL^n x is proved for every f of Gaussian
  decay before T with H f = h on Ω_T: lem:classes(cl:dt) gives the
  derivative ∫ D f(t, x)(1, 0) dL^n x, the jets of DgprHeatJets.v give
  h = D f(t, x)(1, 0) + Δ f_t(x), and lem:classes(cl:div) gives
  ∫ Δ f_t dL^n = 0. The section [x ↦ f(t, x)] has Gaussian decay
  (`dgpr_slice_gaussian`), because its kth differential is the kth
  differential of f at (t, x) composed with [x ↦ (0, x)] in every
  argument.
- **lem:DGPR31** (`dgpr_lemma_3_1_conditional`, `DgprLemma31Final.v`).
  The outer integral ∫_0^T … dL^1 t is Federer's upper integral over the
  set [0, T) (2.4.10), `measure_subset_upper_integral L1 [set t | 0 <= t < T]`,
  of the upper integrals over R^n (2.4.2); [0, T) and [0, T] differ by an
  L^1 null set. The constant is the blueprint's C = (16n + 6)Λ² + 16. The
  map DB is any field whose values are those of D B_t(x) for t < T, and
  |DB_t(x)|² is the sum of |D B_t(x)(ε_i)|². (eq:31:J) is proved without
  Federer 2.4.19: the tangent-line inequality
  r log r ≥ a log a + (1 + log a)(r − a), with a = γ/M, is integrated
  against S (`dgpr_entropy_jensen`). For (eq:31:min) the two cases
  T^{1/2}δ/γ ≤ 1 and > 1 are replaced by the single majorant
  m(t) ≤ 2γ((T − t)^{1/2}((T − t)^{1/2} + γ/δ))^{−1}, whose primitive
  −4γ log((T − t)^{1/2} + γ/δ) gives ∫_0^τ m ≤ 4γ log(1 + T^{1/2}δ/γ)
  (`dgpr_time_min_integral`). The fundamental theorem of calculus on
  [a, b] with b < T is proved for maps of class 1 only on R ∩ {t : t < T}
  (`dgpr_before_ftc`), through the retraction of R onto [a, b]. The
  passage τ → T− uses Federer 2.4.7 (`dgpr_before_upper_integral`). The
  integral bound ∫ ρ_t ‖η_t‖² ≤ m(t) is obtained from the pointwise bound
  ρ‖η‖² ≤ min{(T − t)^{−1} ρ, (T − t)^{−1/2} R}, whose right side is
  summable with integral at most m(t). The Gaussian decay before T of
  ρ log q and of ρ |B|² is a hypothesis of the section
  (`hJgauss`, `hKgauss`) of `dgpr_lemma_3_1_conditional`; lem:regularity
  discharges it in `dgpr_lemma_3_1` (`DgprLemma31Theorem.v`), which
  assumes only (S) and a field DB with the values of D B_t(x); such a
  field exists (`dgpr_lemma31_DB_exists`).
- **lem:DGPR32, integration over [0, τ]** (`dgpr_lemma_3_2_conditional`,
  `DgprLemma32Final.v`). The integral ∫_0^τ … dL^1 t is Federer's upper
  integral over [0, τ] (2.4.10) of a function with values in the
  extended real line, since I(ρ_t) is an upper integral (2.4.2). The
  continuity in t of I(ρ_t) and of the right side of eq:32:I is not
  used: the upper integral is monotone, and the right side of eq:32:I is
  bounded by (n/2)m(t) + C_1 g(t) with the summable majorant g of
  `dgpr_lemma31_majorant`. The constant is 2n + C_1 C, where
  C = (16n + 6)Λ² + 16 is the constant of lem:DGPR31; the bound
  log(1 + T^{1/2}δ/γ) ≤ log((1 + T^{1/2}δ)/γ) uses γ ≤ 1. The estimate
  eq:32:I at a fixed time is the hypothesis `hI32` of the section; it is
  discharged in `dgpr_lemma_3_2` (`DgprLemma32Theorem.v`) with C_1 as in
  the blueprint.
- **lem:DGPR32, eq:32:I** (`dgpr_lemma32_fixed_time`,
  `DgprLemma32Pointwise.v`). The identity I(ρ_t) = −∫ ρ_t Δ log ρ_t is
  obtained from lem:ibp applied to the constant fields ε_j (De = 0), not
  from lem:classes(cl:div). eq:32:DQ is proved at every point where all
  columns e_j = [x ↦ Q(x)(ε_j)] are differentiable, by the comparison
  |DQ(x)(v)| ≤ 2Λ Lip(χ) |DB_t(x)(v)| of the differentials of Q and of
  B_t; by Rademacher's theorem within lem:ibp these points form a set of
  full measure. eq:32:trace is used in the pointwise form
  ρ(n − |Q|²)/(2(T − t)) ≤ (n − m)ρ/(2(T − t))
  + (n/2) min{ρ/(T − t), R/(T − t)^{1/2}} and integrated with
  `dgpr_lemma31_min_integral`, so the set G need not be measurable. The
  integral on the right of eq:32:I is Federer's upper integral, and C_1
  multiplies it in the extended real line. The step "by lem:regularity"
  consists of two facts at time t: D log ρ_t has polynomial growth
  (`dgpr_lemma32_log_rho_growth`), and B_t is Lipschitzian on every ball
  {y : |y − x| ≤ 1} with a constant c(1 + |x|)^c
  (`dgpr_lemma32_B_lipschitz`). The second follows from the polynomial
  growth of B_t: on that convex ball ‖DB_t‖ ≤ c_1(2 + |x|)^{c_1}, and the
  convex-domain criterion of Federer 2.2.7 gives the Lipschitz bound
  (`dgpr_polynomial_local_lipschitz`).


## Section 4: entropy and entropy bounds; section 5: the compact case

- **def:entropy** (`dgpr_entropy`, `dgpr_entropy_tilde`,
  `DgprEntropy.v`). H(ρ_t) is Federer's upper integral (2.4.2) of
  ρ_t log ρ_t, taken as a real number by `fine`; it is defined for every
  t, and for t < T it is the integral of the L^n summable function
  ρ_t log ρ_t (`dgpr_entropy_derivative`). The blueprint defines H(ρ_t)
  as the integral for t < T only.
- **lem:entropy** (`dgpr_entropy_derivative`). The conclusion "H(ρ_t) is
  of class 1 with derivative I(ρ_t)" is a class-one field
  `is_norm_class_one_field` on R ∩ {t : t < T} with the derivative
  [t ↦ [s ↦ s I(ρ_t)]]; since I(ρ_t) is an upper integral with values in
  the extended real line, the derivative uses `fine (I(ρ_t))`, and the
  theorem states that ρ_t |grad log ρ_t|² is summable with integral
  `fine (I(ρ_t))` for t < T. The summability of ρ_t log ρ_t is part of
  the conclusion.
- **lem:upper_entropy** (`dgpr_upper_entropy`, `DgprUpperEntropy.v`).
  The constant is explicit: C = 2n + C1 ((16n + 6)Λ² + 16), the constant
  of lem:DGPR32 (`dgpr_upper_entropy_constant`). The integral over
  [0, τ] in the proof is the upper integral of Federer 2.4.10. The
  intermediate `dgpr_upper_entropy_of` holds for every C0 satisfying the
  conclusion of lem:DGPR32.
- **lem:lower_entropy** (`dgpr_lower_entropy`, `DgprLowerEntropy.v`).
  H^m(E) is assumed to be a real number h > 0 (`HH Ec = h%:E`), so the
  hypothesis H^m(E) < ∞ is explicit. The conclusion
  liminf_{t→T−} H̃(ρ_t) ≥ γ log(γ/H^m(E)) − γ (log c(n) + 2^{-1} n) is
  replaced by the stronger assertion that the inequality holds for
  T − s_0 < t < T, with s_0 the number of lem:tube; the hypothesis t ≥ 0
  is not needed. Jensen's inequality (Federer 2.4.19) for the probability
  densities γ^{-1} ρ_t and γ_s^{-1} G is replaced by the pointwise tangent
  inequality r log r ≥ r log a + r − a, integrated with a = γ γ_s^{-1} G;
  this gives the same bound H(ρ_t) ≥ γ log(γ/γ_s) − (4s)^{-1} ∫ ρ_t d².
  The constant c(n) is that of `dgpr_tube_estimate`,
  1 + 2 (4π)^{n/2} (`dgpr_tube_constant`).
- **lem:compact_case** (`dgpr_compact_case_normalised`,
  `DgprCompactCase.v`). Only the normalised case is formalised: the data
  satisfy (S) for some 0 < T_0 (hence μ(R^n) = 1), μ_0 = μ ⌞ E, E is
  compact and m rectifiable with H^m(E) = h > 0, and 1/2 < γ
  (`dgpr_compact_case_standing`). The conclusion is 1 ≤ C h^{1/m} δ with
  the explicit C = exp(log 2 + C1 (1 + log 4)),
  C1 = C0 + log c(n) + 2^{-1} n, where C0 is the constant of
  lem:upper_entropy. The argument "if δ = 0 the right side
  tends to −∞" is replaced by an explicit choice of T. The data of
  mr:hypotheses_main are treated in the next subsection.

## Section 5: lem:compact_case for the data of mr:hypotheses_main

- **lem:compact_case, the statement** (`dgpr_compact_case_general`,
  `DgprCompactCaseGeneral.v`, and `dgpr_compact_case_inequality`,
  `DgprMainHypothesesCompact.v`). The conclusion is a proposition of λ, Λ
  and C quantified over all Y and all data of mr:hypotheses_main, as for
  thm:main. The constant is explicit: C is that of
  `dgpr_compact_case_standing`, with C0 the constant
  `dgpr_upper_entropy_constant n λ Λ` of lem:upper_entropy. The
  hypotheses 0 < λ and 0 < Λ of the theorem repeat fields of
  mr:hypotheses_main and are not used in the proof. The number
  H^k(M)^{1/k} is the real power of the finite number H^k(M), and the
  inequality is one of extended real numbers.
- **Proof of lem:compact_case, the normalisation**
  (`dgpr_main_standing`, `DgprMainToStanding.v`). The blueprint replaces
  θ by θ/μ(R^n) and Υ by Υ/μ(R^n) and appeals to homogeneity. The
  formalisation does not form the new density. It uses the measures
  a^{-1} μ and a^{-1} ‖Υ‖ (`measure_scale`, the measure c φ of Federer
  2.7.18), with a = μ(R^n), which are the measures of the replaced data,
  and the distribution a^{-1} Υ (`dgpr_variation_value_scale`,
  `dgpr_measure_scale_radon`). The final inequality is multiplied by a.
  The case a = 0 is treated separately, as in the blueprint.
- **Proof of lem:compact_case, the extension of X**
  (`dgpr_main_extension`). The constant value in K is an arbitrary
  element A_0 of K, which exists because K ≠ ∅. The extension is
  μ measurable and satisfies the constraint because μ(R^n ∖ M) = 0
  (`dgpr_main_measure_on`).
- **Proof of lem:compact_case, the dual density** (`dgpr_dual_density`,
  `DgprDualDensity.v`). The hypotheses (S) require a dual density dΥ of
  ‖Υ‖, which the blueprint takes from mr:functionals without comment. The
  formalised density satisfies ‖dΥ(z)‖ ≤ 1 for every z ∈ R^n instead of
  ‖dΥ(z)‖ = 1 for ‖Υ‖ almost all z, as stated in mr:functionals; (S)
  requires only the inequality. Instead of extending Υ to K(R^n, Y) and
  applying mr:functionals, the formalisation applies Federer 4.1.5 to Υ
  on the current domain of R^n (`dgpr_functional_representation`). The
  measure obtained there is carried to R^n by the inclusion and
  identified with ‖Υ‖ by `dgpr_variation_measure_unique`.
- **Proof of lem:compact_case, the parameters of (S)**
  (`dgpr_main_standing`, `dgpr_standing_restrict`). The hypotheses (S)
  are first established with T = 1, μ_0 = a^{-1} μ and γ = 1, and then
  passed to μ_0 = a^{-1} μ ⌞ E and γ = a^{-1} μ(E). The blueprint states
  (S) for every 0 < T directly; `dgpr_standing_time` supplies this.
- **Proof of lem:compact_case, the choice of E**
  (`dgpr_compact_case_general`). The lemma lem:inner is applied to the
  unnormalised measure μ with ε = a/2, which gives μ(E) > a/2, that is,
  γ = a^{-1} μ(E) > 1/2. The inequality H^k(M) < ∞ is a hypothesis of
  mr:hypotheses_main, and 0 < H^k(E) follows from 0 < μ(E) by
  `dgpr_main_measure_hausdorff`.

## Section 5: mr:hypotheses_main and thm:main; section 6: varifolds and the Michael–Simon inequality

- **mr:hypotheses_main** (`dgpr_main_hypotheses`, `DgprMainHypotheses.v`).
  The space Y is a vector space with an inner product CY and a basis eY
  indexed by {0, …, d − 1}. As in (S), the distribution Υ is an element of
  `Hom (smooth_test_space hE) R^o` for a realisation hE of the smooth maps
  R^n → Y (Federer 4.1.1), and σ is not a separate object: the relation
  Υ(g) = −σ(Dg) is the assertion that X • Dg is μ summable with integral
  −Υ(g), for every test function g and its differentials Dg. The
  functions θ and X are total functions on R^n whose values off M play no
  role; the conditions θ ≥ 0 and X(x) ∈ K are imposed for x ∈ M, and X is
  H^k ⌞ M measurable as a map into Hom(R^n, Y) with the norm of Federer
  1.7.9. "Υ is representable by integration and ‖Υ‖(R^n) < ∞" is the
  existence of a Radon measure ‖Υ‖ over R^n with ‖Υ‖(R^n) < ∞ whose
  integral of every nonnegative continuous function f with compact
  support is the variation ‖Υ‖(f) of Federer 4.1.5; such a measure is
  unique (`dgpr_variation_measure_unique`), and its existence implies that
  Υ is representable by integration.
- **thm:main** (`dgpr_main_inequality`). The conclusion is stated as a
  proposition of λ, Λ and C quantified over all Y and all data. The
  number H^k(M)^{1/k} is the real power of the finite number H^k(M), and
  the inequality is one of extended real numbers. The existence of
  0 < C < ∞ is `dgpr_theorem_1_1_rectifiable` (see the subsection on the
  proof of thm:main below).
- **mr:varifolds** (`dgpr_integrand`, `DgprAnisotropicIntegrand.v`). The
  integrand F is a function on Hom(R^n, R^n) which is of class 1 relative
  to G(n, k) (Federer 3.1.22) and positive on G(n, k); its values off
  G(n, k) play no role. The map B_F is `ddg_B` of the DPDRG2018 subproject.
- **def:BF** (`is_dgpr_lambda`, `is_dgpr_Lambda`, `DgprKF.v`). The numbers
  λ(F) and Λ(F) are characterised by predicates (greatest lower bound and
  least upper bound) and are not chosen; uniqueness and existence are
  separate lemmas. The condition dim im A ≥ k is Federer's
  `linear_rank_at_least A k` (3.1.18).
- **lem:KF** (`dgpr_KF_compact_convex`, `dgpr_KF_bounds`,
  `dgpr_lemma_KF`). Compactness refers to the norm topology of
  Hom(R^n, R^n), and convexity is `is_inner_convex`. The assertion
  Λ(F) < ∞ is implicit, Λ(F) being a real number.
- **lem:first_variation** (`dgpr_first_variation`, `dgpr_test_flow`,
  `DgprFirstVariation.v`). The vector field g is an element of the test
  space of a realisation hE of the smooth maps R^n → R^n, and its
  differentials Dg(x) are given together with the hypothesis that Dg(x)
  is the differential of g at x for every x. The first assertion is
  weakened: φ_t is shown to be injective and a proper immersion of class 1
  for |t| < t_0, which are the hypotheses of Allard 3.2 used to define
  φ_{t#} V; that φ_t maps R^n onto R^n is not proved. The number
  δ_F V(g) is not a chosen object: `is_dgpr_first_variation V F g Dg c`
  asserts that F(φ_{t#} V) exists for |t| < δ and that every function
  agreeing with [t ↦ F(φ_{t#} V)] there has the derivative c at 0; this c
  is unique. The proof is that of DDG Lemma A.2 as formalised in
  DPDRG2018 (`ddg_lemma_A_2_constant_lipschitz`); the blueprint's sketch
  is not repeated.
- **thm:MS, the reduction** (`dgpr_theorem_1_6_from_main`,
  `DgprMichaelSimon.v`). The conclusions (eq:MS:MS) and (eq:MS:sobolev)
  are first deduced for every constant C satisfying
  `dgpr_main_inequality hk λ(F) Λ(F) C`; the hypothesis 0 ≤ C is added. It
  is used to pass from the inequality of thm:main for M' to (eq:MS:MS) for
  M ⊇ M', and for (eq:MS:sobolev) when ‖V‖(R^n) = 0. The constant of
  thm:main satisfies it. Theorem 1.6 itself is `dgpr_theorem_1_6` (see
  the subsection on δ_F V and Theorem 1.6 below).
- **thm:MS, δ_F V in the reduction.** In the section `MichaelSimon` of
  `DgprMichaelSimon.v` the linear functional δ_F V is a hypothesis: a
  linear functional S on D(R^n, R^n) with S(g) = δ_F V(g) for every g in
  the sense of `is_dgpr_first_variation`. The functional
  `dgpr_first_variation_functional` satisfies this hypothesis (see the
  subsection on δ_F V and Theorem 1.6 below). The hypothesis "δ_F V is
  representable by integration and ‖δ_F V‖(R^n) < ∞" is the existence of
  a Radon measure ν over R^n with ν(R^n) < ∞ which represents ‖S‖ on the
  nonnegative continuous functions with compact support, as for ‖Υ‖ in
  mr:hypotheses_main.
- **thm:MS, the density hypothesis.** "Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost
  all x" is read as: for ‖V‖ almost all x the density Θ^k(‖V‖, x) exists
  in the extended real numbers and is at least 1. The set M is
  `dgpr_MS_set k ‖V‖`: the points where Θ^k(‖V‖, x) exists, is a real
  number, and is at least 1.
- **Proof of thm:MS, the set M** (`dgpr_MS_borel_part`,
  `DgprVarifoldWeight.v`). The blueprint asserts that M is a Borel set,
  because the upper and lower densities of ‖V‖ are Borel functions. This
  is not formalised (only the Borel property of the superlevel sets of the
  upper density is proved). Instead, by the Borel regularity of ‖V‖, there
  is a Borel set M' ⊆ M with ‖V‖(R^n ∖ M') = 0, and the data of
  mr:hypotheses_main are formed with M' in place of M. Since M' ⊆ M, the
  conclusion (eq:MS:MS) for M follows.
- **Proof of thm:MS, θ and X** (`dgpr_MS_density`, `dgpr_MS_reduction`).
  The density θ is the upper density Θ^{*k}(‖V‖, ·) on M', where it
  equals Θ^k(‖V‖, ·), and 0 off M'. The map X is B_F ∘ t, where t is the
  Borel map of `allard_3_5_1_b_pushforward` with t(x) = Tan^k(‖V‖, x) for
  ‖V‖ almost all x; the blueprint's X, defined through Tan^k(‖V‖, x) and
  a fixed S_0, agrees with it ‖V‖ almost everywhere. The identity
  Υ(g) = −σ(Dg) is derived from V = [x ↦ (x, t(x))]_# ‖V‖ and Federer
  2.4.18(1) (`dgpr_MS_transfer`) instead of (eq:MS:V).

## Section 5: the proof of thm:main; section 6: δ_F V and Theorem 1.6

- **thm:main, the constant** (`dgpr_theorem_1_1_rectifiable`,
  [DgprMainTheorem.v](../theories/DgprMainTheorem.v)). The constant is
  explicit: C = `dgpr_compact_case_constant n C0` with
  C0 = `dgpr_upper_entropy_constant n λ Λ`, the constant of
  lem:compact_case (`dgpr_compact_case_general`). The deduction from
  lem:compact_case (`dgpr_main_from_compact_case`) holds for every C ≥ 0
  satisfying the conclusion of lem:compact_case.
- **Proof of thm:main, the cut-off functions** (`dgpr_main_cutoff`,
  [DgprMainCutoff.v](../theories/DgprMainCutoff.v)). Instead of
  φ_ϱ(x) = φ(ϱ^{-1} x) for a fixed φ, φ_ϱ is the smooth cut-off of
  Federer 3.1.23 for the radii ϱ and 2ϱ, obtained by scaling the
  normalised cut-off with inner radius 1/2. The bound
  |grad φ_ϱ| ≤ c_0/ϱ is stated for the differential:
  |Dφ_ϱ(x)(v)| ≤ c_0 ϱ^{-1} |v|. The parameter ϱ ranges over 0 < ϱ < ∞
  instead of 1 ≤ ϱ < ∞.
- **Proof of thm:main, the distributions Υ_ϱ** (`dgpr_cutoff_bound`,
  [DgprMainTheorem.v](../theories/DgprMainTheorem.v)). The blueprint
  defines Υ_ϱ(g) = −σ_ϱ(Dg) and derives the formula
  Υ_ϱ(g) = Υ(φ_ϱ g) + ∫ Dφ_ϱ(x)(X(x)^*(g(x))) dμ x. The formalisation
  defines Υ_ϱ by the second formula, as Υ ∘ P + J with
  J(g) = ∫ X • (Dφ_ϱ · g) dμ, whose linearity follows from
  `real_integral_linear_map_exists`, and proves Υ_ϱ(g) = −σ_ϱ(Dg). The
  passage from μ to μ_ϱ (`dgpr_density_measure_change`,
  [DgprMainMeasure.v](../theories/DgprMainMeasure.v)) requires the
  H^k ⌞ M measurability of X • Dg, which is proved
  (`dgpr_hom_pairing_measurable`); the blueprint uses it without comment.
- **Proof of thm:main, the variation of Υ_ϱ**
  (`dgpr_bounded_variation_measure`,
  [DgprMainVariation.v](../theories/DgprMainVariation.v)). The blueprint
  shows |Υ_ϱ(g)| ≤ ∫ |g| dν_ϱ with ν_ϱ = ‖Υ‖ + c_0 Λ ϱ^{-1} μ and applies
  mr:functionals. The formalisation proves only
  Υ_ϱ(g) ≤ m (‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n)) whenever |g(x)| ≤ m for
  x ∈ R^n. This bound makes the variation of Υ_ϱ finite, so that Federer
  4.1.5 (`dgpr_functional_representation`) gives a Radon measure ‖Υ_ϱ‖
  with ‖Υ_ϱ‖(R^n) ≤ ‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n). This is the only
  property of ‖Υ_ϱ‖ used.
- **Proof of thm:main, the limit** (`dgpr_main_from_cutoff_bound`). The
  closed balls B(0, ϱ) are replaced by the open balls U(0, j + 1),
  j = 0, 1, 2, …; then μ(U(0, j + 1)) ≤ μ_{j+1}(R^n) and
  μ(U(0, j + 1)) → μ(R^n) by Federer 2.1.5(1).
- **δ_F V as a linear functional** (`dgpr_first_variation_functional`,
  [DgprFirstVariationFunctional.v](../theories/DgprFirstVariationFunctional.v)).
  The blueprint treats δ_F V as a distribution without proving its
  linearity. The formalisation characterises the functional by
  `is_dgpr_first_variation_functional`
  ([DgprFirstVariationFunctionalUP.v](../theories/DgprFirstVariationFunctionalUP.v)),
  proves its existence for a varifold V with ‖V‖(R^n) < ∞ and F of
  class 1 relative to G(n, k) through the integral formula of
  lem:first_variation and the linear dependence of Dg on g
  ([DgprFirstVariationFunctionalConstruction.v](../theories/DgprFirstVariationFunctionalConstruction.v)),
  and chooses it in a sealed module
  ([DgprFirstVariationFunctionalSealed.v](../theories/DgprFirstVariationFunctionalSealed.v)).
  For other V and F the chosen functional is 0; this value plays no role.
- **Theorem 1.6** (`dgpr_theorem_1_6`,
  [DgprTheorem16.v](../theories/DgprTheorem16.v)). The numbers λ(F) and
  Λ(F) are arguments l and L with `is_dgpr_lambda hk F l` and
  `is_dgpr_Lambda k F L`. The hypothesis "δ_F V is representable by
  integration and ‖δ_F V‖(R^n) < ∞" is, as in the reduction, the
  existence of a Radon measure ν over R^n with ν(R^n) < ∞ representing
  the variation of `dgpr_first_variation_functional hE V F` on the
  nonnegative continuous functions with compact support, and ν takes the
  place of ‖δ_F V‖ in the conclusions. The constant is explicit:
  C = `dgpr_compact_case_constant n (dgpr_upper_entropy_constant n l L)`.
