# Heat kernel and heat extensions (blueprint section 3)

This account covers differentiation under the integral sign, def:heat,
lem:kernel, lem:heat_extension and lem:semiconvex of
`blueprint/dgpr_blueprint.tex`, that is, the heat-flow part of section 3
of De Philippis, Gennaioli, Pigati and Rindler (2026), up to (3.16).
Integrals are those of Federer 2.4.2 and, for vector-valued functions,
2.4.12; differentials are those of Federer 3.1.1 (`has_norm_differential`).
The number π, the exponential and the Lebesgue measure L^n are Federer's
(`CircularTrigonometry.half_period`, `RealExponential.exponential`,
`euclidean_lebesgue_measure`).

## Differentiation under the integral sign

`theories/DgprParameterIntegralDifferential.v` and
`theories/DgprParameterIntegralSmooth.v` serve this part and the classes of
lem:classes. Throughout, ν is a measure over a choice type T, X is a normed
space, Z a normed space, and `dgpr_has_integral nu k z` states that z is the
integral 2.4.12 of the total function k : T → Z with respect to ν.

| Statement | Declaration |
| --- | --- |
| Differential at a: if f(x, ·) has integral F(x) for x near a, each f(·, y) has differential Df(x, y) near a, the integrals of Df(a, ·)(v) are L(v), and ‖Df(x, y)(v)‖ ≤ g(y)‖v‖ with g ν summable, then DF(a) = L | `dgpr_parameter_integral_differential` |
| Class 1 on an open set, with locally dominated derivatives | `dgpr_parameter_integral_class_one` |
| Existence of the linear map L from the integrals of Df(a, ·)(v) | `dgpr_integral_hom_exists` |
| Continuity of parameter integrals | `dgpr_parameter_integral_continuous` |
| Directional derivatives (curves) | `dgpr_parameter_integral_directional` |
| Partial derivatives on R^n | `dgpr_parameter_integral_partial` |
| Class k + 1 from class 0 and partial derivatives of class k | `dgpr_class_successor_coordinate_fields` |
| Class ∞ for a family of integrands closed under partial differentiation | `dgpr_parameter_integral_smooth` |

The proofs use the mean value inequality on convex sets
(`norm_differential_convex_bound`) and Lebesgue's dominated convergence
theorem for vector integrals (`total_vector_integral_dominated_limit`,
Federer 2.4.9).

## The heat kernel (def:heat, lem:kernel)

`theories/DgprHeatKernel.v` and `theories/DgprHeatKernelDifferential.v`.
For 0 < s and z ∈ R^n,
p_s(z) = (4πs)^{-n/2} exp(−|z|²/(4s)) (`dgpr_heat_kernel`), where the
factor (4πs)^{-n/2} is written `Num.sqrt (4 * dgpr_pi R * s) ^- n`.

| Item | Declaration |
| --- | --- |
| Γ(1/2)² = π, from α(2) = π and 3.2.13 | `dgpr_gamma_half_sqr` |
| ∫ exp(−|x|²) dL^n x = π^{n/2} | `dgpr_gaussian_integral` |
| Dilation: ∫ g(e^{-1}x) dL^n x = e^n ∫ g dL^n | `dgpr_lebesgue_dilation` |
| lem:kernel(1): ∫ p_s dL^n = 1 | `dgpr_kernel_mass` |
| lem:kernel(2): ∫ \|z\|² p_s(z) dL^n z = 2ns | `dgpr_kernel_moment` |
| lem:kernel(5), first formula: Dp_s(z)(v) = −(2s)^{-1}(z • v) p_s(z) | `dgpr_kernel_differential_formula` |
| lem:kernel(5), second formula, as the differential at z of [x ↦ Dp_s(x)(v)] | `dgpr_kernel_second_formula` |
| lem:kernel(5), both formulas | `dgpr_kernel_formulas` |
| ∂_s p_s(z) = ((4s²)^{-1}\|z\|² − n(2s)^{-1}) p_s(z) | `dgpr_kernel_time_derivative` |
| lem:kernel(3): ∂_s p_s(z) = Δp_s(z), with Δp_s(z) the sum of D²p_s(z)(e_i, e_i) | `dgpr_kernel_heat` |
| lem:kernel(6): p_s(z) ≤ (4πs)^{-n/2} | `dgpr_kernel_max` |
| lem:kernel(4) for j ≤ 2, in uniform form: \|z\| p_s(z) and \|z\|² p_s(z) are bounded by multiples of (4πs)^{-n/2}; bounds of Dp_s and D²p_s | `dgpr_kernel_lin_weight`, `dgpr_kernel_sqr_weight`, `dgpr_kernel_differential_bound`, `dgpr_kernel_second_bound` (in `DgprHeatExtension.v`) |
| lem:kernel(4), j = 1, 2, with c(n,1) = 1/2 and c(n,2) = 1: \|Dp_s(z)(v)\| ≤ 2^{-1}s^{-1/2}(1 + \|z\|s^{-1/2})p_s(z)\|v\| and \|D²p_s(z)(v, w)\| ≤ s^{-1}(1 + \|z\|s^{-1/2})²p_s(z)\|v\|\|w\| | `dgpr_kernel_first_scaled_bound`, `dgpr_kernel_second_scaled_bound` (in `DgprHeatExtensionBounds.v`) |
| p_s is of class ∞ on R^n | `dgpr_kernel_class_infinity` (in `DgprHeatKernelHigher.v`) |
| lem:kernel(4) for every j: ‖D^j p_s(z)‖ ≤ c s^{-j/2}(1 + \|z\|s^{-1/2})^j p_s(z), with D^j the jth differential of Federer 3.1.11 | `dgpr_kernel_higher_bound` (in `DgprHeatKernelHigher.v`) |

The mass and moment are not reduced to one-dimensional integrals by
Fubini's theorem, as in the blueprint, but obtained directly from the
multivariate Gamma integral of Federer 3.2.13 (`gamma_gaussian_product_integral`)
with z_j = 1/2, respectively z_i = 3/2 and z_j = 1/2 for j ≠ i, and the
dilation law of L^n; that integral rests on Fubini's theorem itself.

## Heat extensions (lem:heat_extension)

`theories/DgprHeatExtension.v`. For a measure ν over R^n, a complete normed
space Z and f : R^n → Z, `dgpr_convolution k x` is the integral 2.4.12 of
[y ↦ k(x − y) f(y)] with respect to ν whenever this function is ν summable,
and 0 otherwise; `dgpr_heat_extension s x` is the convolution with p_s.
The standing hypotheses of the theorems are: every open set is ν
measurable, ν(R^n) = m, Z is separable, f is ν measurable and ‖f(y)‖ ≤ M
for all y, and, for (3), ν(R^n ∖ B(0, r)) = 0.

| Item | Declaration |
| --- | --- |
| def:heat: the integral defining u(s, x) exists and equals u(s, x) | `dgpr_heat_extension_integral` |
| Convolution with a bounded kernel of class 1 with bounded continuous derivative is differentiable, with the derivative under the integral sign | `dgpr_convolution_differential` |
| lem:heat_extension(1), j = 1: Du_s(x)(v) = ∫ Dp_s(x − y)(v) f(y) dν y | `dgpr_heat_extension_first` |
| lem:heat_extension(1), j = 2: D²u_s(x)(v, w) = ∫ D²p_s(x − y)(v, w) f(y) dν y | `dgpr_heat_extension_second` |
| lem:heat_extension(3), Gaussian upper bound | `dgpr_heat_extension_gauss` |
| lem:heat_extension(3), lower bound for Z = R and f ≥ 0 | `dgpr_heat_extension_lower` (in `DgprHeatSemiconvex.v`) |

## Log-semiconvexity (lem:semiconvex, DPGPR (3.16))

`theories/DgprHeatSemiconvex.v`. With u the heat extension of (ν, 1),
ν(R^n) > 0 and 0 < s: u_s(x) > 0 (`dgpr_heat_extension_positive`), and
`dgpr_semiconvex` states that log u_s has at x the differential
[w ↦ Du_s(x)(w)/u_s(x)], that |Du_s(x)(w)/u_s(x)| ≤ (2s)^{-1}(|x| + r)|w|
for every w, and that the differential at x of [y ↦ Du_s(y)(v)/u_s(y)],
that is D² log u_s(x)(v, ·), takes at v a value at least −(2s)^{-1}|v|².
The inequality (∫ w dπ)² ≤ ∫ w² dπ is obtained from
∫ (w − a)² p_s(x − y) dν y ≥ 0 with a suitable constant a, in place of
Hölder's inequality 2.4.14.

## Regularity in (s, x) and the heat equation (lem:heat_extension(1))

`theories/DgprHeatKernelFamily.v` and `theories/DgprHeatExtensionSmooth.v`.
The *kernel family* `dgpr_kernel_family` is the smallest set of functions
q(s, z) containing p and closed under q ↦ z_i q, q ↦ s^{-1} q, sums and
scalar multiples. Its members are bounded on [a, b] × R^n, even after
multiplication by (1 + |z|²)^k (`dgpr_kernel_family_bound`), are
continuous in (s, z) (`dgpr_kernel_family_joint_class_zero`), and their
partial derivatives in z_i and in s are again members
(`dgpr_kernel_family_space_derivative`, `dgpr_kernel_family_time_derivative`).
Hence `dgpr_parameter_integral_smooth` applies on R^{n+1}, coordinate 0
being time, and the result is carried over to R × R^n with the product
inner product (Federer 1.7.11) by the isometry `dgpr_time_space_map`.

| Statement | Declaration |
| --- | --- |
| [(s, x) ↦ u(s, x)] is of class ∞ on {(s, x) : 0 < s} ⊆ R × R^n | `dgpr_heat_extension_smooth` |
| [(t, x) ↦ u(T − t, x)] is of class ∞ on Ω_T = {(t, x) : t < T} | `dgpr_heat_extension_backward_smooth` |
| The same on R^{n+1} with time as coordinate 0 | `dgpr_heat_extension_class_coordinates` |
| ∂_s u(s, x) is the integral of ∂_s p_s(x − y) f(y) dν y | `dgpr_heat_extension_time_derivative` |
| ∂_s u(s, x) = Σ_i D²u_s(x)(e_i, e_i), each term an integral of D²p_s | `dgpr_heat_extension_heat` |
| ∂_t[u(T − t, x)] = −Σ_i D²u_{T−t}(x)(e_i, e_i) for t < T | `dgpr_heat_extension_backward_heat` |

Here ∂_s is the curve derivative `has_normed_curve_derivative` of
[t ↦ u(t, x)], and the terms of the sum are the convolutions of
[z ↦ D²p_s(z)(e_i, e_i)]; by `dgpr_heat_extension_second` they are
D²u_s(x)(e_i, e_i).

## Higher derivatives (lem:kernel(4), lem:heat_extension(1),(2) for every j)

`theories/DgprHeatKernelHigher.v` and `theories/DgprHeatExtensionHigher.v`.
The graded family `dgpr_kernel_graded d` replaces the polynomials P_j of
the blueprint: its members of degree d are built from p by
q ↦ s^{-1} z_i q (degree + 1), q ↦ s^{-1} q (degree + 2), sums and scalar
multiples. A member of degree d is bounded by
C s^{-d/2}(1 + |z| s^{-1/2})^d p_s(z) (`dgpr_kernel_graded_bound`), and
its partial derivatives in z are members of degree d + 1
(`dgpr_kernel_graded_space_derivative`). The iterated directional
derivatives of p_s along coordinate vectors (Federer 3.1.11, p. 223) are
members of the corresponding degree (`dgpr_kernel_iterated`), and the norm
of a jth differential is bounded by its values on coordinate vectors
(`norm_higher_differential_finite_partial_bound` of Federer's library).

| Statement | Declaration |
| --- | --- |
| For 0 < s, u_s is of class ∞ on R^n | `dgpr_heat_extension_space_smooth` |
| Iterated coordinate derivatives of p_s and u_s: D_ν u_s(x) = ∫ D_ν p_s(x − y) f(y) dν y | `dgpr_heat_extension_iterated` |
| lem:heat_extension(1), every j: D^α u_s(x) = ∫ D^α p_s(x − y) f(y) dν y for every multi-index α | `dgpr_heat_extension_multi_partial` |
| lem:heat_extension(2), every j: ‖D^j u_s(x)‖ ≤ c s^{-j/2}(1 + (\|x\| + r)s^{-1/2})^j ∫ p_s(x − y)\|f(y)\| dν y | `dgpr_heat_extension_higher_bound` |

## Bounds (lem:heat_extension(2),(3)) and mass (lem:heat_extension(4))

`theories/DgprHeatExtensionBounds.v` and `theories/DgprHeatExtensionMass.v`.
`dgpr_heat_norm_extension s x` is the heat extension of the scalar function
‖f‖, that is, ∫ p_s(x − y)‖f(y)‖ dν y; `dgpr_heat_norm_integral` shows that
this integral exists, and `dgpr_norm_total_integral` that ∫ ‖f‖ dν exists.

| Statement | Declaration |
| --- | --- |
| lem:heat_extension(2), j = 0: ‖u_s(x)‖ ≤ ∫ p_s(x − y)‖f(y)‖ dν y | `dgpr_heat_extension_zero_bound` |
| lem:heat_extension(2), j = 1 with c(n,1) = 1/2: ‖Du_s(x)(v)‖ ≤ 2^{-1}s^{-1/2}(1 + (\|x\| + r)s^{-1/2}) ∫ p_s(x − y)‖f(y)‖ dν y · \|v\| | `dgpr_heat_extension_first_bound` |
| lem:heat_extension(2), j = 2 with c(n,2) = 1 | `dgpr_heat_extension_second_bound` |
| lem:heat_extension(3), first inequality, without integrability hypotheses | `dgpr_heat_extension_gauss_bound` |
| lem:heat_extension(4) for Z = R and f ≥ 0: ∫ u_s dL^n = ∫ f dν | `dgpr_heat_extension_mass` |

The mass identity follows the blueprint: Fubini's theorem 2.6.2 for
L^n × ν (`product_function_fubini`), the measurability of
[(x, y) ↦ p_s(x − y) f(y)] from that of open subsets of R^n × R^n
(`product_open_sets_measurable` with the countable base of R^n), the
translation invariance of L^n (`dgpr_translation_integral`) and
lem:kernel(1).

## Open items

- lem:heat_extension(1) is proved for the multi-index derivatives D^α
  (Federer 3.1.11, p. 223), which determine D^j u_s(x); the identity of
  j linear maps D^j u_s(x)(v_1, …, v_j) = ∫ D^j p_s(x − y)(v_1, …, v_j)
  f(y) dν y for arbitrary v_i is stated only for j ≤ 2.
- lem:heat_extension(4) for signed or vector-valued f.
- Bounds of the derivatives of order j in (t, x) on Ω_T, as used in
  lem:regularity, are not stated; the norms on R × R^n would require the
  transfer of `norm_higher_differential_finite_partial_bound` from R^{n+1}
  through `dgpr_time_space_map`.
