# Classes of maps and integration by parts (blueprint section 3)

This account covers def:classes, lem:classes and lem:ibp of
`blueprint/dgpr_blueprint.tex`, that is, the regularity classes and the
integration by parts identity (3.17) of De Philippis, Gennaioli, Pigati and
Rindler (2026). Differentials are those of Federer 3.1.1
(`has_norm_differential`); the jth differential is Federer's 3.1.11
(`has_norm_higher_differential`) with values in the sealed spaces
`ContinuousMultilinear.space` of continuous j linear maps, normed by the
corrected norm of 3.1.11 (erratum to p. 219). Integrals are Federer's
(`is_measure_integral`, 2.4.2) with respect to `euclidean_lebesgue_measure`,
and vector integrals are those of 2.4.12. Time-space R × R^n carries the
product inner product of Federer 1.7.11.

## def:classes

`theories/DgprGrowthClasses.v`.

| Statement | Declaration |
| --- | --- |
| Polynomial weight c(1 + r)^c | `dgpr_polynomial_weight` |
| Gaussian weight c exp(−r²/c) | `dgpr_gaussian_weight` |
| D^j f(x) = z | `dgpr_higher_differential` |
| ‖D^j f(x)‖ ≤ w(x) for x in S | `dgpr_derivative_bounded` |
| Polynomial growth on R^n | `dgpr_polynomial_growth` |
| Gaussian decay on R^n | `dgpr_gaussian_decay` |
| Ω_T and the strips J × R^n | `dgpr_before`, `dgpr_time_strip` |
| Polynomial growth before T | `dgpr_polynomial_growth_before` |
| Gaussian decay before T | `dgpr_gaussian_decay_before` |
| Gaussian decay implies polynomial growth | `dgpr_gaussian_decay_polynomial_growth`, `dgpr_gaussian_decay_before_polynomial_growth_before` |
| Locally Lipschitzian map of polynomial growth | `dgpr_lipschitz_polynomial_growth` |

The weight inequalities used later (products and sums of weights, and
(1 + r)^c exp(−r²/c') ≤ c'' exp(−r²/c'')) are the lemmas
`dgpr_polynomial_weight_product`, `dgpr_polynomial_weight_sum`,
`dgpr_gaussian_weight_sum` and `dgpr_polynomial_gaussian_weight_product`.

## lem:classes

| Statement | Declaration | File |
| --- | --- | --- |
| Weighted Leibniz estimate for D^k β(f₁, f₂) (Federer 3.1.11) | `dgpr_bilinear_weighted_derivative` | `DgprWeightedBilinear.v` |
| (cl:product) on R^n, polynomial growth | `dgpr_classes_product_polynomial` | `DgprClassesProduct.v` |
| (cl:product) on R^n, Gaussian decay | `dgpr_classes_product_gaussian` | `DgprClassesProduct.v` |
| (cl:product) before T, both classes | `dgpr_classes_product_polynomial_before`, `dgpr_classes_product_gaussian_before`, `dgpr_classes_product` | `DgprClassesProduct.v` |
| (cl:dt) | `dgpr_classes_dt` | `DgprClassesTimeDerivative.v` |
| (cl:div), ∫ div g dL^n = 0 | `dgpr_classes_div` | `DgprDivergenceIntegral.v` |
| (cl:div), ∫ Δf dL^n = 0 | `dgpr_classes_laplacian` | `DgprDivergenceIntegral.v` |
| ∫ Dφ(x)(v) dL^n x = 0 for one direction | `dgpr_directional_integral`, `dgpr_directional_integral_values` | `DgprDivergenceIntegral.v`, `DgprIntegrationByParts.v` |
| div g(x) = trace Dg(x) and Δf(x) = trace D²f(x) | `dgpr_divergence`, `dgpr_divergenceE`, `dgpr_laplacian` | `DgprDivergenceIntegral.v` |

The principal statements are as follows.

- `dgpr_classes_product T f1 f2`: if β is a bounded bilinear map
  (`norm_bounded_bilinear N1 N2 N3 beta`) and f₁, f₂ have polynomial growth
  before T, then so has [p ↦ β(f₁(p), f₂(p))]; if moreover f₂ has Gaussian
  decay before T, then so has this map.
- `dgpr_classes_dt T f Df`: if f : Ω_T → R has Gaussian decay before T and
  Df(p) is the differential of f at p ∈ Ω_T, then for t < T the maps
  [x ↦ f(t, x)] and [x ↦ Df(t, x)(1, 0)] are L^n summable; and whenever
  I(t) and DI(t) are their integrals for t < T, the map I is of class 1 on
  R ∩ {t : t < T} with derivative [s ↦ s DI(t)] at t
  (`is_norm_class_one_field`).
- `dgpr_classes_div g Dg c`: if 0 < c, Dg(x) is the differential of g at
  every x, and |g(x)| + L ≤ c exp(−|x|²/c) for some L ≥ 0 with
  |Dg(x)(v)| ≤ L|v| for all v, then ∫ trace Dg(x) dL^n x = 0.
- `dgpr_classes_laplacian f D2`: if f : R^n → R has Gaussian decay and
  D2(x) = D²f(x) for every x, then ∫ Σ_i D²f(x)(ε_i, ε_i) dL^n x = 0.

Supporting facts on Lebesgue integrals are in `DgprLebesgueIntegrals.v`:
summability of Gaussian weights (Federer 3.2.13 and 2.10.27),
`dgpr_gaussian_weight_summable`; summability of dominated measurable
functions, `dgpr_dominated_summable`; measurability of continuous functions
and of pointwise limits, `dgpr_continuous_measurable`,
`dgpr_limit_measurable`; translation invariance (2.7.16),
`dgpr_translation_integral`.

## lem:ibp

| Statement | Declaration | File |
| --- | --- | --- |
| Differentials given by their values; sums, products, coordinates, postcomposition | `dgpr_differential_values`, `dgpr_values_add`, `dgpr_values_sum`, `dgpr_values_scalar_product`, `dgpr_values_coordinate`, `dgpr_values_postcompose` | `DgprDifferentialCalculus.v` |
| `D[x ↦ A(x)(u(x))](a)(v) = DA(a)(v)(u(a)) + A(a)(Du(a)(v))` | `dgpr_values_evaluation` | `DgprDifferentialCalculus.v` |
| Powers of polynomial weights absorbed by a Gaussian weight | `dgpr_gaussian_absorbs` | `DgprIntegrationByParts.v` |
| (3.17), first case of the proof | `dgpr_ibp_smooth` | `DgprIntegrationByParts.v` |
| Class ∞ hypotheses on ρ to the fields H1, H2 | `dgpr_log_derivative_polynomial_growth`, `dgpr_log_density_fields` | `DgprIntegrationByPartsClasses.v` |
| Class ∞ e with e, De, D²e of polynomial growth to the fields De, E2 | `dgpr_second_order_polynomial_growth`, `dgpr_second_order_fields` | `DgprIntegrationByPartsClasses.v` |
| (3.17), first case, with the class ∞ hypotheses of the blueprint | `dgpr_ibp_smooth_classes` | `DgprIntegrationByPartsClasses.v` |
| Smoothings e_ε = Φ_ε ∗ e of a locally Lipschitzian e (Federer 4.1.2) and their bounds | `dgpr_smoothing_exists`, `dgpr_smoothing_smooth`, `dgpr_smoothing_value_bound`, `dgpr_smoothing_distance`, `dgpr_smoothing_differential_bound`, `dgpr_smoothing_second_bound` | `DgprLipschitzSmoothing.v` |
| Lipschitzian extension of e from B(0, r) | `dgpr_ball_extension` | `DgprLipschitzSmoothing.v` |
| e is differentiable at L^n almost all points (Federer 3.1.6 on balls) | `dgpr_lipschitz_differentiable_ae` | `DgprLipschitzSmoothing.v` |
| De_ε(x)(v) → De(x)(v) for L^n almost all x (Federer 4.1.2, 2.9.9) | `dgpr_smoothing_differential_ae` | `DgprLipschitzSmoothing.v` |
| Bounded convergence for two sequences of integrands with common integrals (Federer 2.4.9) | `dgpr_almost_dominated_limit` | `DgprIntegrationByPartsGeneral.v` |
| (3.17) for ρ given by first-order fields and locally Lipschitzian e | `dgpr_ibp_fields` | `DgprIntegrationByPartsGeneral.v` |
| lem:ibp | `dgpr_ibp` | `DgprIntegrationByPartsGeneral.v` |

`dgpr_ibp_smooth rho H1 H2 e De E2 c` assumes 0 < c, 0 < ρ(x) ≤
c exp(−|x|²/c), Dρ(x)(v) = ρ(x) H1(x)(v) (that is, H1 = D log ρ), that
[y ↦ H1(y)(w)] has differential [v ↦ H2(x)(v)(w)] at x, that De(x) is the
differential of e at x and [y ↦ De(y)(w)] has differential
[v ↦ E2(x)(v)(w)] at x, that E2(x) is symmetric, that
[x ↦ H2(x)(v)(w)] is continuous, and that |e(x)|, ‖De(x)‖, ‖E2(x)‖,
‖H1(x)‖ and ‖H2(x)‖ are bounded by c(1 + |x|)^c. It concludes that there is
a number a such that a is the integral of [x ↦ −ρ(x) H2(x)(e(x))(e(x))] and
of [x ↦ ρ(x)((trace De(x) + H1(x)(e(x)))² − trace(De(x) ∘ De(x)))].

The proof follows the blueprint: lem:classes(cl:div) is applied, coordinate
by coordinate, to b ρ e and ρ De(e), where b = div e + Dh(e), and the
difference of the two divergences is computed pointwise.

`dgpr_ibp_smooth_classes rho e Dh D2h De` assumes the hypotheses of the
first case of the blueprint proof: ρ has Gaussian decay
(`dgpr_gaussian_decay`), 0 < ρ(x), D log ρ has polynomial growth
(`dgpr_log_derivative_polynomial_growth`: log ∘ ρ is of class ∞ and for
each j ≥ 1 there is c with ‖D^j log ρ(x)‖ ≤ c(1 + |x|)^c), and e is of
class ∞ with ‖D^j e(x)‖ ≤ c(1 + |x|)^c for j ≤ 2
(`dgpr_second_order_polynomial_growth`). For any fields with Dh(x) =
D log ρ(x), D2h(x) = D² log ρ(x) and De(x) = De(x), it concludes that both
sides of (3.17) are integrals with a common value. The bridge lemmas
`dgpr_log_density_fields` and `dgpr_second_order_fields` produce the
first-order fields of `dgpr_ibp_smooth`: Dρ = ρ D log ρ by the chain rule
(Federer 3.1.1(3)) and the derivative of log, and the symmetry of D²e and
D² log ρ by Federer 3.1.11.

`dgpr_ibp rho e Dh D2h` is lem:ibp. It assumes that ρ has Gaussian decay,
0 < ρ(x), D log ρ has polynomial growth, e is a locally Lipschitzian map of
polynomial growth (`dgpr_lipschitz_polynomial_growth`), and Dh, D2h are as
above. It concludes that e is differentiable at L^n almost all points and
that, for every field De such that De(x) is the differential of e at L^n
almost all x, there is a number a which is the integral of
[x ↦ −ρ(x) D² log ρ(x)(e(x), e(x))] and of
[x ↦ ρ(x)((trace De(x) + D log ρ(x)(e(x)))² − trace(De(x) ∘ De(x)))].
The intermediate theorem `dgpr_ibp_fields rho H1 H2 e De c` has the
hypotheses of `dgpr_ibp_smooth` on ρ, H1 and H2, and the hypotheses of
lem:ibp on e and De.

The proof of `dgpr_ibp_fields` follows the general case of the blueprint
proof. For ε = 1/(k + 2) the smoothing e_ε = Φ_ε ∗ e of Federer 4.1.2 is
of class ∞ (`dgpr_smoothing_smooth`), with |e_ε(x)| and ‖De_ε(x)‖ bounded
by c(2 + |x|)^c for 0 < ε ≤ 1 and ‖D²e_ε(x)‖ bounded by C(ε) c(2 + |x|)^c.
Hence `dgpr_ibp_smooth` applies to e_ε, with a common value a_k of the two
integrals. Moreover e_ε(x) → e(x) for every x, and De_ε(x) → De(x) for
L^n almost all x; the integrands are dominated by one Gaussian weight
(`dgpr_gaussian_absorbs`), so Lebesgue's bounded convergence theorem
(Federer 2.4.9, `measure_bounded_convergence` and
`real_dominated_integral_limit`) gives the conclusion
(`dgpr_almost_dominated_limit`). The almost everywhere statements are
proved by localisation: e agrees on B(0, k + 1) with the Lipschitzian map
e ∘ P_k, P_k a nonexpanding retraction of R^n onto B(0, k + 1)
(`dgpr_ball_extension`); Rademacher's theorem (Federer 3.1.6,
`federer_3_1_6`) and the convergence of the differentials of smoothings of
Lipschitzian maps (`current_lipschitz_lebesgue_action_smoothing_direction_ae`,
from Federer 4.1.2 and 2.9.9) apply to e ∘ P_k, and the smoothings of e and
of e ∘ P_k agree near x for small ε.

## Open items

- lem:classes(cl:dt) for f with values in a finite dimensional normed
  space; only real-valued f is formalised (`dgpr_classes_dt`).
