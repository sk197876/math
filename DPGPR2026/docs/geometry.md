# Geometric lemmas: tube estimate, inner approximation, dominated functionals

This account covers lem:tube (section "Entropy"), lem:inner (section "The
mass bound") and the first consequence of mr:functionals specialised to
distributions on R^n, in `blueprint/dgpr_blueprint.tex`. Euclidean space is
`inner_metric_space (@euclidean_inner_productP R n)`; L^n is
`euclidean_lebesgue_measure`, H^m is `hausdorff_measure`, the exponential is
`RealExponential.exponential` and π is `dgpr_pi` of
`theories/DgprHeatKernel.v`. Integrals are those of Federer 2.4.2
(`is_measure_integral`).

## The tube estimate (lem:tube)

`theories/DgprTubeEstimate.v`. Throughout, d is the distance function of a
set (`is_metric_set_distance E d`, Federer 2.2.10), k = n − m and
c(n) = 1 + 2 (4π)^(n/2), written `1 + 2 * Num.sqrt (4 * dgpr_pi R) ^+ n`.

| Statement | Declaration |
| --- | --- |
| Suppose 0 < m ≤ n, E ⊆ R^n compact and m rectifiable, H^m(E) > 0, d = dist(·, E). There is 0 < s_0 ≤ 1 such that g ≤ c(n) s^(k/2) H^m(E) whenever 0 < s < s_0 and g is the integral of [x ↦ exp(−d(x)^2/(4s))] | `dgpr_tube_estimate` |
| The function [x ↦ exp(−dist(x, E)^2/(4s))] is L^n summable for compact E and 0 < s, so γ_s exists | `dgpr_tube_summable` |
| Minkowski content (Federer 3.2.37, 3.2.39): if 0 < H^m(E) = h < ∞, there is e > 0 with L^n{d < r} < 2 h α(k) r^k for 0 < r < e | `dgpr_tube_minkowski` |
| Discrete layer sum Σ_(j<K) φ_j (1{t < ρ_(j+1)} − 1{t < ρ_j}) | `dgpr_layer_sum` |
| Its vanishing above ρ_K, upper and lower bounds on the layers | `dgpr_layer_sum_above`, `dgpr_layer_sum_upper`, `dgpr_layer_sum_lower` |
| Integral of the layer sum at a distance function (discrete (eq:tube:layer)) | `dgpr_layer_integral` |
| The layer integral in R^k for the distance from {0} is at most 2 (4π)^(k/2) s^(k/2) | `dgpr_layer_gaussian_bound` |
| Abel summation as an inequality | `dgpr_abel_le` |
| Continuity and L^n summability of [x ↦ exp(−d(x)^2/c)] | `dgpr_distance_gaussian_class`, `dgpr_distance_gaussian_summable` |
| Sublevel sets of distance functions; L^q{|y| < r} = α(q) r^q | `dgpr_distance_sublevel_measurable`, `dgpr_distance_sublevel0`, `dgpr_norm_distance`, `dgpr_norm_sublevel` |
| Scalar facts: exp(x) ≤ (1 − x)^(-1), exp(−a/s) ≤ ((N + 1)s/a)^(N+1), the square comparison, Lipschitz bound of exp on (−∞, 0] | `dgpr_exp_upper`, `dgpr_exp_decay`, `dgpr_shift_square`, `dgpr_exp_nonpos_lipschitz` |

The blueprint uses Fubini's theorem for (eq:tube:layer). The formalisation
replaces it by a discrete layer decomposition: with δ = (s/(2k + 1))^(1/2),
ρ_j = jδ and φ_j = exp(−ρ_j^2/(4s)), the integrand is at most the layer sum
at d(x) plus exp(−r_1^2/(128 s)) exp(−d(x)^2/8); the layer integral is
compared by Abel summation with 2 H^m(E) times the corresponding layer
integral in R^k, which is bounded by a Gaussian integral (Federer 3.2.13,
2.7.16). The constant obtained is the blueprint's c(n).

## Inner approximation (lem:inner)

`theories/DgprInnerApproximation.v`.

| Statement | Declaration |
| --- | --- |
| M ⊆ R^n Borel and countably (H^m, m) rectifiable, H^m(M) < ∞, θ H^m ⌞ M summable and nonnegative on M, μ = (H^m ⌞ M) ⌞ θ, 0 < ε: there is a compact m rectifiable E ⊆ M with μ(R^n ∖ E) < ε | `dgpr_inner_approximation` |
| The same for every measure μ over R^n with μ(R^n) < ∞, Borel sets μ measurable and μ(A) = 0 whenever H^m(M ∩ A) = 0 | `dgpr_inner_approximation_measure` |
| The closure of an m rectifiable set is compact and m rectifiable | `dgpr_rectifiable_closure_compact` |
| Finite unions of compact m rectifiable (closed) sets | `dgpr_prefix_compact_rectifiable`, `dgpr_prefix_closed` |

The measure (H^m ⌞ M) ⌞ θ is
`measure_with_density (measure_restrict H M) (real_total_integrand theta)`
(Federer 2.4.10).

## Dominated functionals on R^n (mr:functionals, first consequence)

`theories/DgprFunctionalsEuclidean.v`, built on `theories/DgprFunctionals.v`.
S is a distribution on R^n with values in a normed space Y with a finite
basis (`Hom (smooth_test_space hE) R^o` with `hE : is_smooth_function_space
hN hNY setT ev`), ν is a Radon measure over R^n, and the hypothesis is
S(φ) ≤ ∫^* |φ| dν for every test function φ (Federer 2.4.2). Federer's
variation measure ‖S‖ lives on the current domain `current_domain R n setT`;
ν is carried to it by `euclidean_full_domain_point`.

| Statement | Declaration |
| --- | --- |
| S is representable by integration (‖S‖(f) < ∞ for f ∈ K(R^n)^+) | `dgpr_dominated_finite_variation` |
| ‖S‖(A) ≤ ν({x : x ∈ A}) for every variation measure ‖S‖ of S (Federer 4.1.5) and every A | `dgpr_dominated_variation` |
| Existence of ‖S‖ and the normalised density, with ‖S‖(A) ≤ ν(A) | `dgpr_dominated_representation` |
| The image of ν on the current domain is a Radon measure; integrals and inverse images under the identification | `dgpr_full_domain_measure_laws`, `dgpr_full_domain_integral`, `dgpr_full_domain_preimage` |
| ‖S‖(f) ≤ ∫ f dν from the pointwise bound of the gauge | `dgpr_dominated_gauge_bound` |
