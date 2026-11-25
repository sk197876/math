# Heated objects, identities and heat operators (blueprint section 4)

This account covers mr:standing (the hypotheses (S)), def:heat_objects,
lem:identities, lem:heat_calculus, lem:regularity, lem:DGPR31 and
lem:DGPR32 of `blueprint/dgpr_blueprint.tex`, that is, section 3 of De
Philippis, Gennaioli, Pigati and Rindler (2026) up to Lemma 3.2.
Integrals are those of Federer 2.4.2 and, for vector-valued functions,
2.4.12; differentials are those of Federer 3.1.1; class ∞ is Federer's
class of 3.1.11 on the open set Ω_T = {(t, x) : t < T} of R × R^n, with
the product inner product of Federer 1.7.11
(`norm_class_all_orders hNT _ (dgpr_before T) _`).

## The hypotheses (S)

`theories/DgprStanding.v`. The hypotheses are the record
`dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma`
(a predicate of the data). The parameters are the following.

| Blueprint | Formalisation |
| --- | --- |
| n, m with 1 ≤ m ≤ n | `n`, `m`, `hm : (0 < m <= n)%N` |
| Y with its inner product | `Y : lmodType R`, `CY`, `hCY : is_inner_product CY`, basis `eY : 'I_d -> Y` |
| Hom(R^n, Y) with A • B = trace(A* ∘ B) and norm \|A\| | `hom_inner_productP BX hCY heX` and `hom_norm BX hCY heX` (Federer 1.7.9) |
| Hom(Y, R) with the norm ‖ψ‖ | `hom_inner_productP hCY (scalar_inner_productP R) heY` and its norm; for covectors this norm is the operator norm |
| K, λ, Λ | `K`, `lam`, `Lam`, with the fields `_K_nonempty`, `_K_compact`, `_K_convex`, `_K_sv`, `_K_norm` |
| μ, r_0 | `mu`, `r0`, with `_mu_measure`, `_mu_borel`, `_mu_mass`, `_r0`, `_mu_support` |
| X : R^n → K, μ measurable | `Xf`, with `_X_measurable` and `_X_values` |
| Υ ∈ D'(R^n, Y) | `Ups : Hom (smooth_test_space hE) R^o` for a space `hE` of smooth functions R^n → Y (Federer 4.1.1) |
| Υ(g) = −σ(Dg) | `_constraint`: for every test function g with differentials Dg, the map X • Dg is μ summable with integral −Υ(g) |
| ‖Υ‖, δ | `ups`, a Radon measure (`_ups_measure`, `_ups_radon`) whose integrals of nonnegative continuous functions with compact support are the values of the variation of Federer 4.1.5 (`_ups_gauge`); `_ups_mass : ups setT = delta%:E` |
| dΥ with ‖dΥ(z)‖ ≤ 1 | `dups`, with `_dups_measurable`, `_dups_bound` and `_dups_action`: Υ(g) = ∫ ⟨g(z), dΥ(z)⟩ d‖Υ‖ z |
| T, μ_0, γ | `T`, `mu0`, `gamma`, with `_T`, `_mu0_measure`, `_mu0_borel`, `_mu0_le`, `_mu0_mass`, `_gamma` |

The functional σ is not a separate object. Hom(R^n, Y) and Hom(Y, R) are
complete and separable (`dgpr_hom_space_complete`,
`dgpr_hom_space_separable`, `dgpr_dual_space_complete`,
`dgpr_dual_space_separable`); this is needed for the vector integrals
defining W and Ψ.

## Jets and heat operators

`theories/DgprHeatJets.v`, `theories/DgprBackwardHeat.v`,
`theories/DgprHeatJetCalculus.v`. Differentials of maps f : R × R^n → Z
enter through their values. The relation
`dgpr_heat_jet NZ f t x a Df D2` states that a is the derivative of
[r ↦ f(r, x)] at t, that `Df y` gives the values of D f_t(y) for every y,
and that `D2 v w` is the differential at x of [y ↦ Df y w] applied to v,
that is D²f_t(x)(v, w). Then H f(t, x) = h and H_ζ f(t, x) = h are the
relations `dgpr_heat_operator NZ f t x h` and
`dgpr_heat_Hzeta hS NZ f t x h`, with Δ f_t(x) the sum over the standard
basis of D² f_t(x)(ε_i, ε_i). The gradient of a real function with
differential values l is `dgpr_gradient_values l`, the sum of
l(ε_i) ε_i.

For a heat extension u of (ν, f) (def:heat) the map
`dgpr_backward_heat hnu hZ f T` is [(t, x) ↦ u(T − t, x)]. Its jet at
(t, x) ∈ Ω_T is `dgpr_backward_heat_jet`, and H of it vanishes
(`dgpr_backward_heat_operator`). The jet calculus provides sums, scalar
multiples, products with real maps, inner squares and compositions with
real functions of class 2 (`dgpr_heat_jet_add`, `_scale`,
`_scalar_product`, `_inner_square`, `_compose`).

## Heated objects (def:heat_objects)

`theories/DgprHeatObjects.v`. Every object takes the hypothesis
`hS : dgpr_standing …` as its first explicit argument.

| Object | Declaration |
| --- | --- |
| U, W, R, Ψ, ρ | `dgpr_heat_U`, `dgpr_heat_W`, `dgpr_heat_R`, `dgpr_heat_Psi`, `dgpr_heat_rho` (backward heat extensions of (μ, 1), (μ, X), (‖Υ‖, 1), (‖Υ‖, dΥ), (μ_0, 1)) |
| S = U + (T − t)^{1/2} R | `dgpr_heat_S` |
| B = S^{−1} W, η = S^{−1} Ψ | `dgpr_heat_B`, `dgpr_heat_eta` |
| κ = R / (2 (T − t)^{1/2} S), q = ρ / S | `dgpr_heat_kappa`, `dgpr_heat_q` |
| D S_t(y)(v) | `dgpr_heat_S_first hS t y v` |
| ζ = grad log S_t | `dgpr_heat_zeta`, equal to S^{−1} times the gradient of the values `dgpr_heat_S_first` |
| grad log ρ_t | `dgpr_heat_grad_log_rho` |
| I(ρ_t) | `dgpr_fisher_information`, the upper integral (Federer 2.4.2) of ρ_t \|grad log ρ_t\|² over L^n |
| H_ζ | `dgpr_heat_Hzeta` |

The objects are total functions; the blueprint's restriction to Ω_T and
to the set where S > 0 and ρ > 0 appears in the hypotheses t < T of the
statements below.

## Identities (lem:identities)

`theories/DgprIdentities.v`, `theories/DgprHeatCalculus.v`,
`theories/DgprIdentitiesDivergence.v`, `theories/DgprIdentitiesSmooth.v`.
Unless stated otherwise, t < T.

| Statement | Declaration |
| --- | --- |
| (spt) ‖Υ‖(R^n ∖ B(0, r_0)) = 0 | `dgpr_identities_spt` |
| (div) U, W, R, Ψ, S, ρ are of class ∞ on Ω_T | `dgpr_identities_smooth_extensions`, `dgpr_identities_smooth_S` |
| (div) ⟨y, div W_t(x)⟩ = ⟨y, Ψ(t, x)⟩ and ‖Ψ(t, x)‖ ≤ R(t, x) | `dgpr_identities_div_W`, `dgpr_identities_div` |
| (div) all of the above | `dgpr_identities_div_smooth` |
| (heat) H U = H W = H R = H Ψ = H ρ = 0 and H S = −κ S | `dgpr_identities_heat` (with `dgpr_identities_heat_extensions`, `dgpr_identities_heat_S`) |
| (mass) ∫ U_t = 1, ∫ R_t = δ, ∫ S_t = 1 + (T − t)^{1/2} δ, ∫ ρ_t = γ | `dgpr_identities_mass` |
| (bounds) 0 < ρ, U ≤ S, κ ≥ 0, U^{−1} W ∈ K, \|B\| ≤ Λ, ‖η‖ ≤ (T − t)^{−1/2} | `dgpr_identities_bounds` |
| (bounds) ρ ≤ U, and all of (bounds) | `dgpr_identities_rho_le_U`, `dgpr_identities_bounds_full` |
| (divB) ⟨y, div B_t(x)⟩ + B(t, x)(ζ(t, x)) • y = ⟨y, η(t, x)⟩ | `dgpr_identities_divB` |
| (sv) U ≥ (T − t)^{1/2} R implies sv_m(B) ≥ λ/2 | `dgpr_identities_sv` |

The covector div W_t(x) ∈ Hom(Y, R) is given by its values: for the
values l of D W_t(x), ⟨y, div W_t(x)⟩ is the sum of
l(ε_i)(ε_i) • y. The same convention is used for div B_t(x). No vector
is identified with a covector.

The barycentre statement U^{−1} W ∈ K (`dgpr_identities_barycentre`) is
proved with the measure μ ⌞ [y ↦ p_{T−t}(x − y)] of Federer 2.4.10 and
lem:barycentre; the vector integral of X with respect to that measure is
identified with W(t, x) through continuous linear functionals.

The proof of (div) chooses the test function g of
`dgpr_heat_kernel_test` (`theories/DgprHeatTestFunction.v`), equal to
[z ↦ p_{T−t}(x − z) y] on an open set containing B(0, r_0), instead of
φ g with a cut-off φ.

## Heat operators (lem:heat_calculus)

`theories/DgprHeatCalculus.v`. Unless stated otherwise, t < T.

| Statement | Declaration |
| --- | --- |
| (S) H(S f) = S H_ζ f − κ S f | `dgpr_heat_calculus_S` |
| (product) H_ζ(g f) = g H_ζ f + (H_ζ g) f + 2 D f_t(x)(grad g_t(x)) | `dgpr_heat_calculus_product` |
| (square) H_ζ \|f\|² = 2 f • H_ζ f + 2 \|D f_t(x)\|² | `dgpr_heat_calculus_square` |
| (chain) H_ζ(Φ ∘ φ) = (Φ' ∘ φ) H_ζ φ + (Φ'' ∘ φ) \|grad φ_t(x)\|² | `dgpr_heat_calculus_chain` |
| (Bq) H_ζ B = κ B and H_ζ q = κ q | `dgpr_heat_calculus_Bq` |

The jets of the maps f, g and φ are hypotheses of the statements, in the
form H_ζ f(t, x) = h together with the values of D f_t(x); the
conclusions are the relations H_ζ(…)(t, x) = (…). In (square) the norm
\|D f_t(x)\|² is the sum of \|D f_t(x)(ε_i)\|². In (chain) the derivatives
Φ' and Φ'' are given functions with the derivative relations on
(0, ∞). The auxiliary `dgpr_heat_calculus_ratio` gives
H_ζ(S^{−1} F) = κ S^{−1} F whenever H F = 0.

## Regularity (lem:regularity)

`theories/DgprIdentitiesSmooth.v`, `theories/DgprBackwardHeatDecay.v`,
`theories/DgprRegularityWeights.v`, `theories/DgprRegularity.v`.

| Statement | Declaration |
| --- | --- |
| The logarithm is of class ∞ on {r : 0 < r} | `dgpr_logarithm_norm_class` |
| [(t, x) ↦ (T − t)^{1/2}] is of class ∞ on Ω_T | `dgpr_sqrt_time_to_go_class` |
| S^{−1} is of class ∞ on Ω_T | `dgpr_heat_S_inverse_smooth` |
| B, η, κ, q are of class ∞ on Ω_T | `dgpr_regularity_smooth` |
| log S, log ρ, log q are of class ∞ on Ω_T | `dgpr_regularity_log_smooth` |
| joint bounds ‖D^j F(t, x)‖ ≤ c (1 + \|x\|)^K u_ν(T − t, x) on time strips, for a backward heat extension F of (ν, f) | `dgpr_backward_heat_joint_bound` |
| Gaussian decay before T of a backward heat extension | `dgpr_backward_heat_gaussian_decay` |
| U, W, R, Ψ, ρ have Gaussian decay before T | `dgpr_regularity_gaussian_extensions` |
| S has Gaussian decay before T | `dgpr_regularity_S_gaussian` |
| B, η, κ, q have polynomial growth before T | `dgpr_regularity_polynomial` |
| log S, log ρ, log q have polynomial growth before T | `dgpr_regularity_log_polynomial` |
| ρ log q and ρ \|B\|² have Gaussian decay before T | `dgpr_regularity_entropy_gaussian`, `dgpr_regularity_B2_gaussian` |

## Lemma 3.1 (lem:DGPR31)

`theories/DgprLemma31.v` (pointwise identities),
`theories/DgprHeatIntegral.v`, `theories/DgprLemma31Main.v` (estimates at
a fixed time), `theories/DgprTimeIntegrals.v`,
`theories/DgprEntropyBound.v` (real analysis on [0, T)),
`theories/DgprLemma31Final.v` (the lemma given the Gaussian decay),
`theories/DgprLemma31Field.v` (the field DB),
`theories/DgprLemma31Theorem.v` (the lemma under (S)). Unless stated
otherwise, t < T.

| Statement | Declaration |
| --- | --- |
| H(ρ log q) = κρ + ρ \|grad log q\|² | `dgpr_lemma31_heat_entropy` |
| H(ρ \|B\|²) = 2ρ \|DB\|² + 4ρ B • DB(grad log q) + 2κρ \|B\|² | `dgpr_lemma31_heat_B2` |
| grad log ρ = ζ + grad log q | `dgpr_lemma31_grad_log_rho` |
| \|B(ζ)\| ≤ ‖η‖ + Σ_i \|DB(ε_i)\| | `dgpr_lemma31_B_zeta_bound` |
| \|B(grad log ρ)\|² ≤ 4‖η‖² + 4n \|DB\|² + 2Λ² \|grad log q\|² | `dgpr_lemma31_B_gradient_bound` |
| ρ‖η‖² ≤ min{(T − t)^{−1} ρ, (T − t)^{−1/2} R} | `dgpr_lemma31_eta_pointwise` |
| the sections of f and of h = H f are summable, and [t ↦ ∫ f_t] is of class 1 with derivative [t ↦ ∫ h_t], for f of Gaussian decay before T | `dgpr_heat_integral` |
| ρ \|DB\|² ≤ H(ρ \|B\|²) + 4Λ² ρ \|grad log q\|² | `dgpr_lemma31_DB_bound` |
| bound of the integrand at a fixed time | `dgpr_lemma31_integrand_bound`, `dgpr_lemma31_time_slice` |
| 0 ≤ ∫ ρ_t \|B_t\|² ≤ Λ² γ | `dgpr_lemma31_K_bound` |
| (eq:31:J) γ log(γ / (1 + (T − t)^{1/2} δ)) ≤ ∫ ρ_t log q_t ≤ 0 | `dgpr_lemma31_entropy_bounds`, `dgpr_entropy_jensen` |
| (eq:31:min) ∫_0^τ m ≤ 4γ log(1 + T^{1/2} δ / γ) | `dgpr_time_min_integral` |
| fundamental theorem of calculus on [a, b] ⊂ (−∞, T) | `dgpr_before_ftc` |
| upper integral over [0, T) from bounds on [0, τ] | `dgpr_before_upper_integral` |
| a majorant g of the inner integral with ∫_0^τ g ≤ Cγ(1 + log((1 + T^{1/2}δ)/γ)) | `dgpr_lemma31_majorant` |
| Lemma 3.1, with C = (16n + 6)Λ² + 16, given the Gaussian decay of ρ log q and ρ \|B\|² | `dgpr_lemma_3_1_conditional` |
| Lemma 3.1 under (S) | `dgpr_lemma_3_1` |
| a field DB with the values of D B_t(x) exists | `dgpr_lemma31_DB_exists` |

The integrand ρ_t(\|DB_t\|² + \|B_t(grad log ρ_t)\|²) is
`dgpr_lemma31_integrand hS DB`, for a field DB with the values of
D B_t(x) (hypothesis `hDB`). Such a field exists
(`dgpr_lemma31_DB_exists`, `theories/DgprLemma31Field.v`): for t < T
the section [x ↦ B(t, x)] has the differential D B(t, x) ∘ i at x, where
i(x) = (0, x) (`dgpr_slice_differential`). The Gaussian decay before T of ρ log q and
ρ \|B\|² are the hypotheses `hJgauss` and `hKgauss` of
`dgpr_lemma_3_1_conditional`; lem:regularity discharges them in
`dgpr_lemma_3_1` (`theories/DgprLemma31Theorem.v`).

## Lemma 3.2 (lem:DGPR32)

`theories/DgprLemma32Spectral.v` (χ and Q = χ^(X* ∘ X)),
`theories/DgprLemma32Calculus.v` (integrals, columns, divergence),
`theories/DgprLemma32Pointwise.v` (eq:32:I at a fixed time),
`theories/DgprLemma32Final.v` (integration of eq:32:I over [0, τ]),
`theories/DgprLemma32Theorem.v` (regularity at time t and the lemma
under (S)).

| Statement | Declaration |
| --- | --- |
| χ(a)² ≤ χ(a) ≤ 16a/(3λ²) for a ≥ 0, Lip(χ) = 16/(3λ²) (eq:32:chi) | `dgpr_chi_le`, `dgpr_chi_sqr_le`, `dgpr_chi_lipschitz` |
| \|Q(w)\|² ≤ 16/(3λ²) \|X(w)\|² (eq:32:QB) and ‖Q‖ ≤ 1 | `dgpr_Q_image`, `dgpr_Q_operator_norm` |
| sv_m(X) ≥ λ/2 implies \|Q\|² ≥ m | `dgpr_Q_hom_norm_lower` |
| \|Q(X) − Q(X')\| ≤ Lip(χ)(\|X\| + \|X'\|)\|X − X'\| | `dgpr_Q_lipschitz` |
| C_1 = (2n + 1)(32Λ/(3λ²))² + 32/(3λ²) > 0 | `dgpr_lemma32_C1`, `dgpr_lemma32_C1_gt0` |
| eq:32:I at a fixed time t < T | `dgpr_lemma32_fixed_time` |
| the section at time t of a map of polynomial growth before T has polynomial growth | `dgpr_slice_polynomial` |
| a map of polynomial growth is Lipschitzian on {y : \|y − x\| ≤ 1} with a constant c(1 + \|x\|)^c | `dgpr_polynomial_local_lipschitz` |
| D log ρ_t has polynomial growth; B_t is locally Lipschitzian of polynomial growth | `dgpr_lemma32_log_rho_growth`, `dgpr_lemma32_B_lipschitz` |
| φ ≤ g on [a, b] and ∫_a^b g = G imply that the upper integral of φ over [a, b] is at most G | `dgpr_segment_upper_integral_le` |
| log(1 + T^{1/2}δ/γ) ≤ log((1 + T^{1/2}δ)/γ) | `dgpr_lemma32_log_bound` |
| Lemma 3.2 from eq:32:I with a constant C_1 ≥ 0, with the constant 2n + C_1((16n + 6)Λ² + 16) | `dgpr_lemma_3_2_conditional` |
| Lemma 3.2 under (S), with C_1 as above | `dgpr_lemma_3_2` |

The integral over [0, τ] is Federer's upper integral over the segment
(2.4.10), `measure_subset_upper_integral L1 `[0, τ]`, of
[t ↦ I(ρ_t) − (n − m)γ/(2(T − t))], with values in the extended real
line. The field DB is that of `dgpr_lemma_3_1`.
