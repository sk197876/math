# Entropy, entropy bounds and the mass bound (blueprint sections 4 and 5)

This account covers def:entropy, lem:entropy, lem:upper_entropy and
lem:lower_entropy of `blueprint/dgpr_blueprint.tex`, that is, section 4 of
De Philippis, Gennaioli, Pigati and Rindler (2026), and lem:compact_case
of section 5, first for normalised data and then for the data of
mr:hypotheses_main, together with the dual density of mr:functionals
that the latter needs. The hypotheses (S) are the
record `dgpr_standing` of [DgprStanding.v](../theories/DgprStanding.v)
(docs/heat-objects.md); ρ is `dgpr_heat_rho hS`, I(ρ_t) is
`dgpr_fisher_information hS t`, L^n is `euclidean_lebesgue_measure` and
L^1 is `lebesgue_scalar_measure`. Logarithm and exponential are those of
Federer's `RealExponential`. The lemma lem:tube is
`dgpr_tube_estimate` of [DgprTubeEstimate.v](../theories/DgprTubeEstimate.v),
and lem:inner is `dgpr_inner_approximation` of
[DgprInnerApproximation.v](../theories/DgprInnerApproximation.v).

| Blueprint | Formalisation | File |
| --- | --- | --- |
| def:entropy, H(ρ_t) and H̃(ρ_t) | `dgpr_entropy`, `dgpr_entropy_tilde` | [DgprEntropy.v](../theories/DgprEntropy.v) |
| proof of lem:entropy: H(ρ log ρ) = ρ \|grad log ρ\|² on Ω_T | `dgpr_entropy_heat` | [DgprEntropy.v](../theories/DgprEntropy.v) |
| proof of lem:entropy: ρ log ρ has Gaussian decay before T | `dgpr_entropy_gaussian` | [DgprEntropy.v](../theories/DgprEntropy.v) |
| lem:entropy, first assertion | `dgpr_entropy_derivative` | [DgprEntropy.v](../theories/DgprEntropy.v) |
| lem:entropy, second assertion | `dgpr_entropy_initial_bound` | [DgprEntropy.v](../theories/DgprEntropy.v) |
| lem:upper_entropy | `dgpr_upper_entropy`, with the constant `dgpr_upper_entropy_constant` | [DgprUpperEntropy.v](../theories/DgprUpperEntropy.v) |
| lem:upper_entropy, for any constant C0 satisfying the conclusion of lem:DGPR32 | `dgpr_upper_entropy_of` | [DgprUpperEntropy.v](../theories/DgprUpperEntropy.v) |
| lem:upper_entropy with the constant of `dgpr_lemma_3_2_conditional` | `dgpr_upper_entropy_conditional` | [DgprUpperEntropy.v](../theories/DgprUpperEntropy.v) |
| lem:lower_entropy | `dgpr_lower_entropy` | [DgprLowerEntropy.v](../theories/DgprLowerEntropy.v) |
| proof of lem:compact_case: (S) for every 0 < T and for μ_0 = μ ⌞ E | `dgpr_standing_time`, `dgpr_standing_restrict` | [DgprCompactCase.v](../theories/DgprCompactCase.v) |
| proof of lem:compact_case, (eq:cc:main) | `dgpr_compact_case_entropy` | [DgprCompactCase.v](../theories/DgprCompactCase.v) |
| lem:compact_case for normalised data, for a constant C0 of lem:upper_entropy | `dgpr_compact_case_normalised` | [DgprCompactCase.v](../theories/DgprCompactCase.v) |
| lem:compact_case for normalised data | `dgpr_compact_case_standing` | [DgprCompactCase.v](../theories/DgprCompactCase.v) |
| mr:functionals, first paragraph: the dual density dΥ of ‖Υ‖ | `dgpr_dual_density` | [DgprDualDensity.v](../theories/DgprDualDensity.v) |
| proof of `dgpr_dual_density`: ‖Υ‖(f) < ∞ for f ∈ K(R^n)^+ | `dgpr_ups_finite_variation` | [DgprDualDensity.v](../theories/DgprDualDensity.v) |
| proof of `dgpr_dual_density`: the norm and the measurability of a covector field | `dgpr_covector_norm_le`, `dgpr_covector_expansion`, `dgpr_dual_field_measurable` | [DgprDualDensity.v](../theories/DgprDualDensity.v) |
| proof of `dgpr_dual_density`: the image of a measure under the inclusion of the current domain of R^n | `dgpr_value_pushforward_measurable`, `dgpr_value_pushforward_measurable_function`, `dgpr_value_pushforward_integral`, `dgpr_value_pushforward_radon` | [DgprDualDensity.v](../theories/DgprDualDensity.v) |
| proof of lem:compact_case: the measure μ of mr:hypotheses_main | `dgpr_main_measure_is_measure`, `dgpr_main_measure_null`, `dgpr_main_measure_on`, `dgpr_main_measure_measurable`, `dgpr_main_measure_open`, `dgpr_main_measure_function`, `dgpr_main_measure_finite`, `dgpr_main_measure_hausdorff` | [DgprMainToStanding.v](../theories/DgprMainToStanding.v) |
| proof of lem:compact_case: the normalisation of μ and ‖Υ‖ | `dgpr_measure_scale_radon`, `dgpr_variation_value_scale` | [DgprMainToStanding.v](../theories/DgprMainToStanding.v) |
| proof of lem:compact_case: the extension of X by a value in K | `dgpr_main_extension`, `dgpr_main_extension_on` | [DgprMainToStanding.v](../theories/DgprMainToStanding.v) |
| proof of lem:compact_case: (S) for the normalised data of mr:hypotheses_main | `dgpr_main_standing` | [DgprMainToStanding.v](../theories/DgprMainToStanding.v) |
| lem:compact_case, the conclusion for the data of mr:hypotheses_main | `dgpr_compact_case_inequality` | [DgprMainHypothesesCompact.v](../theories/DgprMainHypothesesCompact.v) |
| lem:compact_case for the data of mr:hypotheses_main | `dgpr_compact_case_general` | [DgprCompactCaseGeneral.v](../theories/DgprCompactCaseGeneral.v) |

## The entropy

[DgprEntropy.v](../theories/DgprEntropy.v). For t ∈ R,

    H(ρ_t) = ∫ ρ_t log ρ_t dL^n,
    H̃(ρ_t) = H(ρ_t) + 2^{-1} (n − m) γ log(T − t).

The integral is Federer's upper integral (2.4.2), taken as a real number
by `fine`. For t < T the function ρ_t log ρ_t is L^n summable, and its
integral is H(ρ_t); this is the first component of
`dgpr_entropy_derivative`.

The proof of lem:entropy follows the blueprint. The chain rule for the
jets of ρ (`dgpr_heat_jet_compose`, [DgprHeatJetCalculus.v](../theories/DgprHeatJetCalculus.v))
with Φ(r) = r log r and H ρ = 0 (lem:identities(heat)) gives
H(ρ log ρ) = ρ |grad log ρ|² on Ω_T (`dgpr_entropy_heat`). The function
ρ log ρ has Gaussian decay before T by lem:regularity (`dgpr_regularity_log_polynomial`,
`dgpr_regularity_gaussian_extensions`) and lem:classes(cl:product)
(`dgpr_entropy_gaussian`). Then `dgpr_heat_integral`
([DgprHeatIntegral.v](../theories/DgprHeatIntegral.v)) gives a map of
class 1 on R ∩ {t : t < T} whose values are the integrals of ρ_t log ρ_t
and whose derivative has the values ∫ ρ_t |grad log ρ_t|² dL^n. Uniqueness
of integrals identifies these with H(ρ_t) and I(ρ_t)
(`dgpr_entropy_integral_of`, `dgpr_fisher_information_of`), and
`dgpr_class_one_field_agreement` transfers the class 1 assertion. The
bound of H(ρ_0) follows from ρ_0 ≤ γ (4πT)^{-n/2} (`dgpr_entropy_kernel_bound`,
lem:kernel(6)), the monotonicity of the logarithm and lem:identities(mass).

The results `dgpr_entropy_derivative_of` and `dgpr_entropy_initial_bound_of`
assume the Gaussian decay of ρ log ρ as a hypothesis; `dgpr_entropy_derivative`
and `dgpr_entropy_initial_bound` discharge it.

## The upper bound

[DgprUpperEntropy.v](../theories/DgprUpperEntropy.v). The theorem
`dgpr_upper_entropy_of` assumes that a number C0 satisfies the conclusion
of lem:DGPR32,

    ∫_[0,τ] (I(ρ_t) − (n − m) γ / (2 (T − t))) dL^1 t ≤ C0 γ (1 + log((1 + T^{1/2} δ)/γ))
    for 0 ≤ τ < T,

with the upper integral over [0, τ] of Federer 2.4.10, and concludes

    H̃(ρ_τ) ≤ − 2^{-1} m γ log T + C0 γ (1 + log((1 + T^{1/2} δ)/γ))   for 0 ≤ τ < T.

The fundamental theorem of calculus (`dgpr_before_ftc`,
`dgpr_before_ftc_general`, [DgprTimeIntegrals.v](../theories/DgprTimeIntegrals.v))
gives the integrals of [t ↦ I(ρ_t)] and of
[t ↦ (n − m) γ / (2 (T − t))] over [0, τ]; the latter has the primitive
[t ↦ − 2^{-1} (n − m) γ log(T − t)] (`dgpr_time_logarithm_derivative`).
The integral of the difference is at most the upper integral
(`dgpr_segment_upper_integral_ge`), hence at most C0 γ (1 + log((1 + T^{1/2} δ)/γ)).
The bound H̃(ρ_0) ≤ − 2^{-1} m γ log T uses lem:entropy, γ ≤ 1 and
log(4π) ≥ 0 (`dgpr_logarithm_four_pi`, from π ≥ 3, `circular_half_period_at_least_three`).

The theorem `dgpr_upper_entropy` is lem:upper_entropy: it applies
`dgpr_upper_entropy_of` to lem:DGPR32 (`dgpr_lemma_3_2`,
[DgprLemma32Theorem.v](../theories/DgprLemma32Theorem.v)), with a field
DB of differentials of B (`dgpr_lemma31_DB_exists`,
[DgprLemma31Field.v](../theories/DgprLemma31Field.v)). Its constant is

    C = 2n + C1 ((16 n + 6) Λ² + 16),   C1 = (2n + 1)(32 Λ/(3 λ²))² + 32/(3 λ²)

(`dgpr_upper_entropy_constant`, with C1 = `dgpr_lemma32_C1 n lam Lam`); it
depends only on n, λ and Λ, and it is positive
(`dgpr_upper_entropy_constant_gt0`).

The theorem `dgpr_upper_entropy_conditional` takes
C0 = 2n + C1 ((16 n + 6) Λ² + 16), the constant of
`dgpr_lemma_3_2_conditional` ([DgprLemma32Final.v](../theories/DgprLemma32Final.v)),
under the hypotheses `hDB` (a field DB with the values of D B_t(x)) and
`hI32` (eq:32:I at each time with a constant C1 ≥ 0) of that theorem; its
Gaussian decay hypotheses are `dgpr_regularity_entropy_gaussian` and
`dgpr_regularity_B2_gaussian`.

## The lower bound

[DgprLowerEntropy.v](../theories/DgprLowerEntropy.v). Assume (S) and
μ_0 = μ ⌞ E (`hEc : mu0 = measure_restrict mu Ec`), with E compact and
m rectifiable (`compact Ec`, `is_m_rectifiable m Ec`), H^m(E) = h and
0 < h. Then `dgpr_lower_entropy` gives 0 < s_0 with

    γ log(γ/h) − γ (log c(n) + 2^{-1} n) ≤ H̃(ρ_t)   for T − s_0 < t < T,

where c(n) = 1 + 2 (4π)^{n/2} (`dgpr_tube_constant`) is the constant of
lem:tube; s_0 is the number of lem:tube.

With s = T − t, d the distance to E (`MetricSetDistance.value`) and
G(x) = exp(−d(x)²/(4s)), the tangent inequality
r log r ≥ r log a + r − a (`dgpr_entropy_tangent_lower`) with r = ρ_t(x)
and a = γ γ_s^{-1} G(x), where γ_s = ∫ G dL^n, gives

    H(ρ_t) ≥ γ log(γ/γ_s) − (4s)^{-1} ∫ ρ_t d² dL^n

(`dgpr_lower_entropy_fixed`). The second moment is bounded through
ρ_t(x) d(x)² ≤ v(x), where v(x) = ∫ |x − y|² p_s(x − y) dμ_0 y
(`dgpr_lower_entropy_moment_pointwise`), since μ_0(R^n ∖ E) = 0
(`dgpr_lower_entropy_null`). Fubini's theorem (Federer 2.6.2) gives
∫ v dL^n = 2 n s γ (`dgpr_kernel_convolution_mass`, `dgpr_lower_entropy_moment`),
by lem:kernel(2) (`dgpr_kernel_moment`). The number γ_s is positive by
comparison with a translated heat kernel (`dgpr_lower_entropy_gaussian_positive`).
Then lem:tube bounds γ_s by c(n) s^{(n−m)/2} h.

## The compact case for normalised data

[DgprCompactCase.v](../theories/DgprCompactCase.v). The data are those of
(S) for some 0 < T_0, with μ(R^n) = 1 (a field of (S)), μ_0 = μ ⌞ E, E
compact and m rectifiable, H^m(E) = h with 0 < h, and 1/2 < γ. Since T
enters (S) only through 0 < T, (S) holds for every 0 < T
(`dgpr_standing_time`); `dgpr_standing_restrict` gives (S) with
μ_0 = μ ⌞ E and γ = μ(E) from (S) with any μ_0. The proposition
`dgpr_upper_entropy_property C0` is the conclusion of lem:upper_entropy for
these data, every 0 < T and the constant C0; `dgpr_upper_entropy_property_of`
derives it from the conclusion of lem:DGPR32 with the constant C0, and
`dgpr_upper_entropy` proves it for the constant
`dgpr_upper_entropy_constant n lam Lam`.

With C1 = C0 + log c(n) + 2^{-1} n (`dgpr_compact_case_C1`),
C2 = log 2 + C1 (1 + log 4) and C = exp(C2) (`dgpr_compact_case_constant`),
the theorem `dgpr_compact_case_normalised` gives, for C0 ≥ 0,

    1 ≤ C h^{1/m} δ,

with the real power of Federer's `RealPower`. The proof is that of the
blueprint: (eq:cc:main) (`dgpr_compact_case_entropy`) combines
lem:upper_entropy and lem:lower_entropy at the time max{0, T − s_0/2};
δ > 0 (`dgpr_compact_case_delta_gt0`) because the choice
T = exp(2 m^{-1} (C1 (1 + log γ^{-1}) − log(γ/h) + 1)) contradicts
(eq:cc:main) when δ = 0; the choice T = δ^{-2} gives
− log 2 − log h ≤ m log δ + C1 (1 + log 4) (`dgpr_compact_case_log_bound`).
The theorem `dgpr_compact_case_standing` takes C0 = `dgpr_upper_entropy_constant n lam Lam`,
so that C depends only on n, λ and Λ.

## The compact case for the data of mr:hypotheses_main

[DgprDualDensity.v](../theories/DgprDualDensity.v),
[DgprMainToStanding.v](../theories/DgprMainToStanding.v) and
[DgprCompactCaseGeneral.v](../theories/DgprCompactCaseGeneral.v). The data
are those of mr:hypotheses_main (`dgpr_main_hypotheses`,
[DgprMainHypotheses.v](../theories/DgprMainHypotheses.v)), with
μ = (H^k ⌞ M) ⌞ θ (`dgpr_main_measure`) and μ(R^n ∖ B(0, r_0)) = 0 for some
0 < r_0 < ∞. The conclusion of lem:compact_case for these data is the
proposition `dgpr_compact_case_inequality hk lam Lam C` of
[DgprMainHypothesesCompact.v](../theories/DgprMainHypothesesCompact.v):
for every finite dimensional inner product space Y and all such data,

    μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n).

The theorem

    Theorem dgpr_compact_case_general (lam Lam : R) : 0 < lam -> 0 < Lam ->
      dgpr_compact_case_inequality hk lam Lam
        (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam)).

proves it with the constant of `dgpr_compact_case_standing`, which
depends only on n, λ and Λ.

The hypotheses (S) require a dual density of ‖Υ‖: a ‖Υ‖ measurable map
dΥ : R^n → Hom(Y, R), with the norm of Federer 1.7.9 on Hom(Y, R), such
that ‖dΥ(z)‖ ≤ 1 for z ∈ R^n and Υ(g) = ∫ ⟨g(z), dΥ(z)⟩ d‖Υ‖ z for
g ∈ D(R^n, Y). The theorem `dgpr_dual_density` provides it whenever ‖Υ‖
is a Radon measure whose integral of every f ∈ K(R^n)^+ is the variation
‖Υ‖(f) of Federer 4.1.5. By `dgpr_ups_finite_variation` the variation is
finite on K(R^n)^+, so that Federer 4.1.5
(`dgpr_functional_representation`) applies. It gives a Radon measure ρ
over the current domain of R^n and a ρ measurable map k into the unit
ball of the continuous dual of Y, with its weak topology. The image ν of
ρ under the inclusion of the current domain into R^n is a Radon measure
over R^n (`dgpr_value_pushforward_radon`, Federer 2.2.17), and
integrals transfer by Federer 2.4.18(1)
(`dgpr_value_pushforward_integral`). Hence ν represents ‖Υ‖ on
K(R^n)^+, and ν = ‖Υ‖ by `dgpr_variation_measure_unique`. The density is
the covector field determined by k. Its norm is at most 1 by
`dgpr_covector_norm_le`, and it is measurable in the norm topology by
`dgpr_dual_field_measurable`, since its coordinates with respect to the
basis dual to a basis of Y are measurable (`dgpr_covector_expansion`).

Let a = μ(R^n). The number a is finite by `dgpr_main_measure_finite`.
Suppose 0 < a and A_0 ∈ K. The theorem `dgpr_main_standing` gives (S)
for the measure a^{-1} μ (`measure_scale a^-1 mu`, the measure c φ of
Federer 2.7.18, p. 141), the radius r_0, the extension of X by A_0 on R^n ∖ M
(`dgpr_main_extension`), the distribution a^{-1} Υ, its variation
measure a^{-1} ‖Υ‖ (`dgpr_measure_scale_radon`,
`dgpr_variation_value_scale`), the dual density dΥ,
δ = a^{-1} ‖Υ‖(R^n), T = 1, μ_0 = a^{-1} μ and γ = 1. The properties of μ
used there are these: μ is a measure (`dgpr_main_measure_is_measure`);
open sets are μ measurable, because H^k is Borel regular by Federer
2.10.2(1) (`dgpr_main_measure_open`); H^k ⌞ M measurable maps are μ
measurable (`dgpr_main_measure_function`); and μ(R^n ∖ M) = 0
(`dgpr_main_measure_on`). The constraint Υ(g) = −σ(Dg) and the
measurability of the extension of X follow from the last two
properties.

The theorem `dgpr_compact_case_general` follows the blueprint. If a = 0,
there is nothing to prove. Otherwise lem:inner
(`dgpr_inner_approximation`) with ε = a/2 gives a compact k rectifiable
set E ⊆ M with μ(R^n ∖ E) < a/2, hence γ = a^{-1} μ(E) > 1/2. The lemma
`dgpr_standing_restrict` passes from μ_0 = a^{-1} μ to
μ_0 = a^{-1} μ ⌞ E. Since μ is absolutely continuous with respect to
H^k (`dgpr_main_measure_hausdorff`), 0 < H^k(E) ≤ H^k(M) < ∞. The
theorem `dgpr_compact_case_standing` gives 1 ≤ C H^k(E)^{1/k} a^{-1} ‖Υ‖(R^n),
and H^k(E)^{1/k} ≤ H^k(M)^{1/k} by `real_power_monotone`.

## Open items

None. The deduction of thm:main (`dgpr_theorem_1_1_rectifiable`,
[DgprMainTheorem.v](../theories/DgprMainTheorem.v)) from
`dgpr_compact_case_general` by cut-off functions is described in
docs/main-theorem.md.
