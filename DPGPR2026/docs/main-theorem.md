# The main theorem (blueprint section 5, thm:main)

This account covers the proof of thm:main of `blueprint/dgpr_blueprint.tex`,
Theorem 1.1 of De Philippis, Gennaioli, Pigati and Rindler (2026) for
rectifiable data. The data of mr:hypotheses_main are the record
`dgpr_main_hypotheses` of [DgprMainHypotheses.v](../theories/DgprMainHypotheses.v)
(docs/varifolds.md), with μ = (H^k ⌞ M) ⌞ θ (`dgpr_main_measure k M θ`),
and the conclusion of thm:main for the numbers λ, Λ and C is the
proposition `dgpr_main_inequality hk λ Λ C`. The proof deduces thm:main
from lem:compact_case (`dgpr_compact_case_general`,
[DgprCompactCaseGeneral.v](../theories/DgprCompactCaseGeneral.v),
docs/entropy.md) by cut-off functions.

| Blueprint | Formalisation | File |
| --- | --- | --- |
| proof of thm:main: the cut-off functions φ_ϱ and the constant c_0 | `dgpr_main_cutoff` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| proof of thm:main: φ_ϱ is continuous and has a differential at every point | `dgpr_smooth_real_differential` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| proof of thm:main: the map [g ↦ φ_ϱ g] of D(R^n, Y) | `dgpr_test_multiplier` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| proof of thm:main: D(φ_ϱ g) = φ_ϱ Dg + Dφ_ϱ · g | `dgpr_product_differential` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| proof of thm:main: \|X • (Dφ_ϱ · g)\| ≤ c_0 ϱ^{-1} \|X\| \|g\| | `dgpr_rank_one_inner_bound`, `dgpr_hom_norm_le` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| proof of thm:main: continuity of Dg in Hom(R^n, Y) | `dgpr_differential_field_continuous` | [DgprMainCutoff.v](../theories/DgprMainCutoff.v) |
| mr:functionals for Υ_ϱ: a bounded distribution has a variation measure of bounded mass | `dgpr_compact_function_bounded`, `dgpr_variation_mass_bound`, `dgpr_bounded_finite_variation`, `dgpr_bounded_variation_measure` | [DgprMainVariation.v](../theories/DgprMainVariation.v) |
| proof of thm:main: Υ(φ) ≤ m ‖Υ‖(R^n) whenever \|φ\| ≤ m | `dgpr_test_norm_compact`, `dgpr_test_variation_bound` | [DgprMainVariation.v](../theories/DgprMainVariation.v) |
| proof of thm:main: the measures (H^k ⌞ M) ⌞ f | `dgpr_restrict_on`, `dgpr_restrict_borel`, `dgpr_density_measure_is_measure`, `dgpr_density_measure_borel`, `dgpr_density_measure_function`, `dgpr_density_measure_on`, `dgpr_density_measure_finite` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: μ_ϱ(R^n ∖ B(0, 2ϱ)) = 0 and μ(U(0, ϱ)) ≤ μ_ϱ(R^n) | `dgpr_density_measure_zero`, `dgpr_density_measure_compare` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: θ_ϱ is summable and ∫ F dμ_ϱ = ∫ φ_ϱ F dμ | `dgpr_density_product_summable`, `dgpr_density_measure_change` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: measurability of X • Dg and of real products | `dgpr_hom_countable_open_base`, `dgpr_hom_pairing_measurable`, `dgpr_real_total_multiply_measurable`, `dgpr_real_total_subtract_measurable` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: summability of bounded measurable functions | `dgpr_bounded_integral` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: the open balls U(0, r) | `dgpr_open_ball_open` | [DgprMainMeasure.v](../theories/DgprMainMeasure.v) |
| proof of thm:main: differentials of test functions | `dgpr_test_differential`, `dgpr_test_differential_measurable` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |
| proof of thm:main: the inequality for 0 < ϱ < ∞ | `dgpr_cutoff_bound` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |
| proof of thm:main: the limit ϱ → ∞ | `dgpr_main_from_cutoff_bound` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |
| thm:main from lem:compact_case, for any 0 ≤ C | `dgpr_main_from_compact_case` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |
| thm:main (Theorem 1.1 for rectifiable data) | `dgpr_theorem_1_1_rectifiable` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |

## The statements

The main results of [DgprMainTheorem.v](../theories/DgprMainTheorem.v)
are

    Theorem dgpr_main_from_compact_case (lam Lam C : R) : 0 <= C ->
      dgpr_compact_case_inequality hk lam Lam C -> dgpr_main_inequality hk lam Lam C.

    Theorem dgpr_theorem_1_1_rectifiable (lam Lam : R) : 0 < lam -> 0 < Lam ->
      dgpr_main_inequality hk lam Lam
        (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam)).

The second combines the first with `dgpr_compact_case_general`. Thus
thm:main holds with the constant C = `dgpr_compact_case_constant n C0`,
C0 = `dgpr_upper_entropy_constant n λ Λ`, of lem:compact_case; it depends
only on n, λ and Λ, and 0 < C (`dgpr_compact_case_constant_gt0`).

## Cut-off functions and products with test functions

[DgprMainCutoff.v](../theories/DgprMainCutoff.v). The cut-off functions
are the scaled smooth cut-offs of Federer 3.1.23 (`AnnularCutoff`, with
inner radius 1/2, and `scaled_annular_cutoff_exists`). For 0 < ϱ < ∞,
`dgpr_main_cutoff` gives a function φ_ϱ of class ∞ on R^n with
0 ≤ φ_ϱ ≤ 1, φ_ϱ(x) = 1 for |x| ≤ ϱ, φ_ϱ(x) = 0 for |x| ≥ 2ϱ, and

    |L(v)| ≤ c_0 ϱ^{-1} |v|    for v ∈ R^n

whenever L is the differential of φ_ϱ at a point; the constant
0 < c_0 < ∞ does not depend on ϱ. The function φ_ϱ is continuous and has
a differential Dφ_ϱ(x) at every x ∈ R^n (`dgpr_smooth_real_differential`).
Multiplication by φ_ϱ is a linear map P of D(R^n, Y) into itself
(`dgpr_test_multiplier`, from `test_multiplier_operator`, Federer
4.1.1). For g ∈ D(R^n, Y) with differentials Dg(x),

    D(φ_ϱ g)(x) = Dφ_ϱ(x) · g(x) + φ_ϱ(x) Dg(x)    for x ∈ R^n

(`dgpr_product_differential`, from Federer 3.1.11), where ω · b is the
map [v ↦ ω(v) b] of Allard 2.3(4) (`dgpr_rank_one`). Since
X • (ω · b) = ω(X^*(b)) and ‖X^*‖ ≤ |X| ([DgprHomNorms.v](../theories/DgprHomNorms.v)),

    |X • (ω · b)| ≤ a |X| |b|    whenever |ω(v)| ≤ a |v| for v ∈ R^n

(`dgpr_rank_one_inner_bound`).

## Variation measures of bounded distributions

[DgprMainVariation.v](../theories/DgprMainVariation.v). Let Y be finite
dimensional and let S ∈ D'(R^n, Y) satisfy S(φ) ≤ m B whenever
|φ(x)| ≤ m for x ∈ R^n. Then the variation ‖S‖(f) of Federer 4.1.5 is
finite for f ∈ K(R^n)^+ (`dgpr_bounded_finite_variation`), and

    Theorem dgpr_bounded_variation_measure : exists ups,
      [/\ is_measure ups, is_radon_measure ups,
        (ups represents the variation of S on K(R^n)^+) & ups(R^n) ≤ B].

The measure of Federer 4.1.5 lives on the current domain of R^n
(`dgpr_functional_representation`); it is carried to R^n by the inclusion,
as in Federer's `current_ambient_variation`, and its mass is bounded by
`dgpr_variation_mass_bound`. Conversely, if ‖Υ‖ is a Radon measure
representing the variation of Υ with ‖Υ‖(R^n) < ∞, then
Υ(φ) ≤ m ‖Υ‖(R^n) whenever |φ(x)| ≤ m for x ∈ R^n
(`dgpr_test_variation_bound`).

## The measures (H^k ⌞ M) ⌞ f

[DgprMainMeasure.v](../theories/DgprMainMeasure.v). For M ⊆ R^n and
f : R^n → R with f ≥ 0 on M, the measure μ_f = (H^k ⌞ M) ⌞ f is
`dgpr_main_measure k M f`. It is a measure for which the Borel sets and
the H^k ⌞ M measurable functions are measurable, μ_f(R^n ∖ M) = 0, and
μ_f(R^n) < ∞ if f is H^k ⌞ M summable. Moreover μ_f(A) = 0 whenever
f = 0 on M ∩ A (`dgpr_density_measure_zero`), and μ_f(A) ≤ μ_g(R^n)
whenever f ≤ g on M ∩ A and g ≥ 0 on M (`dgpr_density_measure_compare`);
these two facts concern upper integrals and need no measurability. If f
is H^k ⌞ M summable, and w ≥ 0 and F are H^k ⌞ M measurable, then

    ∫ F dμ_{w f} = ∫ w F dμ_f

whenever the right side exists (`dgpr_density_measure_change`, Federer
2.4.10 applied twice). The integrand F = X • Dg is H^k ⌞ M measurable
(`dgpr_hom_pairing_measurable`): X is H^k ⌞ M measurable, Dg is
continuous, Hom(R^n, Y) has a countable base of open sets
(`dgpr_hom_countable_open_base`), and the inner product is continuous.

## The proof

[DgprMainTheorem.v](../theories/DgprMainTheorem.v). Suppose the data of
mr:hypotheses_main are given, and let C ≥ 0 satisfy the conclusion of
lem:compact_case for λ and Λ. For 0 < ϱ < ∞ let φ_ϱ, c_0 and P be as above,
θ_ϱ = φ_ϱ θ and μ_ϱ = (H^k ⌞ M) ⌞ θ_ϱ. Every g ∈ D(R^n, Y) has a
differential at each point (`dgpr_test_differential`), and the
differential is continuous, hence H^k ⌞ M measurable
(`dgpr_test_differential_measurable`). Let

    J(g) = ∫ X(x) • (Dφ_ϱ(x) · g(x)) dμ x    and    Υ_ϱ = Υ ∘ P + J.

The integrand of J(g) equals X • D(φ_ϱ g) − φ_ϱ X • Dg, hence is
μ measurable, and it is bounded by c_0 ϱ^{-1} Λ sup |g| on M; therefore it is
μ summable (`dgpr_bounded_integral`), and J is linear
(`real_integral_linear_map_exists`). The constraint
Υ(φ_ϱ g) = −∫ X • D(φ_ϱ g) dμ and the product rule give

    Υ_ϱ(g) = −∫ φ_ϱ X • Dg dμ = −∫ X • Dg dμ_ϱ.

If |g| ≤ m, then Υ(φ_ϱ g) ≤ m ‖Υ‖(R^n) and J(g) ≤ m c_0 ϱ^{-1} Λ μ(R^n);
hence Υ_ϱ has a variation measure ‖Υ_ϱ‖ with

    ‖Υ_ϱ‖(R^n) ≤ ‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n).

The data K, λ, Λ, M, θ_ϱ, X, Υ_ϱ and ‖Υ_ϱ‖ satisfy mr:hypotheses_main,
and μ_ϱ(R^n ∖ B(0, 2ϱ)) = 0. Since μ(U(0, ϱ)) ≤ μ_ϱ(R^n), lem:compact_case
gives

    μ(U(0, ϱ)) ≤ C H^k(M)^{1/k} (‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n))

(`dgpr_cutoff_bound`). The sets U(0, j + 1), j = 0, 1, 2, …, increase to
R^n, so μ(U(0, j + 1)) increases to μ(R^n) by Federer 2.1.5(1)
(`measure_continuity_below`). If μ(R^n) exceeded C H^k(M)^{1/k} ‖Υ‖(R^n)
by e > 0, the choice of j with C H^k(M)^{1/k} c_0 Λ μ(R^n) < (j + 1) e / 2
and μ(U(0, j + 1)) > C H^k(M)^{1/k} ‖Υ‖(R^n) + e/2 would contradict the
inequality for ϱ = j + 1 (`dgpr_main_from_cutoff_bound`).

The blueprint bounds Υ_ϱ by the measure
ν_ϱ = ‖Υ‖ + c_0 Λ ϱ^{-1} μ; the formalisation bounds only the values of
Υ_ϱ on functions with |g| ≤ m, which bounds the mass of ‖Υ_ϱ‖ (see
docs/divergences.md).
