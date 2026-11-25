# Varifolds and the Michael–Simon inequality (blueprint sections 5 and 6)

This account covers mr:hypotheses_main and the statement of thm:main
(section 5 of `blueprint/dgpr_blueprint.tex`), and mr:varifolds, def:BF,
lem:first_variation, lem:KF and thm:MS (section 6). Section 6 deduces
Theorem 1.6 of De Philippis, Gennaioli, Pigati and Rindler (2026), the
anisotropic Michael–Simon inequality, from thm:main. The conclusions of
thm:MS are first deduced from the conclusion of thm:main
(`dgpr_theorem_1_6_from_main`). Theorem 1.6 itself (`dgpr_theorem_1_6`,
[DgprTheorem16.v](../theories/DgprTheorem16.v)) combines this deduction
with thm:main (`dgpr_theorem_1_1_rectifiable`, docs/main-theorem.md) and
with the first variation δ_F V as a linear functional
(`dgpr_first_variation_functional`).

Allard's notions come from the allard1972 subproject: varifolds and their
weights ([AllardVarifolds.v](../../allard1972/theories/AllardVarifolds.v)),
image varifolds ([AllardImageVarifold.v](../../allard1972/theories/AllardImageVarifold.v)),
rectifiable varifolds ([AllardRectifiableVarifolds.v](../../allard1972/theories/AllardRectifiableVarifolds.v))
and their structure, Allard 3.5(1)
([AllardRectifiableStructure.v](../../allard1972/theories/AllardRectifiableStructure.v)).
The map B_F and DDG Lemma A.2 come from the DPDRG2018 subproject
([DdgAnisotropicIntegrand.v](../../DPDRG2018/theories/DdgAnisotropicIntegrand.v),
[DdgFirstVariation.v](../../DPDRG2018/theories/DdgFirstVariation.v)).
Throughout, R^n is `R_n R n` with the Euclidean inner product, G(n, k) is
`orthogonal_projectors R n k`, G_k(R^n) is `grassmann_bundle R n k`,
Hom(R^n, R^n) carries the inner product A • B = trace(A^* ∘ B) and the
norm |A| of Federer 1.7.9, and H^k is `hausdorff_measure` on R^n.

| Blueprint | Formalisation | File |
| --- | --- | --- |
| mr:hypotheses_main, μ = (H^k ⌞ M) ⌞ θ | `dgpr_main_measure` | [DgprMainHypotheses.v](../theories/DgprMainHypotheses.v) |
| mr:hypotheses_main | `dgpr_main_hypotheses` | [DgprMainHypotheses.v](../theories/DgprMainHypotheses.v) |
| thm:main, the conclusion for λ, Λ and C | `dgpr_main_inequality` | [DgprMainHypotheses.v](../theories/DgprMainHypotheses.v) |
| thm:main (Theorem 1.1 for rectifiable data) | `dgpr_theorem_1_1_rectifiable` | [DgprMainTheorem.v](../theories/DgprMainTheorem.v) |
| mr:functionals, uniqueness of ‖Υ‖ | `dgpr_variation_measure_unique` | [DgprMainHypotheses.v](../theories/DgprMainHypotheses.v) |
| mr:varifolds, the integrand F | `dgpr_integrand` | [DgprAnisotropicIntegrand.v](../theories/DgprAnisotropicIntegrand.v) |
| def:BF, B_F | `dgpr_B` | [DgprAnisotropicIntegrand.v](../theories/DgprAnisotropicIntegrand.v) |
| proof of lem:KF, B_F is continuous | `dgpr_B_continuous` | [DgprAnisotropicIntegrand.v](../theories/DgprAnisotropicIntegrand.v) |
| def:BF, K_F, (AC1), λ(F), Λ(F) | `dgpr_KF`, `dgpr_AC1`, `is_dgpr_lambda`, `is_dgpr_Lambda` | [DgprKF.v](../theories/DgprKF.v) |
| lem:KF, first assertion | `dgpr_KF_compact_convex` | [DgprKF.v](../theories/DgprKF.v) |
| lem:KF, second assertion | `dgpr_KF_bounds`, `dgpr_lemma_KF` | [DgprKF.v](../theories/DgprKF.v) |
| mr:varifolds and lem:first_variation, δ_F V(g) | `is_dgpr_first_variation`, `dgpr_first_variation_unique` | [DgprFirstVariation.v](../theories/DgprFirstVariation.v) |
| lem:first_variation, first assertion | `dgpr_test_flow` | [DgprFirstVariation.v](../theories/DgprFirstVariation.v) |
| lem:first_variation | `dgpr_first_variation` | [DgprFirstVariation.v](../theories/DgprFirstVariation.v) |
| thm:MS, the set M | `dgpr_MS_set` | [DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v) |
| proof of thm:MS, (eq:MS:HM) | `dgpr_MS_HM` | [DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v) |
| proof of thm:MS, ‖V‖(R^n ∖ M) = 0 | `dgpr_MS_set_full`, `dgpr_MS_borel_part` | [DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v) |
| proof of thm:MS, θ and ‖V‖ = (H^k ⌞ M) ⌞ θ | `dgpr_MS_density`, `dgpr_MS_weight_representation`, `dgpr_MS_density_summable` | [DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v) |
| proof of thm:MS, M is countably (H^k, k) rectifiable | `dgpr_MS_rectifiable`, `dgpr_MS_borel_part_finite` | [DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v) |
| proof of thm:MS, Υ(g) = −σ(Dg) | `dgpr_MS_transfer`, `dgpr_MS_constraint` | [DgprMichaelSimon.v](../theories/DgprMichaelSimon.v) |
| proof of thm:MS, ‖Υ‖ = ‖δ_F V‖ | `dgpr_variation_value_opp` | [DgprMichaelSimon.v](../theories/DgprMichaelSimon.v) |
| proof of thm:MS up to thm:main | `dgpr_MS_reduction` | [DgprMichaelSimon.v](../theories/DgprMichaelSimon.v) |
| thm:MS from the conclusion of thm:main | `dgpr_theorem_1_6_from_main` | [DgprMichaelSimon.v](../theories/DgprMichaelSimon.v) |
| thm:MS, δ_F V as a linear functional: the characterising predicate | `is_dgpr_first_variation_functional`, `dgpr_first_variation_functional_unique`, `dgpr_first_variation_functional_integral` | [DgprFirstVariationFunctionalUP.v](../theories/DgprFirstVariationFunctionalUP.v) |
| thm:MS, existence of δ_F V (private) | `dgpr_first_variation_functional_exists` | [DgprFirstVariationFunctionalConstruction.v](../theories/DgprFirstVariationFunctionalConstruction.v) |
| thm:MS, δ_F V (sealed choice) | `DgprFirstVariationFunctional.value`, `DgprFirstVariationFunctional.laws` | [DgprFirstVariationFunctionalSealed.v](../theories/DgprFirstVariationFunctionalSealed.v) |
| thm:MS, δ_F V | `dgpr_first_variation_functional`, `dgpr_first_variation_functional_specification`, `dgpr_first_variation_functional_variation`, `dgpr_first_variation_functional_representation` | [DgprFirstVariationFunctional.v](../theories/DgprFirstVariationFunctional.v) |
| thm:MS (Theorem 1.6) | `dgpr_theorem_1_6` | [DgprTheorem16.v](../theories/DgprTheorem16.v) |

## The data of thm:main

[DgprMainHypotheses.v](../theories/DgprMainHypotheses.v). The record
`dgpr_main_hypotheses hk eY hE K λ Λ M θ X Υ ups` collects the data of
mr:hypotheses_main. The space Y has an inner product CY and a basis eY
indexed by {0, …, d − 1}. The distribution Υ is a linear functional on the
test space D(R^n, Y) of a realisation hE of the smooth maps R^n → Y
(Federer 4.1.1), as in [DgprStanding.v](../theories/DgprStanding.v). The
functions θ and X are total functions on R^n; their values off M play no
role. The measure μ = (H^k ⌞ M) ⌞ θ is `dgpr_main_measure k M θ`, the
measure of Federer 2.4.10. The functional σ is not a separate object: the
field `dgpr_main_constraint` asserts that [x ↦ X(x) • Dg(x)] is μ summable
with integral −Υ(g), for every g ∈ D(R^n, Y) and its differentials Dg(x).
The variation measure ‖Υ‖ of mr:functionals is a Radon measure `ups` over
R^n with `ups(R^n) < ∞` whose integral of every nonnegative continuous
function f with compact support is the variation ‖Υ‖(f) of Federer 4.1.5;
such a measure is unique (`dgpr_variation_measure_unique`).

The conclusion of thm:main for the numbers λ, Λ and C is the proposition
`dgpr_main_inequality hk λ Λ C`: for every finite dimensional inner product
space Y and all data satisfying `dgpr_main_hypotheses`,

    μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n)

in the extended real numbers, with H^k(M)^{1/k} the real power of the
finite number H^k(M). Theorem 1.1 of DPGPR 2026 for rectifiable data
asserts that for 0 < λ and 0 < Λ some 0 < C < ∞ has this property; it is
`dgpr_theorem_1_1_rectifiable`, with the explicit constant of
lem:compact_case (docs/main-theorem.md).

## The integrand and the map B_F

[DgprAnisotropicIntegrand.v](../theories/DgprAnisotropicIntegrand.v). An
integrand is a function F : Hom(R^n, R^n) → R of class 1 relative to
G(n, k) (Federer 3.1.22) with F(S) > 0 for S ∈ G(n, k)
(`dgpr_integrand k F`); its values off G(n, k) play no role. The map B_F of
def:BF is `dgpr_B k F`, which is by definition the map `ddg_B k F` of the
DPDRG2018 subproject (DDG (A.3) for an integrand not depending on the
point); there is no second construction. The file proves that F is locally
Lipschitzian, Lipschitzian and bounded on G(n, k), and that B_F is
continuous on G(n, k) (`dgpr_B_continuous`).

## The set K_F and the numbers λ(F) and Λ(F)

[DgprKF.v](../theories/DgprKF.v). The set K_F = conv B_F[G(n, k)] is
`dgpr_KF k F`, with the convex hull of Federer 2.10.2(1). The condition
(AC1) is `dgpr_AC1 k F`: `linear_rank_at_least A k` (Federer 3.1.18) for
every A ∈ K_F. The numbers λ(F) and Λ(F) are not chosen; they are
characterised by the predicates `is_dgpr_lambda hk F l` (l is the greatest
lower bound of the numbers sv_k(A) for A ∈ K_F) and `is_dgpr_Lambda k F L`
(L is the least upper bound of the numbers |A| for A ∈ K_F), and they are
unique (`dgpr_lambda_unique`, `dgpr_Lambda_unique`).

The first assertion of lem:KF is `dgpr_KF_compact_convex`: K_F is compact
in Hom(R^n, R^n) and convex. The proof follows the blueprint: B_F[G(n, k)]
is compact (`dgpr_B_image_compact`) and lem:hull gives the compactness of
its convex hull. The second assertion is `dgpr_KF_bounds`: under (AC1),
if λ and Λ satisfy the two predicates, then 0 < λ ≤ Λ, sv_k(A) ≥ λ and
|A| ≤ Λ for A ∈ K_F. The existence of λ(F) (under (AC1)) and of Λ(F)
follows from the extreme value theorem for the continuous functions sv_k
and |·| on the nonempty compact set K_F (`dgpr_KF_lambda`, `dgpr_KF_Lambda`);
`dgpr_lemma_KF` combines these results.

## The first variation

[DgprFirstVariation.v](../theories/DgprFirstVariation.v). For
g ∈ D(R^n, R^n) with differentials Dg(x) and φ_t(x) = x + t g(x)
(`ddg_flow`), the image varifold φ_{t#} V is Allard's `image_varifold`
with the differential `ddg_flow_differential Dg t`. Write
F(W) = ∫ F(S) dW(x, S). The predicate `is_dgpr_first_variation V F g Dg c`
asserts that for some 0 < δ the integral F(φ_{t#} V) exists for |t| < δ
and that every function I with I(t) = F(φ_{t#} V) for |t| < δ has the
derivative c at 0 (Federer 2.9.19); the number c = δ_F V(g) is unique
(`dgpr_first_variation_unique`).

The first assertion of lem:first_variation is `dgpr_test_flow`: there is
0 < t_0 such that φ_t is injective and a proper immersion of class 1 for
|t| < t_0. The main assertion is

    Theorem dgpr_first_variation V F g Dg :
      is_varifold V -> V(G_k(R^n)) < ∞ -> F of class 1 relative to G(n, k) ->
      (Dg(x) is the differential of g at x for x ∈ R^n) ->
      exists c, is_dgpr_first_variation V F g Dg c /\
        c = ∫ B_F(S) • Dg(x) dV(x, S),

the integral being asserted to exist. It is DDG Lemma A.2 for an integrand
not depending on the point (`ddg_lemma_A_2_constant_lipschitz`); the
Lipschitz bound and the bound of g required there follow from the
compactness of spt g (`dgpr_test_lipschitz`, `dgpr_test_bounded`).

## The weight of a rectifiable varifold

[DgprVarifoldWeight.v](../theories/DgprVarifoldWeight.v). Let
V ∈ RV_k(R^n) with ‖V‖(R^n) < ∞, and let W = ‖V‖. The set
M = R^n ∩ { x : 1 ≤ Θ^k(W, x) < ∞ } is `dgpr_MS_set k W`: the density
Θ^k(W, x) of Federer 2.10.19, a partial function of x, exists at x and is
a real number at least 1. The inequality (eq:MS:HM),
H^k(M) ≤ ‖V‖(R^n), is `dgpr_MS_HM`; as in the blueprint, it follows from
Federer 2.10.19(3) and H^k ≤ S^k (`finite_upper_density_hausdorff_bound`)
as t → 1−.

Suppose moreover that Θ^k(W, x) ≥ 1 for W almost all x. By Allard 3.5(1),
W(R^n ∖ M) = 0 (`dgpr_MS_set_full`). The Borel regularity of W gives a
Borel set M' ⊆ M with W(R^n ∖ M') = 0 (`dgpr_MS_borel_part`); the data of
mr:hypotheses_main are formed with M' (see docs/divergences.md). Let θ be
the upper density Θ^{*k}(W, ·) on M' and 0 off M' (`dgpr_MS_density V M'`).
Then θ is a Borel function, since the superlevel sets of Θ^{*k}(W, ·) are
Borel sets (`dgpr_upper_superlevel_borel`). The function θ equals
Θ^k(W, ·) H^k almost everywhere (`dgpr_MS_density_ae`): on M' by the
definition of M, and on R^n ∖ M' because the sets
(R^n ∖ M') ∩ { x : Θ^{*k}(W, x) > 1/(j + 1) } are H^k null by Federer
2.10.19(3). Allard 3.5(1)(b), W = H^k ⌞ Θ^k(W, ·), therefore gives

    W = (H^k ⌞ M') ⌞ θ        (dgpr_MS_weight_representation).

The function θ is H^k ⌞ M' summable (`dgpr_MS_density_summable`). The set
M' is countably (H^k, k) rectifiable (`dgpr_MS_rectifiable`): with
V = Σ_i c_i v(E_i) (Allard 3.5) and A = ⋃_i E_i, the set A is countably
(H^k, k) rectifiable, W(R^n ∖ A) = 0, and H^k(M' ∖ A) = 0 by Federer
2.10.19(3). Finally H^k(M') ≤ H^k(M) < ∞ (`dgpr_MS_borel_part_finite`).

## Reduction of thm:MS to thm:main

[DgprMichaelSimon.v](../theories/DgprMichaelSimon.v). The section
`MichaelSimon` fixes the hypotheses of thm:MS: an integrand F
(`dgpr_integrand k F`) satisfying (AC1); a rectifiable varifold V with
V(G_k(R^n)) < ∞ and Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost all x; a linear
functional S on D(R^n, R^n) with `is_dgpr_first_variation V F g Dg (S g)`
for every g and its differentials Dg; and a Radon measure ν over R^n with
ν(R^n) < ∞ representing the variation ‖S‖ on the nonnegative continuous
functions with compact support. The measure ν is ‖δ_F V‖.

Let t be a Borel map of R^n into G(n, k) with t(x) = Tan^k(‖V‖, x) for
‖V‖ almost all x and V = [x ↦ (x, t(x))]_# ‖V‖
(`allard_3_5_1_b_pushforward`), and let X(x) = B_F(t(x)) for x ∈ R^n. If
h is a Borel function on G_k(R^n), then ∫ h dV = ∫ h(x, t(x)) d‖V‖ x
whenever the left side exists (`dgpr_MS_transfer`, by Federer 2.4.18(1)).
Applied to the continuous function [(x, S) ↦ B_F(S) • Dg(x)]
(`dgpr_MS_test_integrand_borel`), this and lem:first_variation give
Υ(g) = −σ(Dg) for Υ = −S (`dgpr_MS_constraint`). The variation of −S
equals that of S (`dgpr_variation_value_opp`). Hence

    Theorem dgpr_MS_reduction l L :
      is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
      exists M' θ X, [/\ M' ⊆ dgpr_MS_set k ‖V‖, ‖V‖ = dgpr_main_measure k M' θ &
        dgpr_main_hypotheses hk (coordinate_basis) hE (dgpr_KF k F) l L M' θ X (−S) ν],

with Y = R^n. Then

    Theorem dgpr_theorem_1_6_from_main C l L :
      0 ≤ C -> is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
      dgpr_main_inequality hk l L C ->
      ‖V‖(R^n) ≤ C H^k(M)^{1/k} ν(R^n) /\
      (1 < k -> ‖V‖(R^n)^{(k − 1)/k} ≤ C ν(R^n)),

with M = `dgpr_MS_set k ‖V‖`. The first inequality is (eq:MS:MS): thm:main
gives it for M' ⊆ M, and H^k(M') ≤ H^k(M) < ∞. The second is
(eq:MS:sobolev): if ‖V‖(R^n) > 0, combine (eq:MS:MS) with (eq:MS:HM) and
divide by ‖V‖(R^n)^{1/k}; otherwise both sides are compared with 0.

## The first variation as a distribution

[DgprFirstVariationFunctionalUP.v](../theories/DgprFirstVariationFunctionalUP.v),
[DgprFirstVariationFunctionalConstruction.v](../theories/DgprFirstVariationFunctionalConstruction.v),
[DgprFirstVariationFunctionalSealed.v](../theories/DgprFirstVariationFunctionalSealed.v)
and [DgprFirstVariationFunctional.v](../theories/DgprFirstVariationFunctional.v).
A linear map S : D(R^n, R^n) → R is the first variation of V with respect
to F, `is_dgpr_first_variation_functional V F S`, if
`is_dgpr_first_variation V F g Dg (S g)` for every g ∈ D(R^n, R^n) and its
differentials Dg. There is at most one such S
(`dgpr_first_variation_functional_unique`). If V is a varifold with
V(G_k(R^n)) < ∞ and F is of class 1 relative to G(n, k), then
S(g) = ∫ B_F(S') • Dg(x) dV(x, S') by lem:first_variation
(`dgpr_first_variation_functional_integral`).

Such S exists under these hypotheses
(`dgpr_first_variation_functional_exists`). The differential Dg of
g ∈ D(R^n, R^n) is unique and depends linearly on g (Federer 3.1.1 and
3.1.11), the function [(x, S') ↦ B_F(S') • Dg(x)] is V summable by
lem:first_variation, and its integral is linear in g
(`real_integral_linear_map_exists`). The functional is chosen in the
sealed module `DgprFirstVariationFunctional`, whose value is 0 when no
such S exists, and the public definition is

    Definition dgpr_first_variation_functional V F : Hom (smooth_test_space hE) R^o.

For a varifold V with V(G_k(R^n)) < ∞ and an integrand F
(`dgpr_integrand k F`), `dgpr_first_variation_functional_variation`
asserts exactly the hypothesis on S of the section `MichaelSimon` of
[DgprMichaelSimon.v](../theories/DgprMichaelSimon.v), and
`dgpr_first_variation_functional_representation` gives the integral
formula of lem:first_variation for δ_F V(g).

## Theorem 1.6

[DgprTheorem16.v](../theories/DgprTheorem16.v). Let F be an integrand
satisfying (AC1), with λ(F) = l and Λ(F) = L, and let V ∈ RV_k(R^n)
satisfy V(G_k(R^n)) < ∞ and Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost all x. Let ν
be a Radon measure over R^n with ν(R^n) < ∞ which represents the
variation of `dgpr_first_variation_functional hE V F` on the nonnegative
continuous functions with compact support; ν is ‖δ_F V‖. With
C = `dgpr_compact_case_constant n (dgpr_upper_entropy_constant n l L)`
and M = `dgpr_MS_set k ‖V‖`,

    Theorem dgpr_theorem_1_6 F l L E ev hE V ν :
      dgpr_integrand k F -> dgpr_AC1 k F -> is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
      is_rectifiable_varifold V -> V(G_k(R^n)) < ∞ ->
      (Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost all x) ->
      is_measure ν -> is_radon_measure ν -> (ν represents ‖δ_F V‖) -> ν(R^n) < ∞ ->
      ‖V‖(R^n) ≤ C H^k(M)^{1/k} ν(R^n) /      (1 < k -> ‖V‖(R^n)^{(k − 1)/k} ≤ C ν(R^n)).

The proof applies `dgpr_theorem_1_6_from_main` with
S = `dgpr_first_variation_functional hE V F` and the constant C ≥ 0 of
`dgpr_theorem_1_1_rectifiable`; 0 < l ≤ L by lem:KF (`dgpr_KF_bounds`).
The constant C depends only on n, λ(F) and Λ(F).

## Open items

- That φ_t maps R^n onto R^n for |t| < t_0 is not proved.
- The assertion of the blueprint that M is a Borel set is not proved; a
  Borel subset M' of M carrying ‖V‖ is used instead.
