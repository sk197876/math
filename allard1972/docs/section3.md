# Allard 3: Varifolds, items 3.1, 3.2(1) and 3.5 (printed pp. 429–432)

[README](../README.md) · [Divergences](divergences.md) · [Axiom audit](assumptions.log)

Source numbering and printed pages refer to W. K. Allard, “On the first
variation of a varifold”, *Ann. of Math. (2)* 95 (1972), 417–491
(bibliography key `Allard1972`); blueprint labels refer to
[blueprint/sections2to5.tex](../blueprint/sections2to5.tex). Allard works in
a smooth submanifold M of R^n; here M = U = R^n throughout, the case needed
for the anisotropic Michael–Simon inequality of DPGPR. G(n, k) is the space of
orthogonal projections of R^n of rank k (section 2, `projection_grassmann R n k`)
and G_k(R^n) = R^n × G(n, k) carries the maximum of the two distances
(`grassmann_bundle R n k`). Measures, Radon measures, Borel functions and
integrals are those of the Federer library (Federer 2.1.2, 2.2.5, 2.3.1,
2.4.2); an integral is a relation `is_measure_integral mu f a` between a
partial integrand and its value in the extended reals.

| File | Contents |
| --- | --- |
| [AllardVarifolds.v](../theories/AllardVarifolds.v) | 3.1: varifolds, the weight ‖V‖ and its integrals. |
| [AllardImageVarifoldMaps.v](../theories/AllardImageVarifoldMaps.v) | 3.2: the maps F_♮(x, S) = (F(x), DF(x)(S)) and J(x, S) = ‖∧_k(DF(x) ∘ S)‖ of G_k(R^n); continuity and properness. |
| [AllardImageVarifoldUP.v](../theories/AllardImageVarifoldUP.v) | 3.2(1): the characteristic property of F_# V and its consequences. |
| [AllardImageVarifoldConstruction.v](../theories/AllardImageVarifoldConstruction.v) | Existence of F_# V as F_♮ # (V⌞J) (private). |
| [AllardImageVarifoldSealed.v](../theories/AllardImageVarifoldSealed.v) | Opaque choice of F_# V. |
| [AllardImageVarifold.v](../theories/AllardImageVarifold.v) | Public interface of F_# V; 3.2(1). |
| [AllardRectifiableVarifolds.v](../theories/AllardRectifiableVarifolds.v) | 3.5: Tan^k(μ, x) as a member of G(n, k), the characteristic property of v(E), RV_k(R^n). |
| [AllardSimpleProjection.v](../theories/AllardSimpleProjection.v) | new:simple_to_projection: the orthogonal projection onto the subspace associated with a unit simple k vector, a continuous function of the k vector. |
| [AllardTangentMeasurability.v](../theories/AllardTangentMeasurability.v) | al:3.5:lem: H^k⌞E measurability of g_E, a Borel version of it, Borel regularity of H^k⌞E. |
| [AllardSetVarifold.v](../theories/AllardSetVarifold.v) | al:3.5:lem: v(E) ∈ V_k(R^n), ‖v(E)‖ = H^k⌞E and the integral formula. |
| [AllardRectifiableSum.v](../theories/AllardRectifiableSum.v) | 3.5: the weight Σ_i c_i H^k⌞E_i of a member of RV_k(R^n). |
| [AllardRectifiableIntegral.v](../theories/AllardRectifiableIntegral.v) | 3.5(1)(b): Σ_i c_i v(E_i) as an image of its weight and its integrals, under hypotheses on Tan^k of the weight. |
| [AllardRectifiableTangent.v](../theories/AllardRectifiableTangent.v) | 3.5(1)(b), new:density_tangent: Tan^k(Σ_i c_i H^k⌞E_i, ·) agrees with Tan^k(H^k⌞E_i, ·) almost everywhere on E_i, exists almost everywhere and is measurable. |
| [AllardRectifiableDensity.v](../theories/AllardRectifiableDensity.v) | 3.5(1), new:density_tangent: Θ^k(Σ_i c_i H^k⌞E_i, x) = Σ_i c_i 1_{E_i}(x) for H^k almost all x, and the density is positive and finite almost everywhere. |
| [AllardRectifiableStructure.v](../theories/AllardRectifiableStructure.v) | 3.5(1): the “only if” half of (a) and part (b) for V ∈ RV_k(R^n). |

Later files import `AllardVarifolds` and `AllardImageVarifold` (which
re-exports `AllardGrassmann`, `AllardVarifolds`, `AllardImageVarifoldMaps` and
`AllardImageVarifoldUP`), never the construction.

## Item map

| Allard | Assertion | Rocq | Status |
| --- | --- | --- | --- |
| 3.1 | V ∈ V_k(R^n) if V is a Radon measure over G_k(R^n). | [`is_varifold`](../theories/AllardVarifolds.v#L48) | Formalised. |
| 3.1 | ‖V‖(A) = V(G_k(R^n) ∩ {(x, S) : x ∈ A}), that is ‖V‖ = π_# V with π(x, S) = x. | [`grassmann_bundle_point`](../theories/AllardVarifolds.v#L60), [`varifold_weight`](../theories/AllardVarifolds.v#L65), [`varifold_weightE`](../theories/AllardVarifolds.v#L70) | Formalised. |
| 3.1 | ‖V‖ is a Radon measure over R^n. | [`allard_3_1`](../theories/AllardVarifolds.v#L108) | Formalised. |
| 3.1 | ∫ f d‖V‖ = ∫ f(x) dV(x, S). | [`allard_3_1_weight_integral`](../theories/AllardVarifolds.v#L121), [`allard_3_1_weight_borel_integral`](../theories/AllardVarifolds.v#L151) | Formalised. |
| 3.1 | The weak topology on V_k(R^n). | — | Not formalised. |
| 3.2 | DF(x)(S): the orthogonal projection onto DF(x)[im S]. | [`projection_grassmann_image`](../theories/AllardImageVarifoldMaps.v#L249), [`projection_grassmann_imageE`](../theories/AllardImageVarifoldMaps.v#L268), [`image_bundle_map_plane`](../theories/AllardImageVarifold.v#L119) | Formalised. |
| 3.2 | F_♮(x, S) = (F(x), DF(x)(S)) and J(x, S) = ‖∧_k(DF(x) ∘ S)‖. | [`image_bundle_map`](../theories/AllardImageVarifoldMaps.v#L330), [`image_bundle_jacobian`](../theories/AllardImageVarifoldMaps.v#L336) | Formalised. |
| 3.2 | J is continuous; J > 0 and F_♮ is continuous if every DF(x) is injective; F_♮ is proper if moreover F is proper. | [`image_bundle_jacobian_continuous`](../theories/AllardImageVarifoldMaps.v#L348), [`image_bundle_jacobian_positive`](../theories/AllardImageVarifoldMaps.v#L365), [`image_bundle_map_continuous`](../theories/AllardImageVarifoldMaps.v#L375), [`image_bundle_map_proper`](../theories/AllardImageVarifoldMaps.v#L397) | Formalised. |
| 3.2 | Hypotheses on F. | [`is_proper_class_one_immersion`](../theories/AllardImageVarifoldUP.v#L51) | Formalised; see the divergences. |
| 3.2(1) | Characteristic property of F_# V. | [`is_image_varifold`](../theories/AllardImageVarifoldUP.v#L66), [`image_varifold_unique`](../theories/AllardImageVarifoldUP.v#L131) | Formalised. |
| 3.2(1) | F_# V. | [`image_varifold`](../theories/AllardImageVarifold.v#L48), [`image_varifoldP`](../theories/AllardImageVarifold.v#L54) | Formalised. |
| 3.2 | F_# V ∈ V_k(R^n). | [`allard_3_2_1_varifold`](../theories/AllardImageVarifold.v#L62) | Formalised. |
| 3.2(1) | F_# V(B) = ∫_{{(x, S) : (F(x), DF(x)(S)) ∈ B}} ‖∧_k(DF(x) ∘ S)‖ dV(x, S) for Borel B. | [`allard_3_2_1`](../theories/AllardImageVarifold.v#L70) | Formalised. |
| 3.2(1) | ∫ α dF_# V = ∫ α(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S). | [`allard_3_2_1_integral`](../theories/AllardImageVarifold.v#L84), [`allard_3_2_1_continuous_integral`](../theories/AllardImageVarifold.v#L96) | Formalised for real valued Borel α. |
| 3.2(1) | F_# V is characterised by 3.2(1). | [`allard_3_2_1_unique`](../theories/AllardImageVarifold.v#L110) | Formalised. |
| 3.2(2) | ‖μ_r # V‖ = r^k μ_r # ‖V‖. | — | Not formalised (not on the Michael–Simon path). |
| 3.5 | Tan^k(μ, x) ∈ G(n, k) where the approximate tangent cone is a k dimensional subspace. | [`approximate_tangent_plane`](../theories/AllardRectifiableVarifolds.v#L77), [`approximate_tangent_plane_exists`](../theories/AllardRectifiableVarifolds.v#L94) | Formalised. |
| 3.5 | E is H^k measurable and E ∩ K is (H^k, k) rectifiable for compact K. | [`is_locally_rectifiable_set`](../theories/AllardRectifiableVarifolds.v#L161) | Formalised. |
| 3.5, al:3.5:lem | g_E is defined at H^k almost all points of E. | [`set_approximate_tangent_plane_ae`](../theories/AllardRectifiableVarifolds.v#L170), [`approximate_tangent_cone_closed_ball_local`](../theories/AllardRectifiableVarifolds.v#L145) | Formalised. |
| 3.5 | v(E)(B) = H^k(g_E^{-1}[B]) for Borel B; v(E) is determined by these values. | [`set_varifold_preimage`](../theories/AllardRectifiableVarifolds.v#L204), [`is_set_varifold`](../theories/AllardRectifiableVarifolds.v#L211), [`set_varifold_unique`](../theories/AllardRectifiableVarifolds.v#L223) | Formalised as a characteristic property. |
| al:3.5:lem | ‖v(E)‖(B) = H^k(E ∩ B) for Borel B. | [`set_varifold_weight_borel`](../theories/AllardRectifiableVarifolds.v#L240) | Formalised. |
| new:simple_to_projection | For a unit simple k vector ξ, the orthogonal projection onto the subspace associated with ξ; it depends continuously on ξ. | [`simple_projection_hom`](../theories/AllardSimpleProjection.v#L108), [`simple_projection_hom_continuous`](../theories/AllardSimpleProjection.v#L226), [`simple_projection_hom_projector`](../theories/AllardSimpleProjection.v#L360), [`simple_projection_hom_image`](../theories/AllardSimpleProjection.v#L374) | Formalised. |
| al:3.5:lem | g_E is H^k⌞E measurable; it agrees H^k⌞E almost everywhere with a Borel function. | [`set_tangent_plane_measurable`](../theories/AllardTangentMeasurability.v#L165), [`set_tangent_borel_version`](../theories/AllardTangentMeasurability.v#L335) | Formalised. |
| 3.5, al:3.5:lem | v(E)(A) = H^k(g_E^{-1}[A]) for A ⊆ G_k(R^n); v(E) ∈ V_k(R^n). | [`set_varifold`](../theories/AllardSetVarifold.v#L59), [`set_varifold_is_varifold`](../theories/AllardSetVarifold.v#L211), [`set_varifold_set_varifold`](../theories/AllardSetVarifold.v#L239) | Formalised. |
| al:3.5:lem | ‖v(E)‖ = H^k⌞E. | [`set_varifold_weight`](../theories/AllardSetVarifold.v#L245) | Formalised. |
| al:3.5:lem | ∫ α dv(E) = ∫_E α(x, Tan^k(H^k⌞E, x)) dH^k x. | [`set_tangent_integrand`](../theories/AllardSetVarifold.v#L291), [`set_varifold_integral`](../theories/AllardSetVarifold.v#L301) | Formalised for real valued Borel α and k ≤ n. |
| 3.5 | RV_k(R^n): V = Σ_i c_i v(E_i) with c_i > 0. | [`is_rectifiable_varifold`](../theories/AllardRectifiableVarifolds.v#L270) | Formalised. |
| 3.5 | ‖V‖ = Σ_i c_i H^k⌞E_i for V = Σ_i c_i v(E_i). | [`rectifiable_sum_measure`](../theories/AllardRectifiableSum.v#L30), [`rectifiable_varifold_weight`](../theories/AllardRectifiableSum.v#L52), [`rectifiable_varifold_representation`](../theories/AllardRectifiableSum.v#L69) | Formalised. |
| 3.5 | Σ_i c_i v(E_i) = [x ↦ (x, t(x))]_# μ, μ = Σ_i c_i H^k⌞E_i, whenever t(x) = Tan^k(H^k⌞E_i, x) for H^k almost all x ∈ E_i and every i. | [`rectifiable_varifold_pushforward`](../theories/AllardRectifiableIntegral.v#L129) | Formalised. |
| 3.5(1)(b) | If Tan^k(μ, ·) is μ measurable and agrees with Tan^k(H^k⌞E_i, ·) at H^k almost all points of E_i for every i, then Σ_i c_i v(E_i)(α) = ∫ α(x, Tan^k(μ, x)) dμ x. | [`measure_tangent_integrand`](../theories/AllardRectifiableIntegral.v#L157), [`rectifiable_varifold_integral`](../theories/AllardRectifiableIntegral.v#L168) | Formalised for real valued Borel α and k ≤ n. |
| new:density_tangent | For μ = Σ_i c_i H^k⌞E_i a Radon measure and every i: Tan^k(μ, x) = Tan^k(H^k⌞E_i, x) for H^k almost all x ∈ E_i; Tan^k(μ, x) ∈ G(n, k) for μ almost all x; [x ↦ Tan^k(μ, x)] is μ measurable. | [`rectifiable_sum_tangent_equal`](../theories/AllardRectifiableTangent.v#L232), [`rectifiable_sum_tangent_agree`](../theories/AllardRectifiableTangent.v#L331), [`rectifiable_sum_tangent_plane_ae`](../theories/AllardRectifiableTangent.v#L353), [`rectifiable_sum_tangent_measurable`](../theories/AllardRectifiableTangent.v#L397) | Formalised. |
| new:density_tangent | For μ = Σ_i c_i H^k⌞E_i finite on compact sets: Θ^k(μ, x) = Σ_i c_i 1_{E_i}(x) for H^k almost all x; 0 < Θ^k(μ, x) < ∞ for μ almost all x. | [`locally_rectifiable_density_ae`](../theories/AllardRectifiableDensity.v#L282), [`rectifiable_sum_density_ae`](../theories/AllardRectifiableDensity.v#L612), [`rectifiable_sum_density_positive_finite`](../theories/AllardRectifiableDensity.v#L656) | Formalised. |
| 3.5(1)(b) | μ = H^k⌞θ with θ = Σ_i c_i 1_{E_i}, and μ = H^k⌞Θ^k(μ, ·), for μ = Σ_i c_i H^k⌞E_i a Radon measure. | [`rectifiable_sum_measure_with_density`](../theories/AllardRectifiableStructure.v#L199), [`rectifiable_sum_measure_metric_density`](../theories/AllardRectifiableStructure.v#L227) | Formalised. |
| 3.5(1)(a), “only if” | For V ∈ RV_k(R^n) and ‖V‖ almost all a: 0 < Θ^k(‖V‖, a) < ∞ and Tan^k(‖V‖, a) ∈ G(n, k). | [`allard_3_5_1_a_only_if`](../theories/AllardRectifiableStructure.v#L347), [`allard_3_5_1_b_tangent_ae`](../theories/AllardRectifiableStructure.v#L276) | Formalised. |
| 3.5(1)(a) | The “if” half; V^{(a)}(β) = β(Tan^k(‖V‖, a)) for ‖V‖ almost all a; 3.5(1)(c). | — | Not formalised (V^{(a)} is Allard 3.3); see `allard_3_5_1_b_pushforward` for the equivalent image representation. |
| 3.5(1)(b) | ‖V‖ = H^k⌞Θ^k(‖V‖, ·); [x ↦ Tan^k(‖V‖, x)] is ‖V‖ measurable; V(α) = ∫ α(x, Tan^k(‖V‖, x)) d‖V‖ x; V is the image of ‖V‖ under [x ↦ (x, t(x))] for a Borel t with t = Tan^k(‖V‖, ·) ‖V‖ almost everywhere. | [`allard_3_5_1_b_weight`](../theories/AllardRectifiableStructure.v#L337), [`allard_3_5_1_b_measurable`](../theories/AllardRectifiableStructure.v#L288), [`allard_3_5_1_b_integral`](../theories/AllardRectifiableStructure.v#L322), [`allard_3_5_1_b_pushforward`](../theories/AllardRectifiableStructure.v#L301), [`allard_3_5_1_b`](../theories/AllardRectifiableStructure.v#L364) | Formalised for real valued Borel α and k ≤ n; the integral is stated with respect to ‖V‖. |

## Statements

With `GB := grassmann_bundle R n k`, `RnM := inner_metric_space (@euclidean_inner_productP R n)`
and `Rn := R_n R n`:

```coq
Record is_varifold (V : set GB -> \bar R) : Prop := {
  varifold_measure : is_measure V;
  varifold_radon : is_radon_measure V }.

Definition varifold_weight (V : set GB -> \bar R) : set RnM -> \bar R :=
  measure_pushforward grassmann_bundle_point V.

Theorem allard_3_1 (V : set GB -> \bar R) :
  is_varifold V -> is_measure (varifold_weight V) /\ is_radon_measure (varifold_weight V).

Theorem allard_3_1_weight_borel_integral (V : set GB -> \bar R) (f : RnM -> R) :
  is_varifold V -> is_borel_function (f : RnM -> real_line_metric R) ->
  forall a, is_measure_integral (varifold_weight V) (real_total_integrand f) a <->
    is_measure_integral V (real_total_integrand (fun z : GB => f z.1)) a.

Record is_proper_class_one_immersion (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) : Prop := {
  immersion_class_one : is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF;
  immersion_injective : forall x, injective (DF x);
  immersion_proper : is_proper_map (fun x : RnM => (F x : RnM)) }.

Definition image_bundle_map (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (z : GB) : GB :=
  ((F z.1 : RnM), projection_grassmann_image (DF z.1) z.2).
Definition image_bundle_jacobian (DF : Rn -> Hom Rn Rn) (z : GB) : R :=
  euclidean_linear_jacobian k (hom_comp (DF z.1) (set_val z.2 : Hom Rn Rn)).

Record is_image_varifold (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W : set GB -> \bar R) : Prop := {
  image_varifold_measure : is_measure W;
  image_varifold_radon : is_radon_measure W;
  image_varifold_integral : forall alpha : GB -> R,
    is_borel_function (alpha : GB -> real_line_metric R) ->
    forall a, is_measure_integral W (real_total_integrand alpha) a <->
      is_measure_integral V (real_total_integrand
        (fun z : GB => alpha (image_bundle_map F DF z) * image_bundle_jacobian DF z)) a }.

Theorem allard_3_2_1_varifold F DF V :
  is_varifold V -> is_proper_class_one_immersion F DF -> is_varifold (image_varifold F DF V).

Theorem allard_3_2_1 F DF V (B : set GB) (s : GB -> R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  borel_set B -> is_characteristic_function B s ->
  is_measure_integral V (real_total_integrand
    (fun z : GB => s (image_bundle_map F DF z) * image_bundle_jacobian DF z))
    (image_varifold F DF V B).

Theorem allard_3_2_1_integral F DF V (alpha : GB -> R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_borel_function (alpha : GB -> real_line_metric R) ->
  forall a, is_measure_integral (image_varifold F DF V) (real_total_integrand alpha) a <->
    is_measure_integral V (real_total_integrand
      (fun z : GB => alpha (image_bundle_map F DF z) * image_bundle_jacobian DF z)) a.

Theorem allard_3_2_1_unique F DF V W :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V W -> W = image_varifold F DF V.

Record is_set_varifold (E : set RnM) (W : set GB -> \bar R) : Prop := {
  set_varifold_varifold : is_varifold W;
  set_varifold_borel : forall B : set GB, borel_set B -> W B = HK (set_varifold_preimage E B) }.

Theorem set_approximate_tangent_plane_ae (E : set RnM) :
  is_locally_rectifiable_set E ->
  measure_almost_everywhere_on HK E
    [set x | exists S, partial_function_graph (approximate_tangent_plane (measure_restrict HK E)) x S].

Theorem set_varifold_weight_borel (E : set RnM) (W : set GB -> \bar R) (B : set RnM) :
  is_locally_rectifiable_set E -> is_set_varifold E W -> borel_set B ->
  varifold_weight W B = HK (E `&` B).

Definition is_rectifiable_varifold (V : set GB -> \bar R) : Prop :=
  is_varifold V /\
  exists (c : nat -> R) (E : nat -> set RnM) (W : nat -> set GB -> \bar R),
    [/\ forall i, 0 < c i, forall i, is_locally_rectifiable_set (E i),
      forall i, is_set_varifold (E i) (W i) &
      forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * W i A)%E)].

Lemma set_tangent_plane_measurable (E : set RnM) :
  is_locally_rectifiable_set E ->
  is_measure_measurable_function (measure_restrict HK E)
    (approximate_tangent_plane (measure_restrict HK E)).

Definition set_varifold (E : set RnM) : set GB -> \bar R :=
  fun A => HK (set_varifold_preimage E A).

Theorem set_varifold_is_varifold E : is_locally_rectifiable_set E -> is_varifold (set_varifold E).
Theorem set_varifold_set_varifold E :
  is_locally_rectifiable_set E -> is_set_varifold E (set_varifold E).
Theorem set_varifold_weight E :
  is_locally_rectifiable_set E -> varifold_weight (set_varifold E) = measure_restrict HK E.

Theorem set_varifold_integral E (f : GB -> R) : (k <= n)%N -> is_locally_rectifiable_set E ->
  is_borel_function (f : GB -> real_line_metric R) -> forall a,
  is_measure_integral (set_varifold E) (real_total_integrand f) a <->
  is_measure_integral (measure_restrict HK E) (set_tangent_integrand E f) a.

Definition rectifiable_sum_measure (c : nat -> R) (E : nat -> set RnM) : set RnM -> \bar R :=
  fun A => nonnegative_sum [set: nat] (fun i => ((c i)%:E * HK (E i `&` A))%E).

Lemma rectifiable_varifold_representation (V : set GB -> \bar R) :
  is_rectifiable_varifold V ->
  exists (c : nat -> R) (E : nat -> set RnM), [/\ forall i, 0 < c i,
    forall i, is_locally_rectifiable_set (E i),
    forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * set_varifold (E i) A)%E) &
    varifold_weight V = rectifiable_sum_measure c E].

Theorem allard_3_5_1_a_only_if (V : set GB -> \bar R) : is_rectifiable_varifold V ->
  measure_almost_everywhere (varifold_weight V)
    [set x | (exists t : R, 0 < t /\
        partial_function_graph (@metric_density R RNM k (varifold_weight V)) x t%:E) /\
      exists S, partial_function_graph (approximate_tangent_plane (varifold_weight V)) x S].

Theorem allard_3_5_1_b (V : set GB -> \bar R) : (k <= n)%N -> is_rectifiable_varifold V ->
  [/\ varifold_weight V = measure_with_density HK (@metric_density R RNM k (varifold_weight V)),
    is_measure_measurable_function (varifold_weight V)
      (approximate_tangent_plane (varifold_weight V)) &
    forall f : GB -> R, is_borel_function (f : GB -> real_line_metric R) -> forall a,
      is_measure_integral V (real_total_integrand f) a <->
      is_measure_integral (varifold_weight V) (measure_tangent_integrand (varifold_weight V) f) a].

Theorem allard_3_5_1_b_pushforward (V : set GB -> \bar R) : (k <= n)%N ->
  is_rectifiable_varifold V ->
  exists t : RnM -> projection_grassmann R n k, [/\ is_borel_function t,
    measure_almost_equal (varifold_weight V) (approximate_tangent_plane (varifold_weight V))
      (partial_function_total t) &
    V = measure_pushforward (fun x : RnM => ((x, t x) : GB)) (varifold_weight V)].
```

Here `HK := @hausdorff_measure R RnM k`; `set_tangent_integrand E f` and
`measure_tangent_integrand μ f` are the partial integrands
[x ↦ f(x, Tan^k(H^k⌞E, x))] and [x ↦ f(x, Tan^k(μ, x))], defined where the
approximate tangent plane exists. `metric_density R RNM k μ` is the partial
function Θ^k(μ, ·) of Federer 2.10.19, defined where the upper and lower
densities agree, `RNM` being R^n with the metric of the Euclidean norm, and
`measure_with_density HK g` is the measure H^k⌞g of Federer 2.4.10,
A ↦ ∫^* g 1_A dH^k, defined on all subsets of R^n.

## Proofs

The weight is the image measure π_# V; it is a Radon measure by Federer
2.2.17, π being continuous and proper because G(n, k) is compact. Its
integrals are those of Federer 2.4.18.

For 3.2(1), J is continuous: near a point (L₀, S₀), with ξ the unit simple
k vector of im S₀, J(L, S) = |∧_k(L ∘ S) ξ| / |∧_k S ξ|
([`jacobian_exterior_factor`](../theories/AllardImageVarifoldMaps.v#L84)),
and numerator and denominator are continuous by Federer 2.7.16
([`jacobian_param_continuous`](../theories/AllardImageVarifoldMaps.v#L121)).
If every DF(x) is injective, then J > 0 and [(x, S) ↦ DF(x)(S)] is continuous
by the continuity of the projection formula (section 2). The measure V⌞J of
Federer 2.4.10 is a Radon measure since J is continuous and nonnegative
([`jacobian_density_radon`](../theories/AllardImageVarifoldConstruction.v#L90)),
and F_♮ # (V⌞J) is a Radon measure by Federer 2.2.17. Its integrals follow
from Federer 2.4.18 and 2.4.10
([`image_varifold_witness`](../theories/AllardImageVarifoldConstruction.v#L117)).
Uniqueness: two measures with the property agree on open sets by the
formula for characteristic functions, hence everywhere, both being Radon
measures (Federer 2.2.5).

For 3.5, Tan^k(H^k⌞E, x) is local: if |x| < j, then H^k⌞(E ∖ B(0, j)) has
density 0 at x, so that the approximate tangent cones of H^k⌞E and of
H^k⌞(E ∩ B(0, j)) at x coincide (Federer's `restricted_approximate_tangent_equal`).
Federer 3.2.19 applied to the rectifiable sets E ∩ B(0, j) shows that
Tan^k(H^k⌞E, x) is a k dimensional subspace for H^k almost all x ∈ E. Hence
‖v(E)‖(B) = v(E)(B × G(n, k)) = H^k(E ∩ B) for Borel B.

The H^k⌞E measurability of g_E (blueprint al:3.5:lem) is first proved for
an (H^k, k) rectifiable set W. Federer 3.2.25 supplies an H^k⌞W measurable
orientation, a map ξ into the unit simple k vectors with Tan^k(H^k⌞W, x)
the subspace associated with ξ(x) for H^k almost all x ∈ W. The map
[ξ ↦ the orthogonal projection onto the subspace of ξ] is continuous
(new:simple_to_projection, `simple_projection_hom_continuous`), hence
Tan^k(H^k⌞W, ·) is H^k⌞W measurable. For a locally rectifiable E, the
sets E ∩ B(0, j) are rectifiable, Tan^k(H^k⌞E, ·) agrees with
Tan^k(H^k⌞(E ∩ B(0, j)), ·) on the interior of B(0, j), and measurability
on a countable cover gives measurability on E. Lusin's theorem in the form
of Federer 2.3.6 then gives a Borel map t of R^n into G(n, k) with
t = g_E at H^k almost all points of E (`set_tangent_borel_version`).

With t, v(E) is the image measure of H^k⌞E under [x ↦ (x, t(x))]
(`set_varifold_pushforward`). The graph of t is a Borel set, and E lies
between Borel sets D ⊆ E ⊆ B with H^k(B ∖ D) = 0; hence H^k⌞E is Borel
regular, and so is its image under the Borel map [x ↦ (x, t(x))]. The
image is finite on compact sets K, since K ⊆ B(0, j) × G(n, k) for some j
and H^k(E ∩ B(0, j)) < ∞. By Federer 2.2.5 it is a Radon measure. The
equality ‖v(E)‖ = H^k⌞E on all sets follows from the existence of g_E at
H^k almost all points of E, and the integral formula follows from Federer
2.4.18 applied to the image measure and from the almost everywhere
equality t = g_E. Finally, ‖Σ_i c_i v(E_i)‖ = Σ_i c_i H^k⌞E_i by the
equality for each E_i.

For 3.5(1), let V = Σ_i c_i v(E_i) and μ = ‖V‖ = Σ_i c_i H^k⌞E_i, a Radon
measure by 3.1. Blueprint new:density_tangent is proved for such μ. First,
Tan^k(μ, x) = Tan^k(H^k⌞E_i, x) for H^k almost all x ∈ E_i
(`rectifiable_sum_tangent_equal`): on the strata of Federer 3.3.18 for
μ⌞B(0, j), the tangent cones of μ⌞S and of H^k⌞S agree, and Federer
2.10.19(4) and 3.2.32 pass from the strata to μ and to H^k⌞E_i. Hence
Tan^k(μ, x) ∈ G(n, k) for μ almost all x, and Tan^k(μ, ·) is μ measurable,
being H^k⌞E_i measurable on each E_i. Secondly, Θ^k(H^k⌞E_i, x) = 1_{E_i}(x)
for H^k almost all x (Federer 3.2.19), and the tails Σ_{i ≥ N} c_i H^k⌞E_i
have small upper density outside small H^k measure (Federer 2.10.19(3));
hence Θ^k(μ, x) = θ(x) = Σ_i c_i 1_{E_i}(x) for H^k almost all x, and
0 < Θ^k(μ, x) < ∞ for μ almost all x. Thirdly, μ = H^k⌞θ: both sides agree
on H^k measurable sets by monotone convergence (Federer 2.4.8); for an
arbitrary set A, a Borel cover B of A with μ(B) = μ(A) gives
(H^k⌞θ)(A) ≤ μ(A), and H^k measurable covers C of A with
(H^k⌞θ)(C) < (H^k⌞θ)(A) + ε give μ(A) ≤ (H^k⌞θ)(A). Replacing θ by
Θ^k(μ, ·), which changes it only on an H^k null set, gives
‖V‖ = H^k⌞Θ^k(‖V‖, ·). Finally, Federer 2.3.6 gives a Borel map t equal to
Tan^k(μ, ·) μ almost everywhere and to Tan^k(H^k⌞E_i, ·) H^k almost
everywhere on each E_i; then V = [x ↦ (x, t(x))]_# μ by al:3.5:lem, and
the integral formula follows from Federer 2.4.18.
