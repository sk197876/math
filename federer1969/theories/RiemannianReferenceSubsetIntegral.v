(** Federer (1969), 3.2.46, p. 282: actual
    coordinate transport of subset integrals, using 2.4.18,
    p. 90, and the original subset convention of
    2.4.10, p. 85. The original measurable source
    and partial integrand graphs are retained exactly. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianReferenceSetImage
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureRestriction MeasurePushforward MeasureSubsetIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence RestrictedIntegralIdentity
  InjectivePushforwardIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_reference_restricted_pushforward]:
    exact coordinate image measure of the original reference
    measure restricted to any S, supporting 3.2.46,
    p. 282. Equality holds on every target test set;
    no measurability of S is needed for this outer law. *)
Theorem riemannian_reference_restricted_pushforward (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (S : set (riemannian_metric_space hg)) :
  measure_pushforward (fun x : riemannian_metric_space hg=>val x)
    (measure_restrict (@riemannian_chart_reference R m A g hg) S)=
  measure_restrict (@euclidean_lebesgue_measure R m)
    ((fun x : riemannian_metric_space hg=>val x) @` S).
Proof.
apply: funext=> T.
rewrite /measure_pushforward /measure_restrict riemannian_chart_reference_value.
congr (euclidean_lebesgue_measure m _).
apply/seteqP; split=> z.
- by move=> [x [hx hT] <-]; split; first exists x.
- move=> [[x hx <-] hT]; exists x; last by [].
  by split.
Qed.

(** Source for [riemannian_reference_subset_integral_iff]:
    actual reference-volume subset integral equals its
    ordinary coordinate integral, supporting 3.2.46, p. 282.
    The two partial integrands need agree only on the
    original S. Signed infinite values and undefined
    integral differences are preserved in both directions. *)
Theorem riemannian_reference_subset_integral_iff (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (S : set (riemannian_metric_space hg))
    (K : partial_function (riemannian_metric_space hg) (extended_real_line R))
    (L : partial_function (R_n R m) (extended_real_line R)) :
  measure_measurable (@riemannian_chart_reference R m A g hg) S ->
  (forall x, S x -> forall z, partial_function_graph K x z <-> partial_function_graph L (val x) z) ->
  forall a, is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S K a <->
    is_measure_subset_integral (@euclidean_lebesgue_measure R m)
      ((fun x : riemannian_metric_space hg=>val x) @` S) L a.
Proof.
move=> hS hAgreement a.
pose X := [the choiceType of riemannian_metric_space hg].
pose E := [the choiceType of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R m A g hg.
pose v := fun x : X=>(val x : E).
pose P := partial_function_precompose v L.
pose T := v @` S.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hT := @riemannian_reference_coordinate_image_measurable R m A g hg S hS.
have hCut x z : partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) S K) x z <->
    partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) S P) x z.
  rewrite !partial_function_zero_extension_graph.
  split.
  - move=> [[hx hz]|[hx hz]].
    + left; split; first exact hx; exact: (hAgreement x hx z).1 hz.
    + right; by split.
  - move=> [[hx hz]|[hx hz]].
    + left; split; first exact hx; exact: (hAgreement x hx z).2 hz.
    + right; by split.
have hInj : injective v by move=> x y h; exact: val_inj h.
have hTransport := @injective_pushforward_integral_iff R X E
  (measure_restrict phi S) (measure_restrict_is_measure hPhi S) v L hInj a.
split=> hi.
- have hP := measure_integral_graph_equivalent hCut hi.
  have hRestricted := (@restricted_integral_zero_extension_iff R X phi hPhi S P a hS).2 hP.
  have hPush := hTransport.1 hRestricted.
  rewrite /v riemannian_reference_restricted_pushforward in hPush.
  exact: (@restricted_integral_zero_extension_iff R E (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) T L a hT).1 hPush.
- have hRestricted := (@restricted_integral_zero_extension_iff R E (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) T L a hT).2 hi.
  have hPush : is_measure_integral (measure_pushforward v (measure_restrict phi S)) L a.
    by rewrite /v riemannian_reference_restricted_pushforward.
  have hP := (@restricted_integral_zero_extension_iff R X phi hPhi S P a hS).1
    (hTransport.2 hPush).
  exact: measure_integral_graph_equivalent (fun x z=>iff_sym (hCut x z)) hP.
Qed.
