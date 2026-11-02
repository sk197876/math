(** Federer (1969), 3.1.3(4), p. 213: a measurable real function
    is approximately continuous along its first k coordinates at almost
    every point. The proof follows the two Fubini applications and 2.9.13. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RealMetricBackground RealLineSeparability
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanApproximateContext
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanSliceTranslation
  EuclideanBlockMeasurableFunctions EuclideanSliceMeasurability
  EuclideanApproximateLimitLocus EuclideanApproximateTranslation ApproximateLimitGraphEquivalence
  PartialFunctionUP PartialFunctionPrecomposition PartialProductSections ProductSections
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasurePushforward
  PushforwardMeasurableSets ProductMeasure ProductMeasurableOrderSections
  ProductAlmostEverywhereSections MeasurableFunctionUP MeasurableRealPairs
  MeasureApproximateLimitUP MeasurableApproximateContinuity CenteredBallRelations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_almost_slice_approximate_continuity]: the
    whole assertion (4) in Federer 3.1.3, p. 213. The ambient dimension
    is written k+l, so every k not exceeding it is represented. The
    conclusion includes an actual value of g at almost every point,
    with the original partial domains in every translated section. *)
Theorem euclidean_almost_slice_approximate_continuity (R : realType) k l
    (g : partial_function (inner_metric_space (@euclidean_inner_productP R (k+l))) (real_line_metric R)) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R (k+l)) g ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R (k+l)) [set a | exists c,
    partial_function_graph g a c /\ is_measure_approximate_limit (@euclidean_lebesgue_measure R k)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
      (partial_function_precompose (@euclidean_slice_translation R k l a) g) (0 : R_n R k) c].
Proof.
move=> hg.
pose F := partial_function_precompose (fun xz=>@euclidean_slice_translation R k l xz.1 xz.2) g.
pose G := partial_function_precompose (@euclidean_block_join R k l) g.
pose V := @centered_closed_ball_relation R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
pose P := [set a | exists c, partial_function_graph g a c /\
  is_measure_approximate_limit (@euclidean_lebesgue_measure R k) V
    (partial_function_precompose (@euclidean_slice_translation R k l a) g) (0 : R_n R k) c].
have hF := euclidean_translated_slices_measurable hg.
have hP : measure_measurable (@euclidean_lebesgue_measure R (k+l)) P.
  exact: euclidean_approximate_limit_locus_measurable hF hg.
have hG := euclidean_block_join_measurable_precompose hg.
have hsections := @product_almost_measurable_order_sections R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R l)] _
  [the orderTopologicalType _ of R^o] [the countType of (rat : Type)]
  (@euclidean_lebesgue_measure R k) (@euclidean_lebesgue_measure R l)
  (euclidean_lebesgue_is_measure R k) (euclidean_lebesgue_is_measure R l)
  (fun q=>ratr q) G (euclidean_lebesgue_countably_measurable R k)
  (euclidean_lebesgue_countably_measurable R l) (@real_rationals_order_dense R) hG.
pose Q := (@euclidean_block_join R k l) @^-1` P.
have hQ : measure_measurable (product_measure (euclidean_lebesgue_is_measure R k)
    (euclidean_lebesgue_is_measure R l)) Q.
  rewrite -euclidean_block_measure; apply: pushforward_measurable_from_preimage.
  have he : (@euclidean_block_split R k l) @^-1` Q = P.
    apply/seteqP; split=> x; change (P (euclidean_block_join (euclidean_block_split x))->P x) ||
      change (P x->P (euclidean_block_join (euclidean_block_split x)));
      by rewrite euclidean_block_splitK.
  by rewrite he.
have hQa : measure_almost_everywhere (@euclidean_lebesgue_measure R l) [set v |
    measure_almost_everywhere (@euclidean_lebesgue_measure R k) (product_horizontal_section Q v)].
  apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R l)
    _ _ _ hsections)=> v hv.
  have [D [hDc hDd]] := real_line_countable_dense R.
  have hcont := @measurable_almost_approximately_continuous R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]
    [the metricType R of real_line_metric R] (@euclidean_lebesgue_measure R k) V D
    (partial_product_horizontal_section G v) (euclidean_approximate_context R k) hDc hDd hv.
  apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R k)
    _ _ _ hcont)=> u [c [hc hlim]].
  exists c; split; first exact hc.
  have hlim0 : is_measure_approximate_limit (@euclidean_lebesgue_measure R k) V
      (partial_product_horizontal_section G v) (u+0) c by rewrite addr0.
  have htr := @euclidean_approximate_limit_translation R k u (0 : R_n R k)
    [the topologicalType of real_line_metric R] (partial_product_horizontal_section G v) c hlim0.
  apply: (@approximate_limit_graph_equivalent R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]
    [the topologicalType of real_line_metric R] _ _ _ _ _ _ _ htr)=> z y.
  change (partial_function_graph g (euclidean_block_join (u+z,v)) y <->
    partial_function_graph g (euclidean_slice_translation (euclidean_block_join (u,v)) z) y).
  by rewrite euclidean_slice_translation_blocks.
have hproduct := product_almost_everywhere_from_horizontal_sections
  (euclidean_lebesgue_countably_measurable R k) (euclidean_lebesgue_countably_measurable R l) hQ hQa.
change (measure_almost_everywhere (@euclidean_lebesgue_measure R (k+l)) P).
move: hproduct; rewrite /measure_almost_everywhere -euclidean_block_measure /measure_pushforward.
have he : (@euclidean_block_split R k l) @^-1` (~` Q) = ~` P.
  apply/seteqP; split=> x; change (~P (euclidean_block_join (euclidean_block_split x))->~P x) ||
    change (~P x->~P (euclidean_block_join (euclidean_block_split x)));
    by rewrite euclidean_block_splitK.
by rewrite he.
Qed.
