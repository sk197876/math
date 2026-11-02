(** Federer (1969), 3.1.3(4), p. 213: the set E where the section
    approximate limit equals the given measurable value is measurable.
    This expands the printed application of (2) and retains partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RealMetricBackground
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions CenteredBallRelations
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialProductSections
  MeasureUP MeasureFiniteClosure MeasurableFunctionUP MeasurablePostcomposition
  BorelFunctionBasic MeasurableRealEmbedding ExtendedRealOrderTopology
  ProductMeasure MeasureApproximateLimitUP MeasureApproximateOrderLimits
  EuclideanApproximateOrderMeasurable EuclideanApproximateRealOrder MeasurableExtendedAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_approximate_limit_locus_measurable]: the
    measurable set E in Federer 3.1.3(4), p. 213. The two approximate
    order limits are total extended-real functions; the comparison value
    is required to exist on the actual domain of h. *)
Theorem euclidean_approximate_limit_locus_measurable (R : realType) m k
    (f : partial_function
      (inner_metric_space (@euclidean_inner_productP R m) *
       inner_metric_space (@euclidean_inner_productP R k)) (real_line_metric R))
    (h : partial_function (inner_metric_space (@euclidean_inner_productP R m)) (real_line_metric R)) :
  is_measure_measurable_function (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) h ->
  measure_measurable (@euclidean_lebesgue_measure R m) [set x | exists c,
    partial_function_graph h x c /\
    is_measure_approximate_limit (@euclidean_lebesgue_measure R k)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
      (partial_product_vertical_section f x) (0 : R_n R k) c].
Proof.
move=> hf hh.
pose F := partial_function_postcompose f (fun y : real_line_metric R=>(y%:E : extended_real_line R)).
pose H := partial_function_postcompose h (fun y : real_line_metric R=>(y%:E : extended_real_line R)).
have hF : is_measure_measurable_function (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) F.
  apply: (@measurable_function_borel_postcomposition R _ _ _ _
    (product_measure_is_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R k))
    f _ hf).
  apply: continuous_borel_function; exact: real_extended_embedding_continuous.
have hH : is_measure_measurable_function (@euclidean_lebesgue_measure R m) H.
  apply: (@measurable_function_borel_postcomposition R _ _ _ _
    (euclidean_lebesgue_is_measure R m) h _ hh).
  apply: continuous_borel_function; exact: real_extended_embedding_continuous.
pose V := @centered_closed_ball_relation R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
pose U := partial_function_total (fun x=>measure_approximate_upper_limit
  (@euclidean_lebesgue_measure R k) V (partial_product_vertical_section F x) (0 : R_n R k)).
pose L := partial_function_total (fun x=>measure_approximate_lower_limit
  (@euclidean_lebesgue_measure R k) V (partial_product_vertical_section F x) (0 : R_n R k)).
have hU := euclidean_approximate_upper_limit_measurable hF.
have hL := euclidean_approximate_lower_limit_measurable hF.
have he : [set x | exists c, partial_function_graph h x c /\
    is_measure_approximate_limit (@euclidean_lebesgue_measure R k) V
      (partial_product_vertical_section f x) (0 : R_n R k) c]=
    partial_function_agreement H U `&` partial_function_agreement H L.
  apply/seteqP; split.
  - move=> x [c [hc hlim]].
    have [hu hl] := (euclidean_approximate_real_order_iff
      (partial_product_vertical_section f x) (0 : R_n R k) c).1 hlim.
    split; exists c%:E; split; first by exists c.
    + exact hu.
    + by exists c.
    + exact hl.
  - move=> x [[u [[y [hy <-]] hu]] [v [[z [hz <-]] hl]]].
    have hyz := partial_function_single_valued hy hz; rewrite -hyz in hl.
    exists y; split=> //.
    apply: (euclidean_approximate_real_order_iff
      (partial_product_vertical_section f x) (0 : R_n R k) y).2; by split.
change (measure_measurable (@euclidean_lebesgue_measure R m)
  [set x | exists c, partial_function_graph h x c /\
    is_measure_approximate_limit (@euclidean_lebesgue_measure R k) V
      (partial_product_vertical_section f x) (0 : R_n R k) c]).
rewrite he; apply: (@measure_measurable_intersection R _ _ (euclidean_lebesgue_is_measure R m)).
- exact: measurable_extended_agreement (euclidean_lebesgue_is_measure R m) hH hU.
- exact: measurable_extended_agreement (euclidean_lebesgue_is_measure R m) hH hL.
Qed.
