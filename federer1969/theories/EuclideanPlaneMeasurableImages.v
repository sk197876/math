(** Federer (1969), 2.5.10, p. 101: measurability of projected Borel subsets
    of the plane, supplied by 2.2.13, pp. 69–70, as required in 2.10.10, p.
    176. The actual Euclidean topology is retained; the homeomorphic
    Cartesian presentation supplies the complete separable source. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  RealMetricCompleteness RealLineSeparability MetricProductBackground
  MetricProductCompleteness MetricProductSeparability CompleteMetricUP
  EuclideanPlaneCoordinates EuclideanCoordinateTopology ContinuousRetractSource
  MeasureUP BorelRegularMeasureUP TopologicalBorel LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(** Source for [euclidean_plane_separable]: supporting
    separability of R^2 in Federer 2.5.10, p. 101,
    for the Borel partition theorem 2.10.10, p. 176. *)
Lemma euclidean_plane_separable (R : realType) :
  exists D : set (inner_metric_space (@euclidean_inner_productP R 2)),
    countable D /\ dense D.
Proof.
refine (@continuous_retraction_separable
  [the topologicalType of metric_product [the metricType R of real_line_metric R]
    [the metricType R of real_line_metric R]]
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R 2)]
  (@euclidean_plane_join R) (@euclidean_plane_split R)
  (@euclidean_plane_join_continuous R) (@euclidean_plane_splitK R) _).
exact: separable_metric_product (real_line_countable_dense R) (real_line_countable_dense R).
Qed.

(** Source for [euclidean_plane_coordinate_borel_image]:
    direct application of Federer 2.2.13, pp. 69–70,
    to the projection in 2.5.10, p. 101.
    The conclusion is Lebesgue measurability, not Borelness
    of the projected set. Both scalar coordinates are allowed. *)
Lemma euclidean_plane_coordinate_borel_image (R : realType) (i : 'I_2)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  borel_set A -> measure_measurable (@lebesgue_scalar_measure R) ((fun x => x i) @` A).
Proof.
move=> hA.
pose T := [the metricType R of real_line_metric R].
pose P := [the metricType R of metric_product T T].
apply: (@continuous_retract_borel_image_measurable R P
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R 2)] T
  (@euclidean_plane_join R) (@euclidean_plane_split R) (fun x => x i)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  _ _ (@euclidean_plane_join_continuous R) (@euclidean_plane_splitK R)
  (@metric_hausdorff R T) (@euclidean_coordinate_continuous R 2 i) _ A hA).
- exact (@complete_metric_product R T T (@real_line_metric_complete R) (@real_line_metric_complete R)).
- exact: separable_metric_product (real_line_countable_dense R) (real_line_countable_dense R).
- move=> C hC; exact (@borel_regular_borel_measurable R T (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) C (closed_borel_set hC)).
Qed.
