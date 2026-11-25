(** Supporting Federer (1969), 2.10.46, p. 204: a Borel superset of U times
    V, with V Borel, admits a Lebesgue-measurable enlargement of U whose
    rectangle stays inside that superset. Its complement is the first
    projection of the Borel part outside the superset. Apply 2.2.13, pp.
    69–70, to this continuous image; do not assume that the image itself is
    Borel. The existence conclusion is auxiliary, not an additional measure
    axiom. The source for the continuous-image theorem is recorded in
    BorelImageMeasurability.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanMetricCompleteness EuclideanMetricSeparability MetricProductRectangles EuclideanRectangleBorel
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP MeasureBasic MeasureFiniteClosure
  TopologicalBorel BorelRegularMeasureUP BorelImageMeasurability TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_rectangle_first_measurable_hull]:
    supporting removal of first-factor measurability in the
    Gross product equality of 2.10.46, p. 204, by
    2.2.13, pp. 69–70. The second factor and the
    containing set are Borel; the first factor is arbitrary. *)
Theorem euclidean_rectangle_first_measurable_hull (R : realType) m n
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (H : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) :
  borel_set V -> borel_set H ->
  metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V `<=` H ->
  exists W, U `<=` W /\ measure_measurable (@euclidean_lebesgue_measure R m) W /\
    metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) W V `<=` H.
Proof.
move=> hV hH hsub.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))].
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose first := fun z : P=>(@euclidean_block_split R m n z).1.
pose second := fun z : P=>(@euclidean_block_split R m n z).2.
pose B := metric_product_rectangle first second setT V `\` H.
have hB : borel_set B.
  apply: borel_set_difference _ hH.
  apply: euclidean_rectangle_borel _ hV; exact: open_borel_set openT.
have hfirst : continuous first.
  move=> z; apply: continuous_comp (@euclidean_block_split_continuous R m n z) _.
  exact: first_projection_continuous.
have hm := euclidean_lebesgue_is_measure R m.
have hr := euclidean_lebesgue_borel_regular R m.
have [D [hD hden]] := euclidean_metric_separable R (m+n).
have hi : measure_measurable (@euclidean_lebesgue_measure R m) (first @` B).
  apply: (@continuous_borel_image_measurable R P X first _ hm B
    (@euclidean_metric_complete R (m+n)) (ex_intro _ D (conj hD hden))
    (@metric_hausdorff R X) hfirst _ hB).
  move=> C hC; apply: (borel_regular_borel_measurable hm hr); exact: closed_borel_set hC.
exists (~` (first @` B)); split.
  move=> x hx [z [[_ hz] hn] he]; apply: hn; apply: hsub; split=> //.
  change (U (first z)); by rewrite he.
split; first exact: measure_measurable_complement hi.
move=> z [hz hv]; apply: contrapT=> hn; apply: hz.
exists z=> //; split=> //; by split.
Qed.
