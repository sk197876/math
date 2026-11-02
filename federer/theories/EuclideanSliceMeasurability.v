(** Federer (1969), 3.1.3(4), p. 213: g composed with
    alpha(u,v,z)=(u+z,v) is jointly measurable, by (3). *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBlockCoordinates EuclideanSliceTranslation
  EuclideanEpimorphismNull EuclideanBlockMeasurableFunctions ProductMeasure
  PartialFunctionUP PartialFunctionPrecomposition MeasurableFunctionUP MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_translated_slices_measurable]: the first
    inference in the proof of Federer 3.1.3(4), p. 213. The printed
    linear epimorphism and the ordinary block measure identification
    supply joint measurability, including its conull-domain requirement. *)
Theorem euclidean_translated_slices_measurable (R : realType) k l
    (Y : topologicalType)
    (g : partial_function (inner_metric_space (@euclidean_inner_productP R (k+l))) Y) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R (k+l)) g ->
  is_measure_measurable_function (product_measure (euclidean_lebesgue_is_measure R (k+l))
    (euclidean_lebesgue_is_measure R k))
    (partial_function_precompose (fun xz=>@euclidean_slice_translation R k l xz.1 xz.2) g).
Proof.
move=> hg.
pose p := GRing.Linear.clone _ _ _ _ (@euclidean_slice_sum R k l) _.
have hp := @euclidean_slice_sum_surjective R k l.
have hm := euclidean_epimorphism_measurable_precompose (p:=p) hp hg.
have hj := euclidean_block_join_measurable_precompose hm.
apply: (@measurable_function_graph_equivalent R _ Y _ _ _ _ hj).
move=> [x z] y.
change (partial_function_graph g (euclidean_slice_sum (euclidean_block_join (x,z))) y <->
  partial_function_graph g (euclidean_slice_translation x z) y).
by rewrite /euclidean_slice_sum euclidean_block_joinK.
Qed.
