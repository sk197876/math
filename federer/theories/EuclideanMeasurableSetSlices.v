(** Federer (1969), 3.1.4, p. 215: almost every translated
    coordinate slice of the measurable cutoff set B is measurable.
    This expands the section-measurability justification for Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBlockMeasure EuclideanSliceTranslation EuclideanEpimorphismMeasurable
  MeasureUP MeasureAlmostUP ProductMeasure ProductSections ProductSetFubini
  PushforwardMeasurableSets CountablyMeasurableUP CountablyMeasurableSubsets
  CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_translated_set_slices_measurable]:
    supporting joint measurability of translated copies of B in
    Federer 3.1.4, pp. 214–215, by the epimorphism in 3.1.3(4). *)
Lemma euclidean_translated_set_slices_measurable (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l)))) :
  measure_measurable (@euclidean_lebesgue_measure R (k+l)) B ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R (k+l))
    (euclidean_lebesgue_is_measure R k))
    [set az | B (@euclidean_slice_translation R k l az.1 az.2)].
Proof.
move=> hB; rewrite -euclidean_block_measure.
apply: pushforward_measurable_from_preimage.
change (measure_measurable (@euclidean_lebesgue_measure R ((k+l)+k))
  ((@euclidean_slice_sum R k l) @^-1` B)).
exact: euclidean_epimorphism_preimage_measurable (@euclidean_slice_sum_surjective R k l) hB.
Qed.

(** Source for [euclidean_almost_measurable_translated_set_slices]:
    supporting Fubini qualification for the pointwise exceptional-set
    bounds in Federer 3.1.4, p. 215. It is an almost-everywhere
    conclusion, not measurability of every affine restriction. *)
Theorem euclidean_almost_measurable_translated_set_slices (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l)))) :
  measure_measurable (@euclidean_lebesgue_measure R (k+l)) B ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R (k+l)) [set a |
    measure_measurable (@euclidean_lebesgue_measure R k)
      ((@euclidean_slice_translation R k l a) @^-1` B)].
Proof.
move=> hB.
have hm := euclidean_translated_set_slices_measurable hB.
have hc : measure_countably_measurable (product_measure
    (euclidean_lebesgue_is_measure R (k+l)) (euclidean_lebesgue_is_measure R k))
    [set az | B (@euclidean_slice_translation R k l az.1 az.2)].
  apply: (measurable_subset_countably_measurable
    (product_measure_is_measure (euclidean_lebesgue_is_measure R (k+l))
      (euclidean_lebesgue_is_measure R k)) hm (fun _ _=>Logic.I)).
  exact: product_whole_countably_measurable
    (euclidean_lebesgue_countably_measurable R (k+l))
    (euclidean_lebesgue_countably_measurable R k).
exact: (product_set_fubini hc).1.
Qed.
