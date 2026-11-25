(** Federer (1969), 3.1.4, p. 215: almost-everywhere
    measurability of the prefix slices needed in the Fubini estimate.
    The ambient dimension is fixed while the prefix length varies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanPrefixTranslation EuclideanSliceTranslation
  EuclideanAlmostMeasurableSlices EuclideanMeasurableSetSlices
  RealMetricBackground PartialFunctionUP PartialFunctionPrecomposition
  MeasurableFunctionUP MeasureUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_almost_measurable_prefix_slices]:
    the coordinate slice qualification in the proof of Federer 3.1.4,
    p. 215, from 3.1.3(4), p. 213. The empty prefix is retained. *)
Theorem euclidean_almost_measurable_prefix_slices (R : realType) m k
    (g : partial_function (inner_metric_space (@euclidean_inner_productP R m))
      (real_line_metric R)) :
  (k<=m)%N ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) g ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) [set a |
    is_measure_measurable_function (@euclidean_lebesgue_measure R k)
      (partial_function_precompose (@euclidean_prefix_translation R m k a) g)].
Proof.
move=> hk hg.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: g hg; rewrite hn=> g hg.
have he : @euclidean_prefix_translation R (k+(m-k)) k=
    @euclidean_slice_translation R k (m-k).
  apply: funext=> a; apply: funext=> z; exact: euclidean_prefix_translation_blocks.
rewrite he; exact: euclidean_almost_measurable_translated_slices hg.
Qed.

(** Source for [euclidean_almost_measurable_prefix_set_slices]:
    the measurable B sections in the exceptional-set estimate of
    Federer 3.1.4, p. 215. Measurability is asserted almost everywhere,
    not for every restriction to a lower-dimensional affine plane. *)
Theorem euclidean_almost_measurable_prefix_set_slices (R : realType) m k
    (B : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (k<=m)%N -> measure_measurable (@euclidean_lebesgue_measure R m) B ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) [set a |
    measure_measurable (@euclidean_lebesgue_measure R k)
      ((@euclidean_prefix_translation R m k a) @^-1` B)].
Proof.
move=> hk hB.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: B hB; rewrite hn=> B hB.
have he : @euclidean_prefix_translation R (k+(m-k)) k=
    @euclidean_slice_translation R k (m-k).
  apply: funext=> a; apply: funext=> z; exact: euclidean_prefix_translation_blocks.
rewrite he; exact: euclidean_almost_measurable_translated_set_slices hB.
Qed.
