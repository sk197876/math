(** Federer (1969), 3.2.41, printed pp. 277--278:
    zero and infinite original factor volumes are handled by
    translates contained in the actual sum. No measurability
    of either source or its sum is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  VectorSetSum EuclideanVectorSumVolume EuclideanVolumeRootSum
  ExtendedPositivePower MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [brunn_minkowski_zero_left]: supporting zero-factor
    boundary of Federer 3.2.41, pp. 277--278. A point of the
    original zero-volume factor supplies the required translate. *)
Lemma brunn_minkowski_zero_left (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->A !=set0 ->@euclidean_lebesgue_measure R n A=0%E ->
  euclidean_volume_root_sum_bound A B.
Proof.
move=> hn hA hZero.
have hp:(0<(n%:R:R)^-1)%R by rewrite invr_gt0 ltr0n.
rewrite /euclidean_volume_root_sum_bound hZero (extended_positive_power_zero hp) add0e.
exact:(@extended_positive_power_monotone R _ _ (n%:R)^-1
  (measure_nonnegative (euclidean_lebesgue_is_measure R n) B)
  (@euclidean_vector_sum_volume_lower_right R n A B hA) hp).
Qed.

(** Source for [brunn_minkowski_infinite_left]: supporting infinite
    factor boundary of Federer 3.2.41, pp. 277--278. The actual
    sum has infinite outer volume because it contains a translate
    of the infinite-volume source. The other source need only be
    nonempty; its own volume may also be infinite. *)
Lemma brunn_minkowski_infinite_left (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  B !=set0 ->@euclidean_lebesgue_measure R n A= +oo%E ->
  euclidean_volume_root_sum_bound A B.
Proof.
move=> hB hInfinite.
have hBelow:=@euclidean_vector_sum_volume_lower_left R n A B hB.
rewrite hInfinite in hBelow.
have hSum:@euclidean_lebesgue_measure R n (vector_set_sum A B)= +oo%E.
  apply/eqP; by rewrite eq_le hBelow leey.
rewrite /euclidean_volume_root_sum_bound hSum /extended_positive_power.
exact:leey.
Qed.
