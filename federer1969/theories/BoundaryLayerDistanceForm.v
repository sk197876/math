(** Federer (1969), 3.2.42, printed p. 278:
    recover both literal printed distance-strip inequalities
    from the exact tube, closure and core forms. Distance
    functions are arbitrary representatives satisfying the
    already established infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume RealPower BoundaryLayerVolume MetricDistanceBoundaryLayers
  MetricSetDistanceUP MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_42_distance_strips]: literal
    distance-strip form of Federer 3.2.42, p. 278, in
    dimensions at least two. Only the independent distance
    laws identify the supplied representatives. Finite
    closure volume is the original hypothesis; the actual
    source may be nonmeasurable and unbounded. *)
Theorem federer_3_2_42_distance_strips (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+2)))
    (d e:inner_metric_space (@euclidean_inner_productP R k.+2)->R) (r:R):
  is_metric_set_distance S d ->is_metric_set_distance (~`S) e ->
  (@euclidean_lebesgue_measure R k.+2 (closure S) < +oo)%E ->0<r ->
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2 (closure S)))
      ((k.+1)%:R/(k.+2)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+2 [set x | (0<d x<r)%R]*r^-1%:E)%E /\
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2 [set x | (r<=e x)%R]))
      ((k.+1)%:R/(k.+2)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+2 [set x | (0<e x<r)%R]*r^-1%:E)%E.
Proof.
move=>hD hE hFinite hr.
have [hOuter hInner]:=@federer_3_2_42 R k S r hFinite hr.
rewrite (@metric_positive_distance_strip R _ S d r hD) (@metric_distance_inner_core R _ S e r hE)
  (@metric_complement_positive_strip R _ S e r hE).
exact:(conj hOuter hInner).
Qed.
