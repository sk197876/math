(** Federer (1969), 2.10.46, p. 203, last paragraph: cover the first factor
    by small balls after estimating each cylinder. This supporting
    comparison uses the spherical covering laws and S^m=L^m from 2.10.35, p.
    197. Positive dimension allows the radius bound to be recovered from the
    diameter cutoff. this local small-ball formulation is not separately
    stated there. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallDiameter EuclideanClosedBallVolume HausdorffDiameterCost HausdorffRadiusCost
  HausdorffMeasureUP HausdorffMeasure EuclideanSphericalLebesgue MetricClosedBalls
  MeasureUP MetricDiameter MetricScaleEnvelope MetricScaleWeightedBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_ball_cost_volume]: supporting
    equality of diameter cost and volume for a closed ball in
    positive dimension, used for the coverings of 2.10.46,
    p. 203, by 2.10.2 and 2.7.16(1). *)
Lemma positive_euclidean_ball_cost_volume (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (r : R) :
  0<=r -> hausdorff_diameter_cost n.+1 (metric_closed_ball a r)=
    euclidean_lebesgue_measure n.+1 (metric_closed_ball a r).
Proof.
move=> hr; rewrite /hausdorff_diameter_cost /hausdorff_power_cost
  (euclidean_closed_ball_diameter a hr) -EFin_expe -EFinM
  hausdorff_doubled_radius_normalisation.
exact: esym (euclidean_closed_ball_normalized_volume a hr).
Qed.

(** Source for [small_ball_measure_lebesgue_bound]: supporting
    first-factor covering passage in 2.10.46, p. 203.
    A measure bounded by b times volume on every sufficiently
    small closed ball is bounded by b times Lebesgue outer
    measure on every subset. No regularity of mu is assumed. *)
Theorem small_ball_measure_lebesgue_bound (R : realType) n
    (mu : set (inner_metric_space (@euclidean_inner_productP R n.+1)) -> \bar R)
    (b cap : R) :
  is_measure mu -> 0<b -> 0<cap ->
  (forall a r, 0<r -> r<=cap ->
    (mu (metric_closed_ball a r)<=b%:E*euclidean_lebesgue_measure n.+1 (metric_closed_ball a r))%E) ->
  forall A, (mu A<=b%:E*euclidean_lebesgue_measure n.+1 A)%E.
Proof.
move=> hm hb hcap hball A.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)].
pose J := @positive_closed_metric_balls R X.
pose S := fun j : J=>val j.
pose c := fun j : J=>@hausdorff_diameter_cost R X n.+1 (val j).
pose eta := (cap+cap)%:E.
pose nu := metric_scale_envelope S c eta.
have hn := metric_scale_envelope_specification S c eta.
have hgen j : (extended_metric_diameter (S j)<=eta)%E -> (mu (S j)<=b%:E*c j)%E.
  have [a [r [hr he]]] := set_valP j.
  have heq : S j=metric_closed_ball a r by apply/seteqP; split=> x hx; [exact: (he x).1 hx|exact: (he x).2 hx].
  change ((extended_metric_diameter (S j)<=eta)%E ->
    (mu (S j)<=b%:E*hausdorff_diameter_cost n.+1 (S j))%E).
  rewrite heq.
  rewrite (positive_euclidean_ball_cost_volume a (ltW hr)) (euclidean_closed_ball_diameter a (ltW hr)).
  move=> hdiam; have hrcap : r<=cap by move: hdiam; rewrite /eta lee_fin=> hh; lra.
  exact: hball a r hr hrcap.
have hbound := @measure_bounded_by_scaled_metric_envelope R X J S c eta nu mu b hn hm hb hgen A.
apply: le_trans hbound _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW hb.
apply: le_trans _ (@euclidean_spherical_measure_lebesgue_bound R n.+1 A).
apply: (@caratheodory_limit_upper R X J S c (@spherical_measure R X n.+1)
  (@spherical_measure_specification R X n.+1) A eta nu _ hn).
by rewrite /eta lte_fin addr_gt0.
Qed.
