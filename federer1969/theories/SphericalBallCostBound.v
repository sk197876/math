(** Ball cost comparison supporting Federer (1969), 2.10.19(3)–(5), p. 181.
    This concerns the initial integer degrees and includes zero-diameter
    positive-radius balls. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter EuclideanBallDiameter
  HausdorffDiameterCost HausdorffPowerCostLaws EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_ball_cost_bound]: supporting normalized ball cost
    bound for 2.10.19(3)–(5), p. 181 The radius is positive even when the
    diameter is zero. *)
Lemma spherical_ball_cost_bound (R : realType) (X : metricType R)
    (m : nat) (a : X) (r : R) : 0<r ->
  (hausdorff_diameter_cost m (metric_closed_ball a r)<=(euclidean_unit_ball_volume R m*r^+m)%:E)%E.
Proof.
move=> hr.
have hd := metric_ball_diameter_upper a (ltW hr).
have hh := @hausdorff_power_cost_monotone R m (extended_metric_diameter (metric_closed_ball a r))
  (r+r)%:E (metric_diameter_nonnegative (extended_metric_diameter_specification _)) hd.
have h2 : (2 : R)^+m!=0 by rewrite expf_neq0 // pnatr_eq0.
have he : hausdorff_normalisation R m*(r+r)^+m=euclidean_unit_ball_volume R m*r^+m.
  rewrite -mulr2n -mulr_natl exprMn mulrA /hausdorff_normalisation divfK //.
move: hh; by rewrite hausdorff_power_cost_finite he.
Qed.
