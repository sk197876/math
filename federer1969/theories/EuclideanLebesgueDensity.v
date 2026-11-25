(** Federer (1969), 2.10.35, printed p. 197: the n-dimensional density of
    Lebesgue measure is one at every point, as used in its application of
    2.10.19(3), p. 181. Derive it from the already proved actual closed-ball
    volume; only positive radii enter the upper and lower limits. All
    natural dimensions are retained. No relevant correction occurs in
    Federer's working erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanClosedBallVolume EuclideanBallVolume
  MetricDensities PositiveRadiusLimitCongruence PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lebesgue_ball_density]: supporting
    exact ball quotient in 2.10.35,
    p. 197, from the ball-volume formula
    of 2.7.16(1), p. 135. Positive
    radii ensure a positive finite denominator. *)
Lemma euclidean_lebesgue_ball_density (R : realType) (n : nat)
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<r -> metric_ball_density n (@euclidean_lebesgue_measure R n) a r= 1%E.
Proof.
move=> hr; rewrite /metric_ball_density (euclidean_closed_ball_normalized_volume a (ltW hr)).
have hn : euclidean_unit_ball_volume R n*r^+n!= 0.
  by rewrite gt_eqF //; exact: metric_ball_density_denominator_positive hr.
by rewrite inver (negbTE hn) -EFinM divff.
Qed.

(** Source for [euclidean_lebesgue_upper_lower_density]: direct
    density-one fact used in 2.10.35,
    p. 197, with both limiting values
    recorded separately for the partial density. *)
Theorem euclidean_lebesgue_upper_lower_density (R : realType) (n : nat)
    (a : inner_metric_space (@euclidean_inner_productP R n)) :
  upper_metric_density n (@euclidean_lebesgue_measure R n) a= 1%E /\
  lower_metric_density n (@euclidean_lebesgue_measure R n) a= 1%E.
Proof.
have [hu hl] := @positive_radius_limits_congr R
  (metric_ball_density n (@euclidean_lebesgue_measure R n) a) (fun _=>1%E)
  (fun r hr=>euclidean_lebesgue_ball_density a hr).
have [hc hd] := @positive_radius_limits_constant R 1%E.
by split; [rewrite /upper_metric_density hu hc|rewrite /lower_metric_density hl hd].
Qed.

(** Source for [euclidean_lebesgue_density_one]: direct
    common-density assertion in the proof of
    2.10.35, p. 197. It belongs
    to the actual partial density's graph,
    rather than assigning a default value. *)
Corollary euclidean_lebesgue_density_one (R : realType) (n : nat)
    (a : inner_metric_space (@euclidean_inner_productP R n)) :
  partial_function_graph (metric_density n (@euclidean_lebesgue_measure R n)) a 1%E.
Proof. exact: euclidean_lebesgue_upper_lower_density. Qed.
