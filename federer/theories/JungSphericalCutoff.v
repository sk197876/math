(** Federer (1969), 2.10.42, printed p. 201: compare the spherical and
    Hausdorff covering costs through Jung's containing-ball estimate. Keep
    the estimate at a fixed spherical cutoff before taking the final
    supremum. Natural degrees, including zero, use the existing alpha(m)
    normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric
  HausdorffMeasureUP HausdorffDiameterCost HausdorffPowerCostLaws
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP EuclideanMinimumBallUP
  BoundedJungBall JungConstant SphericalCutoffContainingBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_power_cost_finite_scale]: supporting
    cost factor in 2.10.42, p. 201.
    Multiplying a finite diameter by q multiplies
    its natural-degree cost by q to power m.
    This is an algebraic consequence of 2.10.2's
    printed normalised power cost, p. 171. *)
Lemma hausdorff_power_cost_finite_scale (R : realType) m (q d : R) :
  hausdorff_power_cost m (q*d)%:E=
    ((q^+m)%:E*hausdorff_power_cost m d%:E)%E.
Proof.
rewrite !hausdorff_power_cost_finite -EFinM exprMn.
congr (_%:E); ring.
Qed.

(** Source for [jung_spherical_cutoff_generator_bound]: direct
    covering-generator step for 2.10.42, p. 201.
    A nonempty set of diameter at most d can be
    covered at spherical cutoff t for cost at most
    q^m times its diameter-d Hausdorff cost, when q d<t
    and q=sqrt(2n/(n+1)). The actual minimum ball
    may have radius zero; positive enlarged balls
    are used by the cutoff lemma. *)
Lemma jung_spherical_cutoff_generator_bound (R : realType) n m
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d t : R) :
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) t%:E nu ->
  A !=set0 -> 0<=d -> @jung_factor R n*d<t -> (extended_metric_diameter A<=d%:E)%E ->
  (nu A<=((@jung_factor R n)^+m)%:E*hausdorff_power_cost m d%:E)%E.
Proof.
move=> hn hne hd hcap hdiam.
have [b [r [hmin [hbound _]]]] := @bounded_jung_minimum_ball R n A d hne hd hdiam.
have hr := minimum_ball_radius_nonnegative_law hmin.
have hrt : r+r<t := le_lt_trans hbound hcap.
have hh := @spherical_cutoff_containing_ball_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m nu A b r t
  hn (minimum_ball_contains_law hmin) hr hrt.
have hcost : (hausdorff_power_cost m (r+r)%:E<=
    hausdorff_power_cost m (@jung_factor R n*d)%:E)%E.
  apply: hausdorff_power_cost_monotone; first by rewrite lee_fin addr_ge0.
  by rewrite lee_fin.
have hb := le_trans hh hcost.
by rewrite hausdorff_power_cost_finite_scale in hb.
Qed.
