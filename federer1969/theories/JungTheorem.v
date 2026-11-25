(** Federer (1969), 2.10.41, printed p. 200: Jung's theorem in its complete
    minimum-diameter-ball form. The source has positive finite actual
    diameter; no compactness is required. The conclusion compares actual
    closed-ball diameters, not just their radii, and identifies every tied
    minimum ball. The working erratum has no relevant entry for book p. 200. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  MetricDiameterUP MetricDiameter EuclideanBallDiameter EuclideanBallDiameterFactor
  EuclideanMinimumBallUP BoundedJungBall JungConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_diameter_nonempty]: supporting
    nonemptiness forced by the printed positive-diameter
    hypothesis of 2.10.41, p. 200. This
    elementary consequence of the diameter laws holds
    in every metric space. *)
Lemma positive_diameter_nonempty (R : realType) (X : metricType R) (S : set X) (d : R) :
  0<d -> extended_metric_diameter S=d%:E -> S !=set0.
Proof.
move=> hd hdiam; apply: contrapT=> hnone.
have hzero : (extended_metric_diameter S<=0)%E.
  apply: (metric_diameter_least (extended_metric_diameter_specification S))=> // x y hx hy.
  exfalso; apply: hnone; by exists x.
have hz : d<=0 by move: hzero; rewrite hdiam lee_fin.
have hh := lt_le_trans hd hz; by rewrite ltxx in hh.
Qed.

(** Source for [federer_2_10_41]: direct complete Jung
    theorem in 2.10.41, p. 200. For positive
    finite actual source diameter d, a closed containing
    ball of minimum actual diameter exists uniquely and
    has diameter at most sqrt(2n/(n+1)) d.
    The final uniqueness clause identifies both the
    parameters and the actual set of every tied ball. *)
Theorem federer_2_10_41 (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (d : R) :
  0<d -> extended_metric_diameter S=d%:E ->
  exists b r, is_minimum_enclosing_ball S b r /\
    (extended_metric_diameter (metric_closed_ball b r)<=(@jung_factor R n*d)%:E)%E /\
    forall z t, 0<=t -> S `<=` metric_closed_ball z t ->
      (extended_metric_diameter (metric_closed_ball b r)<=
        extended_metric_diameter (metric_closed_ball z t))%E /\
      (extended_metric_diameter (metric_closed_ball z t)=
        extended_metric_diameter (metric_closed_ball b r) ->
        z=b /\ t=r /\ metric_closed_ball z t=metric_closed_ball b r).
Proof.
case: n S=> [|n] S hd hdiam.
- have hz : d<=0.
    move: hdiam; rewrite euclidean_zero_dimensional_diameter=> hh.
    rewrite -(@lee_fin R d 0) -hh.
    exact: lexx.
  have hh := lt_le_trans hd hz; by rewrite ltxx in hh.
- have hne := positive_diameter_nonempty hd hdiam.
  have hle : (extended_metric_diameter S<=d%:E)%E by rewrite hdiam.
  have [b [r [hmin [hbound huniq]]]] := @bounded_jung_minimum_ball R n.+1 S d hne (ltW hd) hle.
  have hr := minimum_ball_radius_nonnegative_law hmin.
  exists b,r; split=> //; split.
  + rewrite euclidean_closed_ball_diameter // lee_fin; exact hbound.
  + move=> z t ht hcover; split.
    * rewrite !euclidean_closed_ball_diameter // lee_fin.
      have hh := @minimum_ball_radius_least_law R n.+1 S b r hmin z t ht hcover; lra.
    * rewrite !euclidean_closed_ball_diameter // => heq.
      have hrt : t=r.
        have hh := congr1 (@fine R) heq.
        change (t+t=r+r) in hh.
        lra.
      have hzt : is_minimum_enclosing_ball S z t.
        constructor=> // y s hs hys.
        rewrite hrt; exact (@minimum_ball_radius_least_law R n.+1 S b r hmin y s hs hys).
      have [hz ht'] := huniq z t hzt.
      split=> //; split=> //; by rewrite hz ht'.
Qed.
