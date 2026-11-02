(** Supporting Euclidean ball geometry for Federer (1969), 2.10.2(2), p.
    171, the alternative open-ball covering family. In positive dimension
    both open and closed balls of positive radius have diameter twice that
    radius. The argument uses an isometric coordinate line, not a
    general-metric identity. its coordinate geometry is cited in
    EuclideanCoordinateMetric.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric FiniteCoordinates
  EuclideanCoordinateMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_ball_diameter_upper]: supporting general-metric
    diameter bound used in Federer 2.10.2(2), p. 171 *)
Lemma metric_ball_diameter_upper (R : realType) (X : metricType R) (a : X) (r : R) :
  0<=r -> (extended_metric_diameter (metric_closed_ball a r)<=(r+r)%:E)%E.
Proof.
move=> hr; apply: (metric_diameter_least (extended_metric_diameter_specification (metric_closed_ball a r))).
- by rewrite lee_fin addr_ge0.
- move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
Qed.

(** Source for [metric_closed_ball_diameter_from_line]:
    supporting sharp diameter for Federer 2.10.2(2),
    p. 171, when an actual isometric real line through
    the center is supplied. No such line is assumed
    for arbitrary metric spaces. *)
Lemma metric_closed_ball_diameter_from_line (R : realType) (X : metricType R)
    (a : X) (f : R -> X) (r : R) : 0<=r -> f 0=a ->
  (forall s t, mdist (f s) (f t)=`|s-t|) ->
  extended_metric_diameter (metric_closed_ball a r)=(r+r)%:E.
Proof.
move=> hr hf0 hf; apply/eqP; rewrite eq_le (metric_ball_diameter_upper a hr) /=.
have hplus : metric_closed_ball a r (f r).
  by rewrite /metric_closed_ball /= -hf0 hf sub0r normrN ger0_norm.
have hminus : metric_closed_ball a r (f (-r)).
  by rewrite /metric_closed_ball /= -hf0 hf sub0r opprK ger0_norm.
have hh := metric_diameter_upper (extended_metric_diameter_specification (metric_closed_ball a r)) hplus hminus.
by rewrite hf opprK ger0_norm ?addr_ge0 in hh.
Qed.

(** Source for [metric_open_ball_diameter_from_line]:
    supporting open-ball diameter for Federer 2.10.2(2),
    p. 171. Interior opposite points approach twice the
    radius; this includes no assertion about arbitrary
    metric balls without the supplied isometric line. *)
Lemma metric_open_ball_diameter_from_line (R : realType) (X : metricType R)
    (a : X) (f : R -> X) (r : R) : 0<r -> f 0=a ->
  (forall s t, mdist (f s) (f t)=`|s-t|) ->
  extended_metric_diameter [set x | mdist a x<r]=(r+r)%:E.
Proof.
move=> hr hf0 hf; pose U := [set x | mdist a x<r].
have hup : (extended_metric_diameter U<=(r+r)%:E)%E.
  apply: le_trans (@extended_metric_diameter_mono R X U (metric_closed_ball a r) _) (metric_ball_diameter_upper a (ltW hr)).
  by move=> x hx; exact: ltW hx.
apply/eqP; rewrite eq_le hup /= leNgt; apply/negP=> hbad.
have hn := metric_diameter_nonnegative (extended_metric_diameter_specification U).
case he: (extended_metric_diameter U) hn hbad=> [d| |] hn hbad; last 2 first.
- by [].
- by [].
have hd : 0<=d by move: hn; rewrite lee_fin.
have hdl : d<r+r by move: hbad; rewrite lte_fin.
pose s := (r+d/2)/2.
have hs : 0<s by rewrite /s; lra.
have hsr : s<r by rewrite /s; lra.
have hds : d<s+s by rewrite /s; lra.
have hp : U (f s) by rewrite /U /= -hf0 hf sub0r normrN ger0_norm //; exact: ltW hs.
have hm : U (f (-s)) by rewrite /U /= -hf0 hf sub0r opprK ger0_norm //; exact: ltW hs.
have hh := metric_diameter_upper (extended_metric_diameter_specification U) hp hm.
have hss : 0<=s+s by apply: addr_ge0; exact: ltW hs.
rewrite he hf opprK (ger0_norm hss) lee_fin in hh.
by have := lt_le_trans hds hh; rewrite ltxx.
Qed.

(** Source for [euclidean_coordinate_line_isometry]: supporting
    coordinate line for the Euclidean open-ball alternative
    in Federer 2.10.2(2), p. 171, using the actual
    dot-product metric of 1.7.1, p. 28. *)
Lemma euclidean_coordinate_line_isometry (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  exists f : R -> inner_metric_space (@euclidean_inner_productP R n.+1),
    f 0=a /\ forall s t, mdist (f s) (f t)=`|s-t|.
Proof.
exists (fun t => euclidean_coordinate_line ord0 a t); split.
- by rewrite /euclidean_coordinate_line scale0r addr0.
- move=> s t; rewrite euclidean_coordinate_line_distance real_line_metric_distanceE; by [].
Qed.

(** Source for [euclidean_closed_ball_diameter]: supporting
    diameter identity for the closed balls in Federer
    2.10.2(2), p. 171, in positive Euclidean dimension. *)
Theorem euclidean_closed_ball_diameter (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (r : R) :
  0<=r -> extended_metric_diameter (metric_closed_ball a r)=(r+r)%:E.
Proof.
move=> hr; have [f [hf0 hf]] := euclidean_coordinate_line_isometry a.
exact: metric_closed_ball_diameter_from_line hr hf0 hf.
Qed.

(** Source for [euclidean_open_ball_diameter]: supporting
    diameter identity for the alternative open balls in
    Federer 2.10.2(2), p. 171, in positive dimension. *)
Theorem euclidean_open_ball_diameter (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (r : R) :
  0<r -> extended_metric_diameter [set x | mdist a x<r]=(r+r)%:E.
Proof.
move=> hr; have [f [hf0 hf]] := euclidean_coordinate_line_isometry a.
exact: metric_open_ball_diameter_from_line hr hf0 hf.
Qed.
