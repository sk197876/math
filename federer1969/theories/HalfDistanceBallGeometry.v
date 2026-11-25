(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic
  MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


(** Source for [metric_set_distance_near_member]: supporting selection of z
    near y in the covering proof of Federer 2.9.17, p. 162. A strict number
    above the abstract distance infimum is exceeded by some member's point
    distance in the required direction. *)
Lemma metric_set_distance_near_member (R : realType) (X : metricType R)
    (A : set X) (d : X -> R) (hd : is_metric_set_distance A d) (y : X) (b : R) :
  d y<b -> exists z, A z /\ mdist y z<b.
Proof.
move=> hb; apply: contrapT=> hn.
have hl : b<=d y.
  apply: (@metric_set_distance_greatest R X A d hd y b)=> z hz.
  rewrite leNgt; apply/negP=> hlt; apply: hn; by exists z.
by have := lt_le_trans hb hl; rewrite ltxx.
Qed.

(** Source for [half_distance_ball_avoids_set]: supporting
    disjointness of the balls B(y,dist(y,C_n)/2) from C_n
    in Federer 2.9.17, p. 162. This uses only
    the abstract distance lower bound and its strict positivity;
    closedness is used separately to establish that positivity. *)
Lemma half_distance_ball_avoids_set (R : realType) (X : metricType R)
    (A : set X) (d : X -> R) (hd : is_metric_set_distance A d) (y : X) :
  0<d y -> metric_closed_ball y (d y/2) `<=` ~` A.
Proof.
move=> hp z hz hAz.
have hl := @metric_set_distance_lower R X A d hd y z hAz.
have hh := le_trans hl hz.
have hs : d y/2<d y by lra.
by have := lt_le_trans hs hh; rewrite ltxx.
Qed.

(** Source for [half_distance_ball_geometry]: direct geometric
    estimates in the covering proof of Federer 2.9.17,
    p. 162. For x in the closed set, y in B(x,r)
    outside it and s=dist(y,A)/2, obtain s>0, s<=r/2,
    B(y,s) contained in B(x,2r) minus A, and z in A
    with distance(y,z)<3s. The ball notation in the subsequent
    mass estimate follows erratum p. 3, book p. 162
    lines 24–25. No nearest point is assumed to exist. *)
Lemma half_distance_ball_geometry (R : realType) (X : metricType R)
    (A : set X) (d : X -> R) (hd : is_metric_set_distance A d) (x y : X) (r : R) :
  closed A -> A x -> ~ A y -> 0<r -> metric_closed_ball x r y ->
  let s := d y/2 in
  0<s /\ s<=r/2 /\ metric_closed_ball y s `<=` (metric_closed_ball x (2*r) `\` A) /\
    exists z, A z /\ mdist y z<3*s.
Proof.
move=> hA hx hy hr hxy s.
have hp := @metric_set_distance_positive_outside_closed R X A d hd y hA hy.
have hs : 0<s by rewrite /s divr_gt0 // ltr0n.
have hdy : d y<=r.
  have h := @metric_set_distance_lower R X A d hd y x hx.
  rewrite metric_sym in h; exact: le_trans h hxy.
have hsr : s<=r/2 by rewrite /s ler_pdivrMr ?ltr0n //; lra.
split=> //; split=> //; split.
- move=> z hz; split.
  + apply: le_trans (metric_triangle x y z) _.
    have hb := lerD hxy hz; apply: le_trans hb _; lra.
  + exact: (half_distance_ball_avoids_set hd hp) z hz.
- have hb : d y<3*s by rewrite /s; lra.
  exact (@metric_set_distance_near_member R X A d hd y (3*s) hb).
Qed.
