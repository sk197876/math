(** Federer (1969), 3.2.33, p. 270: small nonempty
    open intervals within a prescribed open subset of (0,1). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import RealMetricBackground RealOpenIntervals MetricClosedBalls MetricOpenShrinking.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_unit_interval_small_neighborhood]: supporting
    the choice of U_j in Federer 3.2.33, p. 270.
    Shrink a closed metric ball inside the actual open set
    and (0,1), and cap its radius by one quarter.
    The endpoints are strict interior points and the entire
    open interval lies in the given set. *)
Lemma open_unit_interval_small_neighborhood (R:realType)
    (U:set (real_line_metric R)) (c:R):
  open U ->U c ->real_open_interval 0 1 c ->
  exists a b:R,0<a /\a<c /\c<b /\b<1 /\b-a<= 1/2 /\real_open_interval a b `<=` U.
Proof.
move=>hU hc hT.
pose O:=U `&` real_open_interval 0 1.
have hOpen:open O:=openI hU (@real_open_interval_open R 0 1).
have [r [hr hBall]]:=metric_open_contains_closed_ball hOpen (conj hc hT).
pose q:R:=Order.min r (1/4).
have hQuarter:(0<(1/4:R)) by rewrite divr_gt0 // ltr0n.
have hq:0<q by rewrite /q lt_min hr hQuarter.
have hqr:q<=r by rewrite /q ge_min lexx.
have hqQuarter:q<= 1/4 by rewrite /q ge_min lexx orbT.
have hLeft:O (c-q).
  apply:hBall; change (is_true (mdist (c:real_line_metric R) (c-q)<=r)).
  have hEq:c-(c-q)= q by ring.
  rewrite real_line_metric_distanceE hEq (ger0_norm (ltW hq)); exact hqr.
have hRight:O (c+q).
  apply:hBall; change (is_true (mdist (c:real_line_metric R) (c+q)<=r)).
  have hEq:c-(c+q)= -q by ring.
  rewrite real_line_metric_distanceE hEq normrN (ger0_norm (ltW hq)); exact hqr.
exists (c-q),(c+q); split; first exact hLeft.2.1.
split; first by lra.
split; first by lra.
split; first exact hRight.2.2.
split; first by lra.
move=>x [hx0 hx1].
have hIn:metric_closed_ball (c:real_line_metric R) r x.
change (is_true (mdist (c:real_line_metric R) x<=r)).
  rewrite real_line_metric_distanceE ler_norml; apply/andP; split; lra.
exact:(hBall x hIn).1.
Qed.
