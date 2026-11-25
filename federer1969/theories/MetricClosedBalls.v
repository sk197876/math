(** Supporting metric topology for Federer (1969), 2.2.8, p. 64: closed
    small-diameter coverings. Here the elementary open- and closed-ball
    facts are proved from the metric laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_closed_ball]: supporting definition for
    Federer 2.2.8, p. 64: the set of points at distance at most
    r from c, used to construct the closed covering sets E(s). *)
Definition metric_closed_ball (R : realType) (T : metricType R)
    (c : T) (r : R) : set T := [set x | mdist c x <= r].

(** Source for [metric_open_ball_open]: supporting general topology for
    Federer 2.2.8, p. 64. *)
Lemma metric_open_ball_open (R : realType) (T : metricType R) (c : T) r :
  open [set x | mdist c x < r].
Proof.
rewrite openE=> x hx.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists (r-mdist c x); first by rewrite /= subr_gt0.
move=> y hy; apply: le_lt_trans (metric_triangle c x y) _.
have hh := ler_ltD (lexx (mdist c x)) hy.
by rewrite addrCA subrr addr0 in hh.
Qed.

(** Source for [metric_closed_ball_closed]: supporting general
    topology for Federer 2.2.8, p. 64: the closed metric ball
    is closed, allowing intersections with closed parent sets. *)
Lemma metric_closed_ball_closed (R : realType) (T : metricType R) (c : T) r :
  closed (metric_closed_ball c r).
Proof.
have ho : open (~` metric_closed_ball c r).
  rewrite openE=> x hx.
  have hr : r < mdist c x by rewrite ltNge; apply/negP.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
  exists (mdist c x-r); first by rewrite /= subr_gt0.
  move=> y hy hcy.
  have htri := metric_triangle c y x.
  rewrite (metric_sym y x) in htri.
  have hh : mdist c y + mdist x y < mdist c x.
    apply: le_lt_trans (lerD hcy (lexx _)) _.
    have hh := ler_ltD (lexx r) hy.
    by rewrite addrCA subrr addr0 in hh.
  by have := le_lt_trans htri hh; rewrite ltxx.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [metric_closed_ball_diameter_bound]: supporting diameter
    estimate in Federer 2.2.8, p. 64: two points in a closed ball of radius
    r are at distance at most r+r. *)
Lemma metric_closed_ball_diameter_bound (R : realType) (T : metricType R)
    (c : T) r x y :
  metric_closed_ball c r x -> metric_closed_ball c r y -> mdist x y <= r+r.
Proof.
move=> hx hy; apply: le_trans (metric_triangle x c y) _.
rewrite (metric_sym x c); exact: lerD hx hy.
Qed.
