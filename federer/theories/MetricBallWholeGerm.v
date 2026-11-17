(** Federer (1969), 3.4.8(13), p. 336:
    a positive closed ball about the origin represents
    the whole germ. Its open ball is an actual
    neighbourhood on which the two sets agree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricClosedBalls SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_closed_ball_whole_germ]: the compact
    neighbourhood representative in the full-dimensional case of
    3.4.8(13), p. 336. This supporting
    statement holds in every metric space. *)
Theorem metric_closed_ball_whole_germ (R:realType) (X:metricType R) (a:X) (r:R):
  0<r ->@set_germ X a (metric_closed_ball a r)=@set_germ X a setT.
Proof.
move=>hr;apply/set_germ_equality_original.
exists [set x:X|mdist a x<r];split;first exact:metric_open_ball_open.
split;first by rewrite /= mdistxx.
apply/seteqP;split.
- by move=>x [hx hOpen];split.
- move=>x [_ hOpen];split;last exact:hOpen.
  exact:ltW hOpen.
Qed.
