(** Federer (1969), 2.9.19, p. 164: the dense continuity points in the
    monotone argument permit perturbing interval endpoints. These are
    order-topological supporting lemmas, not separately numbered claims in
    either source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_real_open_interval_point]: supporting density step in
    Federer 2.9.19, p. 164 Every nonempty open real interval meets a dense
    set. *)
Lemma dense_real_open_interval_point (R : realType) (D : set (real_line_metric R))
    (a b : R) : dense D -> a<b -> exists t, a<t<b /\ D t.
Proof.
move=> hD hab.
have hnon : real_open_interval a b !=set0.
  exists ((a+b)/2); split; lra.
have [t [[hat htb] htD]] := hD (real_open_interval a b) hnon (@real_open_interval_open R a b).
exists t; split=> //; by apply/andP; split.
Qed.

(** Source for [dense_real_inner_left_endpoint]: supporting approximation of
    the left endpoint from inside [a,x] in Federer 2.9.19, p. 164 The
    endpoint x may be retained when a=x, using its membership in D. If a<x,
    the selected point is strictly below x. *)
Lemma dense_real_inner_left_endpoint (R : realType) (D : set (real_line_metric R))
    (a x e : R) : dense D -> D x -> a<=x -> 0<e ->
  exists u, D u /\ a<=u<=x /\ u-a<e /\ (a<x -> u<x).
Proof.
move=> hD hx hax he.
case: (eqVneq a x)=> [->|hne].
- exists x; split=> //; split; first by rewrite lexx.
  split; first by rewrite subrr.
  by move=> hbad; rewrite ltxx in hbad.
- have hax' : a<x by rewrite lt_neqAle hne hax.
  have hb : a<Num.min x (a+e) by rewrite lt_min hax' ltrDl he.
  have [u [/andP [hau hub] huD]] := dense_real_open_interval_point hD hb.
  have hux : u<x.
    have hm : Num.min x (a+e)<=x by rewrite ge_min lexx.
    exact: lt_le_trans hub hm.
  have hue : u<a+e.
    have hm : Num.min x (a+e)<=a+e by rewrite ge_min lexx orbT.
    exact: lt_le_trans hub hm.
  exists u; split=> //; split; first by apply/andP; split; exact: ltW.
  split; first by lra.
  by move=> _.
Qed.

(** Source for [dense_real_inner_right_endpoint]: supporting approximation
    of the right endpoint from inside [x,b] in Federer 2.9.19, p. 164 If
    x<b, the selected point is strictly above x; otherwise x itself is
    available because it belongs to D. *)
Lemma dense_real_inner_right_endpoint (R : realType) (D : set (real_line_metric R))
    (x b e : R) : dense D -> D x -> x<=b -> 0<e ->
  exists v, D v /\ x<=v<=b /\ b-v<e /\ (x<b -> x<v).
Proof.
move=> hD hx hxb he.
case: (eqVneq x b)=> [<-|hne].
- exists x; split=> //; split; first by rewrite lexx.
  split; first by rewrite subrr.
  by move=> hbad; rewrite ltxx in hbad.
- have hxb' : x<b by rewrite lt_neqAle hne hxb.
  have hb : Num.max x (b-e)<b by rewrite gt_max hxb' ltrBlDr ltrDl he.
  have [v [/andP [hlv hvb] hvD]] := dense_real_open_interval_point hD hb.
  have hxv : x<v.
    have hm : x<=Num.max x (b-e) by rewrite le_max lexx.
    exact: le_lt_trans hm hlv.
  have hve : b-e<v.
    have hm : b-e<=Num.max x (b-e) by rewrite le_max lexx orbT.
    exact: le_lt_trans hm hlv.
  exists v; split=> //; split; first by apply/andP; split; exact: ltW.
  split; first by lra.
  by move=> _.
Qed.
