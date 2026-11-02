(** Federer (1969), 3.2.17, p. 254:
    the two ball inclusions at the beginning
    of the density proof. No measurable domain
    or global inverse is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import LipschitzUP MetricBiLipschitzUP MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_bilipschitz_inner_ball_image]:
    K intersect B(a,r/lambda) maps into
    f(K) intersect B(f(a),r), Federer
    3.2.17, p. 254. *)
Lemma metric_bilipschitz_inner_ball_image (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) a r :
  is_metric_bilipschitz_bound K f L -> 0<L -> K a ->
  f @` (K `&` metric_closed_ball a (r/L)) `<=`
    (f @` K) `&` metric_closed_ball (f a) r.
Proof.
move=> hB hL ha y [x [hx hb] <-]; split; first by exists x.
have hh := hB.1.2 a x ha hx.
apply: (le_trans hh _).
have hp := ler_wpM2l (ltW hL) hb.
by rewrite [L*(r/L)]mulrC divfK ?gt_eqF // in hp.
Qed.

(** Source for [metric_bilipschitz_outer_ball_preimage]:
    f(K) intersect B(f(a),r) lies in
    f(K intersect B(a,lambda*r)), Federer
    3.2.17, p. 254. *)
Lemma metric_bilipschitz_outer_ball_preimage (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) a r :
  is_metric_bilipschitz_bound K f L -> K a ->
  ((f @` K) `&` metric_closed_ball (f a) r) `<=`
    f @` (K `&` metric_closed_ball a (L*r)).
Proof.
move=> hB ha y [[x hx <-] hb]; exists x=> //; split=> //.
apply: (le_trans (hB.2 a x ha hx) _).
exact: (ler_wpM2l hB.1.1 hb).
Qed.
