(** Federer (1969), 2.10.47(3), p. 205: an open neighbourhood of the compact
    level E intersect {x_1=t} contains E intersect {t-e<x_1<t+e} for some
    e>0. The same general-topology argument works for any continuous
    real-valued map on a compact set. This is the supporting neighbourhood
    step, not yet continuity or divisibility of the dyadic contents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricOpenShrinking.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_level_open_neighbourhood]: supporting
    compactness sentence in the proof of 2.10.47(3),
    p. 205. The continuous image of the part outside
    the open neighbourhood is compact and avoids t, so
    a positive interval about t avoids that image. *)
Theorem compact_level_open_neighbourhood (R : realType) (X : metricType R)
    (E U : set X) (f : X -> real_line_metric R) (t : R) :
  compact E -> continuous f -> open U ->
  (E `&` [set x | f x=t]) `<=` U ->
  exists e : R, 0<e /\ (E `&` [set x | `|f x-t|<e]) `<=` U.
Proof.
move=> hE hf hU hlevel.
pose D := E `\` U.
have hDclosed : closed D.
  exact: closedI (compact_closed (@metric_hausdorff R X) hE) (open_closedC hU).
have hD : compact D := subclosed_compact hDclosed hE (fun x hx=>hx.1).
have him : compact (f @` D) := continuous_compact (continuous_subspaceT hf) hD.
have hclosed : closed (f @` D) := compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R]) him.
have ht : (~` (f @` D)) t.
  move=> [x [hx hnot] he]; apply: hnot; apply: hlevel; by split.
have [e [he hball]] := @metric_open_contains_closed_ball R [the metricType R of real_line_metric R]
  (~` (f @` D)) t (closed_openC hclosed) ht.
exists e; split=> // x [hx hnear].
apply: contrapT=> hnot.
have hb : metric_closed_ball (t : real_line_metric R) e (f x).
  change (is_true (`|t-f x|<=e)); rewrite distrC; exact: ltW hnear.
apply: (hball (f x) hb); exists x=> //; by split.
Qed.
