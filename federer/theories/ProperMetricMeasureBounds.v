(** Supporting metric-topology step for the Euclidean example in Federer
    (1969), 2.8.8, p. 145: compact closed balls and finiteness on compact
    sets give finiteness on bounded sets, as required in 2.8.1. This is
    background topology, not a separately numbered assertion of 2.8.8. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls
  MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_balls_measure_bounded_finite]:
    supporting finiteness on bounded sets for the Euclidean
    example of Federer 2.8.8, p. 145, under the standing
    hypotheses of 2.8.1, p. 141. A nonempty bounded
    set lies in a compact closed ball centered at one of its
    points; the empty set has measure zero. *)
Lemma compact_balls_measure_bounded_finite (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  (forall (a : X) (r : R), (0 <= r)%R -> compact (metric_closed_ball a r)) ->
  (forall K, compact K -> mu K < +oo) ->
  forall S, metric_set_bounded S -> mu S < +oo.
Proof.
move=> hcompact hfinite S hb.
case: (eqVneq S set0)=> [->|hne]; first by rewrite (measure_empty hm); exact: ltry.
have [a ha] := (set0P S).1 hne.
have hd := extended_metric_diameter_specification S.
have hfin : extended_metric_diameter S \is a fin_num.
  by rewrite (ge0_fin_numE (metric_diameter_nonnegative hd)).
pose M := fine (extended_metric_diameter S).
have hM : (0 <= M)%R.
  have h := metric_diameter_nonnegative hd; by rewrite -(fineK hfin) lee_fin in h.
have hsub : S `<=` metric_closed_ball a M.
  move=> x hx; have h := metric_diameter_upper hd ha hx.
  by rewrite -(fineK hfin) lee_fin in h.
exact: le_lt_trans (@measure_mono R X mu hm _ _ hsub) (hfinite _ (hcompact a M hM)).
Qed.

(** Source for [compact_balls_covering_context]: supporting
    verification of the standing context for the Euclidean
    application in Federer 2.8.8, p. 145. Explicit
    compact-ball and compact-finiteness laws suffice; no
    particular model of Euclidean space is unfolded. *)
Theorem compact_balls_covering_context (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) :
  is_measure mu -> (forall S, F S -> closed S) ->
  (forall U, open U -> measure_measurable mu U) ->
  (forall (a : X) (r : R), (0 <= r)%R -> compact (metric_closed_ball a r)) ->
  (forall K, compact K -> mu K < +oo) -> is_covering_theory_context F mu.
Proof.
move=> hm hclosed hopen hballs hfinite; constructor=> //.
exact (@compact_balls_measure_bounded_finite R X mu hm hballs hfinite).
Qed.
