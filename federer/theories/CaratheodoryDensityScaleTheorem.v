(** Direct statement of Federer (1969), 2.10.17(1), p. 179, with the
    standing nonnegative cost and fineness hypotheses. The stronger indexed
    covering estimate is proved in CaratheodoryDensityScaleBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MeasureUP CoveringRelationUP
  CaratheodoryDensityScaleBound CaratheodoryDensityUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_17_1]: direct part (1) of
    2.10.17, p. 179. The hypotheses retain the
    book's positive threshold and cutoff, original
    generator bound, nonnegative cost and fine relation;
    no quotient convention is involved in this part. *)
Theorem federer_2_10_17_1 (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (mu nu : set X -> \bar R)
    (A : set X) (t : R) (delta : \bar R) :
  (forall S, F S -> 0<=c S) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta nu ->
  is_measure mu -> (0<t)%R -> 0<delta ->
  (forall S, F S -> extended_metric_diameter S<=delta -> mu (A `&` S)<=t%:E*c S) ->
  mu A<=t%:E*nu A.
Proof.
move=> hc hf hn hm ht hd hgen.
apply: (@caratheodory_density_scale_bound R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) delta nu mu A t hn hm ht)=> j hj.
exact: hgen _ (set_valP j) hj.
Qed.
