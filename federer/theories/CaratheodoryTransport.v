(** Supporting passage from cover transport to the final measure in Federer
    (1969), 2.10.2(1), p. 171. The same comparison for each positive cutoff
    gives the supremum comparison. Source context and distinction from the
    full Lipschitz multiplicity theorem: MetricScaleTransport.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleTransport CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_transport]: supporting infimum/supremum
    comparison for the closed-cover replacement in Federer 2.10.2(1), p. 171
    The generator map is supplied explicitly, and all diameter and cost
    comparisons are proved premises rather than hidden assumptions about the
    measures. *)
Theorem caratheodory_limit_transport (R : realType) (X Y : metricType R)
    (J K : choiceType) (S : J -> set X) (T : K -> set Y)
    (c : J -> \bar R) (d : K -> \bar R) (f : X -> Y) (u : J -> K)
    (mu : set X -> \bar R) (rho : set Y -> \bar R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit T d rho ->
  (forall k, 0<=d k) ->
  (forall j x, S j x -> T (u j) (f x)) ->
  (forall j, extended_metric_diameter (T (u j))<=extended_metric_diameter (S j)) ->
  (forall j, d (u j)<=c j) ->
  forall A, rho (f @` A)<=mu A.
Proof.
move=> hm hr hd hmap hdiam hcost A.
apply: (caratheodory_limit_least hr)=> delta xi hp hx.
pose nu := metric_scale_envelope S c delta.
have hn := @metric_scale_envelope_specification R X J S c delta.
apply: le_trans (@metric_scale_envelope_transport R X Y J K S T c d f u delta nu xi
  hn hx hd hmap hdiam hcost A) _.
exact (@caratheodory_limit_upper R X J S c mu hm A delta nu hp hn).
Qed.
