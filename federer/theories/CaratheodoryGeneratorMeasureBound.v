(** Generator-to-measure comparison supporting Federer (1969), 2.10.35, p.
    197: the displayed cost inequalities imply inequalities of the resulting
    measures. Apply countable subadditivity at a single positive cutoff,
    then the abstract limiting supremum. This general supporting statement
    does not attribute a new numbered theorem to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MetricScaleEnvelope MetricScaleMeasureBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_bounded_by_caratheodory_generators]: supporting
    measure comparison from generator costs in
    2.10.35, p. 197. Neither finite
    costs nor measurable generators or targets
    are required. Only the existing abstract
    covering and supremum laws are used. *)
Theorem measure_bounded_by_caratheodory_generators (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu nu : set X -> \bar R) :
  is_measure mu -> is_caratheodory_limit S c nu ->
  (forall j, (mu (S j)<=c j)%E) -> forall A, (mu A<=nu A)%E.
Proof.
move=> hm hn hc A.
pose eta := metric_scale_envelope S c 1%E.
have he := @metric_scale_envelope_specification R X J S c 1%E.
have hb : (mu A<=eta A)%E.
  apply: (@measure_bounded_by_metric_scale_envelope R X J S c 1%E eta mu he hm)=> j hj.
  exact: hc j.
have h1 : (0<1 :> \bar R)%E by rewrite lte_fin ltr01.
exact: le_trans hb (@caratheodory_limit_upper R X J S c nu hn A 1%E eta h1 he).
Qed.
