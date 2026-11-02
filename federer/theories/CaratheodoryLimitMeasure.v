(** Federer (1969), 2.10.1, p. 170: the supremum of the approximating
    measures measures X. The covering inequality is proved directly from
    their measure laws, before any assertion about Borel sets. Source
    context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleCutoffCost CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_is_measure]: the measure assertion
    immediately following the supremum formula in Federer 2.10.1, p. 170 No
    finiteness or separability is required. *)
Theorem caratheodory_limit_is_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_caratheodory_limit S cost mu ->
  (forall j, 0<=cost j) -> is_measure mu.
Proof.
move=> hmu hc; constructor.
- move=> A.
  have hn := @metric_scale_envelope_specification R X J S cost 1.
  have hm := metric_scale_envelope_is_measure hn hc.
  apply: le_trans (@measure_nonnegative R X _ hm A) _.
  apply: (@caratheodory_limit_upper R X J S cost mu hmu A 1 _ _ hn).
  by [].
- move=> A F hF hcov; apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
  have hm := metric_scale_envelope_is_measure hn hc.
  apply: le_trans (@measure_countable_cover R X nu hm A F hF hcov) _.
  apply: nonnegative_sum_mono=> B _.
  exact (@caratheodory_limit_upper R X J S cost mu hmu B delta nu hd hn).
Qed.
