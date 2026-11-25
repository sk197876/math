(** Public size-delta envelope for Federer (1969), 2.10.1, p. 170. Its
    measure laws and monotonicity follow from the abstract infimum
    specification. Source context: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  MetricScaleCutoffCost MetricScaleEnvelopeSealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope]: the size-delta
    approximating measure in Federer 2.10.1, p. 170. *)
Definition metric_scale_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) := @MetricScaleEnvelope.value R X J S cost delta.

(** Source for [metric_scale_envelope_specification]: public
    covering-infimum laws, Federer 2.10.1, p. 170. *)
Lemma metric_scale_envelope_specification (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) :
  is_metric_scale_envelope S cost delta (metric_scale_envelope S cost delta).
Proof. exact: MetricScaleEnvelope.laws. Qed.

(** Source for [metric_scale_envelope_measure]: the preliminary envelope
    measures X, Federer 2.10.1, p. 170 *)
Theorem metric_scale_envelope_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) :
  (forall j, 0<=cost j) -> is_measure (metric_scale_envelope S cost delta).
Proof.
exact: (metric_scale_envelope_is_measure (metric_scale_envelope_specification S cost delta)).
Qed.
