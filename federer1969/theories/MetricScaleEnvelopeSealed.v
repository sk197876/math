(** Opaque size-delta covering envelope for Federer (1969), 2.10.1, p. 170.
    Source context: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricScaleEnvelopeUP MetricScaleEnvelopeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type MetricScaleEnvelopeSignature.
(** Source for [value]: the approximating measure of Federer
    2.10.1, p. 170, specified by its admissible covers. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> \bar R -> set X -> \bar R.
(** Source for [laws]: the covering-infimum laws of
    Federer 2.10.1, p. 170. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (delta : \bar R),
  is_metric_scale_envelope S cost delta (@value R X J S cost delta).
End MetricScaleEnvelopeSignature.

Module MetricScaleEnvelope : MetricScaleEnvelopeSignature.
(** Source for [value]: private choice of the proved
    infimum witness, Federer 2.10.1, p. 170. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (delta : \bar R) :=
  projT1 (cid (@metric_scale_envelope_exists R X J S cost delta)).
(** Source for [laws]: the chosen witness has the
    required infimum laws, Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (delta : \bar R) :
  is_metric_scale_envelope S cost delta (@value R X J S cost delta).
Proof. exact: projT2 (cid (@metric_scale_envelope_exists R X J S cost delta)). Qed.
End MetricScaleEnvelope.
