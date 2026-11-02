(** Federer (1969), 2.10.24, p. 186: sealed weighted covering infimum. Only
    its defining order laws are exposed. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type WeightedMetricEnvelopeSignature.
(** Source for [value]: abstract lambda_delta of
    2.10.24, p. 186. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> (set X -> \bar R) -> \bar R -> (X -> \bar R) -> \bar R.
(** Source for [laws]: the infimum specification
    of 2.10.24, p. 186. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R),
  is_weighted_metric_envelope S c psi delta (@value R X J S c psi delta).
End WeightedMetricEnvelopeSignature.
Module WeightedMetricEnvelope : WeightedMetricEnvelopeSignature.
(** Source for [value]: selection of proved
    infimum existence for 2.10.24, p. 186. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R) :=
  projT1 (cid (@weighted_metric_envelope_exists R X J S c psi delta)).
(** Source for [laws]: proved order laws for
    the selected infimum in 2.10.24, p. 186. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R) :
  is_weighted_metric_envelope S c psi delta (@value R X J S c psi delta).
Proof. exact: projT2 (cid (@weighted_metric_envelope_exists R X J S c psi delta)). Qed.
End WeightedMetricEnvelope.
