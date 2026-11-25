(** Public lambda_delta for Federer (1969), 2.10.24, pp. 186–187. The
    infimum implementation stays sealed; downstream results use only its
    order laws. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_envelope]: direct
    lambda_delta of 2.10.24, p. 186,
    through the sealed infimum interface. *)
Definition weighted_metric_envelope (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R) :=
  @WeightedMetricEnvelope.value R X J S c psi delta.

(** Source for [weighted_metric_envelope_specification]: the
    public value satisfies the defining infimum laws
    of 2.10.24, p. 186. *)
Lemma weighted_metric_envelope_specification (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R) :
  is_weighted_metric_envelope S c psi delta (weighted_metric_envelope S c psi delta).
Proof. exact: WeightedMetricEnvelope.laws. Qed.
