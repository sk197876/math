(** Federer (1969), 2.10.24, p. 187: the weighted approximation has a limit
    as the positive cutoff decreases to zero. Specify that increasing limit
    as the supremum of all positive-cutoff weighted infima before proving
    existence. Source context and weighted-cover definition:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_weighted_metric_limit]: supporting
    order specification of the displayed cutoff limit
    in 2.10.24, p. 187. Positive infinity
    is included among cutoffs; limiting values may
    be infinite and no equality with an integral is assumed. *)
Record is_weighted_metric_limit (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) : Prop := {
  (** Source for [weighted_metric_limit_upper]: every
      positive-cutoff approximation is bounded by the
      increasing limit in 2.10.24, p. 187. *)
  weighted_metric_limit_upper : forall f delta lambda, 0<delta ->
    is_weighted_metric_envelope S c psi delta lambda -> lambda f<=L f;
  (** Source for [weighted_metric_limit_least]: least
      upper bound characterization of the cutoff limit
      in 2.10.24, p. 187. *)
  weighted_metric_limit_least : forall f b,
    (forall delta lambda, 0<delta -> is_weighted_metric_envelope S c psi delta lambda -> lambda f<=b) -> L f<=b
}.
