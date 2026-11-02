(** Federer (1969), 2.10.24, p. 187: private existence of the weighted
    positive-cutoff supremum, using the project's sealed extended-real
    completeness. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_limit_exists]: supporting
    existence of the increasing cutoff limit in
    2.10.24, p. 187, without assuming an
    integral equality or finite limiting value. *)
Theorem weighted_metric_limit_exists (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :
  exists L, is_weighted_metric_limit S c psi L.
Proof.
exists (fun f=>extended_real_sup [set b | exists delta,
  0<delta /\ b=weighted_metric_envelope S c psi delta f]).
constructor.
- move=> f delta lambda hd hl.
  have he := @weighted_metric_envelope_unique R X J S c psi delta lambda
    (weighted_metric_envelope S c psi delta) hl (weighted_metric_envelope_specification _ _ _ _).
  rewrite he; apply: extended_real_sup_upper; exists delta; by split.
- move=> f b hb; apply: extended_real_sup_least=> a [delta [hd ->]].
  exact: hb delta _ hd (weighted_metric_envelope_specification _ _ _ _).
Qed.
