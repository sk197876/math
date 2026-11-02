(** Consequences of the abstract restricted-limit laws supporting Federer
    (1969), 2.10.24, p. 188. Uniqueness and agreement with any weighted
    limiting functional are proved solely from their specifications. Source
    context: WeightedRestrictionMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricLimitUP WeightedRestrictionMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_restriction_unique]: supporting uniqueness
    of the auxiliary restricted supremum for 2.10.24,
    p. 188, by its least-upper-bound laws alone. *)
Lemma weighted_restriction_unique (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (nu rho : set X -> \bar R) :
  is_weighted_restriction_measure S c psi f nu ->
  is_weighted_restriction_measure S c psi f rho -> nu=rho.
Proof.
move=> hn hr; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (weighted_restriction_least hn)=> delta lambda hd hl.
  exact: (@weighted_restriction_upper R X J S c psi f rho hr A delta lambda hd hl).
- apply: (weighted_restriction_least hr)=> delta lambda hd hl.
  exact: (@weighted_restriction_upper R X J S c psi f nu hn A delta lambda hd hl).
Qed.

(** Source for [weighted_restriction_limit_value]: supporting
    evaluation identity for the auxiliary measure in
    2.10.24, p. 188. Agreement with the limiting
    functional is a theorem of the two specifications,
    so downstream proofs need no concrete witness. *)
Theorem weighted_restriction_limit_value (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (nu : set X -> \bar R) (L : (X -> \bar R) -> \bar R) :
  is_weighted_restriction_measure S c psi f nu -> is_weighted_metric_limit S c psi L ->
  forall A, nu A=L (weighted_function_restriction f A).
Proof.
move=> hn hL A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (weighted_restriction_least hn)=> delta lambda hd hl.
  exact: (@weighted_metric_limit_upper R X J S c psi L hL _ delta lambda hd hl).
- apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  exact: (@weighted_restriction_upper R X J S c psi f nu hn A delta lambda hd hl).
Qed.
