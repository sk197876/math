(** Federer (1969), 2.10.24, p. 187: opaque
    positive-cutoff supremum for weighted coverings. Only
    the abstract supremum laws are exposed. Source
    editions: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricLimitUP WeightedMetricLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type WeightedMetricLimitSignature.
(** Source for [value]: abstract cutoff limit
    of 2.10.24, p. 187. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> (set X -> \bar R) -> (X -> \bar R) -> \bar R.
(** Source for [laws]: supremum specification of
    the limit in 2.10.24, p. 187. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R),
  is_weighted_metric_limit S c psi (@value R X J S c psi).
End WeightedMetricLimitSignature.
Module WeightedMetricLimit : WeightedMetricLimitSignature.
(** Source for [value]: choice of the proved
    supremum witness for 2.10.24, p. 187. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :=
  projT1 (cid (@weighted_metric_limit_exists R X J S c psi)).
(** Source for [laws]: the selected value
    satisfies the abstract limit laws of
    2.10.24, p. 187. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :
  is_weighted_metric_limit S c psi (@value R X J S c psi).
Proof. exact: projT2 (cid (@weighted_metric_limit_exists R X J S c psi)). Qed.
End WeightedMetricLimit.
