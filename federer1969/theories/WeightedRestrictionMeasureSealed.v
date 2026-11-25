(** Opaque witness boundary for the auxiliary restricted weighted measure
    supporting Federer (1969), 2.10.24, p. 188. Expose only its value and
    abstract supremum laws. Source context: WeightedRestrictionMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedRestrictionMeasureUP WeightedRestrictionMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type WeightedRestrictionMeasureSignature.
(** Source for [value]: abstract restricted weighted measure
    supporting 2.10.24, p. 188; no witness is exposed. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> (set X -> \bar R) -> (X -> \bar R) -> set X -> \bar R.
(** Source for [laws]: abstract positive-cutoff supremum laws
    for the auxiliary object supporting 2.10.24, p. 188. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R),
  is_weighted_restriction_measure S c psi f (@value R X J S c psi f).
End WeightedRestrictionMeasureSignature.
Module WeightedRestrictionMeasure : WeightedRestrictionMeasureSignature.
(** Source for [value]: hidden selection of a proved witness
    for the auxiliary object supporting 2.10.24, p. 188. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :=
  projT1 (cid (@weighted_restriction_measure_exists R X J S c psi f)).
(** Source for [laws]: the selected witness satisfies its
    specification for 2.10.24, p. 188; selection remains
    hidden behind opaque module ascription. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_weighted_restriction_measure S c psi f (@value R X J S c psi f).
Proof. exact: projT2 (cid (@weighted_restriction_measure_exists R X J S c psi f)). Qed.
End WeightedRestrictionMeasure.
