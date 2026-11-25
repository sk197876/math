(** Opaque final-measure witness for Federer (1969), 2.10.1, p. 170. The
    interface exposes only the supremum specification over the abstract
    approximations. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CaratheodoryLimitUP CaratheodoryLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type CaratheodoryLimitSignature.
(** Source for [value]: the final measure of Federer
    2.10.1, p. 170. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> set X -> \bar R.
(** Source for [laws]: the final measure's supremum laws,
    Federer 2.10.1, p. 170. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R),
  is_caratheodory_limit S cost (@value R X J S cost).
End CaratheodoryLimitSignature.

Module CaratheodoryLimit : CaratheodoryLimitSignature.
(** Source for [value]: choice of the proved supremum
    witness in Federer 2.10.1, p. 170. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :=
  projT1 (cid (@caratheodory_limit_exists R X J S cost)).
(** Source for [laws]: proved abstract laws of the
    chosen witness, Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :
  is_caratheodory_limit S cost (@value R X J S cost).
Proof. exact: projT2 (cid (@caratheodory_limit_exists R X J S cost)). Qed.
End CaratheodoryLimit.
