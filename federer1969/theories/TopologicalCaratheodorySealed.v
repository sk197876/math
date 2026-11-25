(** Opaque witness for the corrected topological construction supporting
    Federer (1969), 2.10.1, p. 170. Only the abstract supremum laws over
    whole-space open covers are exposed. Source context and distinction from
    the literal printed extension: TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalCaratheodoryUP TopologicalCaratheodoryConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type TopologicalCaratheodorySignature.
(** Source for [value]: abstract corrected topological
    construction supporting Federer 2.10.1, p. 170. *)
Parameter value : forall (R : realType) (X : topologicalType) (J : choiceType),
  (J -> set X) -> (J -> \bar R) -> set X -> \bar R.
(** Source for [laws]: abstract supremum laws for the corrected
    topological version supporting Federer 2.10.1, p. 170. *)
Parameter laws : forall (R : realType) (X : topologicalType) (J : choiceType)
  (S : J -> set X) (cost : J -> \bar R),
  is_topological_caratheodory S cost (@value R X J S cost).
End TopologicalCaratheodorySignature.

Module TopologicalCaratheodory : TopologicalCaratheodorySignature.
(** Source for [value]: choice of the proved abstract witness
    for the corrected topological version of Federer 2.10.1,
    p. 170, hidden by opaque module ascription. *)
Definition value (R : realType) (X : topologicalType) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :=
  projT1 (cid (@topological_caratheodory_exists R X J S cost)).
(** Source for [laws]: proved abstract laws of the corrected
    topological witness supporting Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X : topologicalType) (J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :
  is_topological_caratheodory S cost (@value R X J S cost).
Proof. exact: projT2 (cid (@topological_caratheodory_exists R X J S cost)). Qed.
End TopologicalCaratheodory.
