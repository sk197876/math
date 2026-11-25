(** Federer (1969), 2.2.15, p. 71: opaque first-hit Borel labelling for a
    countable cover. Clients use the proved hit, minimality and fibre laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalBorel BorelDiscreteIndexUP BorelCoverIndexConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type BorelCoverIndexSignature.
(** Source for [value]: abstract countable-cover index
    supporting Federer 2.2.15, p. 71. *)
Parameter value : forall (X : topologicalType) (A : nat -> set X),
  (forall n, borel_set (A n)) -> (forall x, exists n, A n x) -> X -> nat.
(** Source for [laws]: first-hit and Borel-fibre laws
    supporting Federer 2.2.15, p. 71. *)
Parameter laws : forall (X : topologicalType) (A : nat -> set X)
  (hA : forall n, borel_set (A n)) (hc : forall x, exists n, A n x),
  is_first_borel_cover_index A (@value X A hA hc).
End BorelCoverIndexSignature.
Module BorelCoverIndex : BorelCoverIndexSignature.
(** Source for [value]: private witness selection for
    the Borel cover index supporting Federer 2.2.15, p. 71. *)
Definition value (X : topologicalType) (A : nat -> set X)
  (hA : forall n, borel_set (A n)) (hc : forall x, exists n, A n x) :=
  projT1 (cid (@first_borel_cover_index_exists X A hA hc)).
(** Source for [laws]: the selected index has the
    specified laws supporting Federer 2.2.15, p. 71. *)
Lemma laws (X : topologicalType) (A : nat -> set X)
  (hA : forall n, borel_set (A n)) (hc : forall x, exists n, A n x) :
  is_first_borel_cover_index A (@value X A hA hc).
Proof. exact: projT2 (cid (@first_borel_cover_index_exists X A hA hc)). Qed.
End BorelCoverIndex.
