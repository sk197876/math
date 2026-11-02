(** Opaque recurrent-sequence witness for the choice in Federer (1969),
    2.8.2, p. 142. Source context and the nonempty-family convention:
    RecurrentEnumerationUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import RecurrentEnumerationUP RecurrentEnumerationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type RecurrentEnumerationSignature.
(** Source for [value]: the sequence chosen in Federer
    2.8.2, p. 142, specified only by its recurrent enumeration laws. *)
Parameter value : forall (J : choiceType) (P : set J),
  countable P -> (exists j, P j) -> nat -> J.
(** Source for [laws]: eligibility and infinitely repeated
    occurrences in Federer 2.8.2, p. 142. *)
Parameter laws : forall (J : choiceType) (P : set J)
    (hc : countable P) (hn : exists j, P j),
  is_recurrent_enumeration P (@value J P hc hn).
End RecurrentEnumerationSignature.
Module RecurrentEnumeration : RecurrentEnumerationSignature.
(** Source for [value]: private witness selection from the
    proved existence supporting Federer 2.8.2, p. 142. *)
Definition value (J : choiceType) (P : set J)
    (hc : countable P) (hn : exists j, P j) :=
  projT1 (cid (@recurrent_enumeration_exists J P hc hn)).
(** Source for [laws]: the selected sequence has the abstract
    recurrence laws used in Federer 2.8.2, p. 142. *)
Lemma laws (J : choiceType) (P : set J)
    (hc : countable P) (hn : exists j, P j) :
  is_recurrent_enumeration P (@value J P hc hn).
Proof. exact: projT2 (cid (@recurrent_enumeration_exists J P hc hn)). Qed.
End RecurrentEnumeration.
