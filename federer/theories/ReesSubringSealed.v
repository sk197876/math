(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the Rees set is opaque and governed
    by its independent coefficient laws. Source: Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import ReesSubringUP ReesSubringExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ReesSubringSignature.
(** Source for [value]: the original Rees set,
    supporting the cited Lemma 1. *)
Parameter value:forall (A B:comNzRingType),(B->nat->A)->set A->set B.
(** Source for [laws]: its independent original
    coefficient-membership laws, supporting the cited Lemma 1. *)
Parameter laws:forall (A B:comNzRingType) (coefficient:B->nat->A) (I:set A),
  is_rees_subring coefficient I (@value A B coefficient I).
End ReesSubringSignature.
Module ReesSubring:ReesSubringSignature.
(** Source for [value]: a hidden witness of proved
    Rees-set existence, supporting the cited Lemma 1. *)
Definition value (A B:comNzRingType) (coefficient:B->nat->A) (I:set A):set B:=
  projT1 (cid (@rees_subring_exists A B coefficient I)).
(** Source for [laws]: the selected witness satisfies
    the independent original laws, supporting the cited Lemma 1. *)
Lemma laws (A B:comNzRingType) (coefficient:B->nat->A) (I:set A):
  is_rees_subring coefficient I (@value A B coefficient I).
Proof. exact:(projT2 (cid (@rees_subring_exists A B coefficient I))). Qed.
End ReesSubring.
