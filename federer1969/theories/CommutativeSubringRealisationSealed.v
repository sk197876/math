(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: original subrings have opaque ring carriers
    governed by exact inclusion laws. Choice selects a
    proved existence witness. Source: the Rees ring in
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativeSubringRealisationSignature.
(** Source for [space]: an opaque ring carrier for
    the original subring, supporting the cited Lemma 1. *)
Parameter space:forall (A:comNzRingType) (S:set A),is_commutative_subring S->comNzRingType.
(** Source for [inclusion]: the original ring inclusion,
    supporting the cited Rees-ring Lemma 1. *)
Parameter inclusion:forall (A:comNzRingType) (S:set A) (hS:is_commutative_subring S),
  {rmorphism @space A S hS->A}.
(** Source for [laws]: the independent exact image
    and injection laws, supporting the cited Lemma 1. *)
Parameter laws:forall (A:comNzRingType) (S:set A) (hS:is_commutative_subring S),
  is_commutative_subring_realisation S (@inclusion A S hS).
End CommutativeSubringRealisationSignature.
Module CommutativeSubringRealisation:CommutativeSubringRealisationSignature.
(** Source for [space]: the hidden carrier from
    proved existence, supporting the cited Lemma 1. *)
Definition space (A:comNzRingType) (S:set A) (hS:is_commutative_subring S):comNzRingType:=
  projT1 (cid (@commutative_subring_realisation_exists A S hS)).
(** Source for [inclusion]: the hidden witness's original
    inclusion, supporting the cited Rees-ring Lemma 1. *)
Definition inclusion (A:comNzRingType) (S:set A) (hS:is_commutative_subring S):
    {rmorphism @space A S hS->A}:=
  projT1 (cid (projT2 (cid (@commutative_subring_realisation_exists A S hS)))).
(** Source for [laws]: the selected carrier satisfies
    the independent original laws, supporting the cited Lemma 1. *)
Lemma laws (A:comNzRingType) (S:set A) (hS:is_commutative_subring S):
  is_commutative_subring_realisation S (@inclusion A S hS).
Proof.
exact:(projT2 (cid (projT2 (cid (@commutative_subring_realisation_exists A S hS))))).
Qed.
End CommutativeSubringRealisation.
