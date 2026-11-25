(** Federer (1969), 3.4.8(8), p. 329:
    the original subfield behind an opaque field
    carrier and exact inclusion laws. Reuse the
    independently specified subring-inclusion interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringRealisationUP CommutativeSubfieldUP
  CommutativeSubfieldRealisationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativeSubfieldRealisationSignature.
(** Source for [space]: the original coefficient
    subfield carrier, 3.4.8(8), p. 329. *)
Parameter space:forall (L:fieldType) (S:set L),is_commutative_subfield S->fieldType.
(** Source for [inclusion]: the original subfield
    inclusion, 3.4.8(8), p. 329. *)
Parameter inclusion:forall (L:fieldType) (S:set L) (hS:is_commutative_subfield S),
  {rmorphism @space L S hS->L}.
(** Source for [laws]: the independent exact image
    and faithful inclusion laws, 3.4.8(8), p. 329. *)
Parameter laws:forall (L:fieldType) (S:set L) (hS:is_commutative_subfield S),
  is_commutative_subring_realisation S (@inclusion L S hS).
End CommutativeSubfieldRealisationSignature.
Module CommutativeSubfieldRealisation:CommutativeSubfieldRealisationSignature.
(** Source for [space]: hidden selection from the
    proved original subfield existence, p. 329. *)
Definition space (L:fieldType) (S:set L) (hS:is_commutative_subfield S):fieldType:=
  projT1 (cid (@commutative_subfield_realisation_exists L S hS)).
(** Source for [inclusion]: the hidden original
    inclusion witness, 3.4.8(8), p. 329. *)
Definition inclusion (L:fieldType) (S:set L) (hS:is_commutative_subfield S):
  {rmorphism @space L S hS->L}:=
  projT1 (cid (projT2 (cid (@commutative_subfield_realisation_exists L S hS)))).
(** Source for [laws]: the selected field has
    the independent original inclusion laws, p. 329. *)
Lemma laws (L:fieldType) (S:set L) (hS:is_commutative_subfield S):
  is_commutative_subring_realisation S (@inclusion L S hS).
Proof. exact:(projT2 (cid (projT2 (cid (@commutative_subfield_realisation_exists L S hS))))). Qed.
End CommutativeSubfieldRealisation.
