(** Opaque sum interface for Federer (1969), 3.2.41, printed p. 277.
    The mathematical object is specified by its least-pair-sum laws;
    the private construction supplies existence only. Module ascription
    hides the witness. No unproved project axiom is introduced. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets.
From Federer Require Import VectorSetSumUP VectorSetSumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type VectorSetSumSignature.
(** Source for [value]: opaque A+B from the defining display of
    Federer 3.2.41, p. 277. The laws specify its meaning. *)
Parameter value : forall (V : zmodType), set V -> set V -> set V.
(** Source for [laws]: independent pair-inclusion and least-set
    laws of A+B, Federer 3.2.41, p. 277. *)
Parameter laws : forall (V : zmodType) (A B : set V),
  is_vector_set_sum A B (@value V A B).
End VectorSetSumSignature.

Module VectorSetSum : VectorSetSumSignature.
(** Source for [value]: local choice from the proved existence
    of A+B supporting Federer 3.2.41, p. 277. The construction
    and choice remain hidden behind opaque module ascription. *)
Definition value (V : zmodType) (A B : set V) :=
  projT1 (cid (@vector_set_sum_exists V A B)).
(** Source for [laws]: proved independent laws of the opaque
    sum in Federer 3.2.41, p. 277. *)
Lemma laws (V : zmodType) (A B : set V) :
  is_vector_set_sum A B (@value V A B).
Proof. exact: projT2 (cid (@vector_set_sum_exists V A B)). Qed.
End VectorSetSum.
