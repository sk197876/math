(** Opaque envelope assignment for Federer (1969), 2.5.2, p. 92 Only the
    infimum laws are exposed. Source conventions: DaniellCoverUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import DaniellCoverUP DaniellCoverConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DaniellCoverSignature.
(** Source for [value]: the set function in the defining infimum of Federer
    2.5.2, p. 92 *)
Parameter value : forall (R : realType) (X : Type), set (X -> R) -> ((X -> R) -> R) -> set X -> \bar R.
(** Source for [laws]: infimum specification of the selected set function in
    Federer 2.5.2, p. 92 *)
Parameter laws : forall (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R),
  is_daniell_cover_envelope L A (@value R X L A).
End DaniellCoverSignature.
Module DaniellCover : DaniellCoverSignature.
(** Source for [value]: private selection from the proved envelope existence
    for Federer 2.5.2, p. 92 *)
Definition value (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R) :=
  projT1 (cid (@daniell_cover_envelope_exists R X L A)).
(** Source for [laws]: selected envelope laws in Federer 2.5.2, p. 92 *)
Lemma laws (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R) :
  is_daniell_cover_envelope L A (@value R X L A).
Proof. exact: projT2 (cid (@daniell_cover_envelope_exists R X L A)). Qed.
End DaniellCover.
