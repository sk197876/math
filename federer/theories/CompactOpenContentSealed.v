(** Opaque witness for the compact-test supremum in Federer
    (1969), 2.5.14, p. 107. Specifications and source
    editions are in CompactOpenContentUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactOpenContentUP CompactOpenContentConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CompactOpenContentSignature.
(** Source for [value]: alpha(V) from Federer 2.5.14, p. 107. *)
Parameter value : forall (R : realType) (X : topologicalType), ((X -> R) -> R) -> set X -> \bar R.
(** Source for [laws]: the supremum laws for alpha in Federer
    2.5.14, p. 107. *)
Parameter laws : forall (R : realType) (X : topologicalType) (A : (X -> R) -> R),
  is_compact_open_content A (@value R X A).
End CompactOpenContentSignature.
Module CompactOpenContent : CompactOpenContentSignature.
(** Source for [value]: private choice of the supremum witness
    for alpha in Federer 2.5.14, p. 107. *)
Definition value (R : realType) (X : topologicalType) (A : (X -> R) -> R) :=
  projT1 (cid (@compact_open_content_exists R X A)).
(** Source for [laws]: the chosen supremum satisfies the laws
    in Federer 2.5.14, p. 107. *)
Lemma laws (R : realType) (X : topologicalType) (A : (X -> R) -> R) :
  is_compact_open_content A (@value R X A).
Proof. exact: projT2 (cid (@compact_open_content_exists R X A)). Qed.
End CompactOpenContent.
