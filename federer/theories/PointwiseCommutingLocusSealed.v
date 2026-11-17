(** Federer (1969), 3.4.12, p. 339:
    the actual commuting locus is hidden behind its
    independently specified original equations. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import PointwiseCommutingLocusUP PointwiseCommutingLocusExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PointwiseCommutingLocusSignature.
(** Source for [value]: the actual complex-linear
    locus used in 3.4.12, p. 339. *)
Parameter value:forall (G X I:Type) (action:G->X->X) (P:I->X->X),set G.
(** Source for [laws]: exact original scalar commutation,
    3.4.12, p. 339. *)
Parameter laws:forall (G X I:Type) (action:G->X->X) (P:I->X->X),
  is_pointwise_commuting_locus action P (@value G X I action P).
End PointwiseCommutingLocusSignature.
Module PointwiseCommutingLocus:PointwiseCommutingLocusSignature.
(** Source for [value]: select a proved existence
    witness for the actual locus, 3.4.12, p. 339. *)
Definition value (G X I:Type) (action:G->X->X) (P:I->X->X):=
  projT1 (cid (@pointwise_commuting_locus_exists G X I action P)).
(** Source for [laws]: the selected locus has
    its independent original equations, 3.4.12, p. 339. *)
Lemma laws (G X I:Type) (action:G->X->X) (P:I->X->X):
  is_pointwise_commuting_locus action P (@value G X I action P).
Proof. exact:(projT2 (cid (@pointwise_commuting_locus_exists G X I action P))). Qed.
End PointwiseCommutingLocus.
