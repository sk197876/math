(** Federer (1969), 3.4.8(4), p. 326:
    fixed-vector subsets behind exact opaque membership laws. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
From Federer Require Import PointwiseFixingLocusUP PointwiseFixingLocusExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PointwiseFixingLocusSignature.
(** Source for [value]: the original pointwise fixing
    subset, 3.4.8(4), p. 326. *)
Parameter value:forall (G X:Type) (action:G->X->X) n (e:'I_n->X) (J:set 'I_n),set G.
(** Source for [laws]: the exact original fixed-vector
    equations, 3.4.8(4), p. 326. *)
Parameter laws:forall (G X:Type) (action:G->X->X) n (e:'I_n->X) (J:set 'I_n),
  is_pointwise_fixing_locus action e J (@value G X action n e J).
End PointwiseFixingLocusSignature.
Module PointwiseFixingLocus:PointwiseFixingLocusSignature.
(** Source for [value]: private selection of the proved
    membership subset, 3.4.8(4), p. 326. *)
Definition value (G X:Type) (action:G->X->X) n (e:'I_n->X) (J:set 'I_n):=
  projT1 (cid (@pointwise_fixing_locus_exists G X action n e J)).
(** Source for [laws]: the selected subset satisfies
    its independent membership equations,
    3.4.8(4), p. 326. *)
Lemma laws (G X:Type) (action:G->X->X) n (e:'I_n->X) (J:set 'I_n):
  is_pointwise_fixing_locus action e J (@value G X action n e J).
Proof. exact:(projT2 (cid (@pointwise_fixing_locus_exists G X action n e J))). Qed.
End PointwiseFixingLocus.
