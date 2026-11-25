(** Federer (1969), 4.1.4, p. 348: opaque access to
    the actual inner components C_e, with their proved
    original component relation as the public law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerComponentFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type InnerComponentFamilySignature.
(** Source for [value]: the original family of components of a
    in the inward loci, Federer 4.1.4, p. 348. *)
Parameter value:forall (R:realType) (X:topologicalType) (O:R->set X) (a:X),R->set X.
(** Source for [laws]: the exact original component identity,
    Federer 4.1.4, p. 348. *)
Parameter laws:forall (R:realType) (X:topologicalType) (O:R->set X) (a:X),
  is_inner_component_family O a (@value R X O a).
End InnerComponentFamilySignature.
Module InnerComponentFamily:InnerComponentFamilySignature.
(** Source for [value]: the proved component-family witness is
    hidden for Federer 4.1.4, p. 348. *)
Definition value (R:realType) (X:topologicalType) (O:R->set X) (a:X):R->set X:=
  projT1 (cid (@inner_component_family_exists R X O a)).
(** Source for [laws]: the actual opaque C_e satisfies the
    original component identity, Federer 4.1.4, p. 348. *)
Lemma laws (R:realType) (X:topologicalType) (O:R->set X) (a:X):
  is_inner_component_family O a (@value R X O a).
Proof. exact:(projT2 (cid (@inner_component_family_exists R X O a))). Qed.
End InnerComponentFamily.
