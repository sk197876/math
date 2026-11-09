(** Federer (1969), 3.4.5, p. 319: the germ carrier
    and representative map are hidden behind their local-agreement laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP LocalGermConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type LocalGermsSignature.
(** Source for [space]: the germ carrier in 3.4.5, p. 319. *)
Parameter space:forall (X:topologicalType) (Y:Type) (P:choiceType),
  (P->X->Y)->X->choiceType.
(** Source for [germ]: the original representative-to-germ map
    of 3.4.5, p. 319, for the specified representatives. *)
Parameter germ:forall (X:topologicalType) (Y:Type) (P:choiceType)
  (value:P->X->Y) (a:X),P->space value a.
(** Source for [laws]: equality and representation laws from
    3.4.5, p. 319, without further algebraic assumptions. *)
Parameter laws:forall (X:topologicalType) (Y:Type) (P:choiceType)
  (value:P->X->Y) (a:X),is_local_germ_space value a (@germ X Y P value a).
End LocalGermsSignature.
Module LocalGerms:LocalGermsSignature.
(** Source for [space]: private choice of the germ-space
    existence witness, 3.4.5, p. 319. *)
Definition space (X:topologicalType) (Y:Type) (P:choiceType) (value:P->X->Y) (a:X):=
  projT1 (cid (@local_germ_space_exists X Y P value a)).
(** Source for [germ]: the private quotient projection from
    the same existence witness, 3.4.5, p. 319. *)
Definition germ (X:topologicalType) (Y:Type) (P:choiceType) (value:P->X->Y) (a:X):=
  projT1 (cid (projT2 (cid (@local_germ_space_exists X Y P value a)))).
(** Source for [laws]: the selected witnesses satisfy the
    independent local-agreement laws, 3.4.5, p. 319. *)
Lemma laws (X:topologicalType) (Y:Type) (P:choiceType) (value:P->X->Y) (a:X):
  is_local_germ_space value a (@germ X Y P value a).
Proof. exact:(projT2 (cid (projT2 (cid (@local_germ_space_exists X Y P value a))))). Qed.
End LocalGerms.
