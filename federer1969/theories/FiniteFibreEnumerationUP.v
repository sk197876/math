(** Federer (1969), 3.4.8(10), p. 332:
    a finite family lists exactly the
    points in one fibre. Independent laws
    precede the local branch construction. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_finite_fibre_enumeration]:
    membership, exhaustiveness and distinctness of
    the nu points above y in
    3.4.8(10), p. 332. The
    empty finite index type describes an empty fibre. *)
Definition is_finite_fibre_enumeration (I:finType) (X Y:Type)
    (P:X->Y) (Z:set X) (y:Y) (v:I->X):Prop:=
  (forall i,Z (v i) /\P (v i) = y) /\
  (forall x,Z x ->P x = y ->exists i,v i = x) /\injective v.
