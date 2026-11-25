(** Federer (1969), 4.1.5, p. 350:
    S=mu restricted to the actual scalar
    tests. This independent specification uses
    the original evaluations on U before
    proving existence or distribution continuity. *)
From mathcomp Require Import all_boot all_algebra functions reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_scalar_daniell_test_restriction]: the exact
    restriction S=mu|D(U,R) in Federer
    4.1.5, p. 350. *)
Definition is_scalar_daniell_test_restriction (R:realType) (X:Type) (E:lmodType R)
    (values:E->X->R) (A:(X->R)->R) (S:Hom E R^o):Prop:=
  forall phi,S phi=A (values phi).
