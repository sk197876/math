(** Federer (1969), 4.1.1, p. 345: restriction of
    smooth functions supplies the map transposed in the
    compact-support distribution extension. Its pointwise
    law is independent of any representative construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_restriction]: the actual function
    on the smaller domain is the restriction of the
    original function, supporting the open-set maps in
    Federer 4.1.1, p. 345. *)
Definition is_smooth_restriction (R:fieldType) (X:Type) (Y A B:lmodType R)
    (U:X->Prop) (evA:A->X->Y) (evB:B->X->Y) (L:Hom B A):Prop:=
  forall f x,U x ->evA (L f) x=evB f x.
