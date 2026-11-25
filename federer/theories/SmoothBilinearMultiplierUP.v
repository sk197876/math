(** Federer (1969), 4.1.7, pp. 355–356:
    multiply test fields by a fixed smooth form or
    vector field through the original bilinear
    coefficient operation of 4.1.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_bilinear_multiplier]: the
    original fixed-field pointwise action, supporting
    the current products of Federer 4.1.7,
    pp. 355–356. Existence and continuity are separate. *)
Definition is_smooth_bilinear_multiplier (R:realType) (X Y1 Y2 Y3:lmodType R)
    (U:X->Prop) (E1 E2 E3:lmodType R)
    (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3)
    (u:E1) (B:Y1->Y2->Y3) (P:Hom E2 E3):Prop:=
  forall f x,U x->v3 (P f) x=B (v1 u x) (v2 f x).
