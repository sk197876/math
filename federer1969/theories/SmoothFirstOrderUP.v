(** Federer (1969), 4.1.7, p. 356: the
    original first-order form operators used to define
    boundaries act on smooth fields. Their action is
    specified through the actual first differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_first_order_operator]: the
    original bounded coefficient operation on the first
    derivative, supporting d in Federer 4.1.7, p. 356. *)
Definition is_smooth_first_order_operator (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E F:lmodType R) (fv:F->X->Z)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (M:Hom (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY) Z) (P:Hom E F):=
  forall f x,U x->fv (P f) x=M (@D 1%N x f).
