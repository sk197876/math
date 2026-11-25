(** Federer (1969), 4.1.1, p. 345: multiplication of a
    test function by a smooth scalar coefficient, used in T L v_s.
    The operator is specified by its original pointwise action. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smooth_multiplier]: independent pointwise
    law of the scalar multiplication operator, supporting
    (T L v_s)(phi)=T(v_s phi) in Federer 4.1.1, p. 345. *)
Definition is_smooth_multiplier (R:realType) (X Y:lmodType R)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (u:X->R) (P:Hom E E):=
  forall f x,U x -> ev (P f) x=u x*:ev f x.
