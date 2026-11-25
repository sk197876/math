(** Federer (1969), 4.1.1, p. 345: opaque smooth scalar
    multiplication operator. Product representatives are hidden;
    their original evaluation law is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormRegularity SmoothFunctionSpaceUP SmoothMultiplierUP
  SmoothMultiplierExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothMultiplierSignature.
(** Source for [operator]: multiplication by the smooth scalar
    u, supporting T L v_s in Federer 4.1.1, p. 345. *)
Parameter operator:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y),
  is_smooth_function_space hNX hNY U ev -> forall u:X->R,
    norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u ->Hom E E.
(** Source for [laws]: the exact product on the original
    open domain, supporting Federer 4.1.1, p. 345. *)
Parameter laws:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (u:X->R)
    (hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u),
    is_smooth_multiplier U ev u (@operator R X Y NX NY hNX hNY U E ev hE u hu).
End SmoothMultiplierSignature.
Module SmoothMultiplier:SmoothMultiplierSignature.
(** Source for [operator]: select the proved multiplication
    witness, supporting Federer 4.1.1, p. 345. *)
Definition operator (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (u:X->R)
    (hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u):Hom E E:=
  projT1 (cid (smooth_multiplier_exists hE hu)).
(** Source for [laws]: the hidden product satisfies its
    independent pointwise specification, supporting Federer
    4.1.1, p. 345. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (u:X->R)
    (hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u):
    is_smooth_multiplier U ev u (@operator R X Y NX NY hNX hNY U E ev hE u hu).
Proof. exact:(projT2 (cid (smooth_multiplier_exists hE hu))). Qed.
End SmoothMultiplier.
