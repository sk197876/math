(** Federer (1969), 4.1.7, p. 356: actual
    constant smooth coefficient fields used in the
    original coordinate and current identities.
    The public law is independent of a construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothConstantUP SmoothConstantExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SmoothConstantSignature.
(** Source for [operator]: the original constant smooth
    field map, supporting Federer 4.1.7, p. 356. *)
Parameter operator:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:X->Prop)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev),Hom Y E.
(** Source for [laws]: exact original constant values,
    supporting Federer 4.1.7, p. 356. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:X->Prop)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev),
  is_smooth_constant_operator U ev (@operator R X Y NX NY hNX hNY U hU E ev hE).
End SmoothConstantSignature.
Module SmoothConstant:SmoothConstantSignature.
(** Source for [operator]: seal the proved existence
    witness, supporting Federer 4.1.7, p. 356. *)
Definition operator (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:X->Prop)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev):Hom Y E:=
  projT1 (cid (@smooth_constant_operator_exists R X Y NX NY hNX hNY U hU E ev hE)).
(** Source for [laws]: the opaque map satisfies its
    original independent law, supporting Federer
    4.1.7, p. 356. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:X->Prop)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev):
  is_smooth_constant_operator U ev (@operator R X Y NX NY hNX hNY U hU E ev hE).
Proof. exact:(projT2 (cid (@smooth_constant_operator_exists R X Y NX NY hNX hNY U hU E ev hE))). Qed.
End SmoothConstant.
