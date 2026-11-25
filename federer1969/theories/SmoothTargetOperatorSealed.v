(** Federer (1969), 4.1.7, pp. 355–356: opaque
    coefficient-linear smooth operators. The public
    law gives precisely the original pointwise action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  SmoothFunctionSpaceUP SmoothTargetOperatorUP SmoothTargetOperatorExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothTargetOperatorSignature.
(** Source for [operator]: the original smooth
    coefficient operator, supporting Federer 4.1.7,
    pp. 355–356. *)
Parameter operator:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z),
  is_smooth_function_space hNX hNY U ev ->
  is_smooth_function_space hNX hNZ U fv ->forall L:Hom Y Z,
  norm_bounded_linear NY NZ L ->Hom E F.
(** Source for [laws]: original evaluation on the
    actual open domain, supporting Federer 4.1.7,
    pp. 355–356. *)
Parameter laws:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (L:Hom Y Z) (hL:norm_bounded_linear NY NZ L),
  is_smooth_target_operator U ev fv L
    (@operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).
End SmoothTargetOperatorSignature.
Module SmoothTargetOperator:SmoothTargetOperatorSignature.
(** Source for [operator]: hide the proved coefficient
    operator witness, supporting Federer 4.1.7,
    pp. 355–356. *)
Definition operator (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (L:Hom Y Z) (hL:norm_bounded_linear NY NZ L):Hom E F:=
  projT1 (cid (smooth_target_operator_exists hE hF hL)).
(** Source for [laws]: the sealed operator satisfies
    its independent original law, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma laws (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (L:Hom Y Z) (hL:norm_bounded_linear NY NZ L):
  is_smooth_target_operator U ev fv L
    (@operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).
Proof. exact:(projT2 (cid (smooth_target_operator_exists hE hF hL))). Qed.
End SmoothTargetOperator.
