(** Federer (1969), 4.1.7, p. 356: opaque
    smooth first-order operators. Only their original
    action through the actual differential is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFirstOrderUP SmoothFirstOrderExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothFirstOrderSignature.
(** Source for [operator]: the original smooth
    first-order operator, supporting Federer 4.1.7,
    p. 356. *)
Parameter operator:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY)),
  @is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D ->
  forall M:Hom (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY) Z,
    norm_bounded_linear (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY) NZ M ->Hom E F.
(** Source for [laws]: original first-differential
    values on U, supporting Federer 4.1.7, p. 356. *)
Parameter laws:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (M:Hom (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY) Z)
    (hM:norm_bounded_linear (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY) NZ M),
  is_smooth_first_order_operator U fv D M
    (@operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD M hM).
End SmoothFirstOrderSignature.
Module SmoothFirstOrder:SmoothFirstOrderSignature.
(** Source for [operator]: hide the proved first-order
    representative, supporting Federer 4.1.7, p. 356. *)
Definition operator (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (M:Hom (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY) Z)
    (hM:norm_bounded_linear (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY) NZ M):Hom E F:=
  projT1 (cid (@smooth_first_order_operator_exists R X Y Z NX NY NZ hNX hNY hNZ
    U E F ev fv hE hF D hD M hM)).
(** Source for [laws]: the sealed value satisfies its
    independent first-order specification, supporting
    Federer 4.1.7, p. 356. *)
Lemma laws (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hE:is_smooth_function_space hNX hNY U ev)
    (hF:is_smooth_function_space hNX hNZ U fv)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (M:Hom (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY) Z)
    (hM:norm_bounded_linear (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY) NZ M):
  is_smooth_first_order_operator U fv D M
    (@operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD M hM).
Proof.
exact:(projT2 (cid (@smooth_first_order_operator_exists R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hE hF D hD M hM))).
Qed.
End SmoothFirstOrder.
