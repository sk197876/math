(** Federer (1969), 4.1.1, p. 346: opaque directional
    derivative endomorphism of the smooth-function space. Only
    its exact derivative evaluation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothDirectionalDerivativeSignature.
(** Source for [operator]: the smooth directional derivative,
    giving D_j on standard basis directions, Federer 4.1.1, p. 346. *)
Parameter operator:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y),
    is_smooth_function_space hNX hNY U ev ->
    forall D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY),
      @is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D -> X -> Hom E E.
(** Source for [laws]: the actual derivative values on U,
    supporting the test-function operators in Federer 4.1.1, p. 346. *)
Parameter laws:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D) (v:X),
    @is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v
      (@operator R X Y NX NY hNX hNY U E ev hE D hD v).
End SmoothDirectionalDerivativeSignature.
Module SmoothDirectionalDerivative:SmoothDirectionalDerivativeSignature.
(** Source for [operator]: select the proved smooth derivative
    witness, supporting Federer 4.1.1, p. 346. *)
Definition operator (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D) (v:X):Hom E E:=
  projT1 (cid (smooth_directional_derivative_exists hE hD v)).
(** Source for [laws]: the hidden operator has its independent
    exact evaluation law, supporting Federer 4.1.1, p. 346. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D) (v:X):
    @is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v
      (@operator R X Y NX NY hNX hNY U E ev hE D hD v).
Proof. exact:(projT2 (cid (smooth_directional_derivative_exists hE hD v))). Qed.
End SmoothDirectionalDerivative.
