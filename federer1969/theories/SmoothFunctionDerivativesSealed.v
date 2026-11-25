(** Federer (1969), 4.1.1, pp. 343–344: opaque simultaneous
    derivative operators for the abstract smooth-function space.
    Existence and linearity are proved before this seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionDerivativesExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SmoothFunctionDerivativesSignature.
(** Source for [operators]: the original derivatives on E(U,Y),
    Federer 4.1.1, p. 343. *)
Parameter operators : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (value:E->X->Y),
    is_smooth_function_space hNX hNY U value ->
    forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
(** Source for [laws]: the exact, continuous derivative fields,
    with their harmless total-representative convention, satisfy
    the independent laws supporting Federer 4.1.1, pp. 343–344. *)
Parameter laws : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (value:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U value),
    @is_smooth_function_derivatives R X Y NX NY hNX hNY U E value
      (@operators R X Y NX NY hNX hNY U E value hE).
End SmoothFunctionDerivativesSignature.

Module SmoothFunctionDerivatives : SmoothFunctionDerivativesSignature.
(** Source for [operators]: hidden proved derivative witness for
    E(U,Y), Federer 4.1.1, p. 343. *)
Definition operators (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (value:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U value) :
    forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY) :=
  projT1 (cid (smooth_function_derivatives_exist hE)).
(** Source for [laws]: the private witness proves the original
    higher-derivative laws, Federer 4.1.1, pp. 343–344. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (value:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U value) :
    @is_smooth_function_derivatives R X Y NX NY hNX hNY U E value
      (@operators R X Y NX NY hNX hNY U E value hE).
Proof. exact:(projT2 (cid (smooth_function_derivatives_exist hE))). Qed.
End SmoothFunctionDerivatives.
