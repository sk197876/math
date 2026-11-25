(** Federer (1969), 4.1.1, pp. 343–344: opaque exact derivative
    seminorms. Only their independently stated least-bound laws
    are public; compactness proves existence before sealing. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothCompactSet
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothDerivativeSeminormExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SmoothDerivativeSeminormSignature.
(** Source for [value]: the original nu^i_K on the abstract
    smooth-function space, Federer 4.1.1, p. 343. *)
Parameter value : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY)),
    @is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D ->
    smooth_compact_set hNX U -> nat -> E->R.
(** Source for [laws]: the original least nonnegative derivative
    bound, Federer 4.1.1, pp. 343–344. *)
Parameter laws : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (K:smooth_compact_set hNX U) (i:nat),
    @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i
      (@value R X Y NX NY hNX hNY U E ev D hD K i).
End SmoothDerivativeSeminormSignature.

Module SmoothDerivativeSeminorm : SmoothDerivativeSeminormSignature.
(** Source for [value]: private selection of the already proved
    nu^i_K witness, Federer 4.1.1, p. 343. *)
Definition value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (K:smooth_compact_set hNX U) (i:nat) : E->R :=
  projT1 (cid (smooth_derivative_seminorm_exists hD K i)).
(** Source for [laws]: the proved exact derivative seminorm
    satisfies its independent specification, Federer 4.1.1, p. 343. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (K:smooth_compact_set hNX U) (i:nat) :
    @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i
      (@value R X Y NX NY hNX hNY U E ev D hD K i).
Proof. exact:(projT2 (cid (smooth_derivative_seminorm_exists hD K i))). Qed.
End SmoothDerivativeSeminorm.
