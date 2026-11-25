(** Federer (1969), 4.1.1, p. 346: opaque
    globally smooth translations with the original
    pointwise value laws. Their existence has been
    proved before sealing. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP SmoothGlobalTranslationUP
  SmoothGlobalTranslationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothGlobalTranslationSignature.
(** Source for [operator]: the actual translated smooth
    function in Federer 4.1.1, p. 346. *)
Parameter operator:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->X->Y),
  is_smooth_function_space hNX hNY (fun _=>True) ev ->X->Hom E E.
(** Source for [laws]: the original pointwise translation
    identity supporting Federer 4.1.1, p. 346. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY (fun _=>True) ev) c,
  is_smooth_global_translation ev c (@operator R X Y NX NY hNX hNY E ev hE c).
End SmoothGlobalTranslationSignature.
Module SmoothGlobalTranslation:SmoothGlobalTranslationSignature.
(** Source for [operator]: hide the proved translation
    witness for Federer 4.1.1, p. 346. *)
Definition operator (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY (fun _=>True) ev) c:Hom E E:=
  projT1 (cid (@smooth_global_translation_exists R X Y NX NY hNX hNY E ev hE c)).
(** Source for [laws]: the hidden witness satisfies
    the independent translation laws, supporting
    Federer 4.1.1, p. 346. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY (fun _=>True) ev) c:
  is_smooth_global_translation ev c (@operator R X Y NX NY hNX hNY E ev hE c).
Proof. exact:(projT2 (cid (@smooth_global_translation_exists R X Y NX NY hNX hNY E ev hE c))). Qed.
End SmoothGlobalTranslation.
