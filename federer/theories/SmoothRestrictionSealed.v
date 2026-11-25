(** Federer (1969), 4.1.1, p. 345: opaque smooth
    restriction, exposing only the proved original
    evaluation law on the smaller open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP SmoothFunctionSpaceUP
  SmoothRestrictionUP SmoothRestrictionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothRestrictionSignature.
(** Source for [operator]: the smooth restriction map,
    supporting the open-set dual maps in Federer
    4.1.1, p. 345. *)
Parameter operator:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop), (forall x,U x ->norm_domain_interior NX U x) ->
    (forall x,U x ->V x) ->forall (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y),
      is_smooth_function_space hNX hNY U evA ->is_smooth_function_space hNX hNY V evB ->Hom B A.
(** Source for [laws]: original restriction values on U,
    supporting Federer 4.1.1, p. 345. *)
Parameter laws:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hU:forall x,U x ->norm_domain_interior NX U x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB),
    is_smooth_restriction U evA evB (@operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).
End SmoothRestrictionSignature.
Module SmoothRestriction:SmoothRestrictionSignature.
(** Source for [operator]: select the already proved
    restriction witness, supporting Federer 4.1.1,
    p. 345. *)
Definition operator (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hU:forall x,U x ->norm_domain_interior NX U x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB):Hom B A:=
  projT1 (cid (smooth_restriction_exists hU hUV hA hB)).
(** Source for [laws]: the hidden representative satisfies
    the independent restriction specification, supporting
    Federer 4.1.1, p. 345. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hU:forall x,U x ->norm_domain_interior NX U x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB):
    is_smooth_restriction U evA evB (@operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).
Proof. exact:(projT2 (cid (smooth_restriction_exists hU hUV hA hB))). Qed.
End SmoothRestriction.
