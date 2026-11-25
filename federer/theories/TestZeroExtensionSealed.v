(** Federer (1969), 4.1.1, p. 345: opaque actual
    test zero extension. The representative is hidden
    behind the independent original and zero value laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation TestZeroExtensionUP TestZeroExtensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type TestZeroExtensionSignature.
(** Source for [operator]: actual extension by zero of
    tests from U to V, Federer 4.1.1,
    p. 345. *)
Parameter operator:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop),(forall x,V x ->norm_domain_interior NX V x) ->
    (forall x,U x ->V x) ->forall (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB),
    Hom (smooth_test_space hA) (smooth_test_space hB).
(** Source for [laws]: exact original values and zero
    values for the opaque extension, Federer
    4.1.1, p. 345. *)
Parameter laws:forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hV:forall x,V x ->norm_domain_interior NX V x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB),
    is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB)
      (@operator R X Y NX NY hNX hNY U V hV hUV A B evA evB hA hB).
End TestZeroExtensionSignature.
Module TestZeroExtension:TestZeroExtensionSignature.
(** Source for [operator]: select the previously proved
    zero-extension witness, Federer 4.1.1,
    p. 345. *)
Definition operator (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hV:forall x,V x ->norm_domain_interior NX V x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB):
    Hom (smooth_test_space hA) (smooth_test_space hB):=
  projT1 (cid (test_zero_extension_exists hV hUV hA hB)).
(** Source for [laws]: the hidden witness satisfies the
    independently stated extension laws, Federer
    4.1.1, p. 345. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (hV:forall x,V x ->norm_domain_interior NX V x)
    (hUV:forall x,U x ->V x) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB):
    is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB)
      (@operator R X Y NX NY hNX hNY U V hV hUV A B evA evB hA hB).
Proof. exact:(projT2 (cid (test_zero_extension_exists hV hUV hA hB))). Qed.
End TestZeroExtension.
