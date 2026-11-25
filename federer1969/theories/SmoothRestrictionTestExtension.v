(** Federer (1969), 4.1.1, p. 345: restricting
    a test zero extension recovers its original smooth
    function. This exact compatibility supports both the
    fixed-support homeomorphism and the dual image claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces
  SmoothTestEvaluation SmoothRestrictionUP TestZeroExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [smooth_restriction_test_extension_inverse]:
    restriction after zero extension is the identity
    on the original test, supporting Federer
    4.1.1, p. 345. *)
Theorem smooth_restriction_test_extension_inverse (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (A B:lmodType R) (evA:A->X->Y) (evB:B->X->Y)
    (hA:is_smooth_function_space hNX hNY U evA) (hB:is_smooth_function_space hNX hNY V evB)
    (Q:Hom B A) (L:Hom (smooth_test_space hA) (smooth_test_space hB)):
  is_smooth_restriction U evA evB Q ->
  is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L ->
  forall f,Q (smooth_test_inclusion hB (L f))=smooth_test_inclusion hA f.
Proof.
move=>hQ hL f; apply:(smooth_function_extensional hA)=>x hx.
rewrite (hQ _ x hx).
exact:(@test_zero_extension_original R X Y (smooth_test_space hA) (smooth_test_space hB)
  U V (smooth_test_value hA) (smooth_test_value hB) L hL f x hx).
Qed.
