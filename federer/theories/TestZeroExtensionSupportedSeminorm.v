(** Federer (1969), 4.1.8, p. 360: the support
    seminorm of the original test controls every same-order
    seminorm of its zero extension. This supporting estimate
    reuses the exact zero-extension derivative and support laws
    of 4.1.1, p. 345, already used for fixed-step continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionSupport SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothDerivativeSupport
  SmoothTestSpaces SmoothTestEvaluation TestZeroExtensionUP TestZeroExtensionLaws TestZeroExtensionDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestZeroExtensionSupportedSeminorm.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x->V x.
Variables A B:lmodType R.
Variables (evA:A->X->Y) (evB:B->X->Y).
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Variables (DA:forall j,X->Hom A (Z j)) (DB:forall j,X->Hom B (Z j)).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Variable L:Hom (smooth_test_space hA) (smooth_test_space hB).
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.

(** Source for [test_zero_extension_supported_seminorm_bound]:
    the exact same-support, same-order, constant-one estimate
    for actual zero-extended tests, supporting the slice continuity
    in Federer 4.1.8, p. 360. The target compact
    index is arbitrary, and no compact enlargement is assumed. *)
Theorem test_zero_extension_supported_seminorm_bound
    (K:smooth_compact_set hNX U) (C:smooth_compact_set hNX V) i f:
  @smooth_function_support R X Y NX hNX U A evA (smooth_test_inclusion hA f)
    `<=` smooth_compact_carrier K->
  smooth_function_derivative_seminorm hDB C i (smooth_test_inclusion hB (L f))<=
    smooth_function_derivative_seminorm hDA K i (smooth_test_inclusion hA f).
Proof.
move=>hK.
have hSource:=smooth_function_derivative_seminorm_laws hDA K i.
have hSupport:=@test_zero_extension_preserves_compact_bound R X Y NX NY hNX hNY
  U V hUV A B evA evB hA hB L hL K f hK.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
apply:(smooth_derivative_seminorm_least (smooth_function_derivative_seminorm_laws hDB C i)).
- exact:(smooth_derivative_seminorm_nonnegative hSource (smooth_test_inclusion hA f)).
- move=>j hj x hx.
  case:(pselect (smooth_compact_carrier K x))=>[hInside|hOutside].
  + rewrite -(@test_zero_extension_higher_derivative R X Y NX NY hNX hNY U V hU hUV
      A B evA evB hA hB DA DB hDA hDB L hL j f x (smooth_compact_in_domain K x hInside)).
    exact:(smooth_derivative_seminorm_bound hSource (smooth_test_inclusion hA f) hj hInside).
  + rewrite (@smooth_derivative_outside_compact_support R X Y NX NY hNX hNY V hV B evB hB
      DB hDB KV (smooth_test_inclusion hB (L f)) hSupport j x hOutside)
      (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY
        (@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)).1).
    exact:(smooth_derivative_seminorm_nonnegative hSource (smooth_test_inclusion hA f)).
Qed.
End TestZeroExtensionSupportedSeminorm.
