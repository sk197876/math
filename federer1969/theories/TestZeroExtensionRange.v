(** Federer (1969), 4.1.4, p. 348: the actual range
    of test extension by zero contains every larger-domain
    test supported in the original open set. This adapter
    reuses the original fixed-support inverse from 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP SmoothCompactSet SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothTestSubspaces SmoothTestSpaces
  SmoothTestEvaluation SmoothRestrictionUP SmoothRestrictionSealed TestZeroExtensionUP TestZeroExtensionLaws
  TestZeroExtensionFixed TestZeroExtensionFixedInverse LinearSubspaceRepresentationUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestZeroExtensionRange.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.

Local Notation valueB := (smooth_test_value hB).
Local Notation supportB := (@smooth_function_support R X Y NX hNX V TB valueB).

(** Source for [test_zero_extension_range]: every test on V
    supported inside U is the actual zero extension of a
    test on U, supporting the compact-domain localization
    in Federer 4.1.4, p. 348. The previously proved fixed-K
    inverse supplies the witness, retaining its exact support. *)
Theorem test_zero_extension_range g:
  supportB g `<=` U ->exists f:TA,L f=g.
Proof.
move=>hSupport.
pose K:=@Build_smooth_compact_set R X NX hNX U (supportB g)
  hSupport (smooth_test_support_compact hB g).
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
have hFixed:smooth_fixed_support_subspace hB KV (smooth_test_inclusion hB g).
  by move=>x hx.
have[gK hGK]:=subspace_representation_full (smooth_fixed_test_space_laws hB KV) hFixed.
pose F:=@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K.
pose H:=@test_zero_extension_fixed_inverse R X Y NX NY hNX hNY U V hU hUV
  A B evA evB hA hB K.
have hRight:=@test_zero_extension_fixed_right_inverse R X Y NX NY hNX hNY U V hU hUV
  A B evA evB hA hB L hL K gK.
have hStep:=@test_zero_extension_fixed_step_commutes R X Y NX NY hNX hNY U V hUV
  A B evA evB hA hB L hL K (H gK).
change (smooth_test_step hB KV (F (H gK))=L (smooth_test_step hA K (H gK))) in hStep.
rewrite hRight in hStep.
exists (smooth_test_step hA K (H gK)).
rewrite -hStep.
apply:(subspace_representation_injective (smooth_test_space_laws hB)).
by rewrite smooth_test_step_evaluation hGK.
Qed.
End TestZeroExtensionRange.
