(** Federer (1969), 4.1.1, pp. 344–345: every
    smooth compactly supported function is represented by
    the opaque test space. This is proved from the
    independently specified E representation and D image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormRegularity LinearSubspaceRepresentationUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_test_represents_compact_function]:
    every smooth function vanishing off a compact K
    contained in U is an actual test, the union
    definition in Federer 4.1.1, p. 344. *)
Theorem smooth_test_represents_compact_function (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (K:smooth_compact_set hNX U) (f:X->Y):
  norm_class_all_orders hNX hNY U f ->
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  exists g:smooth_test_space hE,forall x,U x ->smooth_test_value hE g x=f x.
Proof.
move=>hClass hZero.
have [a ha]:=smooth_function_evaluation_surjective hE hClass.
have hSupport:@smooth_function_support R X Y NX hNX U E ev a `<=` smooth_compact_carrier K.
  apply:(smooth_function_compact_support_iff hE K a).2=>x hx.
  case:(pselect (U x))=>[hu|hu].
  - by rewrite (ha x hu) (hZero x hx).
  - exact:(@smooth_function_evaluation_outside R X Y NX NY hNX hNY U E ev hE a x hu).
have hMember:smooth_compact_support_subspace hE a by exists K.
have [g hg]:=subspace_representation_full (smooth_test_space_laws hE) hMember.
exists g=>x hx; rewrite /smooth_test_value hg; exact:ha.
Qed.
