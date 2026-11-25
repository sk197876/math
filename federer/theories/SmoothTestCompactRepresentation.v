(** Federer (1969), 4.1.1, pp. 344–345: the
    opaque test representation retains its actual compact
    support bound. This supporting existence form uses
    only the previously proved representation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormRegularity SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_test_represents_with_support]: a
    represented compactly supported smooth function has
    exactly its original values on U and support
    inside the supplied K, supporting Federer
    4.1.1, pp. 344–345. *)
Theorem smooth_test_represents_with_support (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (K:smooth_compact_set hNX U) (f:X->Y):
  norm_class_all_orders hNX hNY U f ->
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  exists g:smooth_test_space hE,(forall x,U x ->smooth_test_value hE g x=f x) /\
    @smooth_function_support R X Y NX hNX U (smooth_test_space hE) (smooth_test_value hE) g `<=`
      smooth_compact_carrier K.
Proof.
move=>hClass hZero.
have [g hg]:=@smooth_test_represents_compact_function R X Y NX NY hNX hNY U E ev hE K f hClass hZero.
exists g; split; first exact hg.
apply:(smooth_function_compact_support_iff hE K (smooth_test_inclusion hE g)).2=>x hx.
case:(pselect (U x))=>[hu|hu].
- change (smooth_test_value hE g x=0); by rewrite (hg x hu) (hZero x hx).
- exact:(@smooth_function_evaluation_outside R X Y NX NY hNX hNY U E ev hE (smooth_test_inclusion hE g) x hu).
Qed.
