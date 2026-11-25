(** Federer (1969), 4.1.7, pp. 355–356: fixed
    coefficient operations shrink the support of smooth
    fields, so they act on the original compact tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTargetOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothTargetSupport.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:set X.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Variable L:Hom Y Z.
Variable P:Hom E F.
Hypothesis hP:is_smooth_target_operator U ev fv L P.
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_target_operator_support_subset]:
    the fixed coefficient image has support contained
    in the original field support, supporting Federer
    4.1.7, pp. 355–356. *)
Theorem smooth_target_operator_support_subset f:
  @smooth_function_support R X Z NX hNX U F fv (P f) `<=`
    @smooth_function_support R X Y NX hNX U E ev f.
Proof.
move=>x [hx hCl]; split=>//.
apply:(@closureS XN [set y|fv (P f) y<>0] [set y|ev f y<>0] _ x hCl)=>y hn hy.
change (fv (P f) y<>0) in hn.
case:(pselect (U y))=>[hu|hu].
- by move:hn; rewrite (@hP f y hu) hy linear0.
- exact:hn (smooth_function_evaluation_outside hF (P f) hu).
Qed.

(** Source for [smooth_target_operator_preserves_support]:
    every original fixed compact-support step is
    preserved, supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_target_operator_preserves_support (K:smooth_compact_set hNX U) f:
  @smooth_function_support R X Y NX hNX U E ev f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Z NX hNX U F fv (P f) `<=` smooth_compact_carrier K.
Proof. move=>hf x hx; exact:(hf x (@smooth_target_operator_support_subset f x hx)). Qed.
End SmoothTargetSupport.
