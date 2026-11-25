(** Federer (1969), 4.1.7, pp. 355–356: fixed
    smooth bilinear operations shrink both supports.
    The proof uses the original closure definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothBilinearMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothBilinearSupport.
Variable R:realType.
Variables X Y1 Y2 Y3:lmodType R.
Variables (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R).
Hypotheses (hNX:is_real_norm NX) (hN1:is_real_norm N1)
  (hN2:is_real_norm N2) (hN3:is_real_norm N3).
Variable U:set X.
Variables E1 E2 E3:lmodType R.
Variables (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3).
Hypothesis hE1:is_smooth_function_space hNX hN1 U v1.
Hypothesis hE2:is_smooth_function_space hNX hN2 U v2.
Hypothesis hE3:is_smooth_function_space hNX hN3 U v3.
Variable B:Y1->Y2->Y3.
Hypothesis hB:bilinear B.
Variable u:E1.
Variable P:Hom E2 E3.
Hypothesis hP:is_smooth_bilinear_multiplier U v1 v2 v3 u B P.
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_bilinear_multiplier_support_subset]:
    the product support is contained in the test
    support, supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_bilinear_multiplier_support_subset f:
  @smooth_function_support R X Y3 NX hNX U E3 v3 (P f) `<=`
    @smooth_function_support R X Y2 NX hNX U E2 v2 f.
Proof.
move=>x [hx hCl]; split=>//.
apply:(@closureS XN [set y|v3 (P f) y<>0] [set y|v2 f y<>0] _ x hCl)=>y hn hy.
change (v3 (P f) y<>0) in hn.
case:(pselect (U y))=>[hu|hu].
- by move:hn; rewrite (@hP f y hu) hy (bil0r hB).
- exact:hn (smooth_function_evaluation_outside hE3 (P f) hu).
Qed.

(** Source for [smooth_bilinear_multiplier_fixed_support_subset]:
    the product also has support inside the fixed
    smooth field's support, supporting Federer
    4.1.7, pp. 355–356. *)
Theorem smooth_bilinear_multiplier_fixed_support_subset f:
  @smooth_function_support R X Y3 NX hNX U E3 v3 (P f) `<=`
    @smooth_function_support R X Y1 NX hNX U E1 v1 u.
Proof.
move=>x [hx hCl]; split=>//.
apply:(@closureS XN [set y|v3 (P f) y<>0] [set y|v1 u y<>0] _ x hCl)=>y hn hy.
change (v3 (P f) y<>0) in hn.
case:(pselect (U y))=>[hu|hu].
- by move:hn; rewrite (@hP f y hu) hy (bil0l hB).
- exact:hn (smooth_function_evaluation_outside hE3 (P f) hu).
Qed.

(** Source for [smooth_bilinear_multiplier_preserves_support]:
    each original compact support step is preserved,
    supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_bilinear_multiplier_preserves_support (K:smooth_compact_set hNX U) f:
  @smooth_function_support R X Y2 NX hNX U E2 v2 f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Y3 NX hNX U E3 v3 (P f) `<=` smooth_compact_carrier K.
Proof. move=>hf x hx; exact:(hf x (@smooth_bilinear_multiplier_support_subset f x hx)). Qed.
End SmoothBilinearSupport.
