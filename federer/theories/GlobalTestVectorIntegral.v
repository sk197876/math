(** Federer (1969), 4.1.4, p. 349: every original
    global Banach-valued test has its actual vector integral.
    Its compact support supplies the existing integral
    existence theorem without whole-target separability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  PartialFunctionBasic MeasureVectorIntegralUP ContinuousCompactFieldIntegral EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [global_test_vector_integral_exists]: the actual
    integral of each f in D(R^n,Y) used in the constant-density
    inference of Federer 4.1.4, p. 349. *)
Theorem global_test_vector_integral_exists (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      hNY (fun _=>True) ev) (f:smooth_test_space hE):
  exists v:Y,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(smooth_test_value hE f x:real_norm_metric_space hNY))) v.
Proof.
have[K hK]:=smooth_test_support_bound hE f.
apply:(@continuous_compact_field_integral_exists R n Y NY hNY hY (smooth_test_value hE f) K).
- exact:(norm_class_continuous (smooth_test_value_smooth hE f 0%N)).
- exact:(smooth_function_compact_support_iff hE K (smooth_test_inclusion hE f)).1 hK.
Qed.
