(** Federer (1969), 4.1.1, p. 346: compact
    smooth tests are measurable and bounded on
    their support. These supporting facts use
    the source norm topology and the original
    zeroth derivative seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassZeroTopology NormRegularity
  ContinuousMultilinearSealed PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureFiniteClosure MeasureSplit SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothFunctionSeminormFamily SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCompactTestMeasurable.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.

(** Source for [smooth_compact_set_measurable]: original
    compact supports are measurable for a measure
    containing the source Borel sets, supporting
    Federer 4.1.1, p. 346. *)
Lemma smooth_compact_set_measurable (K:smooth_compact_set hNX (fun _=>True)):
  measure_measurable mu (smooth_compact_carrier K).
Proof.
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K).
have hComplement:=@hOpen (~` smooth_compact_carrier K) (closed_openC hClosed).
have h:=measure_measurable_complement hComplement; by rewrite setCK in h.
Qed.

(** Source for [smooth_test_value_measurable]: actual
    smooth test values are norm-measurable,
    supporting the weak-dual pairing integral
    in Federer 4.1.1, p. 346. *)
Lemma smooth_test_value_measurable f:
  is_measure_measurable_function mu
    (partial_function_total (smooth_test_value hE f:X->real_norm_metric_space hNY)).
Proof.
have hClass:=norm_class_continuous (smooth_test_value_smooth hE f 0%N).
have hContinuous:continuous (fun x:real_norm_metric_space hNX=>
    (smooth_test_value hE f x:real_norm_metric_space hNY)).
  move=>x; exact (@norm_class_zero_continuous_at R X Y NX NY hNX hNY
    (fun _=>True) (smooth_test_value hE f) x hClass Logic.I).
constructor.
- rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
- move=>A hA; rewrite partial_function_total_preimage; apply:hOpen.
  move: hContinuous; rewrite continuousP=>hRaw; exact:hRaw A hA.
Qed.

(** Source for [smooth_test_zeroth_seminorm_value_bound]:
    nu^0_K bounds the original test values on K,
    supporting the local order-zero estimate
    of the distribution in Federer 4.1.1,
    p. 346. *)
Lemma smooth_test_zeroth_seminorm_value_bound f (K:smooth_compact_set hNX (fun _=>True)) x:
  smooth_compact_carrier K x ->NY (smooth_test_value hE f x)<=
    smooth_function_derivative_seminorm hD K 0%N (smooth_test_inclusion hE f).
Proof.
move=>hx.
have hBound:=smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hD K 0%N)
  (smooth_test_inclusion hE f) (leqnn 0%N) hx.
rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY (fun _=>True) E ev D hD
  (smooth_test_inclusion hE f) x Logic.I) in hBound; exact hBound.
Qed.
End SmoothCompactTestMeasurable.
