(** Federer (1969), 4.1.2, p. 347: linear
    combinations of the actual convolution integrals. These
    total-map forms reuse the exact partial-domain laws
    of the original vector integral in 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic MeasureVectorIntegralUP MeasureVectorIntegralAddition
  MeasureVectorIntegralScale MeasureVectorIntegralDifference MeasureVectorIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TotalVectorIntegralArithmetic.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable N:Y->R.
Hypothesis hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.

(** Source for [measure_vector_integral_graph_equivalent]: equal
    partial integral graphs have the same value,
    supporting Federer 4.1.2, p. 347, by
    the almost-everywhere invariance of 2.4.12, pp. 87–88. *)
Lemma measure_vector_integral_graph_equivalent
    (f g:partial_function X (real_norm_metric_space hN)) y:
  (forall x z,partial_function_graph f x z<->partial_function_graph g x z) ->
  is_measure_vector_integral mu f y ->is_measure_vector_integral mu g y.
Proof.
move=>hGraph hI.
apply:(@measure_vector_integral_almost_equal R X Y N hN mu hm f g y hI).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
  (measurable_function_domain hI.1.2.1.1)).
move=>x [z hz]; exists z; split=>//; exact:(hGraph x z).1 hz.
Qed.

(** Source for [total_vector_integral_add]: additive convolution
    integrals, supporting Federer 4.1.2, p. 347. *)
Lemma total_vector_integral_add (f g:X->Y) y z:
  is_measure_vector_integral mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(g x:real_norm_metric_space hN))) z ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(f x+g x:real_norm_metric_space hN))) (y+z).
Proof.
move=>hf hg.
apply:(measure_vector_integral_graph_equivalent _ (@measure_vector_integral_add R X Y N hN mu hm _ _ y z hf hg))=>x v.
rewrite partial_vector_add_graph; split.
- move=>[p [q [hp [hq he]]]].
  change (f x=p) in hp; change (g x=q) in hq.
  change (f x+g x=v); by rewrite hp hq.
- move=>hv; exists (f x),(g x); by split=>//; split.
Qed.

(** Source for [total_vector_integral_subtract]: the actual
    integral of the convolution error is the difference
    of its integrals, Federer 4.1.2, p. 347. *)
Lemma total_vector_integral_subtract (f g:X->Y) y z:
  is_measure_vector_integral mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(g x:real_norm_metric_space hN))) z ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(f x-g x:real_norm_metric_space hN))) (y-z).
Proof.
move=>hf hg.
apply:(measure_vector_integral_graph_equivalent _ (@measure_vector_integral_subtract R X Y N hN mu hm _ _ y z hf hg))=>x v.
rewrite partial_vector_subtract_graph; split.
- move=>[p [q [hp [hq he]]]].
  change (f x=p) in hp; change (g x=q) in hq.
  change (f x-g x=v); by rewrite hp hq.
- move=>hv; exists (f x),(g x); by split=>//; split.
Qed.

(** Source for [total_vector_integral_scale]: scalar multiples
    of the actual convolution integral, used for
    difference quotients in Federer 4.1.2, p. 347. *)
Lemma total_vector_integral_scale (f:X->Y) y c:
  is_measure_vector_integral mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(c*:f x:real_norm_metric_space hN))) (c*:y).
Proof.
move=>hf.
apply:(measure_vector_integral_graph_equivalent _ (@measure_vector_integral_scale R X Y N hN mu hm c _ y hf))=>x v.
rewrite partial_vector_scale_graph; split.
- move=>[p [hp he]]; change (f x=p) in hp.
  change (c*:f x=v); by rewrite hp.
- move=>hv; exists (f x); by split.
Qed.
End TotalVectorIntegralArithmetic.
