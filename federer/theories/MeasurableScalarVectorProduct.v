(** Federer (1969), 4.1.2, p. 347: the
    product of a measurable scalar kernel and a
    measurable field in the original separable Banach
    target is measurable. This uses 2.3.2(4)–(5). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricJointScale VectorDaniellHypotheses
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasurablePairs MeasurableGraphEquivalence MeasurablePostcomposition BorelFunctionBasic CountableOpenBaseUP SeparableMetricBaseSealed
  CountableOrderIntervals OrderFamilyIntervalOpen MeasurableRealPairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [measurable_scalar_vector_product]: the
    actual Banach-valued kernel integrand is measurable,
    supporting Federer 4.1.2, p. 347.
    No finite target basis is required. *)
Theorem measurable_scalar_vector_product (R:realType) (X:choiceType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (mu:set X->\bar R) (hm:is_measure mu)
    (a:X->R) (f:X->Y):is_separable_normed_space hNY ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(a x:real_line_metric R))) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(a x*:f x:real_norm_metric_space hNY))).
Proof.
move=>[C [hCc hCd]] ha hf.
pose d:=fun q:rat=>(ratr q:R).
pose U:=@order_family_interval _ [the orderType _ of (R:Type)] rat d.
pose V:=@SeparableMetricBase.value R (real_norm_metric_space hNY) C hCc hCd.
pose hV:=@SeparableMetricBase.laws R (real_norm_metric_space hNY) C hCc hCd.
have hPair:=@measurable_partial_function_pair R X (real_line_metric R) (real_norm_metric_space hNY)
  [the countType of ((option rat*option rat)%type:Type)] nat mu hm
  (partial_function_total (fun x=>(a x:real_line_metric R)))
  (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) U V
  (fun c=>@order_family_interval_open _ [the orderTopologicalType _ of R^o] rat d c)
  (@order_family_intervals_refine _ [the orderTopologicalType _ of R^o] rat d (@real_rationals_order_dense R))
  (countable_base_open hV) (countable_base_refines hV) ha hf.
have hProduct:=@measurable_function_borel_postcomposition R X
  [the topologicalType of (real_line_metric R*real_norm_metric_space hNY)%type] (real_norm_metric_space hNY) mu hm _
  (fun p=>(p.1*:p.2:real_norm_metric_space hNY)) hPair
  (continuous_borel_function (@real_norm_metric_joint_scale_continuous R Y NY hNY)).
apply:(@measurable_function_graph_equivalent R X (real_norm_metric_space hNY) mu _ _ _ hProduct).
move=>x y; split.
- move=>[[u v] [[hu hv] hValue]].
  change (a x=u) in hu; change (f x=v) in hv.
  by rewrite -hu -hv in hValue.
- move=>hValue; exists (a x,f x); split; first by split.
  exact hValue.
Qed.
