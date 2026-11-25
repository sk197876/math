(** Federer (1969), 3.1.4, p. 215: measurable scalar
    remainder inequalities on the prefix/scalar product. The arithmetic
    closure is 2.3.2, pp. 73–74, applied to actual total slice values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity RealMetricBackground
  ScalarApproximateTargetTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPair PartialFunctionPostcomposition MeasureUP MeasureFiniteClosure
  MeasurableFunctionUP MeasurableRealArithmetic MeasurableGraphEquivalence
  MeasurableTotalBasic MeasurableRealEmbedding MeasurableNumericalComparison
  BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ScalarArithmetic.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [measurable_total_real_subtract]: ordinary real
    subtraction in Federer 2.3.2, p. 74, supporting the remainder
    sections in 3.1.4, p. 215. *)
Lemma measurable_total_real_subtract (f g : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(f x-g x : real_line_metric R))).
Proof.
move=> hf hg.
apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R] mu
  (partial_real_function_subtract (partial_function_total f) (partial_function_total g))).
- move=> x z; split.
  + by move=> [[a b] [[<- <-] he]].
  + by move=> he; exists (f x,g x); split; [split|].
- exact: (@measurable_real_function_subtract R X mu hm _ _ hf hg).
Qed.

(** Source for [measurable_total_real_multiply]: ordinary real
    multiplication in Federer 2.3.2, p. 74, used for t g_i(x)
    in 3.1.4, p. 215. *)
Lemma measurable_total_real_multiply (f g : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(f x*g x : real_line_metric R))).
Proof.
move=> hf hg.
apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R] mu
  (partial_real_function_multiply (partial_function_total f) (partial_function_total g))).
- move=> x z; split.
  + by move=> [[a b] [[<- <-] he]].
  + by move=> he; exists (f x,g x); split; [split|].
- exact: (@measurable_real_function_multiply R X mu hm _ _ hf hg).
Qed.

(** Source for [measurable_total_real_absolute]: continuous
    absolute value, Federer 2.3.2(4), p. 73, in the scalar
    remainder estimate of 3.1.4, p. 215. *)
Lemma measurable_total_real_absolute (f : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(`|f x| : real_line_metric R))).
Proof.
move=> hf; apply: (measurable_total_borel_postcomposition hm hf).
apply: continuous_borel_function=> x.
apply: (@continuous_comp [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  [the topologicalType of real_line_metric R]
  (fun y : real_line_metric R=>(y : real_norm_metric_space (scalar_absolute_value_norm R)))
  (fun y : real_norm_metric_space (scalar_absolute_value_norm R)=>(`|y| : real_line_metric R)) x).
- exact: real_scalar_norm_identity_continuous.
- exact: real_norm_metric_norm_continuous.
Qed.

(** Source for [measurable_total_real_strict_comparison]: measurable
    comparison from Federer 2.3.2(2), p. 73, used in T in
    3.1.4, pp. 214–215. Both scalar functions are total. *)
Lemma measurable_total_real_strict_comparison (f g : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_measurable mu [set x | f x<g x].
Proof.
move=> hf hg.
have h := measurable_total_extended_comparison hm
  (measurable_total_real_embedding hm hg) (measurable_total_real_embedding hm hf).
have he : [set x | f x<g x]=~` [set x | ((g x)%:E<=(f x)%:E)%E].
  apply/seteqP; split=> x; rewrite /= lee_fin ltNge; by move/negP.
rewrite he; exact: measure_measurable_complement h.
Qed.

(** Source for [measurable_scalar_remainder_comparison]: the
    strict inequality defining the scalar sections T in Federer
    3.1.4, pp. 214–215. The generic functions represent the
    shifted value, base value, scalar parameter and derivative value. *)
Theorem measurable_scalar_remainder_comparison
    (F H T G : X -> real_line_metric R) (e : R) :
  is_measure_measurable_function mu (partial_function_total F) ->
  is_measure_measurable_function mu (partial_function_total H) ->
  is_measure_measurable_function mu (partial_function_total T) ->
  is_measure_measurable_function mu (partial_function_total G) ->
  measure_measurable mu [set x | e*`|T x|<`|F x-H x-T x*G x|].
Proof.
move=> hF hH hT hG.
apply: measurable_total_real_strict_comparison.
- apply: measurable_total_real_multiply.
  + exact: (@measurable_total_constant R X
      [the topologicalType of real_line_metric R] mu hm e).
  + exact: measurable_total_real_absolute hT.
- apply: measurable_total_real_absolute.
  apply: measurable_total_real_subtract.
  + exact: measurable_total_real_subtract hF hH.
  + exact: measurable_total_real_multiply hT hG.
Qed.
End ScalarArithmetic.
