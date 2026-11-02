(** Federer (1969), 2.5.5, p. 97: the lattice functions and their prescribed
    scalar limits belong to the measurable normed-function collection needed
    for 2.3.10. These adapters retain finite total values and use the
    already proved Borel finite projection. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground ExtendedRealOrderTopology
  ExtendedFiniteProjectionBorel PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  MeasureUP MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableRealNormed
  MeasurablePostcomposition MeasurableGraphEquivalence MeasurableTotalBasic BorelFunctionBasic SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_integrand_measurable_scalar_norm]: conversion from the
    extended-real integral convention to scalar norm-metric measurability in
    the proof of Federer 2.5.5, p. 97 Finite projection changes no function
    value and no domain in this total real case. *)
Lemma real_integrand_measurable_scalar_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_measure_measurable_function mu (real_total_integrand f) ->
  is_measure_measurable_function mu
    (partial_function_total (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))).
Proof.
move=> hf.
have hp := @measurable_function_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm (real_total_integrand f)
  (fun y => (fine y : real_line_metric R)) hf (@extended_finite_projection_borel R).
have hr : is_measure_measurable_function mu (partial_function_total (f : X -> real_line_metric R)).
  apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R] mu _ _ _ hp)=> x z; split.
  - move=> [y [hy hyz]]; have he := (real_total_integrand_graph f x y).1 hy.
    by rewrite -hyz -he.
  - move=> hz; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
    exact: hz.
have hid : continuous (fun x : real_line_metric R => (x : real_norm_metric_space (scalar_absolute_value_norm R))).
  apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=> x y.
  change (`|x-y| <= 1 * `|x-y|); by rewrite mul1r.
exact: (@measurable_total_borel_postcomposition R X [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm f
  (fun y => y) hr (continuous_borel_function hid)).
Qed.

(** Source for [summable_real_function_in_normed_collection]: scalar A
    membership used before the two subsequence extractions in Federer 2.5.5,
    p. 97 No bound on the ambient measure is imposed. *)
Lemma summable_real_function_in_normed_collection (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  summable_real_functions mu f -> is_measurable_normed_function mu
    (partial_function_total (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))).
Proof.
move=> [a ha]; apply: (@measurable_real_function_in_normed_space R X mu hm).
exact: (@real_integrand_measurable_scalar_norm R X mu hm f ha.1).
Qed.
