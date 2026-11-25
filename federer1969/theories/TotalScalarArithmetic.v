(** Federer (1969), 2.4.16, p. 90: supporting total-function arithmetic for
    the weighted sign tests, using 2.3.2, p. 74. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence ScalarSignTest ScalarNormedProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_total_scalar_sign]: supporting measurability
    of sign(f), Federer 2.4.16, pp. 89–90, for total functions. *)
Lemma measurable_total_scalar_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total
    (fun x => (Num.sg (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hf; have hh := @measurable_scalar_sign R X mu hm _ hf.
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hh)=> x z; split.
- by move=> [y [<- hy]].
- by move=> hz; exists (f x); split.
Qed.

(** Source for [measurable_total_scalar_product]: supporting
    measurability of weighted sign products, Federer 2.4.16, p. 90. *)
Lemma measurable_total_scalar_product (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu (partial_function_total
    (fun x => (f x * g x : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hf hg; have hh := @measurable_scalar_normed_product R X mu hm _ _ hf hg.
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hh)=> x z; split.
- by move=> [[a b] [[<- <-] hab]].
- by move=> hz; exists (f x,g x); split=> //; split.
Qed.
