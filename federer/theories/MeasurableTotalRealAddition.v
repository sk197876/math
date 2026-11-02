(** Federer (1969), 2.3.3, p. 76: measurable real partial sums and weights,
    using the numerical closure of 2.3.2, p. 74. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionPair PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasurableRealArithmetic MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [measurable_total_real_add]: supporting total-map
    form of real additive closure in Federer 2.3.2, p. 74,
    used in the greedy partial-sum induction of 2.3.3, p. 76. *)
Lemma measurable_total_real_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu (partial_function_total (fun x => (f x + g x : real_line_metric R))).
Proof.
move=> hf hg.
apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R] mu
  (partial_real_function_add (partial_function_total f) (partial_function_total g))).
- move=> x z; split.
  + by move=> [[a b] [[<- <-] he]].
  + by move=> he; exists (f x,g x); split; [split|].
- exact: (@measurable_real_function_add R X mu hm _ _ hf hg).
Qed.
