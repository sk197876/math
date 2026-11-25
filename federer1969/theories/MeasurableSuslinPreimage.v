(** Federer (1969), 2.3.2(3), p. 73: Suslin inverse images are measurable.
    We follow the printed deduction from 2.1.2, p. 54, restricted image
    measures, and 2.2.12, pp. 68–69, Suslin measurability. The target
    remains an arbitrary topological space. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureSplit MeasureRestriction MeasurePushforward MeasureAlmostUP
  MeasureAlmostEquality MeasurableFunctionUP MeasurableFunctionBorel
  MeasurableAlmostModification MeasurableTotalExtension TopologicalBorel
  SuslinSetUP SuslinMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_total_function_suslin_preimage]: total
    function case of Federer 2.3.2(3), p. 73, by exactly
    the restricted image measure argument cited there. *)
Theorem measurable_total_function_suslin_preimage (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (h : X -> Y) (S : set Y) :
  is_measure_measurable_function mu (partial_function_total h) ->
  is_suslin_set R S -> measure_measurable mu (h @^-1` S).
Proof.
move=> hf hS; apply: (proj2 (@measure_pushforward_restrictions_iff R X Y h mu S))=> A.
apply: (@suslin_set_measurable R Y (measure_pushforward h (measure_restrict mu A))
  (@measure_pushforward_is_measure R X Y h _ (measure_restrict_is_measure hm A)) S _ hS).
move=> C hC.
have hc := @measurable_function_borel_preimage R X Y mu hm _ hf C (closed_borel_set hC).
rewrite partial_function_total_preimage in hc.
exact: (proj1 (@measure_pushforward_restrictions_iff R X Y h mu C) hc A).
Qed.

(** Source for [measurable_function_suslin_preimage]: direct
    Federer 2.3.2(3), p. 73, including partial domains.
    If the target is empty all inverse images are empty; otherwise
    a total extension reduces to the printed restricted-image proof. *)
Theorem measurable_function_suslin_preimage (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (S : set Y) :
  is_measure_measurable_function mu f -> is_suslin_set R S ->
  measure_measurable mu (partial_function_preimage f S).
Proof.
move=> hf hS; case: (pselect (exists y : Y, True))=> [[y0 _]|hn].
- have [h [_ [he hh]]] := @measurable_function_total_extension R X Y mu hm f y0 hf.
  apply: (@almost_equal_preimage_measurable R X Y mu hm (partial_function_total h) f S
    (@measure_almost_equal_sym R X Y mu _ _ he)).
  rewrite partial_function_total_preimage.
  exact: (@measurable_total_function_suslin_preimage R X Y mu hm h S hh hS).
- have he : partial_function_preimage f S = set0.
    apply/seteqP; split=> x; last by move=> [].
    move=> [y _]; exfalso; apply: hn; by exists y.
  rewrite he; exact: measure_measurable_empty hm.
Qed.
