(** Federer (1969), 2.4.19, p. 91: F is continuous only on the closed set C
    containing almost every value of g. No ambient continuous extension of F
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  MeasurableAlmostModification BorelFunctionUP BorelFunctionBasic
  ClosedSubsetBorelRetractionUP ClosedSubsetBorelRetractionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_continuous_closed_range_composite]: supporting
    measurability of F composed with g in Federer 2.4.19, p. 91 Relative
    continuity and conull range suffice, with exact partial domains
    retained. The target may be any topological space. *)
Theorem measurable_continuous_closed_range_composite (R : realType) (X : choiceType)
    (Y : metricType R) (Z : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (C : set Y) (c : metric_subset C) (f : partial_function X Y) (F : Y -> Z) :
  closed C -> continuous (fun y : metric_subset C => F (val y)) ->
  is_measure_measurable_function mu f -> measure_almost_everywhere mu (partial_function_preimage f C) ->
  is_measure_measurable_function mu (partial_function_postcompose f F).
Proof.
move=> hC hF hf hCf.
pose r := @ClosedSubsetBorelRetraction.value R Y C c hC.
have hr := @ClosedSubsetBorelRetraction.laws R Y C c hC.
have hFb : is_borel_function (fun y => F (val (r y))).
  exact: (borel_function_composition hr.1 (continuous_borel_function hF)).
have hmF := @measurable_function_borel_postcomposition R X Y Z mu hm f _ hf hFb.
apply: (@measurable_function_almost_equal R X Z mu hm _ _ hmF).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hCf)=> x [y [hy hCy]].
exists (F y); split; exists y; split=> //.
by rewrite (hr.2 y hCy).
Qed.
