(** Federer (1969), 2.5.7, p. 98: countably measurable supports in the
    total-domain Lp lattice, retaining Definition 2.4.12, p. 86, and 2.3.4,
    p. 76. The lemmas below supply the finite-operation cases. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableSubsets CountablyMeasurableUnions
  TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_scalar_nonzero_locus_measurable]: supporting
    measurable support fact for Federer 2.5.7, p. 98, from 2.3.2(1), p. 73,
    and 2.3.4, p. 76 *)
Lemma total_scalar_nonzero_locus_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_measure_measurable_function mu (total_scalar_function f) ->
  measure_measurable mu (partial_function_nonzero_locus 0 (total_scalar_function f)).
Proof.
move=> hf; apply: (@measurable_function_nonzero_locus R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0 _ _ hf).
change (closed [set (0 : real_norm_metric_space (scalar_absolute_value_norm R))]).
apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [total_scalar_countable_support_subset]: a measurable
    function vanishing wherever f vanishes remains countably measurable,
    supporting Federer 2.5.7, p. 98 *)
Lemma total_scalar_countable_support_subset (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  (forall x, f x=0 -> g x=0) ->
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function g).
Proof.
move=> hf hg hz; constructor=> //.
apply: (@measurable_subset_countably_measurable R X mu hm _
  (partial_function_nonzero_locus 0 (total_scalar_function f))
  (@total_scalar_nonzero_locus_measurable R X mu hm g hg) _ (countably_measurable_function_locus hf)).
move=> x [v [hv hv0]]; exists (f x); split=> // hf0.
apply: hv0; have he : g x=v := hv; rewrite -he; exact: hz x hf0.
Qed.

(** Source for [total_scalar_countable_support_union]: a measurable function
    whose nonzero locus lies in the union of two countably measurable
    supports is countably measurable, supporting the lattice operations in
    Federer 2.5.7, p. 98 *)
Lemma total_scalar_countable_support_union (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g h : X -> R) :
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function f) ->
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function g) ->
  is_measure_measurable_function mu (total_scalar_function h) ->
  (forall x, f x=0 -> g x=0 -> h x=0) ->
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function h).
Proof.
move=> hf hg hh hz; constructor=> //.
have hu := @countably_measurable_binary_union R X mu _ _
  (countably_measurable_function_locus hf) (countably_measurable_function_locus hg).
apply: (@measurable_subset_countably_measurable R X mu hm _ _
  (@total_scalar_nonzero_locus_measurable R X mu hm h hh) _ hu).
move=> x [v [hv hv0]].
case: (eqVneq (f x) 0)=> [hf0|hf0]; last by left; exists (f x); split=> //; exact/eqP.
case: (eqVneq (g x) 0)=> [hg0|hg0]; last by right; exists (g x); split=> //; exact/eqP.
exfalso; apply: hv0; have he : h x=v := hv; rewrite -he; exact: hz x hf0 hg0.
Qed.
