(** Federer (1969), 2.4.17, p. 90, with the conull partial-domain convention
    of 2.3.2, p. 73. These supporting transfer laws permit total
    representatives without changing norms or admissible exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableTotalExtension InnerConvex MeasureExponentDomain MeasureExponentAlmostEquality MeasureReciprocalInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_partial_positive_reciprocal_interval]: the U
    interval assertion of Federer 2.4.17, p. 90, for conull partial domains
    The total-extension reduction uses 2.3.2, p. 73. *)
Lemma measure_partial_positive_reciprocal_interval (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> forall u v w : R,
  measure_positive_reciprocal_exponents mu f u ->
  measure_positive_reciprocal_exponents mu f v ->
  (u <= w)%R -> (w <= v)%R -> measure_positive_reciprocal_exponents mu f w.
Proof.
move=> hf; have [g [he [ha hg]]] := @measurable_function_total_extension R X
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm f 0%R hf.
rewrite (@reciprocal_norm_exponents_almost_equal R X mu hm f _ hf hg ha).
exact: (@measure_positive_reciprocal_interval R X mu hm g hg).
Qed.

(** Source for [measure_partial_positive_reciprocal_convex]: convex-set form
    of U being an interval in Federer 2.4.17, p. 90 Undefined points on a
    null set are allowed. *)
Lemma measure_partial_positive_reciprocal_convex (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  @is_inner_convex R R^o (measure_positive_reciprocal_exponents mu f).
Proof.
move=> hf; have [g [he [ha hg]]] := @measurable_function_total_extension R X
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm f 0%R hf.
rewrite (@reciprocal_norm_exponents_almost_equal R X mu hm f _ hf hg ha).
exact: (@measure_positive_reciprocal_convex R X mu hm g hg).
Qed.
