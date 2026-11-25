(** Federer (1969), 2.4.12, p. 87: finite-image approximants must belong to
    A, whose essential-separability definition is in 2.3.8, p. 78. This
    extends the existing total countable-range argument to exact partial
    domains, without choosing values outside the domain. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient PartialFunctionUP MeasureStepFunctionUP
  MeasureUP MeasureBasic MeasurableFunctionUP MeasurableNormedFunctionUP ClosedLinearSpanUP ClosedLinearSpanSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_countable_partial_range]: supporting
    A membership for finite-image approximants in Federer 2.4.12,
    p. 87. A closed separable linear span contains any countable
    partial range, so the exceptional preimage is empty. *)
Lemma measurable_normed_countable_partial_range (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f -> countable (partial_function_range f) ->
  is_measurable_normed_function mu f.
Proof.
move=> hf hc; split=> //.
pose Z := @ClosedLinearSpan.value R V N hN (partial_function_range f).
have hZ := @ClosedLinearSpan.laws R V N hN (partial_function_range f).
exists Z; split; first exact: ClosedLinearSpan.countable_separable hc.
have he : partial_function_preimage f [set y | ~ Z y] = set0.
  apply/seteqP; split; last by move=> x [].
  move=> x [y [hy hn]]; apply: hn; apply: (closed_linear_span_contains hZ).
  by exists x.
rewrite he; exact: measure_empty.
Qed.
