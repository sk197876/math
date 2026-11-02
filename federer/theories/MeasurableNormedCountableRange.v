(** Federer (1969), 2.3.8, p. 78: supporting countable-range case of
    essential separability. A closed separable linear span contains the
    range. Source context: MeasurableNormedFunctionUP.v. This supplies
    concrete finite- source examples without imposing finite-dimensionality. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  ClosedLinearSpanUP ClosedLinearSpanSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_countable_total_range]: supporting
    sufficient condition for membership in A(mu,Y), Federer
    2.3.8, p. 78, used for the nonhomogeneity and
    nonconvexity examples on pp. 78–79. *)
Lemma measurable_normed_countable_total_range (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space hN) :
  is_measure_measurable_function mu (partial_function_total f) ->
  countable (f @` setT) -> is_measurable_normed_function mu (partial_function_total f).
Proof.
move=> hf hc; split=> //.
pose Z := @ClosedLinearSpan.value R V N hN (f @` setT).
have hZ := @ClosedLinearSpan.laws R V N hN (f @` setT).
exists Z; split; first exact: ClosedLinearSpan.countable_separable hc.
rewrite partial_function_total_preimage.
have he : f @^-1` [set y | ~ Z y] = set0.
  apply/seteqP; split; last by move=> x [].
  move=> x hn; apply: hn; apply: (closed_linear_span_contains hZ); by exists x.
rewrite he; exact: measure_empty.
Qed.
