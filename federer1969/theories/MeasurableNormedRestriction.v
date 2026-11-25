(** Federer (1969), 2.3.8, pp. 78–79, with the erratum p. 1, book p. 78 line
    7: restricting a measurable normed function to a conull source set
    preserves membership and gauge. This supports the finite-average formula
    on the original partial domain. Source context:
    PartialFunctionSourceRestriction.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedBasic MeasureGauge MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [conull_source_restriction_almost_equal]: supporting
    almost equality of a function and its conull restriction in
    Federer 2.3.8, pp. 78–79, using 2.3.1, p. 72. *)
Lemma conull_source_restriction_almost_equal (R : realType) (X : choiceType)
    (Y : Type) (mu : set X -> \bar R) (hm : is_measure mu)
    (A : set X) (f : partial_function X Y) :
  measure_almost_everywhere mu A -> measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_equal mu f (partial_function_source_restrict A f).
Proof.
move=> hA hf; rewrite /measure_almost_equal partial_function_source_restrict_agreement.
exact: measure_almost_everywhere_and hA hf.
Qed.

(** Source for [measurable_normed_conull_restriction]: supporting
    preservation of A(mu,Y) under conull restriction for Federer
    2.3.8, pp. 78–79. Both measurability and essential
    separability follow from the already proved almost-equality rule. *)
Lemma measurable_normed_conull_restriction (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (A : set X) (f : partial_function X (real_norm_metric_space hN)) :
  measure_almost_everywhere mu A -> is_measurable_normed_function mu f ->
  is_measurable_normed_function mu (partial_function_source_restrict A f) /\
  measure_gauge mu N (partial_function_source_restrict A f) = measure_gauge mu N f.
Proof.
move=> hA hf.
have he := @conull_source_restriction_almost_equal R X _ mu hm A f hA
  (measurable_function_domain hf.1).
split.
- exact (@measurable_normed_almost_equal R X V N hN mu hm f _ hf he).
- symmetry; exact: measure_gauge_almost_invariance he.
Qed.
