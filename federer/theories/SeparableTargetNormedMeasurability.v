(** Federer (1969), 2.9.22, p. 167: in the separable case the measurable
    field v belongs to A(Lebesgue,Y), allowing vector integration. This
    supporting adapter uses the definition of A in 2.3.8, p. 78. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureBasic
  MeasurableFunctionUP MeasurableNormedFunctionUP ClosedLinearSpanUP ClosedLinearSpanSealed
  NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [separable_target_measurable_normed]: supporting
    A(Lebesgue,Y) membership before the integral display in Federer
    2.9.22, p. 167. Every measurable partial map into a
    separable normed space is essentially separable: the closed
    span of a countable dense set is the entire target.
    Completeness and reflexivity are unnecessary for this adapter. *)
Lemma separable_target_measurable_normed (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (f : partial_function X (real_norm_metric_space hN)) :
  countable C -> dense C -> is_measure_measurable_function mu f ->
  is_measurable_normed_function mu f.
Proof.
move=> hCc hCd hf; split=> //.
pose Z := ClosedLinearSpan.value C.
have hZ := ClosedLinearSpan.laws C.
have hwhole : forall y : real_norm_metric_space hN, Z y.
  exact: dense_closed_superset_all hCd
    (closed_linear_span_closed hZ) (closed_linear_span_contains hZ).
exists Z; split; first exact: ClosedLinearSpan.countable_separable hCc.
have he : partial_function_preimage f [set y | ~ Z y]=set0.
  apply/seteqP; split=> x; last by [].
  by move=> [y [_ hn]]; exact: hn (hwhole y).
rewrite he; exact: measure_empty hm.
Qed.
