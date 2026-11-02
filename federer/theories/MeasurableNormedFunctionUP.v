(** Federer (1969), 2.3.8, p. 78: the set A(mu,Y) of measurable functions
    essentially valued in a separable linear subspace. Erratum p. 1, book p.
    78 line 7, replaces 'consider the vectorspace' by 'consider the set'. We
    retain partial functions. Completeness is not needed to define the set;
    it is a separate hypothesis for 2.3.9–2.3.10. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient
  MetricSubsetBackground PartialFunctionUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_essentially_separable_normed_function]: direct
    separable-linear-subspace condition in Federer 2.3.8, p. 78,
    opening paragraph. Separability is in the induced metric and
    the exceptional preimage has measure zero. *)
Definition is_essentially_separable_normed_function (R : realType)
    (X : choiceType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) :=
  exists Z : subspace V,
    (exists D : set (metric_subset (fun y : real_norm_metric_space hN => Z y)),
      countable D /\ dense D) /\
    mu (partial_function_preimage f [set y | ~ Z y]) = 0.

(** Source for [is_measurable_normed_function]: the defining set
    A(mu,Y) of Federer 2.3.8, p. 78, with the erratum's set
    correction. We do not assert vector-space laws for partial maps. *)
Definition is_measurable_normed_function (R : realType)
    (X : choiceType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) :=
  is_measure_measurable_function mu f /\
  is_essentially_separable_normed_function mu f.
