(** Federer (1969), 2.3.2, p. 73: basic consequences of the measurable
    partial-function definition, including the null-source boundary. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_whole_space_measurable_function]: supporting
    zero-total-measure boundary of Federer 2.3.2, p. 73.
    Every partial function is measurable when every subset of
    the source is null; the target may be empty. *)
Lemma null_whole_space_measurable_function (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) : mu setT = 0 -> is_measure_measurable_function mu f.
Proof.
move=> ht; have hn A : mu A = 0.
  apply: (@measure_null_subset R X mu hm A setT)=> //; by move=> x hx.
constructor; first exact: hn.
move=> U ho; exact: (@measure_null_measurable R X mu hm _ (hn _)).
Qed.

(** Source for [measurable_empty_function_iff]: supporting empty-
    domain boundary of the first definition in Federer 2.3.2,
    p. 73. This also records why a nonempty null source and
    empty target matter for the subsequent extension remark. *)
Lemma measurable_empty_function_iff (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_measurable_function mu (@partial_function_empty X Y) <-> mu setT = 0.
Proof.
split.
- move=> hf; have h := measurable_function_domain hf.
  by rewrite partial_function_empty_domain measure_almost_everywhere_false in h.
- exact: (@null_whole_space_measurable_function R X Y mu hm _).
Qed.
