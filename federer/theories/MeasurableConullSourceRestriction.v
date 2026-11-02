(** Federer (1969), 3.1.4, p. 214: the difference quotient
    omits the zero scalar increment. Restriction to a conull source
    set preserves measurability, including the exact partial domain. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionSourceRestriction
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_conull_source_restriction]: supporting
    punctured-domain step for the coordinate quotient in Federer
    3.1.4, p. 214, from null-modification and measurability rules of
    2.3.2, p. 73. The target topology is arbitrary. *)
Lemma measurable_conull_source_restriction (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (A : set X) (f : partial_function X Y) :
  measure_almost_everywhere mu A -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_function_source_restrict A f).
Proof.
move=> hA hf; constructor.
- rewrite partial_function_source_restrict_domain.
  exact: (@measure_almost_everywhere_and R X mu hm A (partial_function_domain f) hA (measurable_function_domain hf)).
- move=> U hU.
  have hAm : measure_measurable mu A.
    have hh := measure_measurable_complement (measure_null_measurable hm hA).
    by rewrite setCK in hh.
  have he : partial_function_preimage (partial_function_source_restrict A f) U=
      A `&` partial_function_preimage f U.
    apply/seteqP; split=> x.
    + by move=> [y [[ha hy] hUy]]; split=> //; exists y.
    + by move=> [ha [y [hy hUy]]]; exists y; split=> //; split.
  rewrite he; exact: (@measure_measurable_intersection R X mu hm _ _ hAm (measurable_function_open_preimage hf hU)).
Qed.
