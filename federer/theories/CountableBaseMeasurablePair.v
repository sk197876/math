(** Federer (1969), 2.3.2(5), p. 73: pairing
    measurable maps on their actual common domain. This
    countable-base form supports the original differential
    observables used in 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP PartialFunctionUP PartialFunctionPair
  MeasureUP MeasurableFunctionUP MeasurablePairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_measurable_pair]: the two
    factor case of 2.3.2(5), p. 73, for
    arbitrary supplied countable bases, supporting 3.2.46,
    p. 282. Empty spaces and proper conull domains
    require no designated point or total extension. *)
Lemma countable_base_measurable_pair (R : realType) (X : choiceType)
    (Y Z : topologicalType) (mu : set X -> \bar R)
    (f : partial_function X Y) (g : partial_function X Z)
    (U : nat -> set Y) (V : nat -> set Z) :
  is_measure mu -> is_countable_open_base U -> is_countable_open_base V ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_function_pair f g).
Proof.
move=> hMu hU hV hf hg.
exact (@measurable_partial_function_pair R X Y Z nat nat mu hMu f g U V
  (countable_base_open hU) (countable_base_refines hU)
  (countable_base_open hV) (countable_base_refines hV) hf hg).
Qed.
