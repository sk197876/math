(** Federer (1969), 2.3.3, p. 76: public prescribed- weight characteristic
    expansion. The only erratum entry is typographical: erratum p. 1, book
    p. 76 line 3, italic “and”. The construction remains sealed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic ExtendedRealOrderTopology MeasureUP MeasurableFunctionUP
  WeightedCharacteristicExpansionUP GreedyCharacteristicSystemUP GreedyCharacteristicSystemSealed
  GreedySystemRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_weighted_characteristic_expansion]: direct
    theorem Federer 2.3.3, p. 76, with the stated greedy choice retained in
    the conclusion. The measured source and its measure need not be finite
    or nonempty. *)
Theorem measurable_weighted_characteristic_expansion (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> extended_real_line R) (r : nat -> R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall x, 0 <= f x) -> is_positive_vanishing_divergent_sequence r ->
  exists A g, is_weighted_characteristic_expansion mu f r A g /\
    is_greedy_characteristic_expansion f r A g.
Proof.
move=> hf hpos hw.
pose p := @GreedyCharacteristicSystem.value R X f r.
have hp := @GreedyCharacteristicSystem.laws R X f r.
exists p.1, p.2; split.
- exact: (@greedy_system_weighted_representation R X mu hm f r p.1 p.2 hf hpos hw hp).
- exact: greedy_system_threshold hp.
Qed.
