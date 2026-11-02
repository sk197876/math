(** Product background for the successive parameter integrals of Federer
    (1969), 2.10.16, p. 178. Combine countable bases, Borel regularity, and
    countable finite measurable exhaustions using the proved product laws.
    Federer 2.6.2(4), p. 115, and 2.6.5, p. 120 *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP ProductCountableBaseSealed MeasureUP BorelRegularMeasureUP
  CountablyMeasurableUP CountablyMeasurableProduct ProductMeasure ProductBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_borel_product_background]: supporting
    regularity, countable base and finite measurable exhaustion
    for each parameter product in 2.10.16, p. 178.
    The factor hypotheses are all discharged in the Euclidean
    and compact Haar applications. *)
Lemma countable_borel_product_background (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  (exists U : nat -> set X, is_countable_open_base U) -> (exists V : nat -> set Y, is_countable_open_base V) ->
  is_borel_regular_measure alpha -> is_borel_regular_measure beta ->
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  (exists W : nat -> set (X*Y), is_countable_open_base W) /\
    is_borel_regular_measure (product_measure ha hb) /\
    measure_countably_measurable (product_measure ha hb) setT.
Proof.
move=> [U hU] [V hV] hrX hrY hwX hwY.
split; first by exists (@ProductCountableBase.value X Y U V hU hV); exact: ProductCountableBase.laws.
split; first exact (@product_measure_borel_regular R X Y alpha beta ha hb U V hU hV hrX hrY).
exact (@product_whole_countably_measurable R X Y alpha beta ha hb hwX hwY).
Qed.
