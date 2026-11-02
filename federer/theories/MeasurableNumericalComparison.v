(** Federer (1969), 2.3.3, p. 76: the comparison defining each greedy set is
    measurable. The proof uses the rational-ray tests of 2.3.2, p. 73, and
    local countable measurable-set closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  ExtendedRealOrderTopology CountableOrderIntervals MeasureUP MeasureFiniteClosure
  MeasureCountableClosure MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_extended_comparison]: supporting
    measurability of numerical comparisons used in Federer 2.3.3, p. 76 Both
    functions may take infinite values; rational density detects a strict
    reversal. *)
Lemma measurable_total_extended_comparison (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> extended_real_line R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_measurable mu [set x | f x <= g x].
Proof.
move=> hf hg.
pose A q := [set x | (ratr q : R)%:E < f x] `&` [set x | g x < (ratr q : R)%:E].
have he : [set x | f x <= g x] = ~` (\bigcup_(q in @setT rat) A q).
  apply/seteqP; split=> x.
  - move=> hx [q _ [hqf hgq]].
    have hbad := lt_le_trans (lt_trans hgq hqf) hx; by rewrite ltxx in hbad.
  - move=> hn; rewrite /= leNgt; apply/negP=> hgf.
    have [q [hgq hqf]] := @extended_rationals_order_dense R (g x) (f x) hgf.
    apply: hn; exists q=> //; by split.
rewrite he; apply: measure_measurable_complement.
apply: (@measure_measurable_countable_union R X [the choiceType of (rat : Type)] mu hm setT A (countableP _))=> q _.
apply: (@measure_measurable_intersection R X mu hm).
- have h := @measurable_function_open_preimage R X (extended_real_line R) mu _ hf
    [set y | (ratr q : R)%:E < y] (@order_strict_upper_ray_open _
      [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E).
  by rewrite partial_function_total_preimage in h.
- have h := @measurable_function_open_preimage R X (extended_real_line R) mu _ hg
    [set y | y < (ratr q : R)%:E] (@order_strict_lower_ray_open _
      [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E).
  by rewrite partial_function_total_preimage in h.
Qed.
