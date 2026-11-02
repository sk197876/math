(** The partition-sum comparison used by Federer (1969), 2.10.11, p. 176,
    after the image-cost estimate. Apply 2.10.8, p. 175, and bound the cost
    sum by a finite nonnegative multiple of a Borel regular measure. Include
    a zero multiple and infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumScale MeasureUP MeasureBasic MeasureDisjointSupport
  BorelRegularMeasureUP TopologicalBorel BorelPartition BorelCoverCostUP BorelCaratheodoryMeasure
  BorelPartitionCoverBounds BorelPartitionCharacterization ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_caratheodory_measure_bound]: supporting
    deduction of the integral bound from image costs in
    Federer 2.10.11, p. 176, using the all-partition
    supremum of 2.10.8. The supporting generalisation
    allows any Borel regular comparison measure and all
    targets by taking its Borel hull. Zero constants and
    infinite values obey the printed product convention. *)
Theorem borel_caratheodory_measure_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (D : set X) (a : R) :
  countable D -> dense D -> (0<=a)%R ->
  (forall B, borel_set B -> c B<=a%:E*mu B) ->
  forall A, borel_caratheodory_measure c A<=a%:E*mu A.
Proof.
move=> hD hden ha hcost A.
have hBorel B : borel_set B -> borel_caratheodory_measure c B<=a%:E*mu B.
  move=> hB.
  have hs := @borel_partition_cost_supremum_all R X c hc D B hD hden hB.
  apply: (extended_real_supremum_least hs)=> b [H [hH ->]].
  apply: le_trans (_ : nonnegative_sum H (fun C => a%:E*mu C)<=_).
  - apply: nonnegative_sum_mono=> C hC; exact: hcost C (borel_partition_members hH hC).
  - rewrite nonnegative_sum_scale //; last by move=> C _; exact: measure_nonnegative hm _.
    apply: lee_wpmul2l; first exact ha.
    apply: (@measure_disjoint_sum_bound R X [the choiceType of set X] mu hm B H (fun C => C)).
    + move=> C hC x hx; rewrite -(borel_partition_union hH); by exists C.
    + move=> C hC; exact: (@borel_regular_borel_measurable R X mu hm hr C (borel_partition_members hH hC)).
    + exact: borel_partition_disjoint hH.
have [B [hAB [hB he]]] := borel_regular_cover hr A.
rewrite he; apply: le_trans (@measure_mono R X (borel_caratheodory_measure c)
  (borel_caratheodory_is_measure hc) A B hAB) _.
exact: hBorel hB.
Qed.
