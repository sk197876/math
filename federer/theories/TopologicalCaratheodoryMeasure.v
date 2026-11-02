(** Federer (1969), 2.10.1, p. 170: prove the measure assertion for the
    corrected arbitrary-topological version. Its abstract supremum over
    whole-space open covers obeys the countable covering inequality because
    every fixed-cover envelope does. The literal A-cover version is not
    used: its failure is proved in OpenRefinementNonmonotonicity.v. Source
    context and corrected references: TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP OpenRefiningEnvelopeUP OpenRefiningCoverCost
  TopologicalCaratheodoryUP TopologicalCaratheodoryLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [topological_caratheodory_is_measure]: corrected
    arbitrary-topological measure assertion supporting Federer
    2.10.1, p. 170. Use whole-space open covers. Arbitrary
    nonnegative gauge values, empty spaces, infinite final
    values and nonmeasurable target sets are retained. *)
Theorem topological_caratheodory_is_measure (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_topological_caratheodory S cost mu -> (forall j, 0<=cost j) -> is_measure mu.
Proof.
move=> hm hc; constructor; first exact: topological_caratheodory_nonnegative hm.
move=> A F hF hcov; apply: (topological_caratheodory_least hm)=> H nu hH hn.
have hnu := open_refining_envelope_is_measure hn hc.
apply: le_trans (@measure_countable_cover R X nu hnu A F hF hcov) _.
apply: nonnegative_sum_mono=> B _.
exact (@topological_caratheodory_upper R X J S cost mu hm B H nu hH hn).
Qed.
