(** Federer (1969), 2.10.8, p. 175, proof: the sum of costs on disjoint
    Borel pieces is at most the resulting measure of their containing set.
    We give an indexed form and allow empty pieces. Source context and the
    role in 2.5.10: BorelCoverCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureDisjointSupport
  BorelRegularMeasureUP BorelCoverCostUP BorelCaratheodoryMeasure TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_cost_disjoint_sum_bound]: the
    second display in the proof of Federer 2.10.8,
    p. 175, with the disjoint pieces only required
    to lie in A. Countability is unnecessary for this
    direction, since the sum is determined by finite subsums. *)
Lemma borel_cost_disjoint_sum_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (J : choiceType) (D : set J) (S : J -> set X) (A : set X) :
  (forall j, D j -> borel_set (S j)) ->
  (forall j, D j -> S j `<=` A) ->
  (forall i j, D i -> D j -> i<>j -> S i `&` S j=set0) ->
  nonnegative_sum D (fun j => c (S j))<=borel_caratheodory_measure c A.
Proof.
move=> hS hA hd.
apply: le_trans (_ : nonnegative_sum D (fun j => borel_caratheodory_measure c (S j))<=_).
- apply: nonnegative_sum_mono=> j hj; exact (@borel_caratheodory_cost_bound R X c hc (S j) (hS j hj)).
- apply: (@measure_disjoint_sum_bound R X J (borel_caratheodory_measure c)
    (borel_caratheodory_is_measure hc) A D S hA _ hd)=> j hj.
  exact (@borel_regular_borel_measurable R X (borel_caratheodory_measure c)
    (borel_caratheodory_is_measure hc) (borel_caratheodory_borel_regular hc) (S j) (hS j hj)).
Qed.
