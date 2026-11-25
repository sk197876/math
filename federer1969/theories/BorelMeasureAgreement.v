(** Supporting measure identification in Federer (1969), 2.9.21, p. 166,
    when combining 2.9.7 with the change-of-density formula of 2.4.10.
    Equality of Borel regular measures on Borel sets implies equality on
    every subset by the hull law of 2.2.3, p. 61. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_measures_agree]: supporting uniqueness from
    the Borel-hull specification in Federer 2.2.3, p. 61, used for 2.9.21,
    p. 166 Use a hull for the opposite measure in each inequality; agreement
    only on Borel sets suffices for all subsets. *)
Lemma borel_regular_measures_agree (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) : is_measure mu -> is_measure nu ->
  is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  (forall B, borel_set B -> mu B=nu B) -> mu=nu.
Proof.
move=> hm hn hr hs he; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- have [B [hAB [hB hvalue]]] := borel_regular_cover hs A.
  rewrite hvalue -(he B hB); exact (@measure_mono R X mu hm A B hAB).
- have [B [hAB [hB hvalue]]] := borel_regular_cover hr A.
  rewrite hvalue (he B hB); exact (@measure_mono R X nu hn A B hAB).
Qed.
