(** Federer (1969), 2.10.1, p. 170: Borel generators give Borel supersets
    with equal approximating measure. We reuse the already proved attainment
    of the Borel-superset infimum, which encapsulates that intersection
    argument. No Borel measurability of the preliminary measure is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP TopologicalBorel CountableCoverEnvelopeUP
  CountableCoverEnvelopeLaws BorelRegularisationUP BorelRegularisationBasic
  BorelRegularisationAttainment BorelRegularisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_cover_envelope_borel_hull]: the fixed-family
    Borel-cover assertion used in Federer 2.10.1, p. 170 The preliminary
    measure need not make open sets measurable, a distinction retained from
    the book. *)
Theorem countable_cover_envelope_borel_hull (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (nu : set X -> \bar R) :
  is_countable_cover_envelope S cost nu ->
  (forall j, 0<=cost j) -> (forall j, borel_set (S j)) ->
  forall A, exists B, A `<=` B /\ borel_set B /\ nu A=nu B.
Proof.
move=> hn hc hS A.
have hm := countable_cover_envelope_is_measure hn hc.
pose rho := borel_regularisation nu.
have hr := borel_regularisation_laws nu.
have he : rho A=nu A.
  apply/eqP; rewrite eq_le; apply/andP; split; last first.
    exact (@borel_regularisation_dominates R X nu rho hm hr A).
  apply: (countable_cover_envelope_greatest hn)=> G hG hcov.
  have hB : borel_set (\bigcup_(j in G) S j).
    apply: (borel_set_countable_union hG)=> j _; exact: hS.
  apply: le_trans (@borel_regularisation_lower R X nu rho hr A _ hcov hB) _.
  exact (@countable_cover_envelope_lower R X J S cost nu hn _ G hG (fun x hx => hx)).
have [B [hAB [hB heB]]] := @borel_regularisation_attained R X nu rho hm hr A.
exists B; split=> //; split=> //.
by rewrite -he.
Qed.
