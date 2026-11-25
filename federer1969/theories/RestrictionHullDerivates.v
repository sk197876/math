(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealConventions PartialFunctionUP MeasureUP MeasureHull MeasureDerivationContext
  CoveringRelationUP CoveringRelationLimits MeasureRestriction MeasureDerivates
  BorelRegularMeasureUP CoveringLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restriction_hull_derivate_graph]: direct identity replacing
    the arbitrary set by a measurable hull in Federer 2.9.11, p. 158 Every
    Vitali cell is measurable, so the defining hull test identifies its
    numerator exactly. Equality holds on all partial limit graphs, not only
    almost everywhere. No regularity of phi restricted to the original
    nonmeasurable A is assumed. *)
Lemma restriction_hull_derivate_graph (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) :
  is_measure_derivation_context phi V -> is_measure_hull phi A B ->
  forall x y, partial_function_graph (measure_derivate (measure_restrict phi A) phi V) x y <->
    partial_function_graph (measure_derivate (measure_restrict phi B) phi V) x y.
Proof.
move=> hc hB.
apply: (@covering_limit_graph_equivalent R X V
  (measure_ratio_function (measure_restrict phi A) phi)
  (measure_ratio_function (measure_restrict phi B) phi))=> x S hS y.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hSb := @vitali_relation_borel R X phi V (derivation_context_vitali hc) S
  (ex_intro _ x (conj Logic.I hS)).
have hSm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) S hSb.
have he := @measure_hull_test R X phi A B hB S hSm.
change (extended_divide (phi (A `&` S)) (phi S)=Some y <->
  extended_divide (phi (B `&` S)) (phi S)=Some y).
by rewrite (setIC A S) (setIC B S) he.
Qed.
