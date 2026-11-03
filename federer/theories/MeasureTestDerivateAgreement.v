(** Federer (1969), 3.2.41, printed p. 278, final proof paragraph:
    density hulls may be substituted through equal measurable-test
    masses. This supporting graph substitution expands the appeal to
    2.9.11, p. 158, without assuming either set contains the other. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealConventions PartialFunctionUP MeasureUP
  MeasureDerivationContext CoveringRelationUP CoveringRelationLimits
  MeasureRestriction MeasureDerivates BorelRegularMeasureUP CoveringLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_test_derivate_agreement]: supporting exact
    density substitution for Federer 3.2.41, p. 278. Equality of all
    measurable-test intersection masses gives equality of the whole
    partial derivate graph at every point and value, including its
    defined domain. Neither set is assumed measurable or containing. *)
Lemma measure_test_derivate_agreement (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) :
  is_measure_derivation_context mu V ->
  (forall T, measure_measurable mu T -> mu (T `&` A)=mu (T `&` B)) ->
  forall x y,
    partial_function_graph (measure_derivate (measure_restrict mu A) mu V) x y <->
    partial_function_graph (measure_derivate (measure_restrict mu B) mu V) x y.
Proof.
move=> hc ht.
apply: (@covering_limit_graph_equivalent R X V
  (measure_ratio_function (measure_restrict mu A) mu)
  (measure_ratio_function (measure_restrict mu B) mu))=> x S hS y.
have hmu := derivation_context_measure hc.
have hm := derivation_measure_law hmu.
have hSb := @vitali_relation_borel R X mu V (derivation_context_vitali hc) S
  (ex_intro _ x (conj Logic.I hS)).
have hSm := @borel_regular_borel_measurable R X mu hm (derivation_measure_borel_regular hmu) S hSb.
change (extended_divide (mu (A `&` S)) (mu S)=Some y <->
  extended_divide (mu (B `&` S)) (mu S)=Some y).
by rewrite (setIC A S) (setIC B S) (ht S hSm).
Qed.
