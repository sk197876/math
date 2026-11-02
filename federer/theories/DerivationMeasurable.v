(** Federer (1969), 2.9.6, p. 155: the partial V derivate is phi measurable.
    The proof follows the book's common Borel hull and level-separation
    route, using the conull domain proved in 2.9.5. The local erratum's p.
    155 line 26 entry concerns the exceptional set in 2.9.7, not this
    measurability lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates PartialFunctionUP
  ExtendedRealOrderTopology MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  DerivationExistence DerivationLevelSeparation MeasurableLevelCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_derivate_domain_conull]: supporting
    domain hypothesis for the application of 2.3.2(7)
    in Federer 2.9.6, p. 155. It follows
    from the graph existence established in 2.9.5,
    pp. 154–155, rather than being assumed. *)
Lemma measure_derivate_domain_conull (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_almost_everywhere phi (partial_function_domain (measure_derivate psi phi V)).
Proof.
move=> hc hp.
apply: (@measure_almost_everywhere_mono R X phi (derivation_measure_law (derivation_context_measure hc))
  [set x | exists y, partial_function_graph (measure_derivate psi phi V) x y /\ 0<=y /\ y< +oo]).
- move=> x [y [hy _]]; by exists y.
- exact (@federer_2_9_5 R X phi psi V hc hp).
Qed.

(** Source for [federer_2_9_6]: direct complete lemma
    Federer 2.9.6, p. 155: D(psi,phi,V,.)
    is a phi measurable function. The original class
    M and standing Vitali relation are retained; the
    function has its actual partial domain, proved conull. *)
Theorem federer_2_9_6 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  @is_measure_measurable_function R X (extended_real_line R) phi (measure_derivate psi phi V).
Proof.
move=> hc hp.
have hm := derivation_measure_law (derivation_context_measure hc).
have hd := @measure_derivate_domain_conull R X phi psi V hc hp.
apply: (@measurable_extended_level_separation_iff R X phi hm (measure_derivate psi phi V) hd).2.
exact (@measure_derivate_level_separated R X phi psi V hc hp).
Qed.
