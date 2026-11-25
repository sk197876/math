(** Federer (1969), 2.9.12, pp. 158–159: densities and approximate limits of
    functions on partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP
  MeasureRestriction MeasureDerivates MeasureDerivationContext MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality CharacteristicFunctionUP SummableRealFunctionUP
  CharacteristicDifferentiation DensityHullAgreement DensityMeasurableSets
  MeasureHullNullTransfer MeasureDensityPoints MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_set_density]: direct definition in Federer 2.9.12,
    p. 158, first display The density is the partial covering limit of the
    restricted measure divided by phi. *)
Definition measure_set_density (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :=
  measure_derivate (measure_restrict phi A) phi V.

(** Source for [measure_set_density_measurable]: supporting measurability
    for Federer 2.9.12, p. 158, from 2.9.11 *)
Theorem measure_set_density_measurable (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context phi V ->
  @is_measure_measurable_function R X (extended_real_line R) phi
    (measure_set_density phi V A).
Proof. exact: measurable_set_restriction_derivate. Qed.

(** Source for [density_characteristic_measurability]: direct equivalence in
    Federer 2.9.12, p. 158, first paragraph The supplied real-valued
    characteristic function is embedded in the extended real line. Almost
    equality requires actual values on both graphs. *)
Theorem density_characteristic_measurability (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) (s : X -> R) :
  is_measure_derivation_context phi V -> is_characteristic_function A s ->
  (measure_measurable phi A <->
    measure_almost_equal phi (measure_set_density phi V A) (real_total_integrand s)).
Proof.
move=> hc hs; split.
- move=> hA; exact: (@characteristic_derivate_agreement R X phi V A s hc hA hs).
move=> heq; have hm := derivation_measure_law (derivation_context_measure hc).
have hPA : measure_almost_everywhere phi
    [set x | measure_density_one_points phi V A x <-> A x].
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ heq)=> x [y [hy hsy]].
  have he := (real_total_integrand_graph s x y).1 hsy.
  rewrite -he in hy.
  exact: (@characteristic_agreement_graph_levels R X A s _ x hs hy).1.
have hnull := @measure_agreeing_sets_difference_null R X phi
  (measure_density_one_points phi V A) A hm hPA.
exact: (density_one_points_conclusions A hc).2.2.2.2 hnull.
Qed.
