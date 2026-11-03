(** Federer (1969), 3.2.41, printed p. 278, final proof paragraph:
    S* is formed from density-one points, using 2.9.11, p. 158.
    The original S can be nonmeasurable. The identities below are
    measurable-test equalities; they do not assert that S* minus S
    is null, an assertion unavailable for arbitrary S. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureHull MeasureDensityPoints
  MeasureDerivationContext DerivationBorelHulls DensityHullAgreement
  MeasureHullNullTransfer DensityMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_one_points_measure_test]: supporting use of
    the hull in Federer 3.2.41, p. 278, from 2.9.11, p. 158.
    Every measurable test has equal intersection outer measures
    against S and S*, including when the values are infinite. *)
Lemma density_one_points_measure_test (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop) (A T : set X) :
  is_measure_derivation_context mu V -> measure_measurable mu T ->
  mu (T `&` A)=mu (T `&` measure_density_one_points mu V A).
Proof.
move=> hc hT.
have hm := derivation_measure_law (derivation_context_measure hc).
have [B [_ hB]] := @derivation_measure_borel_hull R X mu A (derivation_context_measure hc).
rewrite (@measure_hull_test R X mu A B hB T hT).
symmetry; exact: measure_agreeing_sets_intersection_value hm
  (density_one_points_hull_agreement hc hB).
Qed.

(** Source for [density_one_points_equal_measure]: supporting equal
    original outer volume of S and S* in Federer 3.2.41, p. 278.
    Both may have infinite measure; no subtraction is used. *)
Lemma density_one_points_equal_measure (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context mu V ->
  mu A=mu (measure_density_one_points mu V A).
Proof.
move=> hc.
have hm := derivation_measure_law (derivation_context_measure hc).
have he := @density_one_points_measure_test R X mu V A setT hc
  (measure_measurable_whole hm).
by rewrite !setTI in he.
Qed.
