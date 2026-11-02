(** Public Caratheodory construction for Federer (1969), 2.10.1, p. 170,
    used as a prerequisite for the Hausdorff-length example in 2.5.10, p.
    101. The selected measure is opaque; its measure, open-set, and
    Borel-regularity results follow from abstract laws. This module does not
    assert the alternative open-cover characterization discussed later on p.
    170. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP TopologicalBorel BorelRegularMeasureUP
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryMetricMeasure
  CaratheodoryBorelRegular CaratheodoryLimitSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_measure]: the final measure
    from the diameter-restricted covering construction in
    Federer 2.10.1, p. 170. *)
Definition caratheodory_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :=
  @CaratheodoryLimit.value R X J S cost.

(** Source for [caratheodory_measure_specification]: the
    supremum specification in Federer 2.10.1, p. 170. *)
Lemma caratheodory_measure_specification (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  is_caratheodory_limit S cost (caratheodory_measure S cost).
Proof. exact: CaratheodoryLimit.laws. Qed.

(** Source for [caratheodory_measure_is_measure]: the final measure obeys
    Federer's measure laws, 2.10.1, p. 170 *)
Theorem caratheodory_measure_is_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  (forall j, 0<=cost j) -> is_measure (caratheodory_measure S cost).
Proof. exact: (caratheodory_limit_is_measure (caratheodory_measure_specification S cost)). Qed.

(** Source for [caratheodory_measure_open_measurable]: every open set is
    measurable, Federer 2.10.1, p. 170 *)
Theorem caratheodory_measure_open_measurable (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  (forall j, 0<=cost j) ->
  forall U, open U -> measure_measurable (caratheodory_measure S cost) U.
Proof. exact: (caratheodory_limit_open_measurable (caratheodory_measure_specification S cost)). Qed.

(** Source for [caratheodory_measure_borel_regular]: Borel generators give a
    Borel regular measure, Federer 2.10.1, p. 170 *)
Theorem caratheodory_measure_borel_regular (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  (forall j, 0<=cost j) -> (forall j, borel_set (S j)) ->
  is_borel_regular_measure (caratheodory_measure S cost).
Proof. exact: (caratheodory_limit_borel_regular (caratheodory_measure_specification S cost)). Qed.
