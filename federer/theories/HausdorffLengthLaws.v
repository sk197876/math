(** Federer (1969), 2.10.2(1), p. 171: Hausdorff length is Borel regular
    because closed covers give the same measure. These consequences use the
    abstract Hausdorff-length specification. The closed-cover comparison and
    general Caratheodory measure laws have been proved independently. Source
    context: HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP TopologicalBorel BorelRegularMeasureUP
  MetricDiameterUP MetricDiameter CaratheodoryLimitMeasure CaratheodoryMetricMeasure
  CaratheodoryMeasure HausdorffLengthUP HausdorffClosedCovers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_length_measure_law]: the
    m=1 measure assertion in Federer 2.10.2(1),
    p. 171, using the general construction of 2.10.1. *)
Theorem hausdorff_length_measure_law (R : realType) (X : metricType R)
    (mu : set X -> \bar R) : is_hausdorff_length mu -> is_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_is_measure hm)=> j.
exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
Qed.

(** Source for [hausdorff_length_open_measurable_law]: the
    open-set measurability inherited from the construction,
    Federer 2.10.1, p. 170, and 2.10.2(1), p. 171. *)
Theorem hausdorff_length_open_measurable_law (R : realType) (X : metricType R)
    (mu : set X -> \bar R) :
  is_hausdorff_length mu -> forall U, open U -> measure_measurable mu U.
Proof.
move=> hm; apply: (caratheodory_limit_open_measurable hm)=> j.
exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
Qed.

(** Source for [hausdorff_length_borel_regular_law]: the Borel regularity
    conclusion of Federer 2.10.2(1), p. 171 Equality with the closed-cover
    measure is proved from the abstract specifications, without assuming
    regularity. *)
Theorem hausdorff_length_borel_regular_law (R : realType) (X : metricType R)
    (mu : set X -> \bar R) :
  is_hausdorff_length mu -> is_borel_regular_measure mu.
Proof.
move=> hm.
pose S (j : @nonempty_closed_metric_sets R X) := val j.
pose cost j := extended_metric_diameter (S j).
pose rho := caratheodory_measure S cost.
have hr : is_closed_hausdorff_length rho := caratheodory_measure_specification S cost.
have he : mu=rho by apply: funext=> A; exact: hausdorff_length_closed_cover_equality hm hr A.
rewrite he; apply: (@caratheodory_measure_borel_regular R X
  (@nonempty_closed_metric_sets R X) S cost).
- move=> j; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
- move=> j; apply: closed_borel_set; exact: (set_valP j).1.
Qed.
