(** Federer (1969), 2.10.2, p. 171: measure laws follow from 2.10.1 after
    specifying the gauge and family. Closed and open generator variants are
    treated separately; no equality between them is presumed. The spherical
    Borel-regularity corollary uses its closed-ball generators. Source
    conventions, integer degrees and positive radii: HausdorffMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffLengthUP HausdorffDiameterCost
  MetricDiameter CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryBorelRegular
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_measure_measure_law]: measure
    assertion implicit in the definition of Federer 2.10.2(1),
    p. 171, by the proved construction laws of 2.10.1. *)
Lemma hausdorff_measure_measure_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) : is_hausdorff_measure m mu -> is_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_is_measure hm)=> j.
exact: hausdorff_diameter_cost_nonnegative.
Qed.

(** Source for [closed_hausdorff_measure_measure_law]: supporting
    measure assertion for the independent closed-cover version
    of Federer 2.10.2(1), p. 171. *)
Lemma closed_hausdorff_measure_measure_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) : is_closed_hausdorff_measure m mu -> is_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_is_measure hm)=> j.
exact: hausdorff_diameter_cost_nonnegative.
Qed.

(** Source for [open_hausdorff_measure_measure_law]: supporting
    measure assertion for the independent open-cover version
    of Federer 2.10.2(1), p. 171. *)
Lemma open_hausdorff_measure_measure_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) : is_open_hausdorff_measure m mu -> is_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_is_measure hm)=> j.
exact: hausdorff_diameter_cost_nonnegative.
Qed.

(** Source for [spherical_measure_measure_law]: measure
    assertion implicit in Federer 2.10.2(2), p. 171,
    using the positive-radius closed-ball family. *)
Lemma spherical_measure_measure_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) : is_spherical_measure m mu -> is_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_is_measure hm)=> j.
exact: hausdorff_diameter_cost_nonnegative.
Qed.

(** Source for [closed_hausdorff_borel_regular_law]: supporting Borel
    regularity for the closed-cover version of Federer 2.10.2(1), p. 171 It
    follows from closed generators before identifying the measure with the
    unrestricted family. *)
Lemma closed_hausdorff_borel_regular_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :
  is_closed_hausdorff_measure m mu -> is_borel_regular_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_borel_regular hm).
- move=> j; exact: hausdorff_diameter_cost_nonnegative.
- move=> j; exact: closed_borel_set (set_valP j).1.
Qed.

(** Source for [open_hausdorff_borel_regular_law]: supporting
    Borel regularity of the open-cover version in Federer
    2.10.2(1), p. 171. Its generators are Borel, so
    2.10.1 applies without a comparison of preliminary measures. *)
Lemma open_hausdorff_borel_regular_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :
  is_open_hausdorff_measure m mu -> is_borel_regular_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_borel_regular hm).
- move=> j; exact: hausdorff_diameter_cost_nonnegative.
- move=> j; exact: open_borel_set (set_valP j).1.
Qed.

(** Source for [spherical_borel_regular_law]: supporting corollary for
    spherical measure in Federer 2.10.2(2), p. 171 All positive-radius
    closed balls are Borel. *)
Lemma spherical_borel_regular_law (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :
  is_spherical_measure m mu -> is_borel_regular_measure mu.
Proof.
move=> hm; apply: (caratheodory_limit_borel_regular hm).
- move=> j; exact: hausdorff_diameter_cost_nonnegative.
- move=> j; apply: closed_borel_set.
  exact: positive_metric_closed_ball_closed (set_valP j).
Qed.

(** Source for [hausdorff_one_degree_length_specification]:
    exact degree-one compatibility with the earlier Hausdorff
    length formalisation of Federer 2.10.2(1), p. 171.
    Replace the normalized cost by diameter using its proved
    coefficient value, not by unfolding a measure construction. *)
Lemma hausdorff_one_degree_length_specification (R : realType) (X : metricType R)
    (mu : set X -> \bar R) : is_hausdorff_measure 1 mu <-> is_hausdorff_length mu.
Proof.
have he : (fun A : @nonempty_metric_sets R X => hausdorff_diameter_cost 1 (val A))=
    (fun A : @nonempty_metric_sets R X => extended_metric_diameter (val A)).
  apply: funext=> A; exact: hausdorff_diameter_cost_one_degree.
by rewrite /is_hausdorff_measure /is_hausdorff_length he.
Qed.
