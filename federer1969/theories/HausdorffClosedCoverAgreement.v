(** Federer (1969), 2.10.2(1), p. 171: all nonempty sets and all nonempty
    closed sets give the same Hausdorff measure. Extend the existing
    degree-one closure proof to the printed normalized integer-degree
    gauges. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffMeasureLaws HausdorffMeasure
  HausdorffLengthUP HausdorffClosedCovers HausdorffDiameterCost
  MetricDiameter MetricDiameterClosure CaratheodoryTransport BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_closed_cover_agreement]: direct closed-cover
    equality in Federer 2.10.2(1), p. 171 Closure preserves the normalized
    cost and diameter, and forgetting closedness gives the reverse cover
    comparison. *)
Theorem hausdorff_closed_cover_agreement (R : realType) (X : metricType R)
    (m : nat) (mu nu : set X -> \bar R) :
  is_hausdorff_measure m mu -> is_closed_hausdorff_measure m nu -> forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hclosed : nu (id @` A)<=mu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_metric_sets R X) (@nonempty_closed_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => hausdorff_diameter_cost m (val j))
    (fun j => hausdorff_diameter_cost m (val j)) id (@nonempty_closed_hull R X)
    mu nu hm hn _ _ _ _ A).
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - move=> j x hx; exact: subset_closure hx.
  - move=> j; change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
    by rewrite extended_metric_diameter_closure.
  - move=> j; change (hausdorff_diameter_cost m (closure (val j))<=hausdorff_diameter_cost m (val j)).
    by rewrite hausdorff_diameter_cost_closure.
have hall : mu (id @` A)<=nu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_closed_metric_sets R X) (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => hausdorff_diameter_cost m (val j))
    (fun j => hausdorff_diameter_cost m (val j)) id (@nonempty_closed_forget R X)
    nu mu hn hm _ _ _ _ A).
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
rewrite image_id in hclosed hall.
by apply/eqP; rewrite eq_le hall hclosed.
Qed.

(** Source for [hausdorff_closed_measure_equality]: public
    closed-cover equality of Federer 2.10.2(1), p. 171,
    between the independently sealed selected measures. *)
Theorem hausdorff_closed_measure_equality (R : realType) (X : metricType R)
    (m : nat) (A : set X) :
  @hausdorff_measure R X m A=@closed_hausdorff_measure R X m A.
Proof.
exact (@hausdorff_closed_cover_agreement R X m _ _
  (@hausdorff_measure_specification R X m)
  (@closed_hausdorff_measure_specification R X m) A).
Qed.

(** Source for [hausdorff_measure_borel_regular]: direct Borel regularity in
    Federer 2.10.2(1), p. 171 Replace unrestricted generators by the proved
    equal closed-cover measure and apply the Borel-generator law of 2.10.1. *)
Theorem hausdorff_measure_borel_regular (R : realType) (X : metricType R) (m : nat) :
  is_borel_regular_measure (@hausdorff_measure R X m).
Proof.
have he : @hausdorff_measure R X m=@closed_hausdorff_measure R X m.
  apply: funext=> A; exact: hausdorff_closed_measure_equality.
rewrite he; exact: closed_hausdorff_borel_regular_law (@closed_hausdorff_measure_specification R X m).
Qed.
