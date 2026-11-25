(** The cost comparison underlying Federer (1969), 2.10.11, p. 176,
    specialized to Hausdorff length and a Borel cost bounded by diameter.
    The source covering family consists of all nonempty sets; replacing them
    by closures makes them valid Borel generators without changing diameter,
    as in 2.10.2(1), p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalBorel MetricDiameter MetricDiameterClosure
  BorelCoverCostUP BorelCaratheodoryMeasure CaratheodoryTransport
  HausdorffLengthUP HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_closed_cover_member]: closure is
    a Borel cover member with unchanged diameter, supporting
    Federer 2.10.2(1), p. 171, and the
    cover comparison in 2.10.11, p. 176. *)
Definition borel_closed_cover_member (R : realType) (X : metricType R)
    (A : @nonempty_metric_sets R X) : @borel_metric_sets R X :=
  Sub (closure (val A)) (mem_set (closed_borel_set (@closed_closure X (val A)))).

(** Source for [borel_cost_hausdorff_length_bound]: the
    defining-cover comparison used in Federer 2.10.11,
    p. 176, for one-dimensional Hausdorff measure.
    The multiplicity integral is identified separately; this
    theorem proves only the measure comparison from the costs. *)
Theorem borel_cost_hausdorff_length_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) : is_borel_cover_cost c ->
  (forall A, borel_set A -> c A<=extended_metric_diameter A) ->
  forall A, borel_caratheodory_measure c A<=hausdorff_length A.
Proof.
move=> hc hd A.
have h : borel_caratheodory_measure c (id @` A)<=hausdorff_length A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_metric_sets R X) (@borel_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => extended_metric_diameter (val j)) (fun j => c (val j))
    id (@borel_closed_cover_member R X) (@hausdorff_length R X)
    (borel_caratheodory_measure c) (@hausdorff_length_specification R X)
    (borel_caratheodory_specification c) _ _ _ _ A).
  - move=> j; exact (@borel_cover_cost_nonnegative R X c hc (val j) (set_valP j)).
  - move=> j x hx; exact: subset_closure hx.
  - move=> j; change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
    by rewrite extended_metric_diameter_closure.
  - move=> j; change (c (closure (val j))<=extended_metric_diameter (val j)).
    rewrite -(extended_metric_diameter_closure (val j)); apply: hd.
    exact: closed_borel_set (@closed_closure X (val j)).
by rewrite image_id in h.
Qed.
