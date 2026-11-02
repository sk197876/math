(** Public selected T^m for Federer (1969), 2.10.3, p. 171. The general
    Caratheodory operator is sealed; its supplied endpoint gauge has an
    independently sealed supremum. The alternative covering statements of p.
    172 are separate theorems. Source context: ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  HausdorffLengthUP ExteriorMeasureGauge ExteriorMeasureUP
  CaratheodoryMeasure CaratheodoryLimitMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [exterior_diameter_measure]: direct selected
    result of the construction defining T^m in Federer
    2.10.3, p. 171. The printed item assumes positive
    degree; the natural-degree interface also permits
    auxiliary boundary calculations in degree zero. *)
Definition exterior_diameter_measure (R : realType) (n m : nat) :=
  caratheodory_measure
    (fun j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => exterior_diameter_cost m (val j)).

(** Source for [exterior_diameter_measure_specification]:
    proved covering laws of the selected measure in
    Federer 2.10.3, p. 171. Existence comes from
    the already sealed general construction, rather than
    an unproved measure-existence premise. *)
Lemma exterior_diameter_measure_specification (R : realType) (n m : nat) :
  is_exterior_diameter_measure m (@exterior_diameter_measure R n m).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [exterior_diameter_measure_is_measure]:
    measure assertion in the definition of Federer
    2.10.3, p. 171, using the proved nonnegative
    gauge and Caratheodory construction laws of 2.10.1. *)
Theorem exterior_diameter_measure_is_measure (R : realType) (n m : nat) :
  is_measure (@exterior_diameter_measure R n m).
Proof.
apply: (caratheodory_limit_is_measure (@exterior_diameter_measure_specification R n m))=> j.
exact: exterior_diameter_cost_nonnegative.
Qed.
