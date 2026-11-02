(** Federer (1969), 2.10.3, p. 172: open generators give the same final
    exterior-diameter measure. Specify this family independently; equality
    is proved later. Source context and the actual gauge:
    ExteriorDiameterUP.v. No equality of fixed-cutoff approximations is
    assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasureUP
  ExteriorMeasureGauge CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_open_exterior_diameter_measure]: independent
    open-cover specification for Federer 2.10.3, p. 172.
    The family retains the nonempty convention on p. 171
    and the same normalized exterior-product gauge. *)
Definition is_open_exterior_diameter_measure (R : realType) (n m : nat)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : @nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => exterior_diameter_cost m (val j)) nu.
