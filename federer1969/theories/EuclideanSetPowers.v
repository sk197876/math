(** Federer (1969), 2.10.29, p. 195: the finite Cartesian power A^q as a
    subset of the actual Euclidean space R^q. Coordinate membership
    specifies the set; it chooses no points or implementation of A. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_set_power]: direct
    A^q in R^q in 2.10.29, p. 195,
    defined by membership of every scalar
    coordinate in A. The definition also
    includes the empty-product carrier R^0. *)
Definition euclidean_set_power (R : realType) (q : nat) (A : set (real_line_metric R)) :
    set (inner_metric_space (@euclidean_inner_productP R q)) :=
  [set x | forall i, A (x i)].

Arguments euclidean_set_power {R} q A.
