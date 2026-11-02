(** Federer (1969), 2.10.29, p. 195: the positive finite Cartesian powers of
    a subset of R^d. Specify first-factor and successor membership laws in
    the actual Euclidean block coordinates. Existence and selection are
    separate. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanMeasurePowerUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_block_set_power]: direct
    first-factor and Cartesian successor membership
    specification for [A(m,n)*A(m,nu)]^q in
    2.10.29, p. 195, before choosing a
    recursive implementation. Stage q has q+1 factors. *)
Record is_euclidean_block_set_power (R : realType) d
    (C : set (inner_metric_space (@euclidean_inner_productP R d)))
    (U : forall q, set (inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension d q)))) : Prop := {
  (** Source for [euclidean_block_set_power_first]: direct
      single-factor base of the finite Cartesian
      power used in 2.10.29, p. 195. *)
  euclidean_block_set_power_first : U 0%N=C;
  (** Source for [euclidean_block_set_power_successor]: direct
      Cartesian successor in 2.10.29, p. 195,
      expressed by the two Euclidean block
      membership conditions. No closedness or mass
      conclusion is imposed as a defining law. *)
  euclidean_block_set_power_successor : forall q, U q.+1=
    [set x | U q (@euclidean_block_split R (euclidean_power_dimension d q) d x).1 /\
      C (@euclidean_block_split R (euclidean_power_dimension d q) d x).2]
}.
