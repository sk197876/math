(** Federer (1969), 2.10.29, p. 195: public finite Cartesian powers of a
    subset of R^d, using only the opaque membership specification. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanMeasurePowerUP EuclideanBlockSetPowerUP EuclideanBlockSetPowerSealed EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_set_power]: public
    actual Euclidean set power supporting
    2.10.29, p. 195. The construction
    stays behind the opaque specification. *)
Definition euclidean_block_set_power (R : realType) d
    (C : set (inner_metric_space (@euclidean_inner_productP R d))) :=
  @EuclideanBlockSetPower.value R d C.

(** Source for [euclidean_block_set_power_specification]: direct
    first-factor and successor membership laws
    in 2.10.29, p. 195, from the
    opaque implementation. *)
Lemma euclidean_block_set_power_specification (R : realType) d
    (C : set (inner_metric_space (@euclidean_inner_productP R d))) :
  is_euclidean_block_set_power C (@euclidean_block_set_power R d C).
Proof. exact: EuclideanBlockSetPower.laws. Qed.

(** Source for [euclidean_block_set_power_firstE]: supporting
    single-factor identity in 2.10.29, p. 195. *)
Lemma euclidean_block_set_power_firstE (R : realType) d
    (C : set (inner_metric_space (@euclidean_inner_productP R d))) :
  @euclidean_block_set_power R d C 0%N=C.
Proof. exact (euclidean_block_set_power_first (euclidean_block_set_power_specification C)). Qed.

(** Source for [euclidean_block_set_power_successorE]: direct
    Cartesian membership identity at the next
    finite power in 2.10.29, p. 195. *)
Lemma euclidean_block_set_power_successorE (R : realType) d
    (C : set (inner_metric_space (@euclidean_inner_productP R d))) q :
  @euclidean_block_set_power R d C q.+1=
    [set x | @euclidean_block_set_power R d C q (@euclidean_block_split R (euclidean_power_dimension d q) d x).1 /\
      C (@euclidean_block_split R (euclidean_power_dimension d q) d x).2].
Proof. exact (euclidean_block_set_power_successor (euclidean_block_set_power_specification C) q). Qed.
