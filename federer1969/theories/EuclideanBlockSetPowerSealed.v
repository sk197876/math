(** Opaque finite Cartesian set powers for Federer (1969), 2.10.29, p. 195.
    The private recursion is exposed only through its two proved membership
    laws. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanMeasurePowerUP EuclideanBlockSetPowerUP EuclideanBlockSetPowerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EUCLIDEAN_BLOCK_SET_POWER.
(** Source for [value]: abstract finite Euclidean
    set power for 2.10.29, p. 195. *)
Parameter value : forall (R : realType) d,
  set (inner_metric_space (@euclidean_inner_productP R d)) -> forall q,
    set (inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension d q))).
(** Source for [laws]: defining Cartesian membership
    laws for 2.10.29, p. 195. *)
Parameter laws : forall (R : realType) d (C : set (inner_metric_space (@euclidean_inner_productP R d))),
  is_euclidean_block_set_power C (@value R d C).
End EUCLIDEAN_BLOCK_SET_POWER.
Module EuclideanBlockSetPower : EUCLIDEAN_BLOCK_SET_POWER.
(** Source for [value]: selected existence witness
    of the finite set powers in 2.10.29,
    p. 195, hidden by opaque ascription. *)
Definition value (R : realType) d (C : set (inner_metric_space (@euclidean_inner_productP R d))) :=
  projT1 (cid (@euclidean_block_set_power_exists R d C)).
(** Source for [laws]: proved Cartesian membership
    specification for 2.10.29, p. 195. *)
Lemma laws (R : realType) d (C : set (inner_metric_space (@euclidean_inner_productP R d))) :
  is_euclidean_block_set_power C (@value R d C).
Proof. exact: projT2 (cid (@euclidean_block_set_power_exists R d C)). Qed.
End EuclideanBlockSetPower.
