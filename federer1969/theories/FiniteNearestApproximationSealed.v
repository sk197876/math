(** Federer (1969), 2.4.12, p. 87: opaque access to finite Borel
    nearest-point approximations used for finite-image density. The
    implementation is sealed. *)
From mathcomp Require Import all_boot boolp reals topology.
From Federer Require Import FiniteNearestApproximationUP FiniteNearestApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FiniteNearestApproximationSignature.
(** Source for [value]: abstract approximation labels supporting
    finite-image density in Federer 2.4.12, p. 87. *)
Parameter value : forall (R : realType) (Y : metricType R), (nat -> Y) -> nat -> Y -> nat.
(** Source for [laws]: only the finite-prefix, Borel-fibre and
    nearest-point laws for Federer 2.4.12, p. 87, are exposed. *)
Parameter laws : forall (R : realType) (Y : metricType R) (y : nat -> Y),
  is_finite_nearest_approximation y (@value R Y y).
End FiniteNearestApproximationSignature.
Module FiniteNearestApproximation : FiniteNearestApproximationSignature.
(** Source for [value]: private choice of the proved approximation
    witness supporting Federer 2.4.12, p. 87. *)
Definition value (R : realType) (Y : metricType R) (y : nat -> Y) :=
  projT1 (cid (@finite_nearest_approximation_exists R Y y)).
(** Source for [laws]: the chosen witness satisfies the abstract
    laws supporting finite-image density in Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (Y : metricType R) (y : nat -> Y) :
  is_finite_nearest_approximation y (@value R Y y).
Proof. exact: projT2 (cid (@finite_nearest_approximation_exists R Y y)). Qed.
End FiniteNearestApproximation.
