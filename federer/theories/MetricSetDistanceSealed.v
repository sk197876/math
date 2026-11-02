(** Federer (1969), 2.2.10, p. 66: sealed distance to a nonempty set. The
    infimum witness is private; clients use its lower-bound and
    greatest-lower-bound laws. Source context and conventions:
    MetricSetDistanceUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type MetricSetDistanceSignature.
(** Source for [value]: abstract distance function supporting
    Federer 2.2.10, p. 66, with a nonempty-set premise. *)
Parameter value : forall (R : realType) (T : metricType R)
  (A : set T), A !=set0 -> T -> R.
(** Source for [laws]: infimum laws of the distance used in Federer 2.2.10,
    p. 66. *)
Parameter laws : forall (R : realType) (T : metricType R)
  (A : set T) (hn : A !=set0), is_metric_set_distance A (@value R T A hn).
End MetricSetDistanceSignature.
Module MetricSetDistance : MetricSetDistanceSignature.
(** Source for [value]: private choice of the proved distance
    witness supporting Federer 2.2.10, p. 66. *)
Definition value (R : realType) (T : metricType R) (A : set T) (hn : A !=set0) :=
  projT1 (cid (@metric_set_distance_exists R T A hn)).
(** Source for [laws]: the selected witness satisfies the abstract
    distance laws supporting Federer 2.2.10, p. 66. *)
Lemma laws (R : realType) (T : metricType R) (A : set T) (hn : A !=set0) :
  is_metric_set_distance A (@value R T A hn).
Proof. exact: projT2 (cid (@metric_set_distance_exists R T A hn)). Qed.
End MetricSetDistance.
