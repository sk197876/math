(** Federer (1969), 2.10.2(2), p. 171: in Euclidean space the spherical
    measure can also be obtained from open balls. Specify this alternative
    independently, for any metric space, before proving the Euclidean
    equality. Positive real radii follow 2.8.1, p. 141. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls HausdorffDiameterCost
  CaratheodoryLimitUP CaratheodoryMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_positive_metric_open_ball]: supporting
    abstract generator predicate for the open-ball alternative
    in Federer 2.10.2(2), p. 171. Representations by
    centers and positive radii need not be unique. *)
Definition is_positive_metric_open_ball (R : realType) (X : metricType R) (A : set X) :=
  exists a : X, exists r : R, 0<r /\ forall x, A x <-> mdist a x<r.

(** Source for [positive_open_metric_balls]: direct alternative
    family in Federer 2.10.2(2), p. 171, with
    strictly positive finite real radii. *)
Definition positive_open_metric_balls (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type (@is_positive_metric_open_ball R X)].

(** Source for [positive_open_ball_satisfies_laws]: supporting
    existence of the generators in the alternative family
    of Federer 2.10.2(2), p. 171. *)
Lemma positive_open_ball_satisfies_laws (R : realType) (X : metricType R) (a : X) (r : R) :
  0<r -> is_positive_metric_open_ball [set x | mdist a x<r].
Proof. move=> hr; exists a,r; split=> // x; by []. Qed.

(** Source for [positive_metric_open_ball_nonempty]: supporting
    nonemptiness for the open-ball family of Federer
    2.10.2(2), p. 171. The center belongs to its ball. *)
Lemma positive_metric_open_ball_nonempty (R : realType) (X : metricType R) (A : set X) :
  is_positive_metric_open_ball A -> A !=set0.
Proof.
move=> [a [r [hr hA]]]; exists a; apply/(hA a); by rewrite mdistxx.
Qed.

(** Source for [is_open_ball_spherical_measure]: independent
    Caratheodory specification for the alternative spherical
    measure in Federer 2.10.2(2), p. 171. It does
    not assume equality with the closed-ball construction. *)
Definition is_open_ball_spherical_measure (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :=
  is_caratheodory_limit (fun j : @positive_open_metric_balls R X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) mu.

(** Source for [open_ball_spherical_measure]: supporting
    selected alternative measure for Federer 2.10.2(2),
    p. 171, using the existing sealed Caratheodory operator. *)
Definition open_ball_spherical_measure (R : realType) (X : metricType R) (m : nat) :=
  caratheodory_measure (fun j : @positive_open_metric_balls R X => val j)
    (fun j => hausdorff_diameter_cost m (val j)).

(** Source for [open_ball_spherical_measure_specification]:
    proved existence laws for the alternative in Federer
    2.10.2(2), p. 171, before its Euclidean comparison. *)
Lemma open_ball_spherical_measure_specification (R : realType) (X : metricType R) (m : nat) :
  is_open_ball_spherical_measure m (@open_ball_spherical_measure R X m).
Proof. exact: caratheodory_measure_specification. Qed.
