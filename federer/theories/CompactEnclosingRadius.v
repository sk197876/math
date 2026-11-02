(** Public enclosing radius supporting Federer (1969), 2.10.31, pp. 195–196.
    The value is opaque; all consequences use only its least
    containing-radius laws. Source context: CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricClosedBalls CompactSetDistanceProfile CompactEnclosingRadiusUP
  CompactEnclosingRadiusLaws CompactEnclosingRadiusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_radius]: supporting
    least centred ball radius used for the
    compact-class infimum of 2.10.31, p. 195. *)
Definition compact_enclosing_radius (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) := @CompactEnclosingRadius.value R X a C.
Arguments compact_enclosing_radius {R X} a C.

(** Source for [compact_enclosing_radius_specification]: supporting
    abstract radius laws for 2.10.31, p. 195. *)
Lemma compact_enclosing_radius_specification (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) :
  is_compact_enclosing_radius a C (compact_enclosing_radius a C).
Proof. exact: CompactEnclosingRadius.laws. Qed.
Arguments compact_enclosing_radius_specification {R X} a C.

(** Source for [compact_enclosing_radius_nonnegative]: supporting
    nonnegative minimal radius in 2.10.31, p. 195. *)
Lemma compact_enclosing_radius_nonnegative (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) : 0<=compact_enclosing_radius a C.
Proof. exact: enclosing_radius_nonnegative_law (compact_enclosing_radius_specification a C). Qed.
Arguments compact_enclosing_radius_nonnegative {R X} a C.

(** Source for [compact_enclosing_radius_contains]: supporting
    containing-ball assertion in 2.10.31, pp. 195–196. *)
Lemma compact_enclosing_radius_contains (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) : val C `<=` metric_closed_ball a (compact_enclosing_radius a C).
Proof. exact: enclosing_radius_contains_law (compact_enclosing_radius_specification a C). Qed.
Arguments compact_enclosing_radius_contains {R X} a C.

(** Source for [compact_enclosing_radius_least]: supporting
    least-bound comparison for 2.10.31, pp. 195–196. *)
Lemma compact_enclosing_radius_least (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) (s : R) :
  0<=s -> val C `<=` metric_closed_ball a s -> compact_enclosing_radius a C<=s.
Proof. move=> hs hC; exact (enclosing_radius_least_law (compact_enclosing_radius_specification a C) hs hC). Qed.
Arguments compact_enclosing_radius_least {R X} a C {s} _ _.

(** Source for [compact_enclosing_radius_attains]: supporting
    point on the least containing sphere for
    2.10.31, pp. 195–196. This is derived
    from the abstract laws rather than revealed
    by the opaque existence construction. *)
Lemma compact_enclosing_radius_attains (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) :
  exists x, val C x /\ mdist a x=compact_enclosing_radius a C.
Proof. exact (compact_enclosing_radius_attained (compact_enclosing_radius_specification a C)). Qed.
Arguments compact_enclosing_radius_attains {R X} a C.
