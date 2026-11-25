(** Federer (1969), 2.10.41, printed p. 200: one may replace the source by
    its closure in Jung's theorem. A closed ball contains the source
    precisely when it contains its closure; the abstract minimum-radius laws
    are therefore unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls EuclideanMinimumBallUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_ball_contains_closure]: supporting
    compact-source reduction in 2.10.41, p. 200.
    The closure has exactly the same closed containing
    balls. This holds in an arbitrary metric space. *)
Lemma closed_ball_contains_closure (R : realType) (X : metricType R)
    (S : set X) (b : X) (r : R) :
  S `<=` metric_closed_ball b r -> closure S `<=` metric_closed_ball b r.
Proof.
move=> hS x hx; apply: (@metric_closed_ball_closed R X b r).
exact: (@closureS X S (metric_closed_ball b r) hS x hx).
Qed.

(** Source for [minimum_ball_closure_laws]: supporting
    forward closure reduction for the minimum ball
    in 2.10.41, p. 200, retaining the same
    centre and radius. No boundedness is required
    for the adapter itself. *)
Lemma minimum_ball_closure_laws (R : realType) n S b r :
  @is_minimum_enclosing_ball R n S b r -> is_minimum_enclosing_ball (closure S) b r.
Proof.
move=> hD; constructor.
- exact: minimum_ball_radius_nonnegative_law hD.
- exact: closed_ball_contains_closure (minimum_ball_contains_law hD).
- move=> z t ht hC.
  apply: (@minimum_ball_radius_least_law R n S b r hD z t ht).
  move=> x hx; exact: hC x (subset_closure hx).
Qed.

(** Source for [minimum_ball_source_laws]: supporting
    return from the compact closure to the original
    source in 2.10.41, p. 200. Any closed
    ball competing for the source also contains its closure. *)
Lemma minimum_ball_source_laws (R : realType) n S b r :
  @is_minimum_enclosing_ball R n (closure S) b r -> is_minimum_enclosing_ball S b r.
Proof.
move=> hD; constructor.
- exact: minimum_ball_radius_nonnegative_law hD.
- move=> x hx; exact (@minimum_ball_contains_law R n (closure S) b r hD x (subset_closure hx)).
- move=> z t ht hS.
  exact (@minimum_ball_radius_least_law R n (closure S) b r hD z t ht
    (closed_ball_contains_closure hS)).
Qed.
