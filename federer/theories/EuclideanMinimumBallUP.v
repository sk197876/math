(** Federer (1969), 2.10.41, printed p. 200: a closed enclosing ball with
    least radius. Specify its laws without choosing a centre or radius. In
    positive Euclidean dimension diameter is twice radius, so the later
    theorem recovers the exact printed minimum-diameter statement. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_minimum_enclosing_ball]: supporting
    abstract least-radius characterisation of the minimum
    ball in 2.10.41, p. 200. Existence,
    centre uniqueness and the sharp Jung bound are
    proved separately, never assumed as fields. *)
Record is_minimum_enclosing_ball (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (b : inner_metric_space (@euclidean_inner_productP R n)) (r : R) : Prop := {
  (** Source for [minimum_ball_radius_nonnegative_law]: supporting
      nonnegative closed-ball radius in 2.10.41, p. 200. *)
  minimum_ball_radius_nonnegative_law : 0<=r;
  (** Source for [minimum_ball_contains_law]: direct
      enclosing assertion in 2.10.41, p. 200. *)
  minimum_ball_contains_law : S `<=` metric_closed_ball b r;
  (** Source for [minimum_ball_radius_least_law]: supporting
      least-radius form of the minimum-diameter assertion
      in 2.10.41, p. 200. *)
  minimum_ball_radius_least_law : forall z t, 0<=t -> S `<=` metric_closed_ball z t -> r<=t
}.
