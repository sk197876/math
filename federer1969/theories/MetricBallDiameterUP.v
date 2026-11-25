(** Supporting geometric specification for Federer (1969), 2.10.2(2), p.
    171, the Euclidean open-ball alternative. A nonnegative real factor
    describes the diameters of positive-radius open and closed balls.
    Euclidean positive dimensions have factor two; dimension zero has factor
    zero. This is a general supporting predicate, not an additional
    assertion about arbitrary metric spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_ball_diameter_factor]: supporting
    geometric laws sufficient for the open-ball replacement
    in Federer 2.10.2(2), p. 171. Existence is proved
    for Euclidean space independently of the measure theorem. *)
Record is_metric_ball_diameter_factor (R : realType) (X : metricType R) (c : R) : Prop := {
  (** Source for [ball_diameter_factor_nonnegative]: supporting
      nonnegative diameter multiplier for Federer 2.10.2(2), p. 171. *)
  ball_diameter_factor_nonnegative : 0<=c;
  (** Source for [closed_ball_diameter_factor]: supporting
      closed-ball diameter law for Federer 2.10.2(2), p. 171. *)
  closed_ball_diameter_factor : forall a : X, forall r : R, 0<r ->
    extended_metric_diameter (metric_closed_ball a r)=(c*r)%:E;
  (** Source for [open_ball_diameter_factor]: supporting
      open-ball diameter law for Federer 2.10.2(2), p. 171. *)
  open_ball_diameter_factor : forall a : X, forall r : R, 0<r ->
    extended_metric_diameter [set x | mdist a x<r]=(c*r)%:E
}.
