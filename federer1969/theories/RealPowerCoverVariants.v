(** Federer 2.10.2, p. 171: independently specified open, closed-ball,
    open-ball and convex variants of the real-degree diameter construction.
    The positive normalization coefficient is explicit in these supporting
    laws. Every selected value comes from the earlier sealed general
    Caratheodory construction; no new implementation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost MetricRealPowerMeasureUP
  MetricRealPowerMeasure MetricRealPowerMeasureLaws HausdorffLengthUP
  HausdorffMeasureUP SphericalOpenBallUP HausdorffConvexCovers
  CaratheodoryLimitUP CaratheodoryMeasure CaratheodoryBorelRegular MeasureUP
  RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_diameter_cost_ge0]: Federer 2.10.2,
    p. 171; supporting nonnegative generator costs, with no restriction
    on the exponent needed for this sign assertion. *)
Lemma metric_real_diameter_cost_ge0 (R:realType) (X:metricType R)
    (c p:R) (A:set X):
  (0<=c)%R -> 0<=metric_real_diameter_cost c p A.
Proof. exact:metric_real_power_cost_nonnegative. Qed.

(** Source for [is_open_metric_real_power_measure]: Federer 2.10.2(1),
    p. 171; independent covering specification using nonempty open sets. *)
Definition is_open_metric_real_power_measure (R:realType) (X:metricType R)
    (c p:R) (mu:set X->\bar R):Prop:=
  is_caratheodory_limit (fun j:@nonempty_open_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) mu.

(** Source for [is_spherical_metric_real_power_measure]: Federer
    2.10.2(2), p. 171; independent positive-radius closed-ball specification. *)
Definition is_spherical_metric_real_power_measure (R:realType) (X:metricType R)
    (c p:R) (mu:set X->\bar R):Prop:=
  is_caratheodory_limit (fun j:@positive_closed_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) mu.

(** Source for [is_open_ball_metric_real_power_measure]: Federer
    2.10.2(2), p. 171; independent positive-radius open-ball specification. *)
Definition is_open_ball_metric_real_power_measure (R:realType) (X:metricType R)
    (c p:R) (mu:set X->\bar R):Prop:=
  is_caratheodory_limit (fun j:@positive_open_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) mu.

(** Source for [is_convex_metric_real_power_measure]: Federer 2.10.2(1),
    p. 171; independent nonempty convex-cover specification in the original
    arbitrary-dimensional normed vector space. *)
Definition is_convex_metric_real_power_measure (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (c p:R)
    (mu:set (real_norm_metric_space hN)->\bar R):Prop:=
  is_caratheodory_limit
    (fun j:nonempty_convex_sets V=>(val j:set (real_norm_metric_space hN)))
    (fun j=>@metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j)) mu.

(** Source for [open_metric_real_power_measure]: Federer 2.10.2(1),
    p. 171; public value from the sealed general covering object. *)
Definition open_metric_real_power_measure (R:realType) (X:metricType R) (c p:R):=
  caratheodory_measure (fun j:@nonempty_open_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)).

(** Source for [spherical_metric_real_power_measure]: Federer 2.10.2(2),
    p. 171; public value from the sealed general covering object. *)
Definition spherical_metric_real_power_measure (R:realType) (X:metricType R) (c p:R):=
  caratheodory_measure (fun j:@positive_closed_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)).

(** Source for [open_ball_metric_real_power_measure]: Federer 2.10.2(2),
    p. 171; public value from the sealed general covering object. *)
Definition open_ball_metric_real_power_measure (R:realType) (X:metricType R) (c p:R):=
  caratheodory_measure (fun j:@positive_open_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)).

(** Source for [open_metric_real_power_specification]: Federer 2.10.2(1),
    p. 171; the selected open variant satisfies its independent laws. *)
Lemma open_metric_real_power_specification (R:realType) (X:metricType R) (c p:R):
  is_open_metric_real_power_measure c p (@open_metric_real_power_measure R X c p).
Proof. exact:caratheodory_measure_specification. Qed.

(** Source for [spherical_metric_real_power_specification]: Federer 2.10.2(2),
    p. 171; the selected closed-ball variant satisfies its independent laws. *)
Lemma spherical_metric_real_power_specification (R:realType) (X:metricType R) (c p:R):
  is_spherical_metric_real_power_measure c p (@spherical_metric_real_power_measure R X c p).
Proof. exact:caratheodory_measure_specification. Qed.

(** Source for [open_ball_metric_real_power_specification]: Federer 2.10.2(2),
    p. 171; the selected open-ball variant satisfies its independent laws. *)
Lemma open_ball_metric_real_power_specification (R:realType) (X:metricType R) (c p:R):
  is_open_ball_metric_real_power_measure c p (@open_ball_metric_real_power_measure R X c p).
Proof. exact:caratheodory_measure_specification. Qed.
