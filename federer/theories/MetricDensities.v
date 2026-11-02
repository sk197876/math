(** Federer (1969), 2.10.19, p. 181: upper, lower and common m-dimensional
    densities, using the ball volume alpha(m) from 2.7.16(1), p. 135. This
    file treats the book's initial nonnegative integer degrees, including
    zero. The optional real- degree Gamma extension of 2.10.2 remains
    separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MeasureUP MeasureBasic EuclideanBallVolume
  PositiveRadiusLimits PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_ball_density]: direct normalized
    ball expression alpha(m)^(-1) r^(-m) mu B(a,r)
    in 2.10.19, p. 181, at integer degree.
    Its limit only uses r>0, where the denominator
    is positive finite even for m=0. *)
Definition metric_ball_density (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) (a : X) (r : R) : \bar R :=
  mu (metric_closed_ball a r)/(euclidean_unit_ball_volume R m*r^+m)%:E.

(** Source for [upper_metric_density]: direct upper density of 2.10.19, p.
    181 *)
Definition upper_metric_density (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) (a : X) :=
  positive_radius_upper_limit (metric_ball_density m mu a).

(** Source for [lower_metric_density]: direct lower
    density of 2.10.19, p. 181; the infimum and
    supremum use only strictly positive radii. *)
Definition lower_metric_density (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) (a : X) :=
  positive_radius_lower_limit (metric_ball_density m mu a).

(** Source for [metric_density]: direct common density
    in the paragraph after the first two displays
    of 2.10.19, p. 181. Its domain consists exactly
    of points where upper and lower densities agree. *)
Definition metric_density (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) : partial_function X (\bar R).
Proof.
refine (@Build_partial_function X (\bar R)
  (fun x y => upper_metric_density m mu x=y /\ lower_metric_density m mu x=y) _).
move=> x y z [hy _] [hz _]; exact: eq_trans (esym hy) hz.
Defined.

(** Source for [metric_ball_density_denominator_positive]: supporting
    domain fact for the positive-radius quotient of
    2.10.19, p. 181. This excludes any reliance on
    the zero-denominator convention from 2.10.17. *)
Lemma metric_ball_density_denominator_positive (R : realType) m (r : R) :
  (0<r)%R -> (0<euclidean_unit_ball_volume R m*r^+m)%R.
Proof.
move=> hr; apply: mulr_gt0; first exact: (euclidean_unit_ball_volumeE R m).2.
exact: exprn_gt0 hr.
Qed.

(** Source for [metric_ball_density_zero_degree]: supporting
    degree-zero boundary of 2.10.19, p. 181, using
    alpha(0)=1 and r^0=1, including positive radii
    in a space with isolated points. *)
Lemma metric_ball_density_zero_degree (R : realType) (X : metricType R)
    (mu : set X -> \bar R) a r : metric_ball_density 0 mu a r=mu (metric_closed_ball a r).
Proof. by rewrite /metric_ball_density euclidean_unit_ball_volume0 expr0 mulr1 inve1 mule1. Qed.

(** Source for [metric_density_graph]: supporting domain
    and value equations for the common density of
    2.10.19, p. 181. No default value is assigned
    at points where the densities disagree. *)
Lemma metric_density_graph (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a y :
  partial_function_graph (metric_density m mu) a y <->
  upper_metric_density m mu a=y /\ lower_metric_density m mu a=y.
Proof. by []. Qed.

(** Source for [metric_densities_ordered]: supporting
    lower density at most upper density in 2.10.19,
    p. 181; it follows from the positive-radius
    limit laws without any measure or finiteness premise. *)
Lemma metric_densities_ordered (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a : lower_metric_density m mu a<=upper_metric_density m mu a.
Proof. exact: positive_radius_limits_ordered. Qed.
