(** Federer (1969), 2.8.8, p. 145: use diameter as the weight and impose the
    displayed diametric regularity condition for closed balls. These
    predicates state laws independently of selected implementations. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_diameter_weight]: the choice
    delta(S)=diam(S)=sup rho(S times S) in Federer 2.8.8,
    p. 145. Its laws use the existing abstract diameter
    specification. The weight is finite real valued on F,
    allowing exactly the bounded sets used in the applications. *)
Definition is_real_diameter_weight (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) :=
  forall S, F S -> is_extended_metric_diameter S (d S)%:E.

(** Source for [is_positive_closed_ball_family]: the family of closed balls
    in Federer 2.8.8, p. 145, with positive real radii as used in the
    displayed growth estimate Positive radius does not imply positive
    diameter in a general metric space. *)
Definition is_positive_closed_ball_family (R : realType) (X : metricType R)
    (F : set (set X)) :=
  forall S, F S -> exists a r, (0 < r)%R /\ S = metric_closed_ball a r.

(** Source for [is_diametrically_regular_ball_family]: the
    displayed condition phi B[a,(1+2 tau)r]<lambda phi B(a,r)
    in Federer 2.8.8, p. 145. The brackets indicate
    closed balls in both places. The scalar bounds and measure
    laws are separate hypotheses in subsequent consequences. *)
Definition is_diametrically_regular_ball_family (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (tau lambda : R) :=
  forall a r, (0 < r)%R -> F (metric_closed_ball a r) ->
    mu (metric_closed_ball a ((1 + 2 * tau) * r)%R) <
      lambda%:E * mu (metric_closed_ball a r).
