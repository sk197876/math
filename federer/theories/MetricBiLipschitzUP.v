(** Federer (1969), 3.2.17, p. 254:
    a common Lipschitz constant for a restriction
    and its actual inverse. Specify the two
    distance inequalities without extending the inverse
    outside its image domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_bilipschitz_bound]: the
    two lambda bounds in Federer 3.2.17,
    p. 254. The inverse inequality also
    proves univalence on K. A nonnegative
    bound is permitted in this supporting predicate. *)
Definition is_metric_bilipschitz_bound (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) :=
  is_metric_lipschitz_bound K f L /\
  forall x y, K x -> K y -> mdist x y<=L*mdist (f x) (f y).
