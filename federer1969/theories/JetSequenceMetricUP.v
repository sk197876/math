(** Federer (1969), 3.4.5, p. 319: the exact
    countable jet metric, specified before constructing the sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum BoundedDistanceScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [jet_metric_weight]: the exact coefficient
    2^(-m), starting at m=0, in the metric of
    3.4.5, p. 319. It is twice the positive-index
    coefficient used for the sequence space of 2.2.6. *)
Definition jet_metric_weight (R:realType) m:R:=((2:R)^-1)^+m.
Arguments jet_metric_weight {R} m.

(** Source for [is_jet_sequence_distance]: the exact displayed
    distance in 3.4.5, p. 319, with independently
    given jets and their actual operator norms. The predicate
    specifies the series, without assuming convergence or metric laws. *)
Definition is_jet_sequence_distance (R:realType) (G:choiceType)
    (Z:nat->lmodType R) (N:forall m,Z m->R) (jet:forall m,G->Z m)
    (d:G->G->R):Prop:=
  forall alpha beta,
    nonnegative_sum setT (fun m=>
      (jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E)=
    (d alpha beta)%:E.
