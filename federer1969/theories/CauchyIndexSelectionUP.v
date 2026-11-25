(** Federer (1969), 2.3.10, p. 80: choose increasing integers N(n) for the
    Cauchy estimates. The abstract selector below applies to prescribed
    positive tolerances; the geometric sequence is supplied by the measure
    application. *)
From mathcomp Require Import all_boot all_order classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [is_cauchy_index_selection]: abstract increasing
    choice of N(n) in Federer 2.3.10, p. 80, with
    a tail estimate at each prescribed tolerance. *)
Definition is_cauchy_index_selection (R : realType) (d : nat -> nat -> \bar R)
    (b : nat -> R) (s : nat -> nat) :=
  (forall n, (s n < s n.+1)%N) /\ forall n i j,
    (s n <= i)%N -> (s n <= j)%N -> d i j < (b n)%:E.
