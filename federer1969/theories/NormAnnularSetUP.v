(** Federer (1969), 3.2.16, p. 253:
    independent laws for the set formed from
    good approximation sets in successive annuli. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_norm_annular_set]: the displayed
    union defining T in Federer 3.2.16,
    p. 253. Closed outer balls and deleted
    closed inner balls fix both boundary conventions. *)
Definition is_norm_annular_set (R : realType) (X : lmodType R)
    (NX : X -> R) (S : nat -> set X) (a : X) (rho : nat -> R)
    (T : set X) : Prop :=
  forall x, T x <-> exists n, S n x /\ NX (x-a)<=rho n /\ rho n.+1<NX (x-a).
