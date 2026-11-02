(** Federer (1969), 2.3.3, p. 76: private recursive witness for the
    prescribed-weight greedy expansion. Existence is separated from the
    abstract recurrence and its consequences. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [greedy_scalar_witness]: private recursive partial
    sums for the induction in Federer 2.3.3, p. 76. *)
Fixpoint greedy_scalar_witness (R : realType) (r : nat -> R) (t : \bar R) n : R :=
  if n is m.+1 then
    let a := greedy_scalar_witness r t m in
    if (a+r m)%R%:E <= t then (a+r m)%R else a
  else 0%R.

(** Source for [greedy_scalar_exists]: existence of partial sums
    satisfying the greedy recursion of Federer 2.3.3, p. 76.
    Positivity and divergence are only needed for its later conclusions. *)
Theorem greedy_scalar_exists (R : realType) (r : nat -> R) (t : \bar R) :
  exists s, is_greedy_scalar_expansion r t s.
Proof. exists (greedy_scalar_witness r t); constructor; by []. Qed.
