(** Federer (1969), 3.1.1, p. 210: the sequence used in the proof of
    the inverse function theorem, specified by its initial value and
    recurrence. This interface makes no convergence assumption. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_inverse_function_iteration]: the displayed
    iteration u_0=0 and u_(n+1)=y-g(u_n) in Federer 3.1.1, p. 210. *)
Record is_inverse_function_iteration (R : fieldType) (X : lmodType R)
    (g : X -> X) (y : X) (u : nat -> X) : Prop := {
  (** Source for [inverse_iteration_zero]: the initial value in
      Federer 3.1.1, p. 210. *)
  inverse_iteration_zero : u 0%N = 0;
  (** Source for [inverse_iteration_step]: the recursive equation
      in Federer 3.1.1, p. 210. *)
  inverse_iteration_step : forall n, u n.+1 = y-g (u n)
}.

(** Source for [inverse_function_iteration_unique]: supporting
    uniqueness of the recursive sequence in Federer 3.1.1, p. 210. *)
Lemma inverse_function_iteration_unique (R : fieldType) (X : lmodType R)
    (g : X -> X) (y : X) (u v : nat -> X) :
  is_inverse_function_iteration g y u ->
  is_inverse_function_iteration g y v -> forall n, u n = v n.
Proof.
move=> hu hv; elim=> [|n ih].
- by rewrite (inverse_iteration_zero hu) (inverse_iteration_zero hv).
- by rewrite (inverse_iteration_step hu) (inverse_iteration_step hv) ih.
Qed.
