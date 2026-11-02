(** Private recursive existence witness for the inverse-function
    iteration in Federer (1969), 3.1.1, p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InverseFunctionIterationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inverse_function_iteration_exists]: existence of
    the recursive sequence displayed in Federer 3.1.1, p. 210.
    Recursion supplies only a witness of the abstract recurrence laws. *)
Lemma inverse_function_iteration_exists (R : fieldType) (X : lmodType R)
    (g : X -> X) (y : X) :
  exists u : nat -> X, is_inverse_function_iteration g y u.
Proof.
pose u := fix u (n : nat) : X := if n is k.+1 then y-g (u k) else 0.
exists u; constructor=> //.
Qed.
