(** Public iteration used in the inverse-function proof of
    Federer (1969), 3.1.1, p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InverseFunctionIterationUP InverseFunctionIterationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [inverse_function_iteration]: the sequence u_n
    displayed in Federer 3.1.1, p. 210, accessed through its sealed laws. *)
Definition inverse_function_iteration (R : fieldType) (X : lmodType R)
    (g : X -> X) (y : X) := @InverseFunctionIteration.sequence R X g y.

(** Source for [inverse_function_iteration_specification]: the public
    sequence satisfies Federer's recurrence, 3.1.1, p. 210. *)
Theorem inverse_function_iteration_specification (R : fieldType)
    (X : lmodType R) (g : X -> X) (y : X) :
  is_inverse_function_iteration g y (inverse_function_iteration g y).
Proof. exact: InverseFunctionIteration.laws. Qed.
