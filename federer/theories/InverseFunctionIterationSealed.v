(** Opaque recursive sequence for Federer (1969), 3.1.1, p. 210.
    The interface exposes the recurrence, not its implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InverseFunctionIterationUP InverseFunctionIterationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type InverseFunctionIterationSignature.
(** Source for [sequence]: the sequence u_n in Federer 3.1.1, p. 210. *)
Parameter sequence : forall (R : fieldType) (X : lmodType R),
  (X -> X) -> X -> nat -> X.
(** Source for [laws]: initial value and recurrence in Federer
    3.1.1, p. 210, before the geometric convergence argument. *)
Parameter laws : forall (R : fieldType) (X : lmodType R) (g : X -> X) (y : X),
  is_inverse_function_iteration g y (@sequence R X g y).
End InverseFunctionIterationSignature.
Module InverseFunctionIteration : InverseFunctionIterationSignature.
(** Source for [sequence]: private selection of the recursive witness
    of the displayed iteration in Federer 3.1.1, p. 210. *)
Definition sequence (R : fieldType) (X : lmodType R) (g : X -> X) (y : X) :=
  sval (constructive_indefinite_description (inverse_function_iteration_exists g y)).
(** Source for [laws]: the selected sequence satisfies the recurrence
    in Federer 3.1.1, p. 210. *)
Lemma laws (R : fieldType) (X : lmodType R) (g : X -> X) (y : X) :
  is_inverse_function_iteration g y (@sequence R X g y).
Proof. exact: (svalP (constructive_indefinite_description
  (inverse_function_iteration_exists g y))). Qed.
End InverseFunctionIteration.
