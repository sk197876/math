(** Federer (1969), 2.2.14, p. 70: private existence witness for the
    characteristic-function laws. Classical set membership is background;
    later statements use only the laws. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_function_exists]: existence of
    the two-valued map defined in Federer 2.2.14, p. 70.
    A classical case distinction constructs a witness to the
    abstract laws, without adding project axioms. *)
Theorem characteristic_function_exists (R : realType) (X : Type) (A : set X) :
  exists f : X -> R, is_characteristic_function A f.
Proof.
exists (fun x => if asbool (A x) then 1 else 0); constructor=> x hx.
- by rewrite (asboolT hx).
- case: ifP=> // /asboolP hA; exact: False_ind _ (hx hA).
Qed.
