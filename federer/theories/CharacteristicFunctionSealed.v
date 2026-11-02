(** Federer (1969), 2.2.14, p. 70: opaque interface for the
    characteristic-function witness. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import CharacteristicFunctionUP CharacteristicFunctionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type CharacteristicFunctionSignature.
(** Source for [value]: abstract characteristic function of
    a set, as defined in Federer 2.2.14, p. 70. *)
Parameter value : forall (R : realType) (X : Type), set X -> X -> R.
(** Source for [laws]: pointwise one/zero laws of the
    characteristic function in Federer 2.2.14, p. 70. *)
Parameter laws : forall (R : realType) (X : Type) (A : set X),
  is_characteristic_function A (@value R X A).
End CharacteristicFunctionSignature.

Module CharacteristicFunction : CharacteristicFunctionSignature.
(** Source for [value]: private selection of the proved
    characteristic-function witness for Federer 2.2.14, p. 70. *)
Definition value (R : realType) (X : Type) (A : set X) :=
  projT1 (cid (@characteristic_function_exists R X A)).
(** Source for [laws]: the selected function satisfies
    the defining laws of Federer 2.2.14, p. 70. *)
Lemma laws (R : realType) (X : Type) (A : set X) :
  is_characteristic_function A (@value R X A).
Proof. exact: projT2 (cid (@characteristic_function_exists R X A)). Qed.
End CharacteristicFunction.
