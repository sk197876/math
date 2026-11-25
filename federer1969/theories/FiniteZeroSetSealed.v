(** Federer (1969), 3.4.5, p. 320: the
    original finite zero set behind an opaque membership law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import FiniteAnalyticVarietyUP FiniteZeroSetExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FiniteZeroSetSignature.
(** Source for [value]: var(U,F), 3.4.5, p. 320. *)
Parameter value:forall (A:zmodType) (X:Type),set X->forall I:finType,(I->X->A)->set X.
(** Source for [laws]: the exact simultaneous-equation
    membership law, 3.4.5, p. 320. *)
Parameter laws:forall (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A),
  is_original_zero_set U f (@value A X U I f).
End FiniteZeroSetSignature.
Module FiniteZeroSet:FiniteZeroSetSignature.
(** Source for [value]: private witness of the proved
    zero-set existence theorem, 3.4.5, p. 320. *)
Definition value (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A):=
  projT1 (cid (@original_zero_set_exists A X U I f)).
(** Source for [laws]: the chosen set satisfies the
    original membership specification, 3.4.5, p. 320. *)
Lemma laws (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A):
  is_original_zero_set U f (@value A X U I f).
Proof. exact:(projT2 (cid (@original_zero_set_exists A X U I f))). Qed.
End FiniteZeroSet.
