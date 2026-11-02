(** Opaque scalar lower-limit interface supporting Federer (1969), 2.4.6, p.
    84. Source context and abstract specification: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedLowerLimitUP ExtendedLowerLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

Module Type ExtendedLowerLimitSignature.
(** Source for [value]: scalar lower limit in Federer
    2.4.6, p. 84, supplied through its order laws. *)
Parameter value : forall (R : realType), (nat -> \bar R) -> \bar R.
(** Source for [laws]: supremum laws for the scalar lower
    limit in Federer 2.4.6, p. 84. *)
Parameter laws : forall (R : realType) (u : nat -> \bar R),
  is_extended_lower_limit u (@value R u).
End ExtendedLowerLimitSignature.
Module ExtendedLowerLimit : ExtendedLowerLimitSignature.
(** Source for [value]: private selection of the proved
    lower-limit witness supporting Federer 2.4.6, p. 84. *)
Definition value (R : realType) (u : nat -> \bar R) :=
  projT1 (cid (extended_lower_limit_exists u)).
(** Source for [laws]: the selected witness satisfies the
    abstract laws needed in Federer 2.4.6, p. 84. *)
Lemma laws (R : realType) (u : nat -> \bar R) :
  is_extended_lower_limit u (@value R u).
Proof. exact: projT2 (cid (extended_lower_limit_exists u)). Qed.
End ExtendedLowerLimit.
