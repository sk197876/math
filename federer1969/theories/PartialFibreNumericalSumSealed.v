(** Federer (1969), 3.2.3(2), p. 243: opaque fibre-sum interface exposing only its proved graph specification. The construction stays private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFibreNumericalSumUP PartialFibreNumericalSumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type PartialFibreNumericalSumSignature.
(** Source for [value]: pointwise numerical sum in Federer
    3.2.3(2), p. 243, supplied through its graph laws. *)
Parameter value : forall (R : realType) (X : choiceType) (Y : Type),
  (X -> Y) -> partial_function X (extended_real_line R) -> partial_function Y (extended_real_line R).
(** Source for [laws]: abstract graph laws of the sum used
    in Federer 3.2.3(2), p. 243. *)
Parameter laws : forall (R : realType) (X : choiceType) (Y : Type)
  (p : X -> Y) (u : partial_function X (extended_real_line R)),
  is_partial_fibre_numerical_sum p u (@value R X Y p u).
End PartialFibreNumericalSumSignature.
Module PartialFibreNumericalSum : PartialFibreNumericalSumSignature.
(** Source for [value]: private selection of the proved
    sum witness supporting Federer 3.2.3(2), p. 243. *)
Definition value (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (u : partial_function X (extended_real_line R)) :=
  projT1 (cid (partial_fibre_numerical_sum_exists p u)).
(** Source for [laws]: the witness satisfies the public
    specification needed for Federer 3.2.3(2), p. 243. *)
Lemma laws (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (u : partial_function X (extended_real_line R)) :
  is_partial_fibre_numerical_sum p u (@value R X Y p u).
Proof. exact: projT2 (cid (partial_fibre_numerical_sum_exists p u)). Qed.
End PartialFibreNumericalSum.
