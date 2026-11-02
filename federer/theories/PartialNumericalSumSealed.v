(** Opaque pointwise-sum interface for Federer (1969), 2.4.8, p. 84. Source
    context and specification: PartialNumericalSumUP.v. The graph
    construction stays private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialNumericalSumUP PartialNumericalSumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type PartialNumericalSumSignature.
(** Source for [value]: pointwise numerical sum in Federer
    2.4.8, p. 84, supplied through its graph laws. *)
Parameter value : forall (R : realType) (X : Type) (J : choiceType),
  set J -> (J -> partial_function X (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: abstract graph laws of the sum used
    in Federer 2.4.8, p. 84. *)
Parameter laws : forall (R : realType) (X : Type) (J : choiceType)
  (D : set J) (f : J -> partial_function X (extended_real_line R)),
  is_partial_function_numerical_sum D f (@value R X J D f).
End PartialNumericalSumSignature.
Module PartialNumericalSum : PartialNumericalSumSignature.
(** Source for [value]: private selection of the proved
    sum witness supporting Federer 2.4.8, p. 84. *)
Definition value (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :=
  projT1 (cid (partial_numerical_sum_exists D f)).
(** Source for [laws]: the witness satisfies the public
    specification needed for Federer 2.4.8, p. 84. *)
Lemma laws (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum D f (@value R X J D f).
Proof. exact: projT2 (cid (partial_numerical_sum_exists D f)). Qed.
End PartialNumericalSum.
