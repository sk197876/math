(** Federer (1969), 1.7.6, p. 33: sealed existence witness for the operator
    norm. Only the number and its abstract norm laws are exported; the
    compactness construction is hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InnerProductUP LinearBasis OperatorNormUP
  OperatorNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type OperatorNormSig.
(** Source for [value]: Federer 1.7.6, p. 33, the norm number
    for a map with finite-dimensional source. *)
Parameter value : forall (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}), R.
(** Source for [laws]: Federer 1.7.6, p. 33, the exported
    number satisfies the abstract upper-bound and attainment laws. *)
Parameter laws : forall (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}),
  is_operator_norm hB hC f (@value R V U B C hB hC n b hb f).
End OperatorNormSig.
Module OperatorNorm : OperatorNormSig.
(** Source for [value]: Federer 1.7.6, p. 33, choose the
    proved norm witness inside an opaque module. *)
Definition value (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :=
  sval (constructive_indefinite_description (operator_norm_exists hB hC hb f)).
(** Source for [laws]: Federer 1.7.6, p. 33, the selected
    witness obeys the abstract norm specification. *)
Lemma laws (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  is_operator_norm hB hC f (@value R V U B C hB hC n b hb f).
Proof. exact: (svalP (constructive_indefinite_description
  (operator_norm_exists hB hC hb f))). Qed.
End OperatorNorm.
