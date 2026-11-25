(** Federer (1969), 1.7.4, p. 30: the adjoint specified by its defining
    equation, used also by 1.7.3 on that page. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP LinearBasis AdjointUP AdjointConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AdjointSig.
(** Source for [map]: Federer 1.7.4, p. 30, the adjoint
    linear map, specified independently of coordinates. *)
Parameter map : forall (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R),
  is_inner_product B -> is_inner_product C ->
  forall n (b : 'I_n -> V), is_basis b -> {linear V -> U} -> {linear U -> V}.
(** Source for [laws]: Federer 1.7.4, p. 30, the defining
    inner-product equation of the adjoint. *)
Parameter laws : forall (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}),
  is_adjoint B C f (@map R V U B C hB hC n b hb f).
End AdjointSig.
Module Adjoint : AdjointSig.
(** Source for [map]: Federer 1.7.4, p. 30, select the
    proved adjoint witness and hide its coordinate construction. *)
Definition map (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :=
  sval (constructive_indefinite_description
    (@adjoint_witness_exists R V U B C hB hC n b hb f)).
(** Source for [laws]: Federer 1.7.4, p. 30, the chosen
    map satisfies the abstract defining equation. *)
Lemma laws (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  is_adjoint B C f (@map R V U B C hB hC n b hb f).
Proof. exact: (svalP (constructive_indefinite_description
  (@adjoint_witness_exists R V U B C hB hC n b hb f))). Qed.
End Adjoint.
