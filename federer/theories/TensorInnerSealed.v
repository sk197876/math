(** Federer (1969), 1.7.9, p. 35: sealed tensor inner product. Only the
    product and its abstract characterising laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP TensorProduct TensorInnerUP TensorInnerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type TensorInnerSig.
(** Source for [product]: Federer 1.7.9, p. 35,
    the characterised inner product on the tensor space. *)
Parameter product : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C),
  tensor_space V W -> tensor_space V W -> R.
(** Source for [laws]: Federer 1.7.9, p. 35,
    the exported product satisfies the abstract specification. *)
Parameter laws : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C),
  is_tensor_inner_product B C (@product R V W B C hB hC).
End TensorInnerSig.
Module TensorInner : TensorInnerSig.
(** Source for [product]: Federer 1.7.9, p. 35,
    select the proved existence witness inside the sealed module. *)
Definition product (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :=
  sval (constructive_indefinite_description (tensor_inner_exists hB hC)).
(** Source for [laws]: Federer 1.7.9, p. 35,
    the selected witness obeys the characterising tensor-product laws. *)
Lemma laws (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :
  is_tensor_inner_product B C (@product R V W B C hB hC).
Proof. exact: (svalP (constructive_indefinite_description (tensor_inner_exists hB hC))). Qed.
End TensorInner.
