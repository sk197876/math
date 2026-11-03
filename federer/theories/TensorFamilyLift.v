(** Federer 1.1.1, p. 9, used in 1.1.2, p. 10: the unique linear
    factorisation through an abstract finite-family tensor product. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import TensorUP TensorFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Lift.
Variable K : fieldType.
Variable n : nat.
Variable V : 'I_n -> lmodType K.
Variable T : lmodType K.
Variable mu : {dffun forall i, V i} -> T.
Variable hmu : is_tensor_product_family mu.
Variable Z : lmodType K.
Variable beta : {dffun forall i, V i} -> Z.
Variable hbeta : multilinear beta.

(** Source for [abstract_tensor_family_lift]: Federer 1.1.1, p. 9;
    the uniquely specified factorisation, selected from its proved
    existence. No tensor construction is inspected. *)
Definition abstract_tensor_family_lift : {linear T -> Z} :=
  proj1_sig (cid (tensor_family_universal hmu hbeta)).

(** Source for [abstract_tensor_family_liftE]: Federer 1.1.1, p. 9,
    the defining equation g composed with mu equals beta. *)
Lemma abstract_tensor_family_liftE x :
  abstract_tensor_family_lift (mu x) = beta x.
Proof. exact: (proj1 (proj2_sig (cid (tensor_family_universal hmu hbeta)))). Qed.
End Lift.
