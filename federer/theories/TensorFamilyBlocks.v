(** Federer 1.1.2, p. 10: splitting an arbitrary heterogeneous argument
    list into its first m and last k coordinates. Supporting bookkeeping
    for the printed grouping isomorphism; no tensor implementation enters. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorFamily TensorFamilyPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Blocks.
Variable K : fieldType.
Variables m k : nat.
Variable V : 'I_(m+k) -> lmodType K.
Local Notation A := {dffun forall i : 'I_m, V (lshift k i)}.
Local Notation B := {dffun forall i : 'I_k, V (rshift m i)}.
Local Notation C := {dffun forall i, V i}.

(** Source for [tensor_block_left]: Federer 1.1.2, p. 10;
    the first block of arguments, with original factor types retained. *)
Definition tensor_block_left (x : C) : A := [ffun i => x (lshift k i)].

(** Source for [tensor_block_right]: Federer 1.1.2, p. 10;
    the second block of arguments. *)
Definition tensor_block_right (x : C) : B := [ffun i => x (rshift m i)].

(** Source for [tensor_block_values]: Federer 1.1.2, p. 10;
    evaluation of a pair of blocks at a disjoint block index. *)
Definition tensor_block_values (a : A) (b : B) (s : 'I_m + 'I_k) : V (unsplit s) :=
  match s with inl i => a i | inr j => b j end.

(** Source for [tensor_block_join]: Federer 1.1.2, p. 10;
    concatenation of the two argument blocks, preserving every factor. *)
Definition tensor_block_join (a : A) (b : B) : C :=
  [ffun i => tensor_index_transport (splitK i) (tensor_block_values a b (split i))].

(** Source for [tensor_block_join_unsplit]: Federer 1.1.2, p. 10;
    concatenation evaluates to the argument at its actual block index. *)
Lemma tensor_block_join_unsplit a b s :
  tensor_block_join a b (unsplit s) = tensor_block_values a b s.
Proof.
rewrite /tensor_block_join ffunE.
rewrite (eq_irrelevance (splitK (unsplit s)) (congr1 unsplit (unsplitK s))).
generalize (unsplitK s); move: (split (unsplit s))=> r e.
by case: s / e.
Qed.

(** Source for [tensor_block_join_left]: Federer 1.1.2, p. 10;
    the first block is unchanged by concatenation. *)
Lemma tensor_block_join_left a b : tensor_block_left (tensor_block_join a b) = a.
Proof.
apply/ffunP=> i; rewrite /tensor_block_left ffunE.
exact: (tensor_block_join_unsplit a b (inl i)).
Qed.

(** Source for [tensor_block_join_right]: Federer 1.1.2, p. 10;
    the second block is unchanged by concatenation. *)
Lemma tensor_block_join_right a b : tensor_block_right (tensor_block_join a b) = b.
Proof.
apply/ffunP=> i; rewrite /tensor_block_right ffunE.
exact: (tensor_block_join_unsplit a b (inr i)).
Qed.

(** Source for [tensor_block_joinK]: Federer 1.1.2, p. 10;
    splitting and concatenating restores the entire original list. *)
Lemma tensor_block_joinK x :
  tensor_block_join (tensor_block_left x) (tensor_block_right x) = x.
Proof.
apply/ffunP=> i; rewrite /tensor_block_join ffunE.
have h s : tensor_block_values (tensor_block_left x) (tensor_block_right x) s =
    x (unsplit s).
  by case: s=> j; rewrite /tensor_block_values /tensor_block_left /tensor_block_right ffunE.
by rewrite h tensor_index_transport_value.
Qed.

(** Source for [tensor_block_ext]: Federer 1.1.2, p. 10;
    equality of both blocks determines the original argument list. *)
Lemma tensor_block_ext (x y : C) :
  tensor_block_left x = tensor_block_left y ->
  tensor_block_right x = tensor_block_right y -> x = y.
Proof. by move=> hl hr; rewrite -(tensor_block_joinK x) -(tensor_block_joinK y) hl hr. Qed.

(** Source for [tensor_block_left_with_left]: Federer 1.1.2, p. 10;
    a first-block update changes precisely that first-block coordinate. *)
Lemma tensor_block_left_with_left x j (v : V (lshift k j)) :
  tensor_block_left (family_with x v) =
  family_with (tensor_block_left x) v.
Proof.
apply/ffunP=> i; rewrite /tensor_block_left ffunE.
case: (eqVneq j i)=> [<-|hji].
- by rewrite !family_with_in.
- by rewrite !family_with_out ?eq_lshift // ffunE.
Qed.

(** Source for [tensor_block_right_with_left]: Federer 1.1.2, p. 10;
    a first-block update leaves the second block unchanged. *)
Lemma tensor_block_right_with_left x j (v : V (lshift k j)) :
  tensor_block_right (family_with x v) = tensor_block_right x.
Proof.
apply/ffunP=> i; by rewrite /tensor_block_right ffunE family_with_out ?eq_lrshift // ffunE.
Qed.

(** Source for [tensor_block_right_with_right]: Federer 1.1.2, p. 10;
    a second-block update changes precisely its second-block coordinate. *)
Lemma tensor_block_right_with_right x j (v : V (rshift m j)) :
  tensor_block_right (family_with x v) =
  family_with (tensor_block_right x) v.
Proof.
apply/ffunP=> i; rewrite /tensor_block_right ffunE.
case: (eqVneq j i)=> [<-|hji].
- by rewrite !family_with_in.
- by rewrite !family_with_out ?eq_rshift // ffunE.
Qed.

(** Source for [tensor_block_left_with_right]: Federer 1.1.2, p. 10;
    a second-block update leaves the first block unchanged. *)
Lemma tensor_block_left_with_right x j (v : V (rshift m j)) :
  tensor_block_left (family_with x v) = tensor_block_left x.
Proof.
apply/ffunP=> i; by rewrite /tensor_block_left ffunE family_with_out ?eq_rlshift // ffunE.
Qed.

(** Source for [tensor_block_join_with_left]: Federer 1.1.2, p. 10;
    concatenation commutes with a first-block coordinate change. *)
Lemma tensor_block_join_with_left a b j (v : V (lshift k j)) :
  tensor_block_join (family_with a v) b = family_with (tensor_block_join a b) v.
Proof.
apply: tensor_block_ext.
- by rewrite tensor_block_left_with_left !tensor_block_join_left.
- by rewrite tensor_block_right_with_left !tensor_block_join_right.
Qed.

(** Source for [tensor_block_join_with_right]: Federer 1.1.2, p. 10;
    concatenation commutes with a second-block coordinate change. *)
Lemma tensor_block_join_with_right a b j (v : V (rshift m j)) :
  tensor_block_join a (family_with b v) = family_with (tensor_block_join a b) v.
Proof.
apply: tensor_block_ext.
- by rewrite tensor_block_left_with_right !tensor_block_join_left.
- by rewrite tensor_block_right_with_right !tensor_block_join_right.
Qed.
End Blocks.
