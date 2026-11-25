(** Federer 1.1.2, printed p. 10: permuting an arbitrary finite family of
    factors gives a linear isomorphism, with the displayed pure-tensor law.
    Only the independent tensor universal properties enter the proof. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP TensorFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Reindex.
Variable K : fieldType.
Variable n : nat.
Variable V : 'I_n -> lmodType K.
Variable p : 'S_n.

(** Source for [tensor_index_transport]: Federer 1.1.2, p. 10, permutation
    isomorphism; supporting dependent-type bookkeeping, not a new object. *)
Definition tensor_index_transport i j (e : i = j) (v : V i) : V j :=
  match e with erefl => v end.

(** Source for [tensor_index_transport_value]: Federer 1.1.2, p. 10;
    transporting a coordinate along equality retains that coordinate. *)
Lemma tensor_index_transport_value (x : {dffun forall i, V i}) i j (e : i = j) :
  tensor_index_transport e (x i) = x j.
Proof. by case: j / e. Qed.

(** Source for [tensor_permute_arguments]: Federer 1.1.2, p. 10, the
    argument list (v_lambda(1),...,v_lambda(n)) for every permutation. *)
Definition tensor_permute_arguments (x : {dffun forall i, V i}) :
    {dffun forall i, V (p i)} := [ffun i => x (p i)].

(** Source for [tensor_unpermute_arguments]: Federer 1.1.2, p. 10;
    inverse coordinate permutation, with equality transport made explicit. *)
Definition tensor_unpermute_arguments (y : {dffun forall i, V (p i)}) :
    {dffun forall i, V i} :=
  [ffun i => tensor_index_transport (permKV p i) (y ((p^-1)%g i))].

(** Source for [tensor_unpermute_permute]: Federer 1.1.2, p. 10;
    the inverse permutation restores every original argument. *)
Lemma tensor_unpermute_permute :
  cancel tensor_permute_arguments tensor_unpermute_arguments.
Proof.
move=> x; apply/ffunP=> i.
by rewrite /tensor_unpermute_arguments /tensor_permute_arguments !ffunE
  tensor_index_transport_value.
Qed.

(** Source for [tensor_permute_unpermute]: Federer 1.1.2, p. 10;
    the permutation restores every argument of the reordered family. *)
Lemma tensor_permute_unpermute :
  cancel tensor_unpermute_arguments tensor_permute_arguments.
Proof.
move=> y; apply/ffunP=> i.
rewrite /tensor_permute_arguments /tensor_unpermute_arguments !ffunE.
rewrite (eq_irrelevance (permKV p (p i)) (congr1 p (permK p i))).
generalize (permK p i); move: ((p^-1)%g (p i)) => j e.
by case: i / e.
Qed.

(** Source for [tensor_permute_with]: Federer 1.1.2, p. 10;
    changing an original argument changes exactly its reordered coordinate. *)
Lemma tensor_permute_with x j (v : V (p j)) :
  tensor_permute_arguments (family_with x v) =
  family_with (tensor_permute_arguments x) v.
Proof.
apply/ffunP=> i; rewrite /tensor_permute_arguments ffunE.
case: (eqVneq j i)=> [<-|hji].
- by rewrite !family_with_in.
- by rewrite !family_with_out ?(inj_eq (@perm_inj _ p)) // ffunE.
Qed.

(** Source for [tensor_unpermute_with]: Federer 1.1.2, p. 10;
    inverse permutation respects each varying argument. *)
Lemma tensor_unpermute_with y j (v : V (p j)) :
  tensor_unpermute_arguments (family_with y v) =
  family_with (tensor_unpermute_arguments y) v.
Proof.
apply: (can_inj tensor_unpermute_permute).
by rewrite tensor_permute_with !tensor_permute_unpermute.
Qed.

(** Source for [multilinear_permute_arguments]: Federer 1.1.2, p. 10;
    reordered pure products are multilinear in the original arguments. *)
Lemma multilinear_permute_arguments (Z : lmodType K)
    (f : {dffun forall i, V (p i)} -> Z) :
  multilinear f -> multilinear (fun x => f (tensor_permute_arguments x)).
Proof.
move=> hf x i; have [j <-] : exists j, p j = i.
  by exists ((p^-1)%g i); rewrite permKV.
move=> a v w; rewrite !tensor_permute_with; exact: hf.
Qed.

(** Source for [multilinear_unpermute_arguments]: Federer 1.1.2, p. 10;
    inverse-reordered pure products are multilinear. *)
Lemma multilinear_unpermute_arguments (Z : lmodType K)
    (f : {dffun forall i, V i} -> Z) :
  multilinear f -> multilinear (fun y => f (tensor_unpermute_arguments y)).
Proof. move=> hf y j a v w; rewrite !tensor_unpermute_with; exact: hf. Qed.

(** Source for [tensor_family_permutation_isomorphism]: Federer 1.1.2,
    p. 10, first displayed isomorphism. For any permutation and tensor
    products specified by their universal properties, mutually inverse
    linear maps permute the factors of every pure tensor as printed. *)
Theorem tensor_family_permutation_isomorphism
    (T U : lmodType K) (mu : {dffun forall i, V i} -> T)
    (nu : {dffun forall i, V (p i)} -> U) :
  is_tensor_product_family mu -> is_tensor_product_family nu ->
  exists (F : {linear T -> U}) (G : {linear U -> T}),
    (forall x, F (mu x) = nu (tensor_permute_arguments x)) /\
    (forall y, G (nu y) = mu (tensor_unpermute_arguments y)) /\
    cancel F G /\ cancel G F.
Proof.
move=> hmu hnu.
have [F [hF _]] := tensor_family_universal hmu
  (multilinear_permute_arguments (tensor_family_multilinear hnu)).
have [G [hG _]] := tensor_family_universal hnu
  (multilinear_unpermute_arguments (tensor_family_multilinear hmu)).
exists F, G; split=> //; split=> //; split.
- apply: (tensor_family_ext hmu (linear_comp G F) (linear_id _))=> x /=.
  by rewrite hF hG tensor_unpermute_permute.
- apply: (tensor_family_ext hnu (linear_comp F G) (linear_id _))=> y /=.
  by rewrite hG hF tensor_permute_unpermute.
Qed.
End Reindex.
