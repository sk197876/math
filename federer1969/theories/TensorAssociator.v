(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.2, grouping factors; used for the diagram in 1.3.3.
    Both associations are constructed from the tensor universal property. *)
Section Associator.
Variable K : fieldType.
Variables A B C : lmodType K.
Local Notation L := (tensor_space (tensor_space A B) C).
Local Notation R := (tensor_space A (tensor_space B C)).

(** Source for [tensor_associator_inner_bilinear]: Federer (1969), 1.1.2, p.
    10, second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_inner_bilinear (c : C) :
  bilinear (fun a : A => fun b : B => tensor_inj a (tensor_inj b c)).
Proof.
split.
- by move=> b k a a'; rewrite tensor_inj_addl tensor_inj_scalel.
- by move=> a k b b'; rewrite tensor_inj_addl tensor_inj_scalel tensor_inj_addr tensor_inj_scaler.
Qed.
(** Source for [tensor_associator_fun]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Definition or construction used
    to formalise this passage. *)
Definition tensor_associator_fun (x : tensor_space A B) (c : C) : R :=
  tensor_lift (tensor_associator_inner_bilinear c) x.
(** Source for [tensor_associator_funE]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_funE a b c :
  tensor_associator_fun (tensor_inj a b) c = tensor_inj a (tensor_inj b c).
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_associator_fun0]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_fun0 c : tensor_associator_fun 0 c = 0.
Proof. exact: linear0. Qed.
(** Source for [tensor_associator_funD]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_funD x y c :
  tensor_associator_fun (x + y) c = tensor_associator_fun x c + tensor_associator_fun y c.
Proof. exact: linearD. Qed.
(** Source for [tensor_associator_funZ]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_funZ a x c : tensor_associator_fun (a *: x) c = a *: tensor_associator_fun x c.
Proof. exact: linearZ. Qed.
(** Source for [tensor_associator_fun_bilinear]: Federer (1969), 1.1.2, p.
    10, second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_associator_fun_bilinear : bilinear tensor_associator_fun.
Proof.
split; first by move=> c; exact: linearP.
move=> x k c d; elim/tensor_induction: x => [|x y hx hy|a x hx|a b].
- by rewrite !tensor_associator_fun0 scaler0 add0r.
- rewrite !tensor_associator_funD hx hy.
  by rewrite scalerDr addrACA.
- rewrite !tensor_associator_funZ hx scalerDr !scalerA.
  by rewrite (mulrC a k).
- by rewrite !tensor_associator_funE !tensor_inj_addr !tensor_inj_scaler.
Qed.
(** Source for [tensor_associator]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Definition or construction used
    to formalise this passage. *)
Definition tensor_associator : {linear L -> R} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift tensor_associator_fun_bilinear) _.
(** Source for [tensor_associatorE]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_associatorE a b c :
  tensor_associator (tensor_inj (tensor_inj a b) c) = tensor_inj a (tensor_inj b c).
Proof.
exact: eq_trans (@tensor_liftE K (tensor_space A B) C R tensor_associator_fun
  tensor_associator_fun_bilinear (tensor_inj a b) c) (tensor_associator_funE a b c).
Qed.

(** Source for [tensor_unassociator_inner_bilinear]: Federer (1969), 1.1.2,
    p. 10, second displayed isomorphism, grouping factors. In words:
    Grouping consecutive tensor factors gives a canonical linear
    isomorphism, taking a tensor of two blocks to the concatenated tensor.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma tensor_unassociator_inner_bilinear (a : A) :
  bilinear (fun b : B => fun c : C => tensor_inj (tensor_inj a b) c).
Proof.
split.
- by move=> c k b b'; rewrite tensor_inj_addr tensor_inj_scaler tensor_inj_addl tensor_inj_scalel.
- by move=> b k c c'; rewrite tensor_inj_addr tensor_inj_scaler.
Qed.
(** Source for [tensor_unassociator_fun]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Definition or
    construction used to formalise this passage. *)
Definition tensor_unassociator_fun (a : A) (x : tensor_space B C) : L :=
  tensor_lift (tensor_unassociator_inner_bilinear a) x.
(** Source for [tensor_unassociator_funE]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_unassociator_funE a b c :
  tensor_unassociator_fun a (tensor_inj b c) = tensor_inj (tensor_inj a b) c.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_unassociator_fun0]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_unassociator_fun0 a : tensor_unassociator_fun a 0 = 0.
Proof. exact: linear0. Qed.
(** Source for [tensor_unassociator_funD]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_unassociator_funD a x y :
  tensor_unassociator_fun a (x + y) = tensor_unassociator_fun a x + tensor_unassociator_fun a y.
Proof. exact: linearD. Qed.
(** Source for [tensor_unassociator_funZ]: Federer (1969), 1.1.2, p. 10,
    second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_unassociator_funZ a b x : tensor_unassociator_fun a (b *: x) = b *: tensor_unassociator_fun a x.
Proof. exact: linearZ. Qed.
(** Source for [tensor_unassociator_fun_bilinear]: Federer (1969), 1.1.2, p.
    10, second displayed isomorphism, grouping factors. In words: Grouping
    consecutive tensor factors gives a canonical linear isomorphism, taking
    a tensor of two blocks to the concatenated tensor. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma tensor_unassociator_fun_bilinear : bilinear tensor_unassociator_fun.
Proof.
split; last by move=> a; exact: linearP.
move=> x k a d; elim/tensor_induction: x => [|x y hx hy|b x hx|b c].
- by rewrite !tensor_unassociator_fun0 scaler0 add0r.
- rewrite !tensor_unassociator_funD hx hy.
  by rewrite scalerDr addrACA.
- rewrite !tensor_unassociator_funZ hx scalerDr !scalerA.
  by rewrite (mulrC b k).
- by rewrite !tensor_unassociator_funE !tensor_inj_addl !tensor_inj_scalel.
Qed.
(** Source for [tensor_unassociator]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Definition or construction used
    to formalise this passage. *)
Definition tensor_unassociator : {linear R -> L} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift tensor_unassociator_fun_bilinear) _.
(** Source for [tensor_unassociatorE]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_unassociatorE a b c :
  tensor_unassociator (tensor_inj a (tensor_inj b c)) = tensor_inj (tensor_inj a b) c.
Proof.
exact: eq_trans (@tensor_liftE K A (tensor_space B C) L tensor_unassociator_fun
  tensor_unassociator_fun_bilinear a (tensor_inj b c)) (tensor_unassociator_funE a b c).
Qed.

(** Source for [tensor_triple_ext_l]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_triple_ext_l (Z : lmodType K) (f g : {linear L -> Z}) :
  (forall a b c, f (tensor_inj (tensor_inj a b) c) = g (tensor_inj (tensor_inj a b) c)) ->
  forall x, f x = g x.
Proof.
move=> he; apply: (tensor_ext (tensor_exists (tensor_space A B) C) f g) => x c.
elim/tensor_induction: x => [|x y hx hy|a x hx|a b].
- by rewrite tensor_inj0l !linear0.
- by rewrite tensor_inj_addl !linearD hx hy.
- by rewrite tensor_inj_scalel !linearZ hx.
exact: he.
Qed.
(** Source for [tensor_triple_ext_r]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_triple_ext_r (Z : lmodType K) (f g : {linear R -> Z}) :
  (forall a b c, f (tensor_inj a (tensor_inj b c)) = g (tensor_inj a (tensor_inj b c))) ->
  forall x, f x = g x.
Proof.
move=> he; apply: (tensor_ext (tensor_exists A (tensor_space B C)) f g) => a x.
elim/tensor_induction: x => [|x y hx hy|b x hx|b c].
- by rewrite tensor_inj0r !linear0.
- by rewrite tensor_inj_addr !linearD hx hy.
- by rewrite tensor_inj_scaler !linearZ hx.
exact: he.
Qed.
Arguments tensor_triple_ext_l {Z} f g _ x.
Arguments tensor_triple_ext_r {Z} f g _ x.
(** Source for [tensor_associatorK]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_associatorK : cancel tensor_associator tensor_unassociator.
Proof.
apply: (tensor_triple_ext_l (linear_comp tensor_unassociator tensor_associator) (linear_id L)) => a b c.
change (tensor_unassociator (tensor_associator (tensor_inj (tensor_inj a b) c)) = tensor_inj (tensor_inj a b) c).
by rewrite tensor_associatorE tensor_unassociatorE.
Qed.
(** Source for [tensor_unassociatorK]: Federer (1969), 1.1.2, p. 10, second
    displayed isomorphism, grouping factors. In words: Grouping consecutive
    tensor factors gives a canonical linear isomorphism, taking a tensor of
    two blocks to the concatenated tensor. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_unassociatorK : cancel tensor_unassociator tensor_associator.
Proof.
apply: (tensor_triple_ext_r (linear_comp tensor_associator tensor_unassociator) (linear_id R)) => a b c.
change (tensor_associator (tensor_unassociator (tensor_inj a (tensor_inj b c))) = tensor_inj a (tensor_inj b c)).
by rewrite tensor_unassociatorE tensor_associatorE.
Qed.
End Associator.
Arguments tensor_triple_ext_l {K A B C Z} f g _ x.
Arguments tensor_triple_ext_r {K A B C Z} f g _ x.
