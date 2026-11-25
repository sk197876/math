(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP TensorProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Functoriality, first at the level of the abstract universal property. *)
Section AbstractMaps.
Variable K : fieldType.
Variables V W V' W' T T' : lmodType K.
Variables (mu : V -> W -> T) (mu' : V' -> W' -> T').

(** Source for [bilinear_pre]: Federer (1969), 1.1.1, p. 9, final naturality
    paragraph and displayed formula. In words: Linear maps on the factors
    induce a unique linear map of tensor products sending each pure tensor
    to the tensor of the images. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma bilinear_pre (f : {linear V -> V'}) (g : {linear W -> W'}) :
  bilinear mu' -> bilinear (fun v w => mu' (f v) (g w)).
Proof.
move=> [b1 b2]; split.
  by move=> w a v v'; rewrite linearP /= b1.
by move=> v a w w'; rewrite linearP /= b2.
Qed.

(** Source for [tensor_map_exists]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph and displayed formula. In words: Linear maps on the
    factors induce a unique linear map of tensor products sending each pure
    tensor to the tensor of the images. Supporting lemma for this passage;
    not separately stated in the book. *)
Theorem tensor_map_exists (H : is_tensor_product mu)
    (H' : is_tensor_product mu')
    (f : {linear V -> V'}) (g : {linear W -> W'}) :
  exists h : {linear T -> T'},
    (forall v w, h (mu v w) = mu' (f v) (g w)) /\
    (forall h' : {linear T -> T'},
      (forall v w, h' (mu v w) = mu' (f v) (g w)) -> forall t, h' t = h t).
Proof.
apply: (tensor_universal H).
exact: bilinear_pre f g (tensor_bilinear H').
Qed.
End AbstractMaps.

(** Chosen induced maps for the independently constructed tensor product. *)
Section InducedMap.
Variable K : fieldType.
Variables V W V' W' : lmodType K.
Variables (f : {linear V -> V'}) (g : {linear W -> W'}).

(** Source for [tensor_map]: Federer (1969), 1.1.1, p. 9, final naturality
    paragraph and displayed formula. In words: Linear maps on the factors
    induce a unique linear map of tensor products sending each pure tensor
    to the tensor of the images. Definition or construction used to
    formalise this passage. *)
Definition tensor_map : {linear tensor_space V W -> tensor_space V' W'} :=
  GRing.Linear.clone _ _ _ _
    (tensor_lift (bilinear_pre f g (tensor_inj_bilinear V' W'))) _.

(** Source for [tensor_mapE]: Federer (1969), 1.1.1, p. 9, final naturality
    paragraph and displayed formula. In words: Linear maps on the factors
    induce a unique linear map of tensor products sending each pure tensor
    to the tensor of the images. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_mapE v w :
  tensor_map (tensor_inj v w) = tensor_inj (f v) (g w).
Proof. exact: tensor_liftE. Qed.
End InducedMap.

Section FunctorLaws.
Variable K : fieldType.
Variables V W V' W' V'' W'' : lmodType K.

(** Source for [tensor_map_id]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph. In words: The maps induced on tensor products act
    componentwise on pure tensors; identities and composition therefore pass
    to tensor products. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma tensor_map_id (t : tensor_space V W) :
  tensor_map (linear_id V) (linear_id W) t = t.
Proof.
apply: (tensor_ext (tensor_exists V W)
  (tensor_map (linear_id V) (linear_id W)) (linear_id _)) t.
by move=> v w; rewrite tensor_mapE.
Qed.

(** Source for [tensor_map_comp]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph. In words: The maps induced on tensor products act
    componentwise on pure tensors; identities and composition therefore pass
    to tensor products. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma tensor_map_comp (f : {linear V -> V'}) (g : {linear W -> W'})
    (f' : {linear V' -> V''}) (g' : {linear W' -> W''})
    (t : tensor_space V W) :
  tensor_map f' g' (tensor_map f g t) =
  tensor_map (linear_comp f' f) (linear_comp g' g) t.
Proof.
apply: (tensor_ext (tensor_exists V W)
  (linear_comp (tensor_map f' g') (tensor_map f g))
  (tensor_map (linear_comp f' f) (linear_comp g' g))) t.
by move=> v w /=; rewrite !tensor_mapE tensor_liftE.
Qed.
End FunctorLaws.

Section Symmetry.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [tensor_flip_bilinear]: Federer (1969), 1.1.2, p. 10, first
    displayed isomorphism, permutation of factors. In words: Permuting the
    tensor factors gives a linear isomorphism taking a pure tensor to the
    pure tensor with its entries in that order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_flip_bilinear : bilinear (fun v : V => fun w : W => tensor_inj w v).
Proof. by have [b1 b2] := tensor_inj_bilinear W V; split. Qed.

(** Source for [tensor_swap]: Federer (1969), 1.1.2, p. 10, first displayed
    isomorphism, permutation of factors. In words: Permuting the tensor
    factors gives a linear isomorphism taking a pure tensor to the pure
    tensor with its entries in that order. Definition or construction used
    to formalise this passage. *)
Definition tensor_swap : {linear tensor_space V W -> tensor_space W V} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift tensor_flip_bilinear) _.

(** Source for [tensor_swapE]: Federer (1969), 1.1.2, p. 10, first displayed
    isomorphism, permutation of factors. In words: Permuting the tensor
    factors gives a linear isomorphism taking a pure tensor to the pure
    tensor with its entries in that order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_swapE v w : tensor_swap (tensor_inj v w) = tensor_inj w v.
Proof. exact: tensor_liftE. Qed.
End Symmetry.

Section SymmetryLaws.
Variable K : fieldType.
Variables V W V' W' : lmodType K.

(** Source for [tensor_swapK]: Federer (1969), 1.1.2, p. 10, first displayed
    isomorphism, permutation of factors. In words: Permuting the tensor
    factors gives a linear isomorphism taking a pure tensor to the pure
    tensor with its entries in that order. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_swapK : cancel (tensor_swap V W) (tensor_swap W V).
Proof.
apply: (tensor_ext (tensor_exists V W)
  (linear_comp (tensor_swap W V) (tensor_swap V W)) (linear_id _)).
by move=> v w /=; rewrite !tensor_swapE.
Qed.

(** Source for [tensor_swap_natural]: Federer (1969), 1.1.2, p. 10, first
    displayed isomorphism, permutation of factors. In words: Permuting the
    tensor factors gives a linear isomorphism taking a pure tensor to the
    pure tensor with its entries in that order. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma tensor_swap_natural (f : {linear V -> V'}) (g : {linear W -> W'})
    (t : tensor_space V W) :
  tensor_swap V' W' (tensor_map f g t) =
  tensor_map g f (tensor_swap V W t).
Proof.
apply: (tensor_ext (tensor_exists V W)
  (linear_comp (tensor_swap V' W') (tensor_map f g))
  (linear_comp (tensor_map g f) (tensor_swap V W))) t.
by move=> v w /=; rewrite !tensor_mapE !tensor_swapE tensor_mapE.
Qed.
End SymmetryLaws.
