(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The interface is independent of any construction and of finite dimension. *)
Section UniversalProperty.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [bilinear]: Federer (1969), 1.1.1, p. 8, opening definition.
    In words: An n-linear function is linear in each argument when all other
    arguments are fixed. Definition or construction used to formalise this
    passage. *)
Definition bilinear (T : lmodType K) (mu : V -> W -> T) : Prop :=
  (forall w, linear (mu^~ w)) /\ (forall v, linear (mu v)).

(** Source for [is_tensor_product]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Record is_tensor_product (T : lmodType K) (mu : V -> W -> T) : Prop := {
  tensor_bilinear : bilinear mu;
  tensor_universal :
    forall (Z : lmodType K) (beta : V -> W -> Z), bilinear beta ->
    exists f : {linear T -> Z},
      (forall v w, f (mu v w) = beta v w) /\
      (forall g : {linear T -> Z},
        (forall v w, g (mu v w) = beta v w) -> forall t, g t = f t)
}.

(** Source for [bilinear_post]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma bilinear_post (T Z : lmodType K) (mu : V -> W -> T)
    (f : {linear T -> Z}) :
  bilinear mu -> bilinear (fun v w => f (mu v w)).
Proof.
move=> [mu1 mu2]; split.
  by move=> w a v v'; rewrite (mu1 w) linearP.
by move=> v a w w'; rewrite (mu2 v) linearP.
Qed.

(** Source for [tensor_ext]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_ext (T : lmodType K) (mu : V -> W -> T)
    (H : is_tensor_product mu) (Z : lmodType K)
    (f g : {linear T -> Z}) :
  (forall v w, f (mu v w) = g (mu v w)) -> forall t, f t = g t.
Proof.
move=> e.
have [h [hmu huniq]] := tensor_universal H
  (bilinear_post g (tensor_bilinear H)).
by move=> t; rewrite (huniq f e) (huniq g (fun v w => erefl _)).
Qed.
End UniversalProperty.
Arguments tensor_ext {K V W T mu} H {Z} f g _ t.

Section LinearComposition.
Variable K : fieldType.
Variables U V W : lmodType K.

(** Source for [linear_id]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition linear_id : {linear V -> V} := GRing.Linear.clone _ _ _ _ (@idfun V) _.
(** Source for [linear_comp]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition linear_comp (f : {linear V -> W}) (g : {linear U -> V}) :
    {linear U -> W} := GRing.Linear.clone _ _ _ _ (f \o g) _.
End LinearComposition.

(** A linear isomorphism is recorded by mutually inverse linear maps. *)
Section Uniqueness.
Variable K : fieldType.
Variables V W T T' : lmodType K.
Variables (mu : V -> W -> T) (mu' : V -> W -> T').
Hypotheses (H : is_tensor_product mu) (H' : is_tensor_product mu').

(** Source for [tensor_unique]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_unique :
  exists (f : {linear T -> T'}) (g : {linear T' -> T}),
    (forall v w, f (mu v w) = mu' v w) /\
    (forall v w, g (mu' v w) = mu v w) /\
    cancel f g /\ cancel g f /\
    (forall f' : {linear T -> T'},
      (forall v w, f' (mu v w) = mu' v w) -> forall t, f' t = f t).
Proof.
have [f [fmu fu]] := tensor_universal H (tensor_bilinear H').
have [g [gmu gu]] := tensor_universal H' (tensor_bilinear H).
exists f, g; split=> //; split=> //; split.
  apply: (tensor_ext H (linear_comp g f) (linear_id T)) => v w /=.
  by rewrite fmu gmu.
split.
  apply: (tensor_ext H' (linear_comp f g) (linear_id T')) => v w /=.
  by rewrite gmu fmu.
exact: fu.
Qed.
End Uniqueness.
