(** Federer (1969), 1.7.10, p. 35: the endomorphism f associated with a
    bilinear form S satisfies B(f(x),y)=S(x,y), where B is the fixed inner
    product. The working erratum has no correction to this item. This
    specification does not assume that S is symmetric. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AdjointLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_bilinear_representative]: Federer 1.7.10,
    p. 35, last display: the associated linear endomorphism is
    characterised by its inner products with arbitrary vectors. *)
Definition is_bilinear_representative (R : fieldType) (V : lmodType R)
    (B S : V -> V -> R) (f : {linear V -> V}) :=
  forall x y, B (f x) y = S x y.

(** Source for [bilinear_representative_unique]: Federer 1.7.10,
    p. 35, supporting uniqueness of the endomorphism used in the
    definition of discriminant and trace. *)
Theorem bilinear_representative_unique (R : realFieldType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (f g : {linear V -> V}) :
  is_bilinear_representative B S f -> is_bilinear_representative B S g -> f =1 g.
Proof.
move=> hf hg x; apply: (@inner_vectors_ext R V B hB) => y.
by rewrite (inner_symmetric hB y (f x)) (inner_symmetric hB y (g x)) hf hg.
Qed.
