(** Federer (1969), 1.7.11, p. 36: the Cartesian product S times T carries
    the inner product used by the displayed orthonormal basis. Its value is
    the sum of the two factor inner products. This supporting specification
    makes that metric explicit. The ingredient inner-product definitions are
    2.53, p. 18, and 10.1, p. 93. The local erratum contains no correction
    to book p. 36. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_product_inner_product]: Federer 1.7.11,
    p. 36, supporting specification of the inner product on the
    Cartesian product, whose orthonormal basis the proof displays. *)
Record is_product_inner_product (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (D : (V * W)%type -> (V * W)%type -> R) : Prop := {
  product_inner_laws : is_inner_product D;
  product_inner_pairs : forall x y, D x y = B x.1 y.1 + C x.2 y.2
}.

(** Source for [product_inner_unique]: Federer 1.7.11,
    p. 36, supporting uniqueness of the metric on the Cartesian
    product from its defining pair formula. *)
Theorem product_inner_unique (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (D E : (V * W)%type -> (V * W)%type -> R) :
  is_product_inner_product B C D -> is_product_inner_product B C E ->
  forall x y, D x y = E x y.
Proof. move=> hD hE x y; by rewrite (product_inner_pairs hD) (product_inner_pairs hE). Qed.
