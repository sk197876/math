(** Federer (1969), 1.7.11, p. 36: public Cartesian-product metric for the
    difference map and its displayed orthonormal basis. Source context and
    ingredients: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ProductInnerUP ProductInnerSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Interface.
Variable R : realFieldType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.

(** Source for [product_inner]: Federer 1.7.11, p. 36,
    the Cartesian-product metric used in the difference-map proof. *)
Definition product_inner := @ProductInner.product R V W B C hB hC.

(** Source for [product_innerP]: Federer 1.7.11, p. 36,
    the public product metric satisfies its defining specification. *)
Theorem product_innerP : is_product_inner_product B C product_inner.
Proof. exact: ProductInner.laws. Qed.

(** Source for [product_inner_productP]: Federer 1.7.11,
    p. 36, the product metric is an inner product. *)
Theorem product_inner_productP : is_inner_product product_inner.
Proof. exact: product_inner_laws product_innerP. Qed.

(** Source for [product_innerE]: Federer 1.7.11, p. 36,
    supporting pair formula: the inner product is the sum of the
    products of the corresponding components. *)
Theorem product_innerE x y : product_inner x y = B x.1 y.1 + C x.2 y.2.
Proof. exact (@product_inner_pairs R V W B C product_inner product_innerP x y). Qed.
End Interface.
