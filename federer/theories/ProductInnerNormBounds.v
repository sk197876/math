(** Federer (1969), 1.7.11, p. 36: the actual
    Cartesian inner metric. Supporting coordinate contraction bounds
    for the product charts of 3.2.47, p. 282,
    and the product domain of 3.2.48, p. 284.
    The factors need not be finite dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import Hom InnerProductUP InnerProductLaws InnerNorm ProductInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [product_inner_first_norm_bound]: projection onto
    the first factor is a contraction for the product inner
    metric of 1.7.11, p. 36; supporting 3.2.47–48,
    pp. 282–284. *)
Lemma product_inner_first_norm_bound (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) (z:V*W):
  inner_norm hB z.1<=inner_norm (product_inner_productP hB hC) z.
Proof.
rewrite -(ler_sqr (inner_norm_nonnegative hB z.1)
  (inner_norm_nonnegative (product_inner_productP hB hC) z)) !inner_norm_sqr product_innerE.
have hOther:=inner_nonnegative hC z.2; by nra.
Qed.

(** Source for [product_inner_second_norm_bound]: projection onto
    the second factor is a contraction, supporting the actual
    product metric in 3.2.47–48, pp. 282–284,
    by the Cartesian sum law of 1.7.11, p. 36. *)
Lemma product_inner_second_norm_bound (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) (z:V*W):
  inner_norm hC z.2<=inner_norm (product_inner_productP hB hC) z.
Proof.
rewrite -(ler_sqr (inner_norm_nonnegative hC z.2)
  (inner_norm_nonnegative (product_inner_productP hB hC) z)) !inner_norm_sqr product_innerE.
have hOther:=inner_nonnegative hB z.1; by nra.
Qed.

(** Source for [product_first_projection_hom]: the actual linear
    first coordinate in the product charts and product map of
    3.2.47–48, pp. 282–284. *)
Definition product_first_projection_hom (R:realType) (V W:lmodType R):Hom [the lmodType R of (V*W)%type] V.
Proof.
apply:(@HomMap R [the lmodType R of (V*W)%type] V (@fst V W)).
by apply/asboolP=>c x y.
Defined.

(** Source for [product_second_projection_hom]: the actual linear
    second coordinate in the product charts and product map of
    3.2.47–48, pp. 282–284. *)
Definition product_second_projection_hom (R:realType) (V W:lmodType R):Hom [the lmodType R of (V*W)%type] W.
Proof.
apply:(@HomMap R [the lmodType R of (V*W)%type] W (@snd V W)).
by apply/asboolP=>c x y.
Defined.
