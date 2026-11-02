(** Federer (1969), 1.7.11, p. 36: existence of the Cartesian-product inner
    product used in the difference-map computation. This construction is a
    witness for the abstract pair formula and is hidden behind a sealed
    module. Source context and the absence of a direct. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws ProductInnerUP TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [product_inner_exists]: Federer 1.7.11,
    p. 36, supporting existence of the product metric, proved
    from the two factor inner-product specifications. *)
Theorem product_inner_exists (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :
  exists D, is_product_inner_product B C D.
Proof.
exists (fun x y : (V * W)%type => B x.1 y.1 + C x.2 y.2).
constructor; last by [].
constructor.
- split=> [y a x z|x a y z] /=.
  + rewrite (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB))
      (bilDl (inner_bilinear hC)) (bilZl (inner_bilinear hC)).
    change (a * B x.1 y.1 + B z.1 y.1 + (a * C x.2 y.2 + C z.2 y.2) =
      a * (B x.1 y.1 + C x.2 y.2) + (B z.1 y.1 + C z.2 y.2)).
    by rewrite mulrDr addrACA.
  + rewrite (bilDr (inner_bilinear hB)) (bilZr (inner_bilinear hB))
      (bilDr (inner_bilinear hC)) (bilZr (inner_bilinear hC)).
    change (a * B x.1 y.1 + B x.1 z.1 + (a * C x.2 y.2 + C x.2 z.2) =
      a * (B x.1 y.1 + C x.2 y.2) + (B x.1 z.1 + C x.2 z.2)).
    by rewrite mulrDr addrACA.
- move=> x y; by rewrite (inner_symmetric hB) (inner_symmetric hC).
- move=> [x y] /=.
  rewrite lt_def (addr_ge0 (inner_nonnegative hB x) (inner_nonnegative hC y)) andbT.
  rewrite (paddr_eq0 (inner_nonnegative hB x) (inner_nonnegative hC y))
    (inner_self_eq0 hB) (inner_self_eq0 hC).
  by rewrite xpair_eqE.
Qed.
