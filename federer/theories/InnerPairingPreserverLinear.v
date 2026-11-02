(** Federer (1969), 3.2.36, p. 273: a map preserving all
    inner products is linear, as required for the isometric-injection
    assertion. This follows solely from 1.7.1--2, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_pairing_preserver_linear]: the linearity step
    behind the isometric-injection assertion of Federer 3.2.36,
    p. 273, from the definite bilinear forms of 1.7.1--2,
    p. 28. Expanding the self-pairing of each additive or scalar
    residual proves that residual zero. No linearity, finite dimension
    or surjectivity of the original map is assumed. *)
Theorem inner_pairing_preserver_linear (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C) (g:V->W):
  (forall x y,C (g x) (g y)=B x y) ->linear g.
Proof.
move=>hInner.
have hAdd x y:g (x+y)=g x+g y.
  apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hC); apply/eqP.
  rewrite !(bilBl (inner_bilinear hC)) !(bilBr (inner_bilinear hC))
    !(bilDl (inner_bilinear hC)) !(bilDr (inner_bilinear hC)) !hInner.
  rewrite !(bilDl (inner_bilinear hB)) !(bilDr (inner_bilinear hB)); ring.
have hScale (a:R) x:g (a*:x)=a*:g x.
  apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hC); apply/eqP.
  rewrite !(bilBl (inner_bilinear hC)) !(bilBr (inner_bilinear hC))
    !(bilZl (inner_bilinear hC)) !(bilZr (inner_bilinear hC)) !hInner.
  rewrite !(bilZl (inner_bilinear hB)) !(bilZr (inner_bilinear hB)); ring.
move=>a x y; by rewrite hAdd hScale.
Qed.
