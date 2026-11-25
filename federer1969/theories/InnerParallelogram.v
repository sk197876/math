(** Federer (1969), 1.7.13, p. 37: the parallelogram identity in the
    diameter estimate for the sets C_s. This supporting identity follows
    from the bilinear expansions of 1.7.1, p. 28, for any inner-product
    space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm BilinearNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_parallelogram]: Federer 1.7.13,
    p. 37, equality in the displayed diameter computation:
    the sum of squared norms of x+y and x-y equals twice
    the sum of squared norms of x and y. *)
Theorem inner_parallelogram (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (x y : V) :
  inner_norm hB (x+y)^+2 + inner_norm hB (x-y)^+2 =
    (2 : R) * (inner_norm hB x^+2 + inner_norm hB y^+2).
Proof.
rewrite !inner_norm_sqr !(inner_sum_square hB)
  (bilNl (inner_bilinear hB)) !(bilNr (inner_bilinear hB)) opprK -opprD.
rewrite mulr_natl mulr2n.
rewrite [B x x + (B x y + B x y) + B y y]addrAC
  [B x x - (B x y + B x y) + B y y]addrAC addrACA subrr addr0.
by [].
Qed.
