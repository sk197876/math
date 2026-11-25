(** Federer (1969), 2.10.40, printed p. 200: expand the squared distance
    from b+epsilon u to a for a unit direction u. This supporting quadratic
    identity is proved in an arbitrary real inner-product space, not by
    choosing coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm BilinearNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_unit_perturbation_square]: direct
    scalar expansion in the contact-centre argument
    of 2.10.40, p. 200. In words, the
    perturbation adds epsilon squared and subtracts twice
    epsilon times u dot (a-b) from the original squared distance. *)
Lemma inner_unit_perturbation_square (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u b a : V) (e : R) :
  B u u= 1 -> inner_norm hB (b+e*:u-a)^+2=
    e^+2+inner_norm hB (b-a)^+2-2*e*B u (a-b).
Proof.
move=> hu.
have he : b+e*:u-a=e*:u+(b-a) by rewrite [b+e*:u]addrC addrA.
rewrite he !inner_norm_sqr (inner_quadratic_expansion hB) hu mulr1
  -[b-a]opprB (bilNr (inner_bilinear hB)).
ring.
Qed.
